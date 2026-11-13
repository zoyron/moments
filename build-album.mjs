// Run it after adding or removing files: node build-album.mjs
//
// 1. Prepares assets/ for the web (macOS only, with its built-in sips and avconvert):
//    HEIC photos become JPG, photos over 2400px are shrunk, and videos that aren't
//    720p H.264 (iPhone HEVC, .mov, 1080p/4K) are converted. The converted file replaces
//    the original (your phone still has it). Files already fine are left alone.
// 2. Writes album.js: one spread per photo or video, oldest first by when it was taken.
//    The date comes from the camera's own record inside the file (photo EXIF, video header);
//    files without one (WhatsApp images, screenshots) fall back to the file's modified date.
import { readdirSync, writeFileSync, readFileSync, openSync, readSync, writeSync, closeSync, statSync,
  existsSync, renameSync, unlinkSync, utimesSync } from 'node:fs';
import { execFileSync } from 'node:child_process';

const PHOTO = ['jpg', 'jpeg', 'png', 'webp', 'avif', 'gif'];
const VIDEO = ['mp4', 'webm'];
const MAX_PHOTO = 2400;   // the book never draws a photo wider than ~2000px
const MAX_VIDEO = 720;    // the short side of a converted video

// ---- photo: EXIF DateTimeOriginal (falls back to the plain DateTime tag) ----
function exifDate(buf) {
  const i = buf.indexOf('Exif\0\0');
  const t = i >= 0 ? i + 6 : buf.indexOf('II*\0') >= 0 ? buf.indexOf('II*\0') : buf.indexOf('MM\0*');
  if (t < 0 || t + 8 > buf.length) return null;
  const le = buf.toString('latin1', t, t + 2) === 'II';
  const u16 = o => (le ? buf.readUInt16LE(t + o) : buf.readUInt16BE(t + o));
  const u32 = o => (le ? buf.readUInt32LE(t + o) : buf.readUInt32BE(t + o));
  const tags = ifd => {
    const out = {};
    if (t + ifd + 2 > buf.length) return out;
    const n = u16(ifd);
    for (let k = 0; k < n; k++) {
      const e = ifd + 2 + k * 12;
      if (t + e + 12 > buf.length) break;
      out[u16(e)] = { count: u32(e + 4), value: u32(e + 8) };
    }
    return out;
  };
  // strings over 4 bytes sit at an offset; shorter ones (none we read) would be inline
  const text = (tag, n) => (tag && tag.count >= n && t + tag.value + n <= buf.length ? buf.toString('latin1', t + tag.value, t + tag.value + n) : null);
  try {
    const ifd0 = tags(u32(4));
    const sub = ifd0[0x8769] ? tags(ifd0[0x8769].value) : {};
    const when = parseExif(text(sub[0x9003], 19) || text(ifd0[0x0132], 19));
    // phones also record the time zone ("+05:30"), which keeps photos in step with videos (stored in UTC)
    const tz = (text(sub[0x9011], 6) || '').match(/^([+-])(\d{2}):(\d{2})/);
    return when && tz ? when - (tz[1] === '-' ? -1 : 1) * (tz[2] * 60 + +tz[3]) * 60000 : when;
  } catch { return null; }
}
function parseExif(s) {
  const m = s && s.match(/^(\d{4}):(\d{2}):(\d{2}) (\d{2}):(\d{2}):(\d{2})/);
  if (!m || m[1] === '0000') return null;
  return Date.UTC(+m[1], m[2] - 1, +m[3], +m[4], +m[5], +m[6]);
}

// ---- video: walk the MP4/MOV boxes for the creation time, size and codec ----
const MP4_EPOCH = 2082844800;   // seconds from 1904 (the MP4 clock) to 1970
function mp4Info(path) {
  const fd = openSync(path, 'r'), size = statSync(path).size, head = Buffer.alloc(16);
  const info = { created: null, createdAt: -1, createdWide: false, w: 0, h: 0, codec: null };
  const read = (at, n) => { const b = Buffer.alloc(n); readSync(fd, b, 0, n, at); return b; };
  const walk = (from, to) => {
    for (let at = from; at + 8 <= to;) {
      readSync(fd, head, 0, 16, at);
      let len = head.readUInt32BE(0), hdr = 8;
      if (len === 1) { len = Number(head.readBigUInt64BE(8)); hdr = 16; }
      else if (len === 0) len = to - at;
      if (len < hdr) break;
      const type = head.toString('latin1', 4, 8), body = at + hdr;
      if (type === 'mvhd') {
        const v = read(body, 12);
        info.createdWide = v[0] === 1;
        info.createdAt = body + 4;
        const secs = info.createdWide ? Number(v.readBigUInt64BE(4)) : v.readUInt32BE(4);
        info.created = secs > 0 ? (secs - MP4_EPOCH) * 1000 : null;
      } else if (type === 'tkhd') {
        const v = read(body, len - hdr);
        const w = v.readUInt32BE(v.length - 8) / 65536, h = v.readUInt32BE(v.length - 4) / 65536;
        if (w && h && !info.w) { info.w = w; info.h = h; }
      } else if (type === 'stsd' && !info.codec) {
        const c = read(body + 12, 4).toString('latin1');
        if (/^(avc1|avc3|hvc1|hev1|av01|vp09|mp4v|apcn|apch)$/.test(c)) info.codec = c;
      } else if (['moov', 'trak', 'mdia', 'minf', 'stbl'].includes(type)) {
        walk(body, at + len);
      }
      at += len;
    }
  };
  try { walk(0, size); } finally { closeSync(fd); }
  return info;
}
const mp4Date = path => mp4Info(path).created;

// stamp a converted video with its original's date, so it keeps its place in the album
function setMp4Date(path, ms) {
  const info = mp4Info(path);
  if (info.createdAt < 0) return;
  const secs = Math.round(ms / 1000) + MP4_EPOCH, b = Buffer.alloc(info.createdWide ? 8 : 4);
  if (info.createdWide) b.writeBigUInt64BE(BigInt(secs)); else b.writeUInt32BE(secs);
  const fd = openSync(path, 'r+');
  try { writeSync(fd, b, 0, b.length, info.createdAt); } finally { closeSync(fd); }
}

// ---- step 1: get assets/ ready for the web ----
const run = (cmd, args) => execFileSync(cmd, args, { stdio: 'pipe' }).toString();
// write to a hidden temp file first, so a failed conversion never loses anything
function replace(path, out, convert) {
  // don't overwrite a different file that already has the new name (photo.heic next to photo.jpg)
  for (let n = 2; out.toLowerCase() !== path.toLowerCase() && existsSync(out); n++) out = out.replace(/(-\d+)?(\.[^.]+)$/, `-${n}$2`);
  const tmp = 'assets/.tmp-' + out.split('/').pop();
  try {
    convert(tmp);
    const { atime, mtime } = statSync(path);
    unlinkSync(path);
    renameSync(tmp, out);
    utimesSync(out, atime, mtime);
    return out;
  } catch (e) {
    if (existsSync(tmp)) unlinkSync(tmp);
    console.warn(`couldn't convert ${path}: ${String(e.stderr || e.message).trim().split('\n')[0]}`);
    return null;
  }
}
const base = f => f.replace(/\.[^.]+$/, '');

if (process.platform === 'darwin') {
  for (const f of readdirSync('assets')) {
    if (f.startsWith('.')) continue;
    const path = 'assets/' + f, ext = f.split('.').pop().toLowerCase();
    if (ext === 'heic' || ext === 'heif' || ext === 'jpg' || ext === 'jpeg' || ext === 'png') {
      const dims = run('sips', ['-g', 'pixelWidth', '-g', 'pixelHeight', path]).match(/\d+/g).slice(-2).map(Number);
      const big = Math.max(...dims) > MAX_PHOTO, heic = ext === 'heic' || ext === 'heif';
      if (!big && !heic) continue;
      const out = heic ? `assets/${base(f)}.jpg` : path;
      const args = [...(big ? ['-Z', String(MAX_PHOTO)] : []), ...(ext === 'png' ? [] : ['-s', 'format', 'jpeg', '-s', 'formatOptions', '85'])];
      if (replace(path, out, tmp => run('sips', [...args, path, '--out', tmp])))
        console.log(`${heic ? 'converted' : 'shrank'} ${f}`);
    } else if (['mp4', 'mov', 'm4v'].includes(ext)) {
      const info = mp4Info(path);
      if (ext === 'mp4' && info.codec === 'avc1' && Math.min(info.w, info.h) <= MAX_VIDEO) continue;
      const when = info.created ?? statSync(path).mtimeMs;
      const out = `assets/${base(f)}.mp4`;
      const done = replace(path, out, tmp => run('avconvert', ['-s', path, '-p', 'Preset1280x720', '-o', tmp]));
      if (done) {
        setMp4Date(done, when);
        console.log(`converted ${f} to 720p H.264`);
      }
    }
  }
} else {
  console.warn('not on a Mac: skipping photo/video conversion, writing album.js only');
}

// ---- step 2: write album.js ----
const album = [];
let fromCamera = 0;
for (const f of readdirSync('assets')) {
  if (f.startsWith('.')) continue;
  const path = 'assets/' + f;
  const ext = f.split('.').pop().toLowerCase();
  const kind = PHOTO.includes(ext) ? 'src' : VIDEO.includes(ext) ? 'video' : null;
  if (!kind) {
    console.warn(`skipped ${path}: not a photo or video the book can show`);
    continue;
  }
  let taken = null;
  try { taken = kind === 'src' ? exifDate(readFileSync(path)) : ext === 'mp4' ? mp4Date(path) : null; } catch { }
  if (taken) fromCamera++;
  // "2026-11-13-goa-sunset.jpg" → "Goa sunset" (read out by screen readers only)
  const words = f.replace(/\.[^.]+$/, '').replace(/^\d{4}-\d{2}-\d{2}[-_ ]*/, '').replace(/[-_]+/g, ' ').trim();
  album.push({
    entry: { [kind]: 'assets/' + encodeURIComponent(f), title: words ? words[0].toUpperCase() + words.slice(1) : f },
    when: taken ?? statSync(path).mtimeMs,
    name: f,
  });
}
album.sort((a, b) => a.when - b.when || a.name.localeCompare(b.name, 'en', { numeric: true }));

writeFileSync('album.js',
  '// written by build-album.mjs: don\'t edit, add files to assets/ instead\n' +
  'window.ALBUM = ' + JSON.stringify(album.map(a => a.entry), null, 2) + ';\n');
console.log(`album.js: ${album.length} spreads (${album.filter(a => a.entry.video).length} videos), ` +
  `${fromCamera} dated by camera, ${album.length - fromCamera} by file date`);

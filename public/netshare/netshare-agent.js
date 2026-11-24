#!/usr/bin/env node
/* Агент «Сетевая папка» для программы «Управление предприятием».
   Запускается на файловом сервере, слушает только 127.0.0.1 и отдаёт список файлов и папок и сами файлы для скачивания (только чтение).
   Программа обращается к нему через обратный SSH-туннель:
     ssh -N -R 127.0.0.1:<порт на сервере программы>:127.0.0.1:<порт агента> <пользователь>@<сервер программы>
   Запуск:
     node netshare-agent.js --token <ключ из программы> [--port 8765] [--allow "D:\,E:\"]
   --allow — какие диски или папки можно показывать (по умолчанию — любые, которые укажет программа). */
'use strict';
const http = require('http'), fs = require('fs'), path = require('path'), crypto = require('crypto');
const arg = (k, d) => { const i = process.argv.indexOf('--' + k); return i > 0 ? process.argv[i + 1] : process.env['NETSHARE_' + k.toUpperCase()] || d; };
const TOKEN = arg('token', ''), PORT = Number(arg('port', 8765)), ALLOW = String(arg('allow', '')).split(',').map(s => s.trim()).filter(Boolean).map(s => path.resolve(s));
if (!TOKEN || TOKEN.length < 16) { console.error('Укажите ключ: --token <ключ из программы>'); process.exit(1); }
const win = process.platform === 'win32', norm = s => win ? s.toLowerCase() : s;
const inside = (child, root) => { const c = norm(path.resolve(child)), r = norm(path.resolve(root)); return c === r || c.startsWith(r.endsWith(path.sep) ? r : r + path.sep); };
const okToken = t => { const a = Buffer.from(String(t || '')), b = Buffer.from(TOKEN); return a.length === b.length && crypto.timingSafeEqual(a, b); };
const send = (res, code, obj) => { const b = Buffer.from(JSON.stringify(obj)); res.writeHead(code, { 'Content-Type': 'application/json; charset=utf-8', 'Content-Length': b.length }); res.end(b); };
http.createServer(async (req, res) => {
  try {
    if (req.method !== 'GET') return send(res, 405, { ok: false, error: 'Только чтение' });
    if (!okToken(req.headers['x-token'])) return send(res, 403, { ok: false, error: 'Неверный ключ агента' });
    const u = new URL(req.url, 'http://127.0.0.1');
    if (u.pathname === '/ping') return send(res, 200, { ok: true, agent: 'sed-netshare', v: 2, platform: process.platform, host: require('os').hostname() });
    if (u.pathname !== '/list' && u.pathname !== '/file') return send(res, 404, { ok: false, error: 'Не найдено' });
    const root = u.searchParams.get('root') || '', sub = u.searchParams.get('path') || '';
    if (!root) return send(res, 400, { ok: false, error: 'Не указан диск или папка' });
    if (ALLOW.length && !ALLOW.some(a => inside(root, a))) return send(res, 403, { ok: false, error: 'Этот диск или папка не разрешены агенту (--allow)' });
    if (sub.split(/[\\/]/).includes('..')) return send(res, 400, { ok: false, error: 'Недопустимый путь' });
    const full = path.resolve(root, sub);
    if (!inside(full, root)) return send(res, 400, { ok: false, error: 'Недопустимый путь' });
    if (u.pathname === '/file') {   // a file for download: the bytes as they are, the name and the size in the headers
      const st = await fs.promises.stat(full); if (!st.isFile()) return send(res, 404, { ok: false, error: 'Файл не найден' });
      res.writeHead(200, { 'Content-Type': 'application/octet-stream', 'Content-Length': st.size, 'X-Name': encodeURIComponent(path.basename(full)) });
      return fs.createReadStream(full).on('error', () => res.destroy()).pipe(res);
    }
    const D = await fs.promises.readdir(full, { withFileTypes: true });
    const entries = [];
    for (const d of D.slice(0, 5000)) {
      let st = null; try { st = await fs.promises.stat(path.join(full, d.name)); } catch {}
      entries.push({ name: d.name, dir: st ? st.isDirectory() : d.isDirectory(), size: st && st.isFile() ? st.size : null, mtime: st ? st.mtime.toISOString() : null });
    }
    send(res, 200, { ok: true, path: sub, total: D.length, entries });
  } catch (e) { send(res, e.code === 'ENOENT' ? 404 : e.code === 'EACCES' || e.code === 'EPERM' ? 403 : 500, { ok: false, error: e.code === 'ENOENT' ? 'Не найдено' : e.code === 'EACCES' || e.code === 'EPERM' ? 'Нет доступа к папке' : String(e.message || e) }); }
}).listen(PORT, '127.0.0.1', () => console.log(`Агент «Сетевая папка» слушает 127.0.0.1:${PORT}${ALLOW.length ? ' · разрешено: ' + ALLOW.join(', ') : ''}`));

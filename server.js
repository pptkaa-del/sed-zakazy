#!/usr/bin/env node
'use strict';
/*
 * Документооборот по заказам — сервер.
 * Только встроенные модули Node.js (22+), без npm-зависимостей.
 *
 *   node server.js                         запустить сервер
 *   node server.js useradd <логин> <роль> "<Имя>" [пароль]
 *   node server.js passwd  <логин> [пароль]
 *   node server.js userdel <логин>
 *   node server.js users
 *   node server.js backup  [файл.json]     выгрузить все записи в JSON
 *
 * Настройки берутся из переменных окружения и из файла sed.env рядом с server.js
 * (строки вида КЛЮЧ=значение; переменные окружения важнее файла).
 *
 * Роли: admin, manager, accountant, viewer.
 */
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const readline = require('node:readline');
const os = require('node:os');

/* sed.env: optional KEY=value file next to server.js (panel hosting without env settings) */
try {
  for (const line of fs.readFileSync(path.join(__dirname, 'sed.env'), 'utf8').split(/\r?\n/)) {
    const m = /^\s*([A-Z_][A-Z0-9_]*)\s*=\s*(.*?)\s*$/.exec(line);
    if (m && !line.trim().startsWith('#') && process.env[m[1]] === undefined) process.env[m[1]] = m[2].replace(/^(['"])(.*)\1$/, '$2');
  }
} catch {}

/* Listening: PORT may be a number or a Unix socket path; SOCKET / APP_SOCKET also accepted. */
const RAW_PORT = process.env.PORT || process.env.SOCKET || process.env.APP_SOCKET || '3000';
const LISTEN_SOCKET = /^\d+$/.test(RAW_PORT) ? null : RAW_PORT;
const PORT = LISTEN_SOCKET ? null : Number(RAW_PORT);
const HOST = process.env.HOST || '0.0.0.0';
/* Data lives outside the app folder by default, so a web server can never serve it as static files. */
const DATA_DIR = path.resolve(process.env.DATA_DIR || path.join(os.homedir(), 'sed-zakazy-data'));
const FILES_DIR = path.join(DATA_DIR, 'files');
const PUBLIC_DIR = path.join(__dirname, 'public');
const MAX_FILE = Number(process.env.MAX_FILE_MB || 50) * 1048576;
const MAX_JSON = 4 * 1048576;
const SESSION_DAYS = Number(process.env.SESSION_DAYS || 14);
const COOKIE_SECURE = process.env.COOKIE_SECURE === '1';
const TRUST_PROXY = process.env.TRUST_PROXY !== '0';

const COLLECTIONS = ['projects', 'orders', 'invoices', 'tasks'];
const ROLES = {
  admin:      'Администратор',
  manager:    'Менеджер',
  accountant: 'Бухгалтер',
  viewer:     'Просмотр',
};
const PAY_FIELDS = ['status', 'paidAt', 'payNo', 'paidAmount', 'paidBy', 'receipt'];
const canEdit = u => u.role === 'admin' || u.role === 'manager';
const canPay = u => u.role === 'admin' || u.role === 'accountant';

fs.mkdirSync(FILES_DIR, { recursive: true });

/* ---------- storage: JSON files with atomic writes ---------- */
function readJSON(file, fallback) {
  try { return JSON.parse(fs.readFileSync(file, 'utf8')); } catch (e) {
    if (e.code !== 'ENOENT') { console.error(`Не удалось прочитать ${file}:`, e.message); process.exit(1); }
    return fallback;
  }
}
function writeJSON(file, value) {
  const tmp = file + '.' + process.pid + '.tmp';
  fs.writeFileSync(tmp, JSON.stringify(value, null, 1));
  fs.renameSync(tmp, file);
}
const DB_FILE = path.join(DATA_DIR, 'db.json');
const USERS_FILE = path.join(DATA_DIR, 'users.json');
const SECRET_FILE = path.join(DATA_DIR, 'secret.key');

function loadDb() {
  const d = readJSON(DB_FILE, { rev: 0, files: {} });
  COLLECTIONS.forEach(c => { d[c] = d[c] || {}; });
  d.files = d.files || {};
  return d;
}
/* The hosting may run several copies of the app (e.g. Passenger) or a CLI command may edit
   users while the server runs: re-read files when another process has changed them. */
const stamp = f => { try { const st = fs.statSync(f); return st.mtimeMs + ':' + st.size + ':' + st.ino; } catch { return ''; } };
let db = loadDb(), dbStamp = stamp(DB_FILE);
let users = readJSON(USERS_FILE, []), usersStamp = stamp(USERS_FILE);
function syncFromDisk() {
  const a = stamp(DB_FILE); if (a !== dbStamp) { db = loadDb(); dbStamp = a; }
  const b = stamp(USERS_FILE); if (b !== usersStamp) { users = readJSON(USERS_FILE, []); usersStamp = b; }
}
const saveDb = () => { db.rev++; writeJSON(DB_FILE, db); dbStamp = stamp(DB_FILE); };
const saveUsers = () => { writeJSON(USERS_FILE, users); usersStamp = stamp(USERS_FILE); };

let secret;
try { secret = fs.readFileSync(SECRET_FILE); } catch {
  secret = crypto.randomBytes(32); fs.writeFileSync(SECRET_FILE, secret, { mode: 0o600 });
}

/* ---------- passwords and sessions ---------- */
function hashPassword(pw, salt = crypto.randomBytes(16).toString('hex')) {
  return { salt, hash: crypto.scryptSync(pw, salt, 64).toString('hex') };
}
function checkPassword(u, pw) {
  const h = crypto.scryptSync(pw, u.salt, 64);
  return crypto.timingSafeEqual(h, Buffer.from(u.hash, 'hex'));
}
const sign = s => crypto.createHmac('sha256', secret).update(s).digest('base64url');
function makeSession(u) {
  const exp = Date.now() + SESSION_DAYS * 864e5;
  const body = `${u.id}.${exp}.${u.ver || 0}`;
  return `${body}.${sign(body)}`;
}
function sessionUser(req) {
  const m = /(?:^|;\s*)sid=([^;]+)/.exec(req.headers.cookie || '');
  if (!m) return null;
  const parts = m[1].split('.');
  if (parts.length !== 4) return null;
  const body = parts.slice(0, 3).join('.');
  const a = Buffer.from(sign(body)), b = Buffer.from(parts[3]);
  if (a.length !== b.length || !crypto.timingSafeEqual(a, b)) return null;
  if (Number(parts[1]) < Date.now()) return null;
  const u = users.find(x => x.id === parts[0]);
  if (!u || String(u.ver || 0) !== parts[2]) return null;
  return u;
}
function cookie(req, value, maxAge) {
  const secure = COOKIE_SECURE || (TRUST_PROXY && req.headers['x-forwarded-proto'] === 'https');
  return `sid=${value}; Path=/; HttpOnly; SameSite=Lax; Max-Age=${maxAge}${secure ? '; Secure' : ''}`;
}

/* login throttling: 10 failed attempts per 10 minutes per IP and login */
const attempts = new Map();
function clientIp(req) {
  return (TRUST_PROXY && String(req.headers['x-forwarded-for'] || '').split(',')[0].trim()) || req.socket.remoteAddress;
}
function throttled(ip) {
  const now = Date.now(), a = (attempts.get(ip) || []).filter(t => now - t < 600e3);
  attempts.set(ip, a);
  return a.length >= 10;
}

/* ---------- http helpers ---------- */
const SEC_HEADERS = {
  'X-Content-Type-Options': 'nosniff',
  'Referrer-Policy': 'same-origin',
  'X-Frame-Options': 'SAMEORIGIN',
};
function send(res, status, body, headers = {}) {
  const isBuf = Buffer.isBuffer(body);
  const data = isBuf || typeof body === 'string' ? body : JSON.stringify(body);
  res.writeHead(status, {
    ...SEC_HEADERS,
    'Content-Type': isBuf || typeof body === 'string' ? 'text/plain; charset=utf-8' : 'application/json; charset=utf-8',
    'Cache-Control': 'no-store',
    ...headers,
  });
  res.end(data);
}
const fail = (res, status, message) => send(res, status, { error: message });
function readBody(req, limit) {
  return new Promise((resolve, reject) => {
    const chunks = []; let size = 0;
    req.on('data', c => {
      size += c.length;
      if (size > limit) { reject(Object.assign(new Error('Слишком большой запрос'), { status: 413 })); req.destroy(); return; }
      chunks.push(c);
    });
    req.on('end', () => resolve(Buffer.concat(chunks)));
    req.on('error', reject);
  });
}
async function readJsonBody(req) {
  const buf = await readBody(req, MAX_JSON);
  try { const v = JSON.parse(buf.toString('utf8') || '{}'); if (v && typeof v === 'object' && !Array.isArray(v)) return v; } catch {}
  throw Object.assign(new Error('Некорректный JSON'), { status: 400 });
}
const newId = () => crypto.randomBytes(9).toString('base64url');
const clean = obj => { const o = { ...obj }; delete o.id; return o; };
const listOf = c => Object.entries(db[c]).map(([id, d]) => ({ id, ...d }));

const MIME = {
  '.html': 'text/html; charset=utf-8', '.js': 'text/javascript; charset=utf-8', '.css': 'text/css; charset=utf-8',
  '.svg': 'image/svg+xml', '.png': 'image/png', '.ico': 'image/x-icon', '.json': 'application/json', '.webmanifest': 'application/manifest+json',
};
/* files that are safe to show inline; everything else is downloaded */
const INLINE = new Set(['application/pdf', 'image/png', 'image/jpeg', 'image/gif', 'image/webp', 'text/plain', 'text/csv']);

/* ---------- API ---------- */
async function api(req, res, url) {
  const p = url.pathname.split('/').filter(Boolean); // ['api', ...]
  const m = req.method;

  if (m !== 'GET' && req.headers['x-sed'] !== '1') return fail(res, 403, 'Запрос отклонён');

  if (p[1] === 'setup' && m === 'GET') return send(res, 200, { needed: users.length === 0 });
  if (p[1] === 'setup' && m === 'POST') {
    if (users.length) return fail(res, 409, 'Администратор уже создан. Войдите со своим логином');
    const b = await readJsonBody(req);
    const err = validateUser(b, true); if (err) return fail(res, 400, err);
    const u = addUser(String(b.login), 'admin', String(b.name).trim(), String(b.password));
    console.log(`Через браузер создан администратор «${u.login}».`);
    return send(res, 200, publicUser(u), { 'Set-Cookie': cookie(req, makeSession(u), SESSION_DAYS * 86400) });
  }
  if (p[1] === 'login' && m === 'POST') {
    const { login = '', password = '' } = await readJsonBody(req);
    const key = clientIp(req) + '|' + String(login).trim().toLowerCase();
    if (throttled(key)) return fail(res, 429, 'Слишком много попыток входа. Подождите 10 минут.');
    const u = users.find(x => x.login === String(login).trim().toLowerCase());
    if (!u || !checkPassword(u, String(password))) {
      attempts.get(key).push(Date.now());
      return fail(res, 401, 'Неверный логин или пароль');
    }
    return send(res, 200, publicUser(u), { 'Set-Cookie': cookie(req, makeSession(u), SESSION_DAYS * 86400) });
  }
  if (p[1] === 'logout' && m === 'POST') return send(res, 200, { ok: true }, { 'Set-Cookie': cookie(req, '', 0) });

  const user = sessionUser(req);
  if (!user) return fail(res, 401, 'Требуется вход');

  if (p[1] === 'me' && m === 'GET') return send(res, 200, publicUser(user));
  if (p[1] === 'users') {
    if (user.role !== 'admin') return fail(res, 403, 'Управлять пользователями может только администратор');
    const target = p[2] && users.find(u => u.id === p[2]);
    if (m === 'GET' && !p[2]) return send(res, 200, users.map(publicUser));
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req);
      const err = validateUser(b, true); if (err) return fail(res, 400, err);
      if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
      return send(res, 200, publicUser(addUser(String(b.login), b.role, String(b.name).trim(), String(b.password))));
    }
    if (!target) return fail(res, 404, 'Пользователь не найден');
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      if (b.role !== undefined) {
        if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
        if (target.id === user.id && b.role !== 'admin') return fail(res, 400, 'Нельзя снять роль администратора с самого себя');
        target.role = b.role;
      }
      if (b.name !== undefined) { if (!String(b.name).trim()) return fail(res, 400, 'Укажите имя'); target.name = String(b.name).trim(); }
      if (b.password !== undefined) {
        if (String(b.password).length < 8) return fail(res, 400, 'Пароль должен быть не короче 8 символов');
        Object.assign(target, hashPassword(String(b.password)), { ver: (target.ver || 0) + 1 });
      }
      saveUsers();
      return send(res, 200, publicUser(target));
    }
    if (m === 'DELETE') {
      if (target.id === user.id) return fail(res, 400, 'Нельзя удалить самого себя');
      users = users.filter(u => u.id !== target.id); saveUsers();
      return send(res, 200, { ok: true });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'rev' && m === 'GET') return send(res, 200, { rev: db.rev });
  if (p[1] === 'data' && m === 'GET') {
    const out = { rev: db.rev, users: Object.fromEntries(users.map(u => [u.id, u.name])) };
    COLLECTIONS.forEach(c => { out[c] = listOf(c); });
    return send(res, 200, out);
  }
  if (p[1] === 'password' && m === 'POST') {
    const { current = '', next = '' } = await readJsonBody(req);
    if (!checkPassword(user, String(current))) return fail(res, 400, 'Текущий пароль указан неверно');
    if (String(next).length < 8) return fail(res, 400, 'Новый пароль должен быть не короче 8 символов');
    Object.assign(user, hashPassword(String(next)), { ver: (user.ver || 0) + 1 });
    saveUsers();
    return send(res, 200, { ok: true }, { 'Set-Cookie': cookie(req, makeSession(user), SESSION_DAYS * 86400) });
  }

  if (p[1] === 'files' && m === 'POST') {
    if (!canEdit(user) && !canPay(user)) return fail(res, 403, 'Недостаточно прав для загрузки файлов');
    let name = 'файл';
    try { name = decodeURIComponent(String(req.headers['x-filename'] || 'файл')); } catch {}
    name = name.replace(/[\\/\r\n"]/g, '_').slice(0, 200) || 'файл';
    const buf = await readBody(req, MAX_FILE);
    if (!buf.length) return fail(res, 400, 'Пустой файл');
    const id = newId();
    fs.writeFileSync(path.join(FILES_DIR, id), buf);
    const type = String(req.headers['content-type'] || 'application/octet-stream').split(';')[0].trim().toLowerCase();
    db.files[id] = { name, type, size: buf.length, at: new Date().toISOString(), by: user.id };
    saveDb();
    return send(res, 200, { id, url: '/files/' + id, name, size: buf.length, at: db.files[id].at, by: user.id });
  }

  const col = p[1], id = p[2];
  if (!COLLECTIONS.includes(col) || p.length > 3) return fail(res, 404, 'Не найдено');

  if (m === 'POST' && !id) {
    if (!canEdit(user)) return fail(res, 403, 'Недостаточно прав');
    const data = clean(await readJsonBody(req));
    data.createdBy = user.id; data.createdAt = data.createdAt || new Date().toISOString();
    if (col === 'invoices') { data.status = 'topay'; PAY_FIELDS.slice(1).forEach(f => delete data[f]); }
    const nid = newId(); db[col][nid] = data; saveDb();
    return send(res, 200, { id: nid, rev: db.rev });
  }
  if (!id || !db[col][id]) return fail(res, 404, 'Запись не найдена');

  if (m === 'PATCH') {
    const patch = clean(await readJsonBody(req));
    delete patch.createdBy; delete patch.createdAt;
    const keys = Object.keys(patch);
    const payKeys = col === 'invoices' ? keys.filter(k => PAY_FIELDS.includes(k)) : [];
    if (payKeys.length && !canPay(user)) return fail(res, 403, 'Отмечать оплату может только бухгалтер или администратор');
    if (keys.length > payKeys.length && !canEdit(user)) return fail(res, 403, 'Недостаточно прав');
    if (col === 'invoices' && db[col][id].status === 'paid' && keys.some(k => !PAY_FIELDS.includes(k) && k !== 'projectId') && !('status' in patch))
      return fail(res, 409, 'Оплаченный счёт нельзя изменить. Сначала снимите отметку об оплате');
    if (col === 'invoices' && 'status' in patch) {
      if (!['topay', 'paid'].includes(patch.status)) return fail(res, 400, 'Неизвестный статус счёта');
      patch.paidBy = patch.status === 'paid' ? user.id : null;
    }
    Object.assign(db[col][id], patch, { updatedAt: new Date().toISOString(), updatedBy: user.id });
    saveDb();
    return send(res, 200, { ok: true, rev: db.rev });
  }
  if (m === 'DELETE') {
    if (!canEdit(user)) return fail(res, 403, 'Недостаточно прав');
    const d = db[col][id];
    if (col === 'projects' && listOf('orders').some(o => o.projectId === id)) return fail(res, 409, 'В проекте есть заказы');
    if (col === 'orders' && listOf('invoices').some(i => i.orderId === id)) return fail(res, 409, 'По заказу есть счета');
    if (col === 'invoices' && d.status === 'paid') return fail(res, 409, 'Оплаченный счёт удалить нельзя');
    delete db[col][id]; saveDb();
    return send(res, 200, { ok: true, rev: db.rev });
  }
  return fail(res, 405, 'Метод не поддерживается');
}
const publicUser = u => ({ id: u.id, login: u.login, name: u.name, role: u.role, roleName: ROLES[u.role] });

function serveFile(req, res, id) {
  if (!sessionUser(req)) return fail(res, 401, 'Требуется вход');
  const meta = db.files[id];
  if (!meta || !/^[\w-]+$/.test(id)) return fail(res, 404, 'Файл не найден');
  const fp = path.join(FILES_DIR, id);
  if (!fs.existsSync(fp)) return fail(res, 404, 'Файл не найден');
  const inline = INLINE.has(meta.type);
  const enc = encodeURIComponent(meta.name);
  res.writeHead(200, {
    ...SEC_HEADERS,
    'Content-Type': inline ? meta.type + (meta.type.startsWith('text/') ? '; charset=utf-8' : '') : 'application/octet-stream',
    'Content-Length': meta.size,
    'Content-Disposition': `${inline ? 'inline' : 'attachment'}; filename="${enc}"; filename*=UTF-8''${enc}`,
    'Content-Security-Policy': "default-src 'none'; img-src 'self'; style-src 'unsafe-inline'; sandbox",
    'Cache-Control': 'private, max-age=86400',
  });
  fs.createReadStream(fp).pipe(res);
}

function serveStatic(req, res, pathname) {
  let rel = pathname === '/' ? '/index.html' : pathname;
  const fp = path.join(PUBLIC_DIR, path.normalize(rel).replace(/^([/\\])+/, ''));
  if (!fp.startsWith(PUBLIC_DIR + path.sep)) return fail(res, 404, 'Не найдено');
  fs.readFile(fp, (err, buf) => {
    if (err) return fail(res, 404, 'Не найдено');
    res.writeHead(200, {
      ...SEC_HEADERS,
      'Content-Type': MIME[path.extname(fp)] || 'application/octet-stream',
      'Cache-Control': 'no-cache',
    });
    res.end(buf);
  });
}

function startServer() {
  if (!users.length) {
    const login = process.env.ADMIN_LOGIN, pw = process.env.ADMIN_PASSWORD;
    if (login && pw) { addUser(login, 'admin', process.env.ADMIN_NAME || 'Администратор', pw); console.log(`Создан администратор «${login}».`); }
  }
  const server = http.createServer(async (req, res) => {
    const url = new URL(req.url, 'http://localhost');
    try { syncFromDisk(); } catch (e) { console.error(e); }
    try {
      if (url.pathname.startsWith('/api/')) return await api(req, res, url);
      if (url.pathname.startsWith('/files/') && req.method === 'GET') return serveFile(req, res, url.pathname.slice(7));
      if (req.method === 'GET') return serveStatic(req, res, url.pathname);
      fail(res, 405, 'Метод не поддерживается');
    } catch (e) {
      if (!e.status) console.error(e);
      if (!res.headersSent) fail(res, e.status || 500, e.status ? e.message : 'Внутренняя ошибка сервера');
    }
  });
  server.requestTimeout = 10 * 60e3;
  if (LISTEN_SOCKET) {
    try { fs.unlinkSync(LISTEN_SOCKET); } catch {}
    server.listen(LISTEN_SOCKET, () => {
      try { fs.chmodSync(LISTEN_SOCKET, 0o666); } catch {}
      console.log(`Документооборот запущен на сокете ${LISTEN_SOCKET}  (данные: ${DATA_DIR})`);
    });
  } else {
    server.listen(PORT, HOST, () => console.log(`Документооборот запущен: http://${HOST === '0.0.0.0' ? 'localhost' : HOST}:${PORT}  (данные: ${DATA_DIR})`));
  }
  if (!users.length) console.log('Пользователей нет: откройте сайт в браузере и создайте администратора.');
  const stop = () => server.close(() => process.exit(0));
  process.on('SIGTERM', stop); process.on('SIGINT', stop);
}

/* ---------- CLI ---------- */
function addUser(login, role, name, pw) {
  const u = { id: 'u_' + newId(), login: login.toLowerCase(), name, role, ...hashPassword(pw), ver: 0, createdAt: new Date().toISOString() };
  users.push(u); saveUsers(); return u;
}
function validateUser(b, isNew) {
  const login = String(b.login || '').trim();
  if (isNew && !/^[a-z0-9._-]{2,40}$/i.test(login)) return 'Логин: от 2 символов, латиница, цифры, точка, дефис или подчёркивание';
  if (isNew && users.some(u => u.login === login.toLowerCase())) return 'Такой логин уже есть';
  if (!String(b.name || '').trim()) return 'Укажите имя';
  if (String(b.password || '').length < 8) return 'Пароль должен быть не короче 8 символов';
  return null;
}
function askPassword(prompt) {
  return new Promise(resolve => {
    if (!process.stdin.isTTY) { console.error('Укажите пароль последним аргументом'); process.exit(1); }
    const rl = readline.createInterface({ input: process.stdin, output: process.stdout, terminal: true });
    rl._writeToOutput = s => { if (s.includes(prompt)) process.stdout.write(s); };
    rl.question(prompt, a => { rl.close(); process.stdout.write('\n'); resolve(a); });
  });
}
async function cli(cmd, args) {
  const need = n => { if (args.length < n) { console.error('Недостаточно аргументов. См. README.md'); process.exit(1); } };
  if (cmd === 'useradd') {
    need(3);
    const [login, role, name] = args;
    if (!ROLES[role]) { console.error('Роль должна быть одной из: ' + Object.keys(ROLES).join(', ')); process.exit(1); }
    if (!/^[a-z0-9._-]{2,40}$/i.test(login)) { console.error('Логин: латиница, цифры, точка, дефис, подчёркивание'); process.exit(1); }
    if (users.some(u => u.login === login.toLowerCase())) { console.error('Такой логин уже есть'); process.exit(1); }
    const pw = args[3] || await askPassword('Пароль: ');
    if (pw.length < 8) { console.error('Пароль должен быть не короче 8 символов'); process.exit(1); }
    addUser(login, role, name, pw);
    console.log(`Пользователь «${login}» (${ROLES[role]}) создан.`);
  } else if (cmd === 'passwd') {
    need(1);
    const u = users.find(x => x.login === args[0].toLowerCase()); if (!u) { console.error('Нет такого пользователя'); process.exit(1); }
    const pw = args[1] || await askPassword('Новый пароль: ');
    if (pw.length < 8) { console.error('Пароль должен быть не короче 8 символов'); process.exit(1); }
    Object.assign(u, hashPassword(pw), { ver: (u.ver || 0) + 1 }); saveUsers();
    console.log('Пароль изменён, прежние входы этого пользователя завершены.');
  } else if (cmd === 'userdel') {
    need(1);
    const n = users.length; users = users.filter(x => x.login !== args[0].toLowerCase()); saveUsers();
    console.log(n === users.length ? 'Нет такого пользователя' : 'Пользователь удалён.');
  } else if (cmd === 'users') {
    if (!users.length) console.log('Пользователей нет.');
    users.forEach(u => console.log(`${u.login.padEnd(20)} ${ROLES[u.role].padEnd(14)} ${u.name}`));
  } else if (cmd === 'backup') {
    const file = args[0] || `backup-${new Date().toISOString().slice(0, 10)}.json`;
    writeJSON(path.resolve(file), db);
    console.log(`Записи выгружены в ${file}. Файлы вложений лежат в ${FILES_DIR}.`);
  } else {
    console.error(`Неизвестная команда «${cmd}». См. README.md`); process.exit(1);
  }
}

const [cmd, ...args] = process.argv.slice(2);
if (cmd) cli(cmd, args); else startServer();

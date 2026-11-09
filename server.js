#!/usr/bin/env node
'use strict';
/*
 * Управление предприятием — сервер.
 * Только встроенные модули Node.js (22+), без npm-зависимостей.
 *
 *   node server.js                         запустить сервер
 *   node server.js useradd <логин> <роль> "<Имя>" [пароль]
 *   node server.js passwd  <логин> [пароль]
 *   node server.js userdel <логин>
 *   node server.js unblock <логин>         снять блокировку
 *   node server.js users
 *   node server.js backup  [файл.json]     выгрузить все записи в JSON
 *
 * Настройки берутся из переменных окружения и из файла sed.env рядом с server.js
 * (строки вида КЛЮЧ=значение; переменные окружения важнее файла).
 *
 * Роли: admin, manager, accountant, user, viewer.
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

const COLLECTIONS = ['projects', 'orders', 'invoices', 'tasks', 'counterparties', 'points'];
const ROLES = {
  admin:      'Администратор',
  manager:    'Менеджер',
  accountant: 'Бухгалтер',
  user:       'Сотрудник',
  viewer:     'Просмотр',
};
const PAY_FIELDS = ['status', 'paidAt', 'payNo', 'paidAmount', 'paidBy', 'receipt'];
const canEdit = u => u.role === 'admin' || u.role === 'manager';
const canPay = u => u.role === 'admin' || u.role === 'accountant';
/* «Сотрудник» загружает счета и правит/удаляет только свои неоплаченные */
const canAddInvoice = u => canEdit(u) || u.role === 'user';
const ownsInvoice = (u, inv) => u.role === 'user' && inv.createdBy === u.id && inv.status !== 'paid';
const SEEN_FIELDS = ['seenAt', 'seenBy', 'seenLastAt', 'seenCount'];
/* Map points: everyone except «Просмотр» adds points and marks them done; author, manager or admin edits and deletes */
const POINT_STATUS_FIELDS = ['status', 'doneAt', 'doneBy'];
const canWork = u => u.role !== 'viewer';
const mayEditPoint = (u, pt) => canEdit(u) || pt.createdBy === u.id;
const validPoint = d => Number.isFinite(Number(d.lat)) && Number.isFinite(Number(d.lng)) && Math.abs(d.lat) <= 90 && Math.abs(d.lng) <= 180;

/* Version of the running app: changes when the code is updated, so open pages can offer a reload */
const APP_VERSION = crypto.createHash('sha1')
  .update(fs.readFileSync(path.join(__dirname, 'server.js')))
  .update((() => { try { return fs.readFileSync(path.join(__dirname, 'public', 'index.html')); } catch { return ''; } })())
  .digest('hex').slice(0, 12);

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
  if (!u || u.blocked || String(u.ver || 0) !== parts[2]) return null;
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
    return send(res, 200, meInfo(u), { 'Set-Cookie': cookie(req, makeSession(u), SESSION_DAYS * 86400) });
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
    if (u.blocked) return fail(res, 403, 'Учётная запись заблокирована. Обратитесь к администратору');
    u.lastLoginAt = new Date().toISOString(); saveUsers();
    return send(res, 200, meInfo(u), { 'Set-Cookie': cookie(req, makeSession(u), SESSION_DAYS * 86400) });
  }
  if (p[1] === 'logout' && m === 'POST') return send(res, 200, { ok: true }, { 'Set-Cookie': cookie(req, '', 0) });

  const user = sessionUser(req);
  if (!user) return fail(res, 401, 'Требуется вход');

  if (p[1] === 'me' && m === 'GET') return send(res, 200, meInfo(user));
  if (p[1] === 'users') {
    if (user.role !== 'admin') return fail(res, 403, 'Управлять пользователями может только администратор');
    const target = p[2] && users.find(u => u.id === p[2]);
    if (m === 'GET' && !p[2]) return send(res, 200, users.map(adminUser));
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req);
      const err = validateUser(b, true); if (err) return fail(res, 400, err);
      if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
      return send(res, 200, adminUser(addUser(String(b.login), b.role, String(b.name).trim(), String(b.password))));
    }
    if (!target) return fail(res, 404, 'Пользователь не найден');
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      if (b.role !== undefined) {
        if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
        if (target.id === user.id && b.role !== 'admin') return fail(res, 400, 'Нельзя снять роль администратора с самого себя');
        target.role = b.role;
      }
      if (b.name !== undefined) { if (!String(b.name).trim()) return fail(res, 400, 'Укажите имя'); target.name = String(b.name).trim().slice(0, 120); }
      if (b.login !== undefined) {
        const login = String(b.login).trim().toLowerCase();
        if (!/^[a-z0-9._-]{2,40}$/.test(login)) return fail(res, 400, 'Логин: от 2 символов, латиница, цифры, точка, дефис или подчёркивание');
        if (users.some(u => u.login === login && u.id !== target.id)) return fail(res, 400, 'Такой логин уже есть');
        target.login = login;
      }
      if (b.blocked !== undefined) {
        if (target.id === user.id) return fail(res, 400, 'Нельзя заблокировать самого себя');
        target.blocked = !!b.blocked;
        if (target.blocked) target.ver = (target.ver || 0) + 1;   // end active sessions
      }
      if (b.password !== undefined) {
        if (String(b.password).length < 8) return fail(res, 400, 'Пароль должен быть не короче 8 символов');
        Object.assign(target, hashPassword(String(b.password)), { ver: (target.ver || 0) + 1 });
      }
      saveUsers();
      return send(res, 200, adminUser(target));
    }
    if (m === 'DELETE') {
      if (target.id === user.id) return fail(res, 400, 'Нельзя удалить самого себя');
      users = users.filter(u => u.id !== target.id); saveUsers();
      return send(res, 200, { ok: true });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'rev' && m === 'GET') return send(res, 200, { rev: db.rev, version: APP_VERSION });
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

  if (p[1] === 'invoices-zip' && m === 'GET') {
    if (!canPay(user)) return fail(res, 403, 'Скачивать архив счетов может бухгалтер или администратор');
    return sendInvoicesZip(res, user, url.searchParams.get('order') || '');
  }

  if (p[1] === 'files' && m === 'POST') {
    if (!canEdit(user) && !canPay(user) && !canAddInvoice(user)) return fail(res, 403, 'Недостаточно прав для загрузки файлов');
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

  /* comments on orders and counterparties: everyone except «Просмотр» may write; author or admin may delete */
  if ((p[1] === 'orders' || p[1] === 'counterparties') && p[3] === 'comments') {
    const o = db[p[1]][p[2]];
    if (!o) return fail(res, 404, 'Запись не найдена');
    o.comments = Array.isArray(o.comments) ? o.comments : [];
    if (m === 'POST' && p.length === 4) {
      if (user.role === 'viewer') return fail(res, 403, 'Недостаточно прав');
      const { text = '' } = await readJsonBody(req);
      const t = String(text).trim().slice(0, 2000);
      if (!t) return fail(res, 400, 'Пустой комментарий');
      const c = { id: newId(), by: user.id, at: new Date().toISOString(), text: t };
      o.comments.push(c); saveDb();
      return send(res, 200, c);
    }
    if (m === 'DELETE' && p.length === 5) {
      const c = o.comments.find(x => x.id === p[4]);
      if (!c) return fail(res, 404, 'Комментарий не найден');
      if (c.by !== user.id && user.role !== 'admin') return fail(res, 403, 'Удалить можно только свой комментарий');
      o.comments = o.comments.filter(x => x.id !== c.id); saveDb();
      return send(res, 200, { ok: true });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }

  const col = p[1], id = p[2];
  if (!COLLECTIONS.includes(col) || p.length > 3) return fail(res, 404, 'Не найдено');

  if (m === 'POST' && !id) {
    if (!(col === 'invoices' ? canAddInvoice(user) : col === 'points' ? canWork(user) : canEdit(user))) return fail(res, 403, 'Недостаточно прав');
    const data = clean(await readJsonBody(req));
    if (col === 'points') {
      if (!validPoint(data)) return fail(res, 400, 'Неверные координаты точки');
      data.lat = Number(data.lat); data.lng = Number(data.lng);
      data.status = 'todo'; delete data.doneAt; delete data.doneBy;
    }
    data.createdBy = user.id; data.createdAt = data.createdAt || new Date().toISOString();
    if (col === 'orders' || col === 'counterparties') data.comments = [];
    if (col === 'invoices') {
      if (!db.orders[data.orderId]) return fail(res, 400, 'Заказ не найден');
      data.projectId = db.orders[data.orderId].projectId || null;
      data.status = 'topay'; [...PAY_FIELDS.slice(1), ...SEEN_FIELDS].forEach(f => delete data[f]);
    }
    const nid = newId(); db[col][nid] = data; saveDb();
    return send(res, 200, { id: nid, rev: db.rev });
  }
  if (!id || !db[col][id]) return fail(res, 404, 'Запись не найдена');

  if (m === 'PATCH') {
    const patch = clean(await readJsonBody(req));
    delete patch.createdBy; delete patch.createdAt;
    if (col === 'orders' || col === 'counterparties') delete patch.comments;   // comments go through their own endpoint
    SEEN_FIELDS.forEach(f => delete patch[f]);   // set only by the server when the accountant downloads
    const keys = Object.keys(patch);
    /* tasks: everyone except «Просмотр» may tick «Выполнено»; other changes need a manager or admin */
    if (col === 'tasks' && keys.length && keys.every(k => k === 'done')) {
      if (!canWork(user)) return fail(res, 403, 'Недостаточно прав');
      const t = db.tasks[id];
      t.done = !!patch.done; t.doneAt = t.done ? new Date().toISOString() : null; t.doneBy = t.done ? user.id : null;
      t.updatedAt = new Date().toISOString(); t.updatedBy = user.id;
      saveDb();
      return send(res, 200, { ok: true, rev: db.rev });
    }
    if (col === 'points') {
      const pt = db.points[id];
      const other = keys.filter(k => !POINT_STATUS_FIELDS.includes(k));
      if (!canWork(user)) return fail(res, 403, 'Недостаточно прав');
      if (other.length && !mayEditPoint(user, pt)) return fail(res, 403, 'Изменить точку может её автор, менеджер или администратор');
      if ('lat' in patch || 'lng' in patch) {
        const t = { lat: patch.lat ?? pt.lat, lng: patch.lng ?? pt.lng };
        if (!validPoint(t)) return fail(res, 400, 'Неверные координаты точки');
        patch.lat = Number(t.lat); patch.lng = Number(t.lng);
      }
      if ('status' in patch) {
        if (!['todo', 'done'].includes(patch.status)) return fail(res, 400, 'Неизвестный статус точки');
        patch.doneAt = patch.status === 'done' ? new Date().toISOString() : null;
        patch.doneBy = patch.status === 'done' ? user.id : null;
      }
      Object.assign(pt, patch, { updatedAt: new Date().toISOString(), updatedBy: user.id });
      saveDb();
      return send(res, 200, { ok: true, rev: db.rev });
    }
    const payKeys = col === 'invoices' ? keys.filter(k => PAY_FIELDS.includes(k)) : [];
    if (payKeys.length && !canPay(user)) return fail(res, 403, 'Отмечать оплату может только бухгалтер или администратор');
    const mayEdit = canEdit(user) || (col === 'invoices' && ownsInvoice(user, db[col][id]));
    if (keys.length > payKeys.length && !mayEdit) return fail(res, 403, 'Недостаточно прав');
    if (col === 'invoices' && patch.orderId !== undefined) {
      if (!db.orders[patch.orderId]) return fail(res, 400, 'Заказ не найден');
      patch.projectId = db.orders[patch.orderId].projectId || null;
    }
    if (col === 'invoices' && patch.file !== undefined && (patch.file && patch.file.id) !== (db[col][id].file && db[col][id].file.id)) {
      SEEN_FIELDS.forEach(f => { patch[f] = null; });   // new invoice file: the accountant has not seen it yet
    }
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
    const d = db[col][id];
    if (col === 'points') {
      if (!mayEditPoint(user, d)) return fail(res, 403, 'Удалить точку может её автор, менеджер или администратор');
    } else if (!canEdit(user) && !(col === 'invoices' && ownsInvoice(user, d))) return fail(res, 403, 'Недостаточно прав');
    if (col === 'projects' && listOf('orders').some(o => o.projectId === id)) return fail(res, 409, 'В проекте есть заказы');
    if (col === 'orders' && listOf('invoices').some(i => i.orderId === id)) return fail(res, 409, 'По заказу есть счета');
    if (col === 'counterparties' && listOf('orders').some(o => o.customerId === id)) return fail(res, 409, 'Контрагент указан заказчиком в заказах');
    if (col === 'invoices' && d.status === 'paid') return fail(res, 409, 'Оплаченный счёт удалить нельзя');
    delete db[col][id]; saveDb();
    return send(res, 200, { ok: true, rev: db.rev });
  }
  return fail(res, 405, 'Метод не поддерживается');
}
const publicUser = u => ({ id: u.id, login: u.login, name: u.name, role: u.role, roleName: ROLES[u.role] });
/* Map background: OpenStreetMap by default, another tile source can be set in sed.env */
const MAP = {
  tiles: process.env.MAP_TILES || 'https://tile.openstreetmap.org/{z}/{x}/{y}.png',
  attribution: process.env.MAP_ATTRIBUTION || '&copy; <a href="https://www.openstreetmap.org/copyright" target="_blank" rel="noopener">OpenStreetMap</a>',
  subdomains: process.env.MAP_SUBDOMAINS || 'abc',
  maxZoom: Number(process.env.MAP_MAX_ZOOM || 19),
};
const meInfo = u => ({ ...publicUser(u), map: MAP });
const adminUser = u => ({ ...publicUser(u), blocked: !!u.blocked, lastLoginAt: u.lastLoginAt || null, createdAt: u.createdAt || null });

/* Remember that the accountant has opened the invoice file(s) */
function markSeen(user, fileIds) {
  if (user.role !== 'accountant') return;
  const ids = new Set([].concat(fileIds));
  const now = new Date().toISOString();
  let changed = false;
  for (const inv of Object.values(db.invoices)) {
    if (!inv.file || !ids.has(inv.file.id)) continue;
    if (!inv.seenAt) { inv.seenAt = now; inv.seenBy = user.id; }
    inv.seenLastAt = now; inv.seenCount = (inv.seenCount || 0) + 1;
    changed = true;
  }
  if (changed) saveDb();
}

/* ---------- ZIP of invoices to pay (stored, no compression; no dependencies) ---------- */
const CRC_TABLE = (() => {
  const t = new Uint32Array(256);
  for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c >>> 0; }
  return t;
})();
function crc32(buf) {
  let c = 0xFFFFFFFF;
  for (let i = 0; i < buf.length; i++) c = CRC_TABLE[(c ^ buf[i]) & 0xFF] ^ (c >>> 8);
  return (c ^ 0xFFFFFFFF) >>> 0;
}
const safeName = s => String(s || '').replace(/[\\/:*?"<>|\r\n\t]+/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 80) || 'без названия';
function writeAsync(res, buf) { return new Promise(r => { if (res.write(buf)) r(); else res.once('drain', r); }); }

async function sendInvoicesZip(res, user, orderFilter) {
  const list = Object.entries(db.invoices).map(([id, i]) => ({ id, ...i }))
    .filter(i => i.status === 'topay' && (!orderFilter || i.orderId === orderFilter))
    .sort((a, b) => String((db.orders[a.orderId] || {}).number || '').localeCompare(String((db.orders[b.orderId] || {}).number || ''), 'ru', { numeric: true })
      || String(a.due || '9').localeCompare(String(b.due || '9')));
  if (!list.length) return fail(res, 404, 'Нет счетов к оплате');

  const now = new Date();
  const dosTime = ((now.getHours() << 11) | (now.getMinutes() << 5) | (now.getSeconds() >> 1)) & 0xFFFF;
  const dosDate = (((now.getFullYear() - 1980) << 9) | ((now.getMonth() + 1) << 5) | now.getDate()) & 0xFFFF;
  const used = new Set(), central = [], seenIds = [];
  const unique = name => {
    let n = name, k = 2; const dot = name.lastIndexOf('.');
    while (used.has(n.toLowerCase())) { n = dot > name.lastIndexOf('/') ? `${name.slice(0, dot)} (${k})${name.slice(dot)}` : `${name} (${k})`; k++; }
    used.add(n.toLowerCase()); return n;
  };
  const csvCell = v => `"${String(v ?? '').replace(/"/g, '""')}"`;
  const money = n => (Number(n) || 0).toFixed(2).replace('.', ',');
  const fmtD = d => d ? String(d).split('-').reverse().join('.') : '';
  const rows = [['Заказ', 'Выставлен счёт заказчику', '№ счёта', 'Дата счёта', 'Поставщик', 'Назначение', 'Сумма, ₽', 'Оплатить до', 'Файл в архиве']];
  let total = 0;

  const stamp = new Date().toISOString().slice(0, 10);
  const zipName = `Счета к оплате ${stamp}.zip`;
  res.writeHead(200, {
    ...SEC_HEADERS,
    'Content-Type': 'application/zip',
    'Content-Disposition': `attachment; filename="invoices-${stamp}.zip"; filename*=UTF-8''${encodeURIComponent(zipName)}`,
    'Cache-Control': 'no-store',
  });
  let offset = 0;
  const addEntry = async (name, data) => {
    const nameBuf = Buffer.from(name, 'utf8'), crc = crc32(data);
    const h = Buffer.alloc(30);
    h.writeUInt32LE(0x04034b50, 0); h.writeUInt16LE(20, 4); h.writeUInt16LE(0x0800, 6); h.writeUInt16LE(0, 8);
    h.writeUInt16LE(dosTime, 10); h.writeUInt16LE(dosDate, 12); h.writeUInt32LE(crc, 14);
    h.writeUInt32LE(data.length, 18); h.writeUInt32LE(data.length, 22); h.writeUInt16LE(nameBuf.length, 26); h.writeUInt16LE(0, 28);
    central.push({ nameBuf, crc, size: data.length, offset });
    await writeAsync(res, h); await writeAsync(res, nameBuf); await writeAsync(res, data);
    offset += 30 + nameBuf.length + data.length;
  };

  for (const i of list) {
    const o = db.orders[i.orderId] || {};
    const folder = safeName(`Заказ ${o.number || '—'} ${o.title || ''}`);
    let inZip = 'нет файла';
    const meta = i.file && db.files[i.file.id];
    if (meta) {
      const fp = path.join(FILES_DIR, i.file.id);
      let data = null; try { data = fs.readFileSync(fp); } catch {}
      if (data) {
        const orig = meta.name || i.file.name || '';
        const ext = /\.[A-Za-z0-9]{1,6}$/.test(orig) ? orig.slice(orig.lastIndexOf('.')) : '';
        inZip = unique(`${folder}/Счёт ${safeName(i.number)} ${safeName(i.supplier)}${ext}`);
        await addEntry(inZip, data);
        seenIds.push(i.file.id);
      } else inZip = 'файл не найден на сервере';
    }
    total += Number(i.amount) || 0;
    rows.push([`${o.number || ''} ${o.title || ''}${o.orderNo ? ` (заказ № ${o.orderNo})` : ''}`.trim(), o.billNo ? `№ ${o.billNo}${o.billDate ? ' от ' + fmtD(o.billDate) : ''}` : '',
      i.number, fmtD(i.date), i.supplier, i.purpose, money(i.amount), fmtD(i.due), inZip]);
  }
  rows.push(['Итого', '', '', '', '', '', money(total), '', '']);
  await addEntry(unique('Реестр счетов к оплате.csv'), Buffer.from('\ufeff' + rows.map(r => r.map(csvCell).join(';')).join('\r\n'), 'utf8'));

  const cdStart = offset; let cdSize = 0;
  for (const e of central) {
    const c = Buffer.alloc(46);
    c.writeUInt32LE(0x02014b50, 0); c.writeUInt16LE(20, 4); c.writeUInt16LE(20, 6); c.writeUInt16LE(0x0800, 8); c.writeUInt16LE(0, 10);
    c.writeUInt16LE(dosTime, 12); c.writeUInt16LE(dosDate, 14); c.writeUInt32LE(e.crc, 16);
    c.writeUInt32LE(e.size, 20); c.writeUInt32LE(e.size, 24); c.writeUInt16LE(e.nameBuf.length, 28);
    c.writeUInt32LE(e.offset, 42);
    await writeAsync(res, c); await writeAsync(res, e.nameBuf);
    cdSize += 46 + e.nameBuf.length;
  }
  const end = Buffer.alloc(22);
  end.writeUInt32LE(0x06054b50, 0); end.writeUInt16LE(central.length, 8); end.writeUInt16LE(central.length, 10);
  end.writeUInt32LE(cdSize, 12); end.writeUInt32LE(cdStart, 16);
  res.end(end);
  markSeen(user, seenIds);
}

function serveFile(req, res, id) {
  const user = sessionUser(req);
  if (!user) return fail(res, 401, 'Требуется вход');
  const meta = db.files[id];
  if (!meta || !/^[\w-]+$/.test(id)) return fail(res, 404, 'Файл не найден');
  const fp = path.join(FILES_DIR, id);
  if (!fs.existsSync(fp)) return fail(res, 404, 'Файл не найден');
  markSeen(user, id);
  const inline = INLINE.has(meta.type);
  const enc = encodeURIComponent(meta.name);
  res.writeHead(200, {
    ...SEC_HEADERS,
    'Content-Type': inline ? meta.type + (meta.type.startsWith('text/') ? '; charset=utf-8' : '') : 'application/octet-stream',
    'Content-Length': meta.size,
    'Content-Disposition': `${inline ? 'inline' : 'attachment'}; filename="${enc}"; filename*=UTF-8''${enc}`,
    'Content-Security-Policy': "default-src 'none'; img-src 'self'; style-src 'unsafe-inline'; sandbox",
    'Cache-Control': 'private, no-cache',
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
      console.log(`Управление предприятием: запущено на сокете ${LISTEN_SOCKET}  (данные: ${DATA_DIR})`);
    });
  } else {
    server.listen(PORT, HOST, () => console.log(`Управление предприятием: запущено на http://${HOST === '0.0.0.0' ? 'localhost' : HOST}:${PORT}  (данные: ${DATA_DIR})`));
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
  } else if (cmd === 'unblock') {
    need(1);
    const u = users.find(x => x.login === args[0].toLowerCase()); if (!u) { console.error('Нет такого пользователя'); process.exit(1); }
    u.blocked = false; saveUsers(); console.log('Блокировка снята.');
  } else if (cmd === 'users') {
    if (!users.length) console.log('Пользователей нет.');
    users.forEach(u => console.log(`${u.login.padEnd(20)} ${ROLES[u.role].padEnd(14)} ${u.blocked ? 'ЗАБЛОКИРОВАН  ' : ''}${u.name}`));
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

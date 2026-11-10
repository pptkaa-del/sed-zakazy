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
 *   node server.js backup  [файл.json]     выгрузить все записи основной организации в JSON
 *   node server.js orgs                    организации и их состояние
 *   node server.js orgunblock <id>         снять блокировку организации и срок
 *   node server.js archive [код]           резервная копия всей системы или организации (папка backups)
 *   node server.js restore <файл.zip> [код] восстановить систему или организацию из копии
 *
 * Настройки берутся из переменных окружения и из файла sed.env рядом с server.js
 * (строки вида КЛЮЧ=значение; переменные окружения важнее файла).
 *
 * Роли: admin, manager, accountant, user (руководитель), worker (работник), viewer.
 * Организации: у каждой свои данные и пользователи. «Основная» хранится прямо в DATA_DIR,
 * остальные — в DATA_DIR/orgs/<id>/. Администратор системы (флаг sys) заводит и блокирует организации.
 */
const http = require('node:http');
const fs = require('node:fs');
const path = require('node:path');
const crypto = require('node:crypto');
const { AsyncLocalStorage } = require('node:async_hooks');
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
const PUBLIC_DIR = path.join(__dirname, 'public');
const MAX_FILE = Number(process.env.MAX_FILE_MB || 50) * 1048576;
const MAX_BACKUP = Number(process.env.BACKUP_MAX_MB || 2048) * 1048576;
const BACKUP_DIR = path.join(DATA_DIR, 'backups');
const MAX_JSON = 4 * 1048576;
const SESSION_DAYS = Number(process.env.SESSION_DAYS || 14);
const COOKIE_SECURE = process.env.COOKIE_SECURE === '1';
const TRUST_PROXY = process.env.TRUST_PROXY !== '0';

const COLLECTIONS = ['projects', 'orders', 'invoices', 'tasks', 'counterparties', 'points', 'stock', 'jobs'];
const ROLES = {
  admin:      'Администратор',
  manager:    'Менеджер',
  accountant: 'Бухгалтер',
  user:       'Руководитель',
  worker:     'Работник',
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
const canWork = u => u.role !== 'viewer' && u.role !== 'worker';
/* Assignments («Задачи сотрудникам»): admins, managers and leaders create them; a worker sees only his own and changes only the status */
const canLead = u => canEdit(u) || u.role === 'user';
const JOB_STATUS = ['new', 'work', 'done'];
const JOB_WORKER_FIELDS = ['status', 'report'];
const onJob = (u, j) => j.leaderId === u.id || (j.workers || []).includes(u.id);
const mayEditJob = (u, j) => canEdit(u) || (u.role === 'user' && (j.createdBy === u.id || j.leaderId === u.id));
function cleanJob(d){
  const out = {};
  if ('title' in d) out.title = String(d.title || '').trim().slice(0, 200);
  if ('description' in d) out.description = String(d.description || '').slice(0, 4000);
  if ('due' in d) out.due = /^\d{4}-\d{2}-\d{2}$/.test(d.due || '') ? d.due : '';
  if ('start' in d) out.start = /^\d{4}-\d{2}-\d{2}$/.test(d.start || '') ? d.start : '';
  if ('orderId' in d) out.orderId = d.orderId && db.orders[d.orderId] ? d.orderId : null;
  if ('leaderId' in d) { const l = orgUsers().find(u => u.id === d.leaderId); out.leaderId = l && ['admin', 'manager', 'user'].includes(l.role) ? l.id : null; }
  if ('workers' in d) out.workers = [...new Set((Array.isArray(d.workers) ? d.workers : []).filter(id => orgUsers().some(u => u.id === id)))].slice(0, 50);
  // up to 5000 places: points from «Редактор карты» keep the object number and its marks
  if ('places' in d) out.places = (Array.isArray(d.places) ? d.places : []).slice(0, 5000)
    .filter(x => x && Number.isFinite(Number(x.lat)) && Number.isFinite(Number(x.lng)) && Math.abs(x.lat) <= 90 && Math.abs(x.lng) <= 180)
    .map(x => ({ id: String(x.id || newId()).slice(0, 40), lat: Math.round(Number(x.lat) * 1e6) / 1e6, lng: Math.round(Number(x.lng) * 1e6) / 1e6, label: String(x.label || '').trim().slice(0, 200),
      ...(x.assignee && users.some(u => u.id === x.assignee) ? { assignee: String(x.assignee) } : {}),
      ...(x.dtNo ? { dtNo: String(x.dtNo).slice(0, 60), cats: (Array.isArray(x.cats) ? x.cats : []).filter(c => ['mkad', 'ttk', 'bridge', 'other', 'check'].includes(c)), road: String(x.road || '').slice(0, 200) } : {}) }));
  if ('report' in d) out.report = String(d.report || '').slice(0, 4000);
  // which photos a worker must take at every point, e.g. «Общий вид», «До замены», «После замены»
  if ('photoSpec' in d) out.photoSpec = [...new Set((Array.isArray(d.photoSpec) ? d.photoSpec : String(d.photoSpec || '').split('\n')).map(x => String(x).trim().slice(0, 80)).filter(Boolean))].slice(0, 20);
  if ('status' in d) out.status = d.status;
  return out;
}
/* Warehouse: managers and admins keep the item list; they and «Сотрудник» record receipts and issues */
const canMoveStock = u => canEdit(u) || u.role === 'user';
const qtyOk = v => Number.isFinite(Number(v)) && Number(v) > 0 && Number(v) < 1e9;
const mayEditPoint = (u, pt) => canEdit(u) || pt.createdBy === u.id;
/* Invoice lines (goods): cleaned on every save; the receipt to the warehouse is posted through its own endpoint */
const r3 = v => Math.round(Number(v) * 1000) / 1000, r2 = v => Math.round(Number(v) * 100) / 100;
function cleanItems(list){
  if (!Array.isArray(list)) return [];
  return list.slice(0, 500).map(x => ({
    id: String(x && x.id || newId()).slice(0, 40),
    name: String(x && x.name || '').trim().slice(0, 300),
    sku: String(x && x.sku || '').trim().slice(0, 100),
    unit: String(x && x.unit || 'шт').trim().slice(0, 20) || 'шт',
    qty: qtyOk(x && x.qty) ? r3(x.qty) : 0,
    price: Number.isFinite(Number(x && x.price)) && Number(x.price) >= 0 ? r2(x.price) : 0,
    sum: Number.isFinite(Number(x && x.sum)) && Number(x.sum) >= 0 ? r2(x.sum) : 0,
    stockId: x && x.stockId && db.stock[x.stockId] ? x.stockId : null,
  })).filter(x => x.name);
}
/* The order's purchase lines bought by this invoice get its supplier and number:
   lines whose name matches a line of the invoice, or that already carry its number; a line with a supplier is left alone */
function fillOrderSuppliers(inv){
  const o = inv && db.orders[inv.orderId];
  if (!o || !Array.isArray(o.components) || !String(inv.supplier || '').trim()) return 0;
  const names = (inv.items || []).map(x => normName(x.name)).filter(Boolean), num = String(inv.number || '').trim();
  let n = 0;
  for (const c of o.components) {
    if (String(c.supplier || '').trim()) continue;
    const cn = normName(c.name); if (!cn) continue;
    const hit = (num && String(c.invNo || '').trim() === num) || names.some(x => x === cn || (cn.length >= 6 && x.includes(cn)) || (x.length >= 6 && cn.includes(x)));
    if (!hit) continue;
    c.supplier = inv.supplier; if (!String(c.invNo || '').trim() && num) c.invNo = num; n++;
  }
  if (n) { o.updatedAt = new Date().toISOString(); }
  return n;
}
/* Supplier of an invoice: found among counterparties by INN or name, otherwise added */
function ensureSupplier(name, inn, user, note){
  name = String(name || '').trim(); inn = String(inn || '').replace(/\D/g, '').slice(0, 12);
  if (!name) return { id: null, created: false };
  const all = listOf('counterparties');
  let c = (inn && all.find(x => x.inn === inn)) || all.find(x => normName(x.name) === normName(name));
  if (c) {
    const d = db.counterparties[c.id];
    if (!(d.roles || []).includes('supplier')) d.roles = [...(d.roles || []), 'supplier'];
    if (inn && !d.inn) d.inn = inn;
    return { id: c.id, created: false };
  }
  const id = newId();
  db.counterparties[id] = { name, inn, roles: ['supplier'], contacts: [], contracts: [], comments: [], note, createdAt: new Date().toISOString(), createdBy: user.id };
  return { id, created: true };
}
const validPoint = d => Number.isFinite(Number(d.lat)) && Number.isFinite(Number(d.lng)) && Math.abs(d.lat) <= 90 && Math.abs(d.lng) <= 180;

/* Version of the running app: changes when the code is updated, so open pages can offer a reload */
const APP_VERSION = crypto.createHash('sha1')
  .update(fs.readFileSync(path.join(__dirname, 'server.js')))
  .update((() => { try { return fs.readFileSync(path.join(__dirname, 'public', 'index.html')); } catch { return ''; } })())
  .digest('hex').slice(0, 12);

fs.mkdirSync(path.join(DATA_DIR, 'files'), { recursive: true });

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
const USERS_FILE = path.join(DATA_DIR, 'users.json');
const ORGS_FILE = path.join(DATA_DIR, 'orgs.json');
const SECRET_FILE = path.join(DATA_DIR, 'secret.key');

function loadDb(file) {
  const d = readJSON(file, { rev: 0, files: {} });
  COLLECTIONS.forEach(c => { d[c] = d[c] || {}; });
  // permanent task numbers, the same for everyone who sees the task
  let jn = Math.max(0, ...Object.values(d.jobs).map(j => j.no || 0));
  Object.values(d.jobs).filter(j => !j.no).sort((a, b) => (a.createdAt || '').localeCompare(b.createdAt || '')).forEach(j => { j.no = ++jn; });
  d.files = d.files || {};
  d.meta = d.meta || {};
  d.dt = d.dt || null;
  return d;
}
/* The hosting may run several copies of the app (e.g. Passenger) or a CLI command may edit
   users while the server runs: re-read files when another process has changed them. */
const stamp = f => { try { const st = fs.statSync(f); return st.mtimeMs + ':' + st.size + ':' + st.ino; } catch { return ''; } };

/* ---------- organizations: each has its own data file and attachments ---------- */
const MAIN_ORG = 'main';
const orgDir = id => id === MAIN_ORG ? DATA_DIR : path.join(DATA_DIR, 'orgs', id);
const firstRun = !fs.existsSync(ORGS_FILE);
let orgs = readJSON(ORGS_FILE, null), orgsStamp;
let users = readJSON(USERS_FILE, []), usersStamp;
if (!orgs) {
  // update from a single-company install: its data and users become the main organization, its admins — system administrators
  orgs = [{ id: MAIN_ORG, name: process.env.ORG_NAME || 'Основная организация', createdAt: new Date().toISOString() }];
  users.forEach(u => { if (!u.orgId) { u.orgId = MAIN_ORG; if (u.role === 'admin') u.sys = true; } });
  if (users.length) writeJSON(USERS_FILE, users);
  writeJSON(ORGS_FILE, orgs);
}
orgsStamp = stamp(ORGS_FILE); usersStamp = stamp(USERS_FILE);
const normUsers = () => users.forEach(u => { if (!u.orgId) u.orgId = MAIN_ORG; });
normUsers();
function syncFromDisk() {
  const b = stamp(USERS_FILE); if (b !== usersStamp) { users = readJSON(USERS_FILE, []); normUsers(); usersStamp = b; }
  const c = stamp(ORGS_FILE); if (c !== orgsStamp) { orgs = readJSON(ORGS_FILE, orgs); orgsStamp = c; }
}
const saveUsers = () => { writeJSON(USERS_FILE, users); usersStamp = stamp(USERS_FILE); };
const saveOrgs = () => { writeJSON(ORGS_FILE, orgs); orgsStamp = stamp(ORGS_FILE); };
const orgById = id => orgs.find(o => o.id === id);

/* the database of the organization the current request works in (AsyncLocalStorage keeps it per request) */
const dbs = new Map();
function orgEntry(id) {
  let e = dbs.get(id);
  if (!e) {
    const dir = orgDir(id);
    e = { id, file: path.join(dir, 'db.json'), files: path.join(dir, 'files') };
    fs.mkdirSync(e.files, { recursive: true });
    e.db = loadDb(e.file); e.stamp = stamp(e.file);
    dbs.set(id, e);
  } else { const st = stamp(e.file); if (st !== e.stamp) { e.db = loadDb(e.file); e.stamp = st; } }
  return e;
}
const als = new AsyncLocalStorage();
const ctx = () => { const e = als.getStore(); if (!e) throw new Error('Нет контекста организации'); return e; };
const db = new Proxy({}, {
  get: (_, k) => ctx().db[k],
  set: (_, k, v) => { ctx().db[k] = v; return true; },
  has: (_, k) => k in ctx().db,
});
const filesDir = () => ctx().files;
const saveDb = () => { const e = ctx(); e.db.rev++; writeJSON(e.file, e.db); e.stamp = stamp(e.file); };
const orgUsers = () => { const id = ctx().id; return users.filter(u => u.orgId === id); };

/* blocked by the system administrator or the paid term is over (the last day still works) */
const localDate = (d = new Date()) => `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`;
const ruDate = s => s ? s.split('-').reverse().join('.') : '';
function orgState(o) {
  if (!o) return { blocked: true, message: 'Организация не найдена. Обратитесь к администратору системы.' };
  if (o.blocked) return { blocked: true, reason: 'manual', message: `Доступ организации «${o.name}» заблокирован администратором системы.${o.blockNote ? ' ' + o.blockNote : ''} Обратитесь к администратору системы.` };
  if (o.until && localDate() > o.until) return { blocked: true, reason: 'expired', message: `Срок работы организации «${o.name}» истёк ${ruDate(o.until)}. Доступ заблокирован. Для продления обратитесь к администратору системы.` };
  const left = o.until ? Math.round((Date.parse(o.until) - Date.parse(localDate())) / 864e5) : null;
  return { blocked: false, left, warn: left !== null && left <= 7 ? `Доступ организации действует до ${ruDate(o.until)} включительно${left === 0 ? ' (последний день)' : ` (осталось ${left} дн.)`}.` : '' };
}

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
  const blockedFail = st => send(res, 423, { error: st.message, orgBlocked: true });
  if (p[1] === 'setup' && m === 'POST') {
    if (users.length) return fail(res, 409, 'Администратор уже создан. Войдите со своим логином');
    const b = await readJsonBody(req);
    const err = validateUser(b, true); if (err) return fail(res, 400, err);
    const u = addUser(String(b.login), 'admin', String(b.name).trim(), String(b.password), MAIN_ORG, true);
    console.log(`Через браузер создан администратор системы «${u.login}».`);
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
    const ost = orgState(orgById(u.orgId)); if (ost.blocked) return blockedFail(ost);
    u.lastLoginAt = new Date().toISOString(); saveUsers();
    return send(res, 200, meInfo(u), { 'Set-Cookie': cookie(req, makeSession(u), SESSION_DAYS * 86400) });
  }
  if (p[1] === 'logout' && m === 'POST') return send(res, 200, { ok: true }, { 'Set-Cookie': cookie(req, '', 0) });

  const user = sessionUser(req);
  if (!user) return fail(res, 401, 'Требуется вход');

  const ost = orgState(orgById(user.orgId));
  if (ost.blocked) return blockedFail(ost);
  if (p[1] === 'me' && m === 'GET') return send(res, 200, meInfo(user));
  if (p[1] === 'orgs') return orgsApi(req, res, p, m, user);
  if (p[1] === 'backups') return backupsApi(req, res, p, m, user);
  // «Работник» sees and changes only the assignments given to him
  if (user.role === 'worker' && !['rev', 'data', 'password', 'jobs'].includes(p[1])) return fail(res, 403, 'Недостаточно прав');
  if (p[1] === 'users') {
    if (user.role !== 'admin') return fail(res, 403, 'Управлять пользователями может только администратор');
    const target = p[2] && orgUsers().find(u => u.id === p[2]);
    if (m === 'GET' && !p[2]) return send(res, 200, orgUsers().map(adminUser));
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req);
      const err = validateUser(b, true); if (err) return fail(res, 400, err);
      if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
      return send(res, 200, adminUser(addUser(String(b.login), b.role, String(b.name).trim(), String(b.password), user.orgId)));
    }
    if (!target) return fail(res, 404, 'Пользователь не найден');
    if (target.sys && !user.sys) return fail(res, 403, 'Учётную запись администратора системы меняет только он сам');
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
      if (target.sys) return fail(res, 400, 'Администратора системы удалить нельзя');
      users = users.filter(u => u.id !== target.id); saveUsers();
      return send(res, 200, { ok: true });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'rev' && m === 'GET') return send(res, 200, { rev: db.rev, version: APP_VERSION });
  if (p[1] === 'data' && m === 'GET') {
    const out = { rev: db.rev, users: Object.fromEntries(orgUsers().map(u => [u.id, u.name])), meta: db.meta,
      staff: orgUsers().filter(u => !u.blocked).map(u => ({ id: u.id, name: u.name, role: u.role })) };
    const mine = j => ({ ...j, places: (j.places || []).filter(x => !x.assignee || x.assignee === user.id) });
    COLLECTIONS.forEach(c => { out[c] = user.role === 'worker' ? (c === 'jobs' ? listOf(c).filter(j => (j.workers || []).includes(user.id)).map(mine) : []) : listOf(c); });
    if (user.role === 'worker') { out.meta = {}; out.staff = []; }
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

  /* accounting balances from a 1C export: rows are matched by article, then by name */
  /* «Редактор карты»: objects with coordinates from a spreadsheet; which of them stand on the MKAD, the TTK or an overpass
     is worked out in the browser from OpenStreetMap and stored here, so everybody sees the same result */
  if (p[1] === 'dt') {
    if (m === 'GET') return send(res, 200, db.dt || { points: [] });
    if (m === 'PUT') {
      if (!canEdit(user)) return fail(res, 403, 'Загружать точки может менеджер или администратор');
      const b = await readJsonBody(req);
      const CATS = ['mkad', 'ttk', 'bridge', 'other', 'check'];
      if (!Array.isArray(b.points) || b.points.length > 50000) return fail(res, 400, 'Нет точек или их слишком много');
      const points = b.points.map(x => ({
        no: String(x.no ?? '').trim().slice(0, 60), lat: Number(x.lat), lng: Number(x.lng),
        cats: (Array.isArray(x.cats) ? x.cats : []).filter(c => CATS.includes(c)),
        road: String(x.road || '').slice(0, 200), bridge: String(x.bridge || '').slice(0, 200), other: String(x.other || '').slice(0, 300),
        dist: x.dist != null && x.dist !== '' && Number.isFinite(Number(x.dist)) ? Math.round(Number(x.dist) * 10) / 10 : null, note: String(x.note || '').slice(0, 300),
        ...(x.checkedAt ? { checkedAt: String(x.checkedAt).slice(0, 40), checkedBy: String(x.checkedBy || '').slice(0, 40), checkedWas: String(x.checkedWas || '').slice(0, 40) } : {}),
        ...(x.addedAt ? { addedAt: String(x.addedAt).slice(0, 40), addedBy: String(x.addedBy || '').slice(0, 40) } : {}),
        ...(x.assignee ? { assignee: String(x.assignee).slice(0, 40), assignedAt: String(x.assignedAt || '').slice(0, 40), assignedBy: String(x.assignedBy || '').slice(0, 40) } : {}),
      })).filter(x => Number.isFinite(x.lat) && Number.isFinite(x.lng) && Math.abs(x.lat) <= 90 && Math.abs(x.lng) <= 180);
      if (!points.length) return fail(res, 400, 'Не нашлось ни одной точки с координатами');
      // a new file of the same objects keeps who they were assigned to
      const prev = new Map(((db.dt && db.dt.points) || []).filter(x => x.assignee).map(x => [x.no, x]));
      points.forEach(x => { const o = prev.get(x.no); if (o && !x.assignee) Object.assign(x, { assignee: o.assignee, assignedAt: o.assignedAt, assignedBy: o.assignedBy }); });
      db.dt = { points, file: String(b.file || '').slice(0, 200), at: new Date().toISOString(), by: user.id,
        classifiedAt: b.classifiedAt || null, radius: b.radius || null, source: String(b.source || '').slice(0, 200) };
      saveDb();
      return send(res, 200, { ok: true, count: points.length, rev: db.rev });
    }
    /* the answer for a point marked «проверить»: what it really stands on */
    if (m === 'PATCH' && p[2] === 'point') {
      if (!(canEdit(user) || user.role === 'user')) return fail(res, 403, 'Отмечать проверку может руководитель, менеджер или администратор');
      const b = await readJsonBody(req), P = db.dt && db.dt.points, i = Number(b.i);
      if (!P || !Number.isInteger(i) || !P[i] || P[i].no !== String(b.no ?? '')) return fail(res, 409, 'Точка не найдена — обновите страницу');
      const cats = (Array.isArray(b.cats) ? b.cats : []).filter(c => ['mkad', 'ttk', 'bridge', 'other'].includes(c));
      const pt = P[i];
      if (cats.includes('other') && !String(b.other || '').trim()) return fail(res, 400, 'Укажите, что именно «другое»');
      if (!pt.checkedAt) pt.checkedWas = (pt.cats || []).join(',');
      pt.cats = cats.includes('other') ? ['other'] : [...new Set(cats)]; pt.other = cats.includes('other') ? String(b.other).trim().slice(0, 300) : '';
      pt.checkedAt = new Date().toISOString(); pt.checkedBy = user.id;
      saveDb();
      return send(res, 200, { ok: true, point: pt, rev: db.rev });
    }
    /* assign (or clear) the executor of many points at once */
    if (m === 'PATCH' && p[2] === 'assign') {
      if (!(canEdit(user) || user.role === 'user')) return fail(res, 403, 'Назначать исполнителя может руководитель, менеджер или администратор');
      const b = await readJsonBody(req), P = db.dt && db.dt.points;
      if (!P) return fail(res, 409, 'Точек нет');
      const who = b.assignee ? orgUsers().find(u => u.id === b.assignee && !u.blocked) : null;
      if (b.assignee && !who) return fail(res, 400, 'Исполнитель не найден');
      const nos = new Set((Array.isArray(b.nos) ? b.nos : []).map(String));
      if (!nos.size) return fail(res, 400, 'Не выделено ни одной точки');
      const at = new Date().toISOString(); let n = 0;
      for (const x of P) if (nos.has(x.no)) {
        if (who) Object.assign(x, { assignee: who.id, assignedAt: at, assignedBy: user.id }); else { delete x.assignee; delete x.assignedAt; delete x.assignedBy; }
        n++;
      }
      saveDb();
      return send(res, 200, { ok: true, count: n, rev: db.rev });
    }
    /* a point added by hand on the map, and removing a point */
    if (m === 'POST' && p[2] === 'point') {
      if (!(canEdit(user) || user.role === 'user')) return fail(res, 403, 'Добавлять точки может руководитель, менеджер или администратор');
      const b = await readJsonBody(req), lat = Number(b.lat), lng = Number(b.lng), no = String(b.no ?? '').trim().slice(0, 60);
      if (!no) return fail(res, 400, 'Укажите номер объекта');
      if (!(Number.isFinite(lat) && Number.isFinite(lng) && Math.abs(lat) <= 90 && Math.abs(lng) <= 180 && (lat || lng))) return fail(res, 400, 'Неверные координаты');
      if (!db.dt) db.dt = { points: [], file: '', at: new Date().toISOString(), by: user.id, classifiedAt: null, radius: null, source: '' };
      if (db.dt.points.some(x => x.no === no)) return fail(res, 409, `Объект ${no} уже есть на карте`);
      const cats = (Array.isArray(b.cats) ? b.cats : []).filter(c => ['mkad', 'ttk', 'bridge', 'other'].includes(c));
      if (cats.includes('other') && !String(b.other || '').trim()) return fail(res, 400, 'Укажите, что именно «другое»');
      const pt = { no, lat: Math.round(lat * 1e6) / 1e6, lng: Math.round(lng * 1e6) / 1e6, cats: cats.includes('other') ? ['other'] : cats, other: cats.includes('other') ? String(b.other).trim().slice(0, 300) : '',
        road: String(b.road || '').trim().slice(0, 200), bridge: '', dist: null, note: String(b.note || '').slice(0, 300), addedAt: new Date().toISOString(), addedBy: user.id };
      db.dt.points.push(pt); saveDb();
      return send(res, 200, { ok: true, i: db.dt.points.length - 1, point: pt, rev: db.rev });
    }
    if (m === 'DELETE' && p[2] === 'point') {
      if (!canEdit(user)) return fail(res, 403, 'Удалять точки может менеджер или администратор');
      const b = await readJsonBody(req), P = db.dt && db.dt.points, i = Number(b.i);
      if (!P || !Number.isInteger(i) || !P[i] || P[i].no !== String(b.no ?? '')) return fail(res, 409, 'Точка не найдена — обновите страницу');
      P.splice(i, 1); saveDb();
      return send(res, 200, { ok: true, rev: db.rev });
    }
    if (m === 'POST' && p[2] === 'overpass') {
      // the same Overpass query from the server, for browsers that cannot reach OpenStreetMap themselves
      if (!canEdit(user)) return fail(res, 403, 'Недостаточно прав');
      const b = await readJsonBody(req), q = String(b.q || '');
      if (!q || q.length > 200000 || !/^\[out:json\]/.test(q)) return fail(res, 400, 'Неверный запрос');
      const errs = [];
      for (const url of ['https://maps.mail.ru/osm/tools/overpass/api/interpreter', 'https://overpass-api.de/api/interpreter', 'https://overpass.kumi.systems/api/interpreter']) {
        try {
          const enc = encodeURIComponent(q), viaGet = enc.length < 7000;   // GET: the mail.ru mirror refuses POST
          const r = await fetch(viaGet ? url + '?data=' + enc : url, { method: viaGet ? 'GET' : 'POST', body: viaGet ? undefined : 'data=' + enc, headers: { ...(viaGet ? {} : { 'Content-Type': 'application/x-www-form-urlencoded' }), 'User-Agent': 'sed-zakazy' }, signal: AbortSignal.timeout(200e3) });
          if (!r.ok) { errs.push(new URL(url).host + ': ' + r.status); continue; }
          const text = await r.text();
          return send(res, 200, text, { 'Content-Type': 'application/json; charset=utf-8' });
        } catch (e) { errs.push(new URL(url).host + ': ' + (e.name === 'TimeoutError' ? 'нет ответа' : e.cause?.code || e.message)); }
      }
      return fail(res, 502, 'сервер тоже не достучался до OpenStreetMap (' + errs.join('; ') + ')');
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'stock-acct' && m === 'POST') {
    if (!canEdit(user) && user.role !== 'accountant') return fail(res, 403, 'Загружать бухгалтерские остатки могут бухгалтер, менеджер или администратор');
    const b = await readJsonBody(req);
    const rows = Array.isArray(b.rows) ? b.rows.slice(0, 20000) : [];
    if (!rows.length) return fail(res, 400, 'В файле не найдено строк с остатками');
    const agg = new Map();
    for (const r of rows) {
      const name = String(r.name || '').trim(), sku = String(r.sku || '').trim(), qty = Number(r.qty);
      if (!name || !Number.isFinite(qty)) continue;
      const key = sku ? 'a:' + normName(sku) : 'n:' + normName(name);
      const cur = agg.get(key) || { name, sku, unit: String(r.unit || '').trim(), qty: 0 };
      cur.qty = Math.round((cur.qty + qty) * 1000) / 1000; agg.set(key, cur);
    }
    const items = Object.entries(db.stock);
    const bySku = new Map(items.filter(([, it]) => it.sku).map(([id, it]) => [normName(it.sku), id]));
    const byName = new Map(items.map(([id, it]) => [normName(it.name), id]));
    const seen = new Set(); let matched = 0, created = 0, skipped = 0;
    const now = new Date().toISOString();
    for (const r of agg.values()) {
      const id = (r.sku && bySku.get(normName(r.sku))) || byName.get(normName(r.name));
      if (id) { if (!seen.has(id)) { db.stock[id].acctQty = r.qty; seen.add(id); matched++; } else db.stock[id].acctQty = Math.round((db.stock[id].acctQty + r.qty) * 1000) / 1000; }
      else if (b.createMissing) {
        const nid = newId();
        db.stock[nid] = { name: r.name, sku: r.sku, unit: r.unit || 'шт', location: '', minQty: 0, note: 'Добавлено из выгрузки 1С', qty: 0, moves: [], acctQty: r.qty, createdAt: now, createdBy: user.id };
        seen.add(nid); created++;
      } else skipped++;
    }
    for (const [id, it] of items) if (!seen.has(id)) it.acctQty = 0;   // not in the export: nothing on the books
    db.meta.acct = { at: now, by: user.id, file: String(b.file || '').slice(0, 200), rows: agg.size, matched, created, skipped };
    saveDb();
    return send(res, 200, db.meta.acct);
  }

  /* write-off list for an order: Excel with highlighting */
  if (p[1] === 'orders' && p[3] === 'writeoff.xlsx' && m === 'GET') {
    const o = db.orders[p[2]];
    if (!o) return fail(res, 404, 'Заказ не найден');
    const buf = writeoffXlsx(o);
    const name = `Списание ${o.number || ''} ${o.title || ''}`.replace(/[\\/:*?"<>|]+/g, ' ').trim().slice(0, 90) + '.xlsx';
    res.writeHead(200, { ...SEC_HEADERS, 'Content-Type': 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
      'Content-Disposition': `attachment; filename="writeoff.xlsx"; filename*=UTF-8''${encodeURIComponent(name)}`, 'Content-Length': buf.length, 'Cache-Control': 'no-store' });
    return res.end(buf);
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
    fs.writeFileSync(path.join(filesDir(), id), buf);
    const type = String(req.headers['content-type'] || 'application/octet-stream').split(';')[0].trim().toLowerCase();
    db.files[id] = { name, type, size: buf.length, at: new Date().toISOString(), by: user.id };
    saveDb();
    return send(res, 200, { id, url: '/files/' + id, name, size: buf.length, at: db.files[id].at, by: user.id });
  }

  /* warehouse receipts and issues: the server keeps the balance */
  if (p[1] === 'stock' && p[3] === 'moves' && m === 'POST' && p.length === 4) {
    const it = db.stock[p[2]];
    if (!it) return fail(res, 404, 'Позиция склада не найдена');
    if (!canMoveStock(user)) return fail(res, 403, 'Недостаточно прав');
    const b = await readJsonBody(req);
    if (!['in', 'out'].includes(b.type)) return fail(res, 400, 'Укажите приход или расход');
    if (!qtyOk(b.qty)) return fail(res, 400, 'Количество должно быть больше нуля');
    const qty = Math.round(Number(b.qty) * 1000) / 1000;
    const bal = Number(it.qty) || 0;
    if (b.type === 'out' && qty > bal + 1e-9) return fail(res, 409, `На складе только ${bal} ${it.unit || ''}`.trim());
    if (b.orderId && !db.orders[b.orderId]) return fail(res, 400, 'Заказ не найден');
    it.qty = Math.round((bal + (b.type === 'in' ? qty : -qty)) * 1000) / 1000;
    it.moves = Array.isArray(it.moves) ? it.moves : [];
    const mv = { id: newId(), type: b.type, qty, orderId: b.orderId || null, note: String(b.note || '').slice(0, 500), by: user.id, at: new Date().toISOString(), balance: it.qty };
    it.moves.push(mv);
    it.updatedAt = mv.at; it.updatedBy = user.id;
    saveDb();
    return send(res, 200, { ok: true, qty: it.qty, move: mv });
  }

  /* receipt to the warehouse from the invoice lines: posted with its own button, cancelled by a manager or admin */
  if (p[1] === 'invoices' && p[3] === 'income' && p.length === 4) {
    const inv = db.invoices[p[2]];
    if (!inv) return fail(res, 404, 'Счёт не найден');
    const label = `счёту № ${inv.number || '—'}${inv.date ? ' от ' + inv.date.split('-').reverse().join('.') : ''}${inv.supplier ? ', ' + inv.supplier : ''}`;
    if (m === 'POST') {
      if (!canMoveStock(user)) return fail(res, 403, 'Недостаточно прав');
      if (inv.income) return fail(res, 409, 'Приход по этому счёту уже оприходован');
      const b = await readJsonBody(req);
      const lines = cleanItems(b.lines).filter(x => x.qty > 0);
      if (!lines.length) return fail(res, 400, 'Нет строк с количеством');
      const at = new Date().toISOString(), out = [];
      let created = 0;
      for (const ln of lines) {
        let it = ln.stockId && db.stock[ln.stockId];
        if (!it) {
          const all = listOf('stock');
          const f = (ln.sku && all.find(x => x.sku && normName(x.sku) === normName(ln.sku))) || all.find(x => normName(x.name) === normName(ln.name));
          if (f) it = db.stock[f.id];
        }
        let sid;
        if (it) sid = Object.keys(db.stock).find(k => db.stock[k] === it);
        else {
          sid = newId(); created++;
          it = db.stock[sid] = { name: ln.name, sku: ln.sku, unit: ln.unit, location: '', minQty: 0, note: 'Добавлено по ' + label, qty: 0, moves: [], acctQty: 0, createdAt: at, createdBy: user.id };
        }
        it.qty = r3((Number(it.qty) || 0) + ln.qty);
        it.moves = Array.isArray(it.moves) ? it.moves : [];
        const mv = { id: newId(), type: 'in', qty: ln.qty, orderId: inv.orderId || null, invoiceId: p[2], note: 'Приход по ' + label, by: user.id, at, balance: it.qty };
        it.moves.push(mv); it.updatedAt = at; it.updatedBy = user.id;
        out.push({ ...ln, stockId: sid, moveId: mv.id });
      }
      inv.items = out.map(({ moveId, ...x }) => x);
      inv.income = { at, by: user.id, lines: out };
      fillOrderSuppliers(inv);
      saveDb();
      return send(res, 200, { ok: true, lines: out.length, created, rev: db.rev });
    }
    if (m === 'DELETE') {
      if (!canEdit(user)) return fail(res, 403, 'Отменить приход может менеджер или администратор');
      if (!inv.income) return fail(res, 409, 'Приход не оприходован');
      // first check that every quantity is still on the shelf, then roll back
      for (const ln of inv.income.lines) {
        const it = db.stock[ln.stockId];
        if (it && (it.moves || []).some(x => x.id === ln.moveId) && (Number(it.qty) || 0) + 1e-9 < ln.qty)
          return fail(res, 409, `«${it.name}»: на складе ${it.qty} ${it.unit || ''}, часть прихода уже израсходована. Отменить приход нельзя`.replace(' ,', ','));
      }
      for (const ln of inv.income.lines) {
        const it = db.stock[ln.stockId]; if (!it) continue;
        const i = (it.moves || []).findIndex(x => x.id === ln.moveId); if (i < 0) continue;
        it.moves.splice(i, 1); it.qty = r3((Number(it.qty) || 0) - ln.qty);
        it.updatedAt = new Date().toISOString(); it.updatedBy = user.id;
      }
      delete inv.income; inv.updatedAt = new Date().toISOString(); inv.updatedBy = user.id;
      saveDb();
      return send(res, 200, { ok: true, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }

  /* a worker's report at a point of a job: the photos the job asks for, extra photos and a comment */
  if (p[1] === 'jobs' && p[3] === 'places' && p[4]) {
    const j = db.jobs[p[2]]; if (!j) return fail(res, 404, 'Работа не найдена');
    const pl = (j.places || []).find(x => x.id === p[4]); if (!pl) return fail(res, 404, 'Точка не найдена');
    const mayReport = mayEditJob(user, j) || ((j.workers || []).includes(user.id) && (!pl.assignee || pl.assignee === user.id)) || j.leaderId === user.id;
    if (!mayReport) return fail(res, 403, 'Это не ваша точка');
    const touch = () => { pl.reportAt = new Date().toISOString(); pl.reportBy = user.id; j.updatedAt = pl.reportAt; j.updatedBy = user.id; };
    pl.photos = pl.photos || {};
    // a closed point stays editable for the worker for 24 hours; managers and the leader may always correct it
    const boss = mayEditJob(user, j) || j.leaderId === user.id;
    if (pl.doneAt && !boss && Date.now() - Date.parse(pl.doneAt) > 864e5 && m !== 'GET') return fail(res, 409, 'Прошло больше суток после закрытия точки — изменить данные может руководитель');
    if (p[5] === 'done' && m === 'POST') {
      const b = await readJsonBody(req), notWorking = !!b.notWorking;
      const missing = (j.photoSpec || []).filter(n => !pl.photos[n]);
      if (missing.length && !notWorking) return fail(res, 400, 'Не хватает фото: ' + missing.join(', '));
      const at = new Date().toISOString(), first = !pl.doneAt;
      Object.assign(pl, { notWorking, comment: String(b.comment ?? pl.comment ?? '').slice(0, 4000) });
      if (first) { pl.doneAt = at; pl.doneBy = user.id; } else { pl.editedAt = at; pl.editedBy = user.id; }
      touch();
      // the job follows its points: in work after the first one, done when every point is closed
      const all = j.places || [], left = all.filter(x => !x.doneAt).length;
      if (!left && j.status !== 'done') Object.assign(j, { status: 'done', doneAt: at, doneBy: user.id });
      else if (left && j.status === 'new') Object.assign(j, { status: 'work', startedAt: at, startedBy: user.id });
      saveDb();
      return send(res, 200, { ok: true, place: pl, left, status: j.status, rev: db.rev });
    }
    if (p[5] === 'done' && m === 'DELETE') {
      if (!boss) return fail(res, 403, 'Открыть точку снова может руководитель');
      delete pl.doneAt; delete pl.doneBy; if (j.status === 'done') j.status = 'work';
      touch(); saveDb();
      return send(res, 200, { ok: true, place: pl, rev: db.rev });
    }
    if (p[5] === 'photo' && m === 'POST') {
      let slot = ''; try { slot = decodeURIComponent(String(req.headers['x-slot'] || '')).slice(0, 80); } catch {}
      let name = 'фото.jpg'; try { name = decodeURIComponent(String(req.headers['x-filename'] || 'фото.jpg')).replace(/[\\/\r\n"]/g, '_').slice(0, 200); } catch {}
      const type = String(req.headers['content-type'] || 'image/jpeg').split(';')[0].trim().toLowerCase();
      if (!/^image\//.test(type)) return fail(res, 400, 'Нужна фотография (изображение)');
      const buf = await readBody(req, MAX_FILE); if (!buf.length) return fail(res, 400, 'Пустой файл');
      const fid = newId(); fs.writeFileSync(path.join(filesDir(), fid), buf);
      db.files[fid] = { name, type, size: buf.length, at: new Date().toISOString(), by: user.id };
      const f = { id: fid, name, type, size: buf.length, at: db.files[fid].at, by: user.id };
      const key = slot && (j.photoSpec || []).includes(slot) ? slot : '_extra';
      if (key === '_extra') pl.photos._extra = [...(pl.photos._extra || []), f].slice(-20); else pl.photos[key] = f;
      touch(); saveDb();
      return send(res, 200, { ok: true, place: pl, rev: db.rev });
    }
    if (p[5] === 'photo' && m === 'DELETE') {
      const b = await readJsonBody(req);
      if (b.slot === '_extra') pl.photos._extra = (pl.photos._extra || []).filter(f => f.id !== b.id); else delete pl.photos[String(b.slot || '')];
      touch(); saveDb();
      return send(res, 200, { ok: true, place: pl, rev: db.rev });
    }
    if (p[5] === 'comment' && m === 'PATCH') {
      const b = await readJsonBody(req); pl.comment = String(b.comment || '').slice(0, 4000); touch(); saveDb();
      return send(res, 200, { ok: true, place: pl, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
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
    if (!(col === 'invoices' ? canAddInvoice(user) : col === 'points' ? canWork(user) : col === 'jobs' ? canLead(user) : canEdit(user))) return fail(res, 403, 'Недостаточно прав');
    let data = clean(await readJsonBody(req));
    if (col === 'jobs') {
      data = cleanJob({ ...data, status: undefined, report: undefined });
      if (!data.title) return fail(res, 400, 'Укажите, что нужно сделать');
      if (!data.workers || !data.workers.length) return fail(res, 400, 'Назначьте хотя бы одного работника');
      data.status = 'new'; data.report = ''; data.places = data.places || [];
      data.no = Math.max(0, ...Object.values(db.jobs).map(j => j.no || 0)) + 1;
      if (!data.leaderId) data.leaderId = canLead(user) ? user.id : null;
    }
    if (col === 'points') {
      if (!validPoint(data)) return fail(res, 400, 'Неверные координаты точки');
      data.lat = Number(data.lat); data.lng = Number(data.lng);
      data.status = 'todo'; delete data.doneAt; delete data.doneBy;
    }
    data.createdBy = user.id; data.createdAt = data.createdAt || new Date().toISOString();
    if (col === 'orders' || col === 'counterparties') data.comments = [];
    if (col === 'stock') { data.qty = 0; data.moves = []; data.acctQty = 0; }
    if (col === 'invoices') {
      if (!db.orders[data.orderId]) return fail(res, 400, 'Заказ не найден');
      data.projectId = db.orders[data.orderId].projectId || null;
      data.status = 'topay'; [...PAY_FIELDS.slice(1), ...SEEN_FIELDS].forEach(f => delete data[f]);
      delete data.income; data.items = cleanItems(data.items);
    }
    let cpCreated = false;
    if (col === 'invoices') { const sup = ensureSupplier(data.supplier, data.supplierInn, user, `Добавлен по счёту № ${data.number || '—'}`); data.supplierId = sup.id; cpCreated = sup.created; }
    const nid = newId(); db[col][nid] = data;
    const linesFilled = col === 'invoices' ? fillOrderSuppliers(data) : 0;
    saveDb();
    return send(res, 200, { id: nid, rev: db.rev, cpCreated, linesFilled });
  }
  if (!id || !db[col][id]) return fail(res, 404, 'Запись не найдена');

  if (m === 'PATCH') {
    const patch = clean(await readJsonBody(req));
    delete patch.createdBy; delete patch.createdAt;
    if (col === 'orders' || col === 'counterparties') delete patch.comments;   // comments go through their own endpoint
    if (col === 'stock') { delete patch.qty; delete patch.moves; delete patch.acctQty; }   // balances change only through moves and the 1C import
    SEEN_FIELDS.forEach(f => delete patch[f]);   // set only by the server when the accountant downloads
    if (col === 'invoices') { delete patch.income; delete patch.supplierId; if ('items' in patch) { if (db.invoices[id].income) delete patch.items; else patch.items = cleanItems(patch.items); } }
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
    if (col === 'jobs') {
      const j = db.jobs[id], c = cleanJob(patch), ck = Object.keys(c);
      if (c.places) { const old = new Map((j.places || []).map(x => [x.id, x])); c.places.forEach(x => { const o = old.get(x.id); if (o) ['photos', 'comment', 'reportAt', 'reportBy', 'doneAt', 'doneBy', 'notWorking', 'editedAt', 'editedBy'].forEach(k => { if (o[k] !== undefined) x[k] = o[k]; }); }); }
      const other = ck.filter(k => !JOB_WORKER_FIELDS.includes(k));
      if (other.length ? !mayEditJob(user, j) : !(mayEditJob(user, j) || onJob(user, j))) return fail(res, 403, 'Недостаточно прав');
      if ('title' in c && !c.title) return fail(res, 400, 'Укажите, что нужно сделать');
      if ('workers' in c && !c.workers.length) return fail(res, 400, 'Назначьте хотя бы одного работника');
      if ('status' in c) {
        if (!JOB_STATUS.includes(c.status)) return fail(res, 400, 'Неизвестный статус');
        const t = new Date().toISOString();
        if (c.status === 'work' && !j.startedAt) { c.startedAt = t; c.startedBy = user.id; }
        c.doneAt = c.status === 'done' ? t : null; c.doneBy = c.status === 'done' ? user.id : null;
      }
      Object.assign(j, c, { updatedAt: new Date().toISOString(), updatedBy: user.id });
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
    let cpCreated = false;
    if (col === 'invoices' && patch.supplier !== undefined && (normName(patch.supplier) !== normName(db.invoices[id].supplier) || !db.invoices[id].supplierId)) {
      const sup = ensureSupplier(patch.supplier, patch.supplierInn, user, `Добавлен по счёту № ${patch.number || db.invoices[id].number || '—'}`); patch.supplierId = sup.id; cpCreated = sup.created;
    }
    Object.assign(db[col][id], patch, { updatedAt: new Date().toISOString(), updatedBy: user.id });
    const linesFilled = col === 'invoices' && ['supplier', 'number', 'items', 'orderId'].some(k => k in patch) ? fillOrderSuppliers(db[col][id]) : 0;
    saveDb();
    return send(res, 200, { ok: true, rev: db.rev, cpCreated, linesFilled });
  }
  if (m === 'DELETE') {
    const d = db[col][id];
    if (col === 'points') {
      if (!mayEditPoint(user, d)) return fail(res, 403, 'Удалить точку может её автор, менеджер или администратор');
    } else if (col === 'jobs') {
      if (!mayEditJob(user, d)) return fail(res, 403, 'Удалить задачу может её автор, руководитель задачи, менеджер или администратор');
    } else if (!canEdit(user) && !(col === 'invoices' && ownsInvoice(user, d))) return fail(res, 403, 'Недостаточно прав');
    if (col === 'projects' && listOf('orders').some(o => o.projectId === id)) return fail(res, 409, 'В проекте есть заказы');
    if (col === 'orders' && listOf('invoices').some(i => i.orderId === id)) return fail(res, 409, 'По заказу есть счета');
    if (col === 'counterparties' && listOf('orders').some(o => o.customerId === id)) return fail(res, 409, 'Контрагент указан заказчиком в заказах');
    if (col === 'invoices' && d.status === 'paid') return fail(res, 409, 'Оплаченный счёт удалить нельзя');
    if (col === 'invoices' && d.income) return fail(res, 409, 'По счёту оприходован товар на склад. Сначала отмените приход');
    delete db[col][id]; saveDb();
    return send(res, 200, { ok: true, rev: db.rev });
  }
  return fail(res, 405, 'Метод не поддерживается');
}
/* ---------- organizations: only the system administrator ---------- */
const ORG_ID = /^[a-z0-9][a-z0-9-]{1,30}$/;
const orgOut = o => {
  const st = orgState(o), us = users.filter(u => u.orgId === o.id);
  return { id: o.id, name: o.name, until: o.until || '', blocked: !!o.blocked, blockNote: o.blockNote || '', note: o.note || '', createdAt: o.createdAt || null,
    state: st.blocked ? st.reason : 'active', left: st.left ?? null, users: us.length,
    admins: us.filter(u => u.role === 'admin').map(u => ({ id: u.id, login: u.login, name: u.name, blocked: !!u.blocked, sys: !!u.sys, lastLoginAt: u.lastLoginAt || null })) };
};
const validDate = v => v === '' || /^\d{4}-\d{2}-\d{2}$/.test(v);
async function orgsApi(req, res, p, m, user) {
  if (!user.sys) return fail(res, 403, 'Организациями управляет только администратор системы');
  const o = p[2] && orgById(p[2]);
  if (m === 'GET' && !p[2]) return send(res, 200, orgs.map(orgOut));
  if (m === 'POST' && !p[2]) {
    const b = await readJsonBody(req);
    const name = String(b.name || '').trim().slice(0, 200);
    if (!name) return fail(res, 400, 'Укажите название организации');
    if (orgs.some(x => x.name.toLowerCase() === name.toLowerCase())) return fail(res, 400, 'Организация с таким названием уже есть');
    const until = String(b.until || ''); if (!validDate(until)) return fail(res, 400, 'Неверная дата');
    const a = b.admin || {};
    const err = validateUser(a, true); if (err) return fail(res, 400, 'Администратор организации: ' + err);
    let id = String(b.id || '').trim().toLowerCase();
    if (id && (!ORG_ID.test(id) || orgById(id))) return fail(res, 400, 'Код организации: латиница, цифры и дефис, не занятый');
    if (!id) do { id = 'o' + crypto.randomBytes(4).toString('hex'); } while (orgById(id));
    const org = { id, name, until, blocked: false, note: String(b.note || '').slice(0, 1000), createdAt: new Date().toISOString(), createdBy: user.id };
    orgs.push(org); saveOrgs(); orgEntry(id);
    addUser(String(a.login), 'admin', String(a.name).trim(), String(a.password), id);
    return send(res, 200, orgOut(org));
  }
  if (!o) return fail(res, 404, 'Организация не найдена');
  if (m === 'PATCH' && p.length === 3) {
    const b = await readJsonBody(req);
    if (b.name !== undefined) {
      const name = String(b.name).trim().slice(0, 200); if (!name) return fail(res, 400, 'Укажите название организации');
      if (orgs.some(x => x !== o && x.name.toLowerCase() === name.toLowerCase())) return fail(res, 400, 'Организация с таким названием уже есть');
      o.name = name;
    }
    if (b.until !== undefined) { if (!validDate(String(b.until))) return fail(res, 400, 'Неверная дата'); o.until = String(b.until); }
    if (b.blocked !== undefined) o.blocked = !!b.blocked;
    if (b.blockNote !== undefined) o.blockNote = String(b.blockNote).slice(0, 500);
    if (b.note !== undefined) o.note = String(b.note).slice(0, 1000);
    // the system administrator must not lock himself out
    if (o.id === user.orgId && orgState(o).blocked) { o.blocked = false; if (o.until && localDate() > o.until) o.until = ''; saveOrgs(); return fail(res, 400, 'Нельзя заблокировать организацию, в которой работает администратор системы'); }
    o.updatedAt = new Date().toISOString(); saveOrgs();
    return send(res, 200, orgOut(o));
  }
  /* administrators of an organization: add, reset password, block */
  if (p[3] === 'admins') {
    if (m === 'POST' && p.length === 4) {
      const b = await readJsonBody(req);
      const err = validateUser(b, true); if (err) return fail(res, 400, err);
      addUser(String(b.login), 'admin', String(b.name).trim(), String(b.password), o.id);
      return send(res, 200, orgOut(o));
    }
    const t = users.find(u => u.id === p[4] && u.orgId === o.id);
    if (!t) return fail(res, 404, 'Пользователь не найден');
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      if (b.password !== undefined) {
        if (String(b.password).length < 8) return fail(res, 400, 'Пароль должен быть не короче 8 символов');
        Object.assign(t, hashPassword(String(b.password)), { ver: (t.ver || 0) + 1 });
      }
      if (b.blocked !== undefined) { if (t.id === user.id) return fail(res, 400, 'Нельзя заблокировать самого себя'); t.blocked = !!b.blocked; if (t.blocked) t.ver = (t.ver || 0) + 1; }
      saveUsers();
      return send(res, 200, orgOut(o));
    }
  }
  return fail(res, 405, 'Метод не поддерживается');
}
/* ---------- backups: a whole system or one organization, a ZIP in DATA_DIR/backups ----------
   inside: manifest.json, orgs.json, users.json, orgs/<id>/db.json, orgs/<id>/files/<file id> */
function readZip(buf) {
  let e = buf.length - 22;
  while (e >= 0 && buf.readUInt32LE(e) !== 0x06054b50) e--;
  if (e < 0) throw Object.assign(new Error('Файл не похож на резервную копию (не ZIP)'), { status: 400 });
  const n = buf.readUInt16LE(e + 10); let o = buf.readUInt32LE(e + 16);
  const out = new Map();
  for (let i = 0; i < n; i++) {
    if (buf.readUInt32LE(o) !== 0x02014b50) throw Object.assign(new Error('Повреждённый архив'), { status: 400 });
    const method = buf.readUInt16LE(o + 10), csize = buf.readUInt32LE(o + 20), nl = buf.readUInt16LE(o + 28), xl = buf.readUInt16LE(o + 30), cl = buf.readUInt16LE(o + 32), lo = buf.readUInt32LE(o + 42);
    const name = buf.slice(o + 46, o + 46 + nl).toString('utf8');
    const start = lo + 30 + buf.readUInt16LE(lo + 26) + buf.readUInt16LE(lo + 28), raw = buf.slice(start, start + csize);
    if (!name.endsWith('/')) out.set(name, method === 0 ? raw : method === 8 ? require('node:zlib').inflateRawSync(raw) : null);
    o += 46 + nl + xl + cl;
  }
  return out;
}
const safeFile = s => /^[\w.-]+$/.test(s) && !s.startsWith('.');
const bIndexFile = () => path.join(BACKUP_DIR, 'index.json');
function backupList() {
  fs.mkdirSync(BACKUP_DIR, { recursive: true });
  const L = readJSON(bIndexFile(), []);
  return L.filter(b => fs.existsSync(path.join(BACKUP_DIR, b.file)));
}
const saveBackupList = L => writeJSON(bIndexFile(), L);
const stampName = () => new Date().toISOString().slice(0, 16).replace('T', '_').replace(':', '-');
function orgFilesEntries(id) {
  const e = orgEntry(id), out = [{ name: `orgs/${id}/db.json`, data: JSON.stringify(e.db) }];
  for (const fid of Object.keys(e.db.files || {})) {
    const fp = path.join(e.files, fid);
    if (safeFile(fid) && fs.existsSync(fp)) out.push({ name: `orgs/${id}/files/${fid}`, data: fs.readFileSync(fp) });
  }
  return out;
}
function makeBackup(orgId, user, note = '', auto = false) {
  const scope = orgId ? [orgById(orgId)] : orgs.slice();
  if (orgId && !scope[0]) throw Object.assign(new Error('Организация не найдена'), { status: 404 });
  const ids = scope.map(o => o.id);
  const manifest = { app: 'sed-zakazy', format: 1, type: orgId ? 'org' : 'system', orgId: orgId || null, orgName: orgId ? scope[0].name : null,
    orgs: scope.map(o => ({ id: o.id, name: o.name })), createdAt: new Date().toISOString(), by: user ? user.name : 'CLI', note };
  const entries = [{ name: 'manifest.json', data: JSON.stringify(manifest, null, 1) }, { name: 'orgs.json', data: JSON.stringify(scope, null, 1) },
    { name: 'users.json', data: JSON.stringify(users.filter(u => ids.includes(u.orgId)), null, 1) }];
  ids.forEach(id => entries.push(...orgFilesEntries(id)));
  const buf = zipStore(entries);
  const file = `${orgId ? 'org-' + orgId : 'system'}-${stampName()}-${crypto.randomBytes(2).toString('hex')}.zip`;
  fs.mkdirSync(BACKUP_DIR, { recursive: true });
  fs.writeFileSync(path.join(BACKUP_DIR, file), buf, { mode: 0o600 });
  const rec = { id: newId(), file, type: manifest.type, orgId: orgId || null, orgName: manifest.orgName, orgs: manifest.orgs, createdAt: manifest.createdAt, by: manifest.by, size: buf.length,
    files: entries.filter(x => x.name.includes('/files/')).length, note, auto };
  const L = backupList(); L.unshift(rec); saveBackupList(L);
  return rec;
}
function loadBackup(rec) {
  const z = readZip(fs.readFileSync(path.join(BACKUP_DIR, rec.file)));
  const j = n => { const b = z.get(n); if (!b) throw Object.assign(new Error(`В копии нет ${n}`), { status: 400 }); return JSON.parse(b.toString('utf8')); };
  const manifest = j('manifest.json');
  if (manifest.app !== 'sed-zakazy') throw Object.assign(new Error('Это не резервная копия «Управления предприятием»'), { status: 400 });
  return { z, manifest, orgs: j('orgs.json'), users: j('users.json') };
}
/* replace one organization's data and attachments with those from the archive */
function writeOrgData(z, id) {
  const dbBuf = z.get(`orgs/${id}/db.json`); if (!dbBuf) throw Object.assign(new Error('В копии нет данных этой организации'), { status: 400 });
  const dir = orgDir(id), fdir = path.join(dir, 'files');
  fs.mkdirSync(fdir, { recursive: true });
  for (const f of fs.readdirSync(fdir)) fs.rmSync(path.join(fdir, f), { force: true, recursive: true });
  const pre = `orgs/${id}/files/`;
  for (const [n, b] of z) if (n.startsWith(pre) && b && safeFile(n.slice(pre.length))) fs.writeFileSync(path.join(fdir, n.slice(pre.length)), b);
  writeJSON(path.join(dir, 'db.json'), JSON.parse(dbBuf.toString('utf8')));
  dbs.delete(id);
}
function restoreBackup(rec, scope, orgId, user) {
  const B = loadBackup(rec);
  const keepMe = u => user && u.id === user.id;     // the administrator who restores keeps his own account and password
  let safety, skipped = [];
  if (scope === 'system') {
    if (B.manifest.type !== 'system') throw Object.assign(new Error('Это копия одной организации — восстановить из неё всю систему нельзя'), { status: 400 });
    safety = makeBackup(null, user, 'Автоматически перед восстановлением системы', true);
    const ids = B.orgs.map(o => o.id);
    if (!ids.includes(MAIN_ORG)) throw Object.assign(new Error('В копии нет основной организации'), { status: 400 });
    ids.forEach(id => writeOrgData(B.z, id));
    // organizations that appeared after the copy was made: their folders stay on disk but they leave the list
    orgs = B.orgs; saveOrgs();
    const me = user && users.find(keepMe);
    users = B.users.filter(u => !keepMe(u)); if (me) users.push(me);
    normUsers(); saveUsers(); dbs.clear();
  } else {
    const src = B.manifest.type === 'org' ? B.manifest.orgId : orgId;
    const o = B.orgs.find(x => x.id === src); if (!o) throw Object.assign(new Error('В копии нет такой организации'), { status: 400 });
    if (orgById(src)) safety = makeBackup(src, user, 'Автоматически перед восстановлением организации', true);
    writeOrgData(B.z, src);
    const cur = orgById(src); if (cur) Object.assign(cur, { name: o.name, until: o.until || '', blocked: !!o.blocked, blockNote: o.blockNote || '', note: o.note || '' }); else orgs.push(o);
    saveOrgs();
    const me = user && users.find(keepMe);
    const incoming = B.users.filter(u => u.orgId === src && !keepMe(u));
    users = users.filter(u => u.orgId !== src || keepMe(u));
    for (const u of incoming) { if (users.some(x => x.login === u.login)) skipped.push(u.login); else users.push(u); }
    if (me && !users.includes(me)) users.push(me);
    saveUsers();
  }
  return { safety, skipped };
}
const backupOut = b => ({ ...b });
async function backupsApi(req, res, p, m, user) {
  if (!user.sys) return fail(res, 403, 'Резервными копиями управляет только администратор системы');
  if (m === 'GET' && !p[2]) return send(res, 200, backupList().map(backupOut));
  if (m === 'POST' && !p[2]) {
    const b = await readJsonBody(req);
    const rec = makeBackup(b.orgId || null, user, String(b.note || '').slice(0, 300));
    return send(res, 200, backupOut(rec));
  }
  if (m === 'POST' && p[2] === 'upload') {
    const buf = await readBody(req, MAX_BACKUP);
    if (!buf.length) return fail(res, 400, 'Пустой файл');
    const tmp = path.join(BACKUP_DIR, 'upload-' + newId() + '.zip');
    fs.mkdirSync(BACKUP_DIR, { recursive: true }); fs.writeFileSync(tmp, buf, { mode: 0o600 });
    let B;
    try { B = loadBackup({ file: path.basename(tmp) }); } catch (e) { fs.rmSync(tmp, { force: true }); throw e.status ? e : Object.assign(new Error('Не удалось прочитать архив: ' + e.message), { status: 400 }); }
    const M = B.manifest;
    const file = `uploaded-${M.type === 'org' ? 'org-' + M.orgId : 'system'}-${stampName()}-${crypto.randomBytes(2).toString('hex')}.zip`;
    fs.renameSync(tmp, path.join(BACKUP_DIR, file));
    const rec = { id: newId(), file, type: M.type, orgId: M.orgId, orgName: M.orgName, orgs: M.orgs || B.orgs.map(o => ({ id: o.id, name: o.name })), createdAt: M.createdAt, by: M.by, size: buf.length,
      files: [...B.z.keys()].filter(n => n.includes('/files/')).length, note: 'Загружена из файла' + (req.headers['x-filename'] ? ' ' + decodeURIComponent(String(req.headers['x-filename'])).slice(0, 120) : ''), uploadedAt: new Date().toISOString(), uploaded: true };
    const L = backupList(); L.unshift(rec); saveBackupList(L);
    return send(res, 200, backupOut(rec));
  }
  const L = backupList(), rec = L.find(b => b.id === p[2]);
  if (!rec) return fail(res, 404, 'Копия не найдена');
  if (m === 'GET' && p[3] === 'download') {
    const fp = path.join(BACKUP_DIR, rec.file), st = fs.statSync(fp);
    res.writeHead(200, { ...SEC_HEADERS, 'Content-Type': 'application/zip', 'Content-Length': st.size, 'Content-Disposition': `attachment; filename="${rec.file}"`, 'Cache-Control': 'no-store' });
    return fs.createReadStream(fp).pipe(res);
  }
  if (m === 'POST' && p[3] === 'restore') {
    const b = await readJsonBody(req);
    const scope = b.scope === 'system' ? 'system' : 'org';
    const r = restoreBackup(rec, scope, b.orgId, user);
    console.log(`${user.login} восстановил ${scope === 'system' ? 'систему' : 'организацию ' + (b.orgId || rec.orgId)} из копии ${rec.file}`);
    return send(res, 200, { ok: true, safety: r.safety ? backupOut(r.safety) : null, skipped: r.skipped });
  }
  if (m === 'DELETE' && p.length === 3) {
    fs.rmSync(path.join(BACKUP_DIR, rec.file), { force: true });
    saveBackupList(L.filter(b => b !== rec));
    return send(res, 200, { ok: true });
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
const meInfo = u => { const o = orgById(u.orgId), st = orgState(o); return { ...publicUser(u), map: MAP, sys: !!u.sys, org: o ? { id: o.id, name: o.name, until: o.until || '' } : null, orgWarn: st.warn || '' }; };
const adminUser = u => ({ ...publicUser(u), sys: !!u.sys, blocked: !!u.blocked, lastLoginAt: u.lastLoginAt || null, createdAt: u.createdAt || null });

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

/* ---------- names, write-off lines and a tiny XLSX writer ---------- */
const normName = s => String(s || '').toLowerCase().replace(/ё/g, 'е').replace(/["«»'“”„]/g, '').replace(/(\d)\s*[x×х*]\s*(?=\d)/g, '$1х').replace(/\s+/g, ' ').trim();
function writeoffLines(o) {
  const byName = new Map(Object.entries(db.stock).map(([id, it]) => [normName(it.name), id]));
  const lines = new Map();
  for (const p of o.products || []) {
    const k = Number(p.qty) || 0;
    for (const c of p.components || []) {
      const sid = (c.stockId && db.stock[c.stockId]) ? c.stockId : byName.get(normName(c.name));
      if (!sid && !String(c.name || '').trim()) continue;
      const it = sid ? db.stock[sid] : null;
      const key = sid ? 'id:' + sid : 'n:' + normName(c.name);
      const L = lines.get(key) || { name: it ? it.name : c.name, sku: it ? it.sku || '' : '', unit: (it && it.unit) || c.unit || 'шт', need: 0, acct: it ? Number(it.acctQty) || 0 : 0, real: it ? Number(it.qty) || 0 : 0, inStock: !!it, products: [] };
      L.need = Math.round((L.need + (Number(c.qty) || 0) * k) * 1000) / 1000;
      if (p.name && !L.products.includes(p.name)) L.products.push(p.name);
      lines.set(key, L);
    }
  }
  return [...lines.values()].map(L => {
    const source = !L.inStock ? 'none' : L.acct >= L.need - 1e-9 ? 'acct' : L.real >= L.need - 1e-9 ? 'real' : 'short';
    const shortage = source === 'acct' || source === 'real' ? 0 : Math.round((L.need - (L.inStock ? Math.max(L.acct, L.real) : 0)) * 1000) / 1000;
    return { ...L, source, shortage };
  }).sort((a, b) => a.name.localeCompare(b.name, 'ru'));
}
const SOURCE_LABEL = { acct: 'Из бухгалтерских остатков', real: 'Из фактических остатков', short: 'Не хватает', none: 'Нет на складе' };
function zipStore(entries) {
  const now = new Date();
  const t = ((now.getHours() << 11) | (now.getMinutes() << 5) | (now.getSeconds() >> 1)) & 0xFFFF;
  const d = (((now.getFullYear() - 1980) << 9) | ((now.getMonth() + 1) << 5) | now.getDate()) & 0xFFFF;
  const parts = [], central = []; let offset = 0;
  for (const e of entries) {
    const name = Buffer.from(e.name, 'utf8'), data = Buffer.isBuffer(e.data) ? e.data : Buffer.from(e.data, 'utf8'), crc = crc32(data);
    const h = Buffer.alloc(30);
    h.writeUInt32LE(0x04034b50, 0); h.writeUInt16LE(20, 4); h.writeUInt16LE(0x0800, 6); h.writeUInt16LE(0, 8); h.writeUInt16LE(t, 10); h.writeUInt16LE(d, 12);
    h.writeUInt32LE(crc, 14); h.writeUInt32LE(data.length, 18); h.writeUInt32LE(data.length, 22); h.writeUInt16LE(name.length, 26); h.writeUInt16LE(0, 28);
    const c = Buffer.alloc(46);
    c.writeUInt32LE(0x02014b50, 0); c.writeUInt16LE(20, 4); c.writeUInt16LE(20, 6); c.writeUInt16LE(0x0800, 8); c.writeUInt16LE(0, 10); c.writeUInt16LE(t, 12); c.writeUInt16LE(d, 14);
    c.writeUInt32LE(crc, 16); c.writeUInt32LE(data.length, 20); c.writeUInt32LE(data.length, 24); c.writeUInt16LE(name.length, 28); c.writeUInt32LE(offset, 42);
    parts.push(h, name, data); central.push(c, name); offset += 30 + name.length + data.length;
  }
  const cd = Buffer.concat(central), end = Buffer.alloc(22);
  end.writeUInt32LE(0x06054b50, 0); end.writeUInt16LE(entries.length, 8); end.writeUInt16LE(entries.length, 10); end.writeUInt32LE(cd.length, 12); end.writeUInt32LE(offset, 16);
  return Buffer.concat([...parts, cd, end]);
}
const xmlEsc = s => String(s ?? '').replace(/[&<>"]/g, c => ({ '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;' }[c])).replace(/[\u0000-\u0008\u000B\u000C\u000E-\u001F]/g, '');
const colName = i => { let s = ''; i++; while (i) { const r = (i - 1) % 26; s = String.fromCharCode(65 + r) + s; i = Math.floor((i - 1) / 26); } return s; };
/* rows: arrays of { v, s } (s = style index); numbers become numeric cells */
function xlsxBuffer(sheetName, rows, widths) {
  const sheetRows = rows.map((r, ri) => `<row r="${ri + 1}">` + r.map((c, ci) => {
    if (c == null) return '';
    const ref = colName(ci) + (ri + 1), cell = typeof c === 'object' ? c : { v: c };
    const st = cell.s ? ` s="${cell.s}"` : '';
    if (typeof cell.v === 'number') return `<c r="${ref}"${st}><v>${cell.v}</v></c>`;
    return `<c r="${ref}"${st} t="inlineStr"><is><t xml:space="preserve">${xmlEsc(cell.v)}</t></is></c>`;
  }).join('') + '</row>').join('');
  const cols = widths ? '<cols>' + widths.map((w, i) => `<col min="${i + 1}" max="${i + 1}" width="${w}" customWidth="1"/>`).join('') + '</cols>' : '';
  const sheet = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">${cols}<sheetData>${sheetRows}</sheetData></worksheet>`;
  const fill = rgb => `<fill><patternFill patternType="solid"><fgColor rgb="FF${rgb}"/><bgColor indexed="64"/></patternFill></fill>`;
  const styles = `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><styleSheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">
<numFmts count="1"><numFmt numFmtId="164" formatCode="#,##0.###"/></numFmts>
<fonts count="3"><font><sz val="11"/><name val="Calibri"/></font><font><b/><sz val="11"/><name val="Calibri"/></font><font><b/><sz val="14"/><name val="Calibri"/></font></fonts>
<fills count="7"><fill><patternFill patternType="none"/></fill><fill><patternFill patternType="gray125"/></fill>${fill('E3E8E5')}${fill('DFF2E4')}${fill('DDEBF8')}${fill('FBE1E1')}${fill('EDEFF2')}</fills>
<borders count="2"><border/><border><left style="thin"><color rgb="FFC8CFCB"/></left><right style="thin"><color rgb="FFC8CFCB"/></right><top style="thin"><color rgb="FFC8CFCB"/></top><bottom style="thin"><color rgb="FFC8CFCB"/></bottom></border></borders>
<cellStyleXfs count="1"><xf numFmtId="0" fontId="0" fillId="0" borderId="0"/></cellStyleXfs>
<cellXfs count="13"><xf/>
<xf fontId="1" fillId="2" borderId="1" applyFont="1" applyFill="1" applyBorder="1"><alignment wrapText="1" vertical="center"/></xf>
<xf borderId="1" applyBorder="1"><alignment wrapText="1" vertical="top"/></xf>
<xf numFmtId="164" borderId="1" applyNumberFormat="1" applyBorder="1"/>
<xf fillId="3" borderId="1" applyFill="1" applyBorder="1"><alignment wrapText="1" vertical="top"/></xf>
<xf numFmtId="164" fillId="3" borderId="1" applyNumberFormat="1" applyFill="1" applyBorder="1"/>
<xf fillId="4" borderId="1" applyFill="1" applyBorder="1"><alignment wrapText="1" vertical="top"/></xf>
<xf numFmtId="164" fillId="4" borderId="1" applyNumberFormat="1" applyFill="1" applyBorder="1"/>
<xf fillId="5" borderId="1" applyFill="1" applyBorder="1"><alignment wrapText="1" vertical="top"/></xf>
<xf numFmtId="164" fillId="5" borderId="1" applyNumberFormat="1" applyFill="1" applyBorder="1"/>
<xf fontId="2" applyFont="1"/>
<xf fillId="6" borderId="1" applyFill="1" applyBorder="1"><alignment wrapText="1" vertical="top"/></xf>
<xf numFmtId="164" fillId="6" borderId="1" applyNumberFormat="1" applyFill="1" applyBorder="1"/>
</cellXfs><cellStyles count="1"><cellStyle name="Normal" xfId="0" builtinId="0"/></cellStyles></styleSheet>`;
  const files = [
    { name: '[Content_Types].xml', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/><Override PartName="/xl/worksheets/sheet1.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/><Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/></Types>' },
    { name: '_rels/.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>' },
    { name: 'xl/workbook.xml', data: `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets><sheet name="${xmlEsc(sheetName).slice(0, 31)}" sheetId="1" r:id="rId1"/></sheets></workbook>` },
    { name: 'xl/_rels/workbook.xml.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet1.xml"/><Relationship Id="rId2" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>' },
    { name: 'xl/styles.xml', data: styles },
    { name: 'xl/worksheets/sheet1.xml', data: sheet },
  ];
  return zipStore(files);
}
function writeoffXlsx(o) {
  const lines = writeoffLines(o);
  const st = { acct: [4, 5], real: [6, 7], short: [8, 9], none: [11, 12] };
  const fmt = iso => iso ? new Date(iso).toLocaleString('ru-RU', { timeZone: process.env.TZ || 'Europe/Moscow' }) : 'не загружались';
  const rows = [
    [{ v: `Список для списания — заказ ${o.number || ''} · ${o.title || ''}`, s: 10 }],
    [`Сформирован: ${fmt(new Date().toISOString())}. Бухгалтерские остатки: ${db.meta.acct ? fmt(db.meta.acct.at) + (db.meta.acct.file ? ' (' + db.meta.acct.file + ')' : '') : 'не загружались'}.`],
    [],
    ['№', 'Наименование', 'Артикул', 'Ед.', 'Нужно', 'Бух. остаток', 'Факт. остаток', 'Списать из', 'Не хватает', 'Изделия'].map(v => ({ v, s: 1 })),
    ...lines.map((L, i) => { const [ts, ns] = st[L.source]; return [
      { v: i + 1, s: ns }, { v: L.name, s: ts }, { v: L.sku, s: ts }, { v: L.unit, s: ts }, { v: L.need, s: ns },
      L.inStock ? { v: L.acct, s: ns } : { v: '—', s: ts }, L.inStock ? { v: L.real, s: ns } : { v: '—', s: ts },
      { v: SOURCE_LABEL[L.source], s: ts }, L.shortage ? { v: L.shortage, s: ns } : { v: '', s: ts }, { v: L.products.join(', '), s: ts }]; }),
    [],
    [{ v: 'Обозначения:', s: 0 }],
    [{ v: 'Хватает бухгалтерского остатка', s: 4 }],
    [{ v: 'Бухгалтерского не хватает, хватает фактического', s: 6 }],
    [{ v: 'Не хватает ни бухгалтерского, ни фактического', s: 8 }],
    [{ v: 'Позиции нет на складе', s: 11 }],
  ];
  return xlsxBuffer('Списание', rows, [5, 42, 16, 7, 11, 13, 13, 30, 12, 30]);
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
      const fp = path.join(filesDir(), i.file.id);
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
  if (orgState(orgById(user.orgId)).blocked) return fail(res, 423, 'Доступ организации заблокирован');
  const meta = db.files[id];
  if (!meta || !/^[\w-]+$/.test(id)) return fail(res, 404, 'Файл не найден');
  const fp = path.join(filesDir(), id);
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
    if (login && pw) { addUser(login, 'admin', process.env.ADMIN_NAME || 'Администратор', pw, MAIN_ORG, true); console.log(`Создан администратор системы «${login}».`); }
  }
  const server = http.createServer(async (req, res) => {
    const url = new URL(req.url, 'http://localhost');
    try { syncFromDisk(); } catch (e) { console.error(e); }
    try {
      if (url.pathname.startsWith('/api/') || url.pathname.startsWith('/files/')) {
        // every request works inside the data of the signed-in user's organization
        const su = sessionUser(req), org = su && orgById(su.orgId) ? su.orgId : MAIN_ORG;
        return await als.run(orgEntry(org), async () => {
          if (url.pathname.startsWith('/api/')) return await api(req, res, url);
          if (req.method === 'GET') return serveFile(req, res, url.pathname.slice(7));
          fail(res, 405, 'Метод не поддерживается');
        });
      }
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
function addUser(login, role, name, pw, orgId = MAIN_ORG, sys = false) {
  const u = { id: 'u_' + newId(), login: login.toLowerCase(), name, role, orgId, ...(sys ? { sys: true } : {}), ...hashPassword(pw), ver: 0, createdAt: new Date().toISOString() };
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
    users.forEach(u => console.log(`${u.login.padEnd(20)} ${ROLES[u.role].padEnd(14)} ${(orgById(u.orgId)?.name || u.orgId).padEnd(24)} ${u.sys ? 'АДМИН СИСТЕМЫ  ' : ''}${u.blocked ? 'ЗАБЛОКИРОВАН  ' : ''}${u.name}`));
  } else if (cmd === 'backup') {
    const file = args[0] || `backup-${new Date().toISOString().slice(0, 10)}.json`;
    const e = orgEntry(args[1] || MAIN_ORG);
    writeJSON(path.resolve(file), e.db);
    console.log(`Записи выгружены в ${file}. Файлы вложений лежат в ${e.files}.`);
  } else if (cmd === 'archive') {
    const r = makeBackup(args[0] || null, null, 'Создана из командной строки');
    console.log(`Резервная копия: ${path.join(BACKUP_DIR, r.file)} (${(r.size / 1048576).toFixed(1)} МБ)`);
  } else if (cmd === 'restore') {
    need(1);
    const src = path.resolve(args[0]); if (!fs.existsSync(src)) { console.error('Нет такого файла'); process.exit(1); }
    fs.mkdirSync(BACKUP_DIR, { recursive: true });
    const file = path.dirname(src) === BACKUP_DIR ? path.basename(src) : 'cli-' + stampName() + '-' + path.basename(src).replace(/[^\w.-]/g, '_');
    if (path.dirname(src) !== BACKUP_DIR) fs.copyFileSync(src, path.join(BACKUP_DIR, file));
    const B = loadBackup({ file });
    const scope = B.manifest.type === 'system' && !args[1] ? 'system' : 'org';
    const r = restoreBackup({ file }, scope, args[1] || B.manifest.orgId, null);
    console.log(`Восстановлено: ${scope === 'system' ? 'вся система' : 'организация ' + (args[1] || B.manifest.orgId)}. Копия прежнего состояния: ${r.safety ? path.join(BACKUP_DIR, r.safety.file) : '—'}${r.skipped.length ? '. Пропущены логины (заняты): ' + r.skipped.join(', ') : ''}`);
  } else if (cmd === 'orgs') {
    orgs.forEach(o => { const st = orgState(o); console.log(`${o.id.padEnd(14)} ${(st.blocked ? (st.reason === 'expired' ? 'СРОК ИСТЁК' : 'ЗАБЛОКИРОВАНА') : 'работает').padEnd(14)} ${(o.until ? 'до ' + ruDate(o.until) : '').padEnd(14)} ${o.name}  (пользователей: ${users.filter(u => u.orgId === o.id).length})`); });
  } else if (cmd === 'orgunblock') {
    need(1);
    const o = orgById(args[0]); if (!o) { console.error('Нет такой организации. Список: node server.js orgs'); process.exit(1); }
    o.blocked = false; o.until = ''; saveOrgs(); console.log(`Организация «${o.name}» разблокирована, срок снят.`);
  } else {
    console.error(`Неизвестная команда «${cmd}». См. README.md`); process.exit(1);
  }
}

const [cmd, ...args] = process.argv.slice(2);
if (cmd) cli(cmd, args); else startServer();

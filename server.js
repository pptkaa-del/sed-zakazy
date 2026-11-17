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

// «products»: the catalogue of products (изделия) with their components from the warehouse
const COLLECTIONS = ['projects', 'orders', 'invoices', 'tasks', 'counterparties', 'points', 'stock', 'jobs', 'products'];
const ROLES = {
  admin:      'Администратор',
  head:       'Руководитель',
  accountant: 'Бухгалтер',
  worker:     'Сотрудник',
  contractor: 'Подрядчик',
};
/* «Сотрудник» and «Подрядчик» work in the field: only their points; a contractor's access ends on a set date */
const FIELD = u => u && (u.role === 'worker' || u.role === 'contractor');
const contractorExpired = u => u && u.role === 'contractor' && u.accessUntil && localDateNow() > u.accessUntil;
function localDateNow() { const d = new Date(); return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`; }
const PAY_FIELDS = ['status', 'paidAt', 'payNo', 'paidAmount', 'paidBy', 'receipt'];
// «Руководитель» works like the administrator but neither marks invoices paid nor manages users
const HEAD = u => u && (u.role === 'admin' || u.role === 'head');
const canEdit = u => HEAD(u);
const canPay = u => u.role === 'admin' || u.role === 'accountant';
/* «Сотрудник» загружает счета и правит/удаляет только свои неоплаченные */
const canAddInvoice = u => canEdit(u);
const ownsInvoice = (u, inv) => false;
const SEEN_FIELDS = ['seenAt', 'seenBy', 'seenLastAt', 'seenCount'];
/* Map points: everyone except «Просмотр» adds points and marks them done; author, manager or admin edits and deletes */
const POINT_STATUS_FIELDS = ['status', 'doneAt', 'doneBy'];
const canWork = u => !FIELD(u);
/* Assignments («Задачи сотрудникам»): admins, managers and leaders create them; a worker sees only his own and changes only the status */
const canLead = u => canEdit(u);
// «В планах», «Ожидание старта», «В работе», «Выполнена»
const JOB_STATUS = ['new', 'wait', 'work', 'done'];
const JOB_WORKER_FIELDS = ['status', 'report'];
const onJob = (u, j) => j.leaderId === u.id || (j.workers || []).includes(u.id);
const mayEditJob = (u, j) => canEdit(u);
function cleanJob(d){
  const out = {};
  if ('title' in d) out.title = String(d.title || '').trim().slice(0, 200);
  if ('description' in d) out.description = String(d.description || '').slice(0, 4000);
  if ('due' in d) out.due = /^\d{4}-\d{2}-\d{2}$/.test(d.due || '') ? d.due : '';
  if ('start' in d) out.start = /^\d{4}-\d{2}-\d{2}$/.test(d.start || '') ? d.start : '';
  if ('orderId' in d) out.orderId = d.orderId && db.orders[d.orderId] ? d.orderId : null;
  if ('leaderId' in d) { const l = orgUsers().find(u => u.id === d.leaderId); out.leaderId = l && HEAD(l) ? l.id : null; }
  // a work: «Производство», «Монтаж» or both; the customer; documents
  if ('kind' in d) out.kind = ['prod', 'mount', 'both'].includes(d.kind) ? d.kind : 'mount';
  if ('customerId' in d) out.customerId = d.customerId && db.counterparties[d.customerId] ? d.customerId : null;
  if ('docs' in d) out.docs = (Array.isArray(d.docs) ? d.docs : []).filter(f => f && db.files[f.id]).slice(0, 200)
    .map(f => ({ id: f.id, name: String(f.name || db.files[f.id].name).slice(0, 200), size: db.files[f.id].size, type: db.files[f.id].type, at: db.files[f.id].at, by: db.files[f.id].by }));
  if ('workers' in d) out.workers = [...new Set((Array.isArray(d.workers) ? d.workers : []).filter(id => orgUsers().some(u => u.id === id)))].slice(0, 50);
  // up to 5000 places: points from «Карта объектов» keep the object number and its marks
  if ('places' in d) out.places = (Array.isArray(d.places) ? d.places : []).slice(0, 5000)
    .filter(x => x && Number.isFinite(Number(x.lat)) && Number.isFinite(Number(x.lng)) && Math.abs(x.lat) <= 90 && Math.abs(x.lng) <= 180)
    .map(x => ({ id: String(x.id || newId()).slice(0, 40), lat: Math.round(Number(x.lat) * 1e6) / 1e6, lng: Math.round(Number(x.lng) * 1e6) / 1e6, label: String(x.label || '').trim().slice(0, 200),
      ...(x.assignee && users.some(u => u.id === x.assignee) ? { assignee: String(x.assignee) } : {}),
      ...(isNeed(x.need) ? { need: x.need } : {}),
      ...(x.dtNo ? { dtNo: String(x.dtNo).slice(0, 60), cats: (Array.isArray(x.cats) ? x.cats : []).filter(c => ['mkad', 'ttk', 'bridge', 'other', 'check'].includes(c)), road: String(x.road || '').slice(0, 200) } : {}) }));
  if ('report' in d) out.report = String(d.report || '').slice(0, 4000);
  // the key features of a work and what is happening with it now; the percent done by hand (when the work has no points)
  // the minimum of points a worker should do in a day on this work («Успеваемость» in «Сотрудники»)
  if ('minPerDay' in d) out.minPerDay = d.minPerDay === null || d.minPerDay === '' || !(Number(d.minPerDay) > 0) ? null : Math.min(10000, Math.round(Number(d.minPerDay)));
  // the warranty after the work is done: its last day; when it passes the work goes to the archive
  if ('warrantyUntil' in d) out.warrantyUntil = /^\d{4}-\d{2}-\d{2}$/.test(d.warrantyUntil || '') ? d.warrantyUntil : '';
  if ('warrantyNote' in d) out.warrantyNote = String(d.warrantyNote || '').trim().slice(0, 500);
  if ('features' in d) out.features = String(d.features || '').trim().slice(0, 2000);
  if ('happening' in d) out.happening = String(d.happening || '').trim().slice(0, 2000);
  if ('progress' in d) out.progress = d.progress === null || d.progress === '' || !Number.isFinite(Number(d.progress)) ? null : Math.max(0, Math.min(100, Math.round(Number(d.progress))));
  // which photos a worker must take at every point, e.g. «Общий вид», «До замены», «После замены»
  // materials for a montage work: warehouse positions and quantities to be written off
  if ('materials' in d) out.materials = (Array.isArray(d.materials) ? d.materials : []).slice(0, 500).filter(x => x && String(x.name || '').trim() && Number(x.qty) > 0)
    .map(x => ({ id: String(x.id || newId()).slice(0, 40), stockId: x.stockId && db.stock[x.stockId] ? x.stockId : null, name: String(x.name).trim().slice(0, 300), qty: Math.round(Number(x.qty) * 1000) / 1000, unit: String(x.unit || 'шт').slice(0, 20) }));
  if ('photoSpec' in d) out.photoSpec = [...new Set((Array.isArray(d.photoSpec) ? d.photoSpec : String(d.photoSpec || '').split('\n')).map(x => String(x).trim().slice(0, 80)).filter(Boolean))].slice(0, 20);
  if ('status' in d) out.status = d.status;
  return out;
}
/* A work with production («Производство» or «Производство и монтаж») gets its own order on «Заказы на производство» */
function nextOrderNumber(){
  const list = listOf('orders'), num = o => /^(.*?)(\d+)$/.exec(String(o.number || '').trim());
  const parsed = list.map(num).filter(Boolean);
  if (!parsed.length) return 'З-1';
  const last = list.slice().sort((a, b) => (b.createdAt || '').localeCompare(a.createdAt || '')).map(num).find(Boolean) || parsed[0];
  const prefix = last[1], width = last[2].length;
  return prefix + String(Math.max(...parsed.filter(m => m[1] === prefix).map(m => Number(m[2]))) + 1).padStart(width, '0');
}
function ensureJobOrder(j, jid, user, changed = {}){
  if (!['prod', 'both'].includes(j.kind) || (j.noOrder && !j.orderId)) return false;
  const cp = j.customerId && db.counterparties[j.customerId];
  const o = j.orderId && db.orders[j.orderId];
  if (o) {   // the work is the master: what changed in it goes to its order
    if (o.jobId !== jid) return false;
    let ch = false;
    if ('title' in changed && j.title) { o.title = j.title; ch = true; }
    if ('due' in changed) { o.deadline = j.due || ''; ch = true; }
    if ('customerId' in changed) { o.customerId = cp ? j.customerId : null; o.customer = cp ? cp.name : ''; ch = true; }
    return ch;
  }
  const oid = newId();
  db.orders[oid] = { number: nextOrderNumber(), orderNo: '', status: 'new', title: j.title || 'Без названия', customerId: cp ? j.customerId : null, customer: cp ? cp.name : '',
    deadline: j.due || '', billNo: '', billDate: '', components: [], specs: (j.docs || []).map(f => ({ ...f })), comments: [], jobId: jid,
    createdBy: user.id, createdAt: new Date().toISOString() };
  j.orderId = oid;
  return true;
}
// marks on map points: special vehicles needed (lift, fencing, both), own fencing, own fencing + lift
const DT_NEEDS = ['lift', 'fence', 'lift_fence', 'own_fence', 'own_fence_lift'];
// the organization's own marks (db.meta.dtNeeds: id, name, colour) are valid too
const isNeed = n => DT_NEEDS.includes(n) || ((db.meta && db.meta.dtNeeds) || []).some(x => x.id === n);
/* Warehouse: managers and admins keep the item list; they and «Сотрудник» record receipts and issues */
const canMoveStock = u => canEdit(u);
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
/* a waybill: the uploaded file and what was read from it (or typed) — number, date, supplier */
function cleanWaybill(w){
  if (!w || !w.file || !db.files[w.file.id]) return null;
  const f = db.files[w.file.id];
  return { file: { id: w.file.id, name: String(w.file.name || f.name || 'накладная').slice(0, 200), type: f.type }, number: String(w.number || '').trim().slice(0, 60),
    date: /^\d{4}-\d{2}-\d{2}$/.test(w.date || '') ? w.date : '', supplier: String(w.supplier || '').trim().slice(0, 300), inn: /^(\d{10}|\d{12})$/.test(w.inn || '') ? w.inn : '' };
}
const waybillLabel = (wb, sup) => `накладной № ${wb.number || '—'}${wb.date ? ' от ' + wb.date.split('-').reverse().join('.') : ''}${(wb.supplier || sup) ? ', ' + (wb.supplier || sup) : ''}`;
/* receipt lines go to the warehouse: a line finds its position by id, article or name, otherwise a new position is made */
function postIncome(lines, label, ref, user){
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
    // a receipt goes both to the actual and to the accounting balance
    it.qty = r3((Number(it.qty) || 0) + ln.qty); it.acctQty = r3((Number(it.acctQty) || 0) + ln.qty);
    it.moves = Array.isArray(it.moves) ? it.moves : [];
    const mv = { id: newId(), type: 'in', acct: true, acctBalance: it.acctQty, qty: ln.qty, orderId: ref.orderId || null, ...(ref.invoiceId ? { invoiceId: ref.invoiceId } : {}), ...(ref.receiptId ? { receiptId: ref.receiptId } : {}), note: 'Приход по ' + label, by: user.id, at, balance: it.qty };
    it.moves.push(mv); it.updatedAt = at; it.updatedBy = user.id;
    out.push({ ...ln, stockId: sid, moveId: mv.id });
  }
  return { at, out, created };
}
/* cancelling a receipt: first check that every quantity is still on the shelf, then roll back; returns an error text or '' */
function rollbackIncome(lines, user){
  for (const ln of lines) {
    const it = db.stock[ln.stockId];
    if (it && (it.moves || []).some(x => x.id === ln.moveId) && (Number(it.qty) || 0) + 1e-9 < ln.qty)
      return `«${it.name}»: на складе ${it.qty} ${it.unit || ''}, часть прихода уже израсходована. Отменить приход нельзя`.replace(' ,', ',');
  }
  for (const ln of lines) {
    const it = db.stock[ln.stockId]; if (!it) continue;
    const i = (it.moves || []).findIndex(x => x.id === ln.moveId); if (i < 0) continue;
    const was = it.moves[i]; it.moves.splice(i, 1); it.qty = r3((Number(it.qty) || 0) - ln.qty); if (was.acct) it.acctQty = r3((Number(it.acctQty) || 0) - ln.qty);
    it.updatedAt = new Date().toISOString(); it.updatedBy = user.id;
  }
  return '';
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
// older roles: «Менеджер» and «Руководитель» become administrators, «Просмотр» — «Сотрудник»
const OLD_ROLES = { manager: 'admin', user: 'admin', viewer: 'worker' };
const normUsers = () => { let ch = false; users.forEach(u => { if (!u.orgId) { u.orgId = MAIN_ORG; ch = true; } if (OLD_ROLES[u.role]) { u.wasRole = u.role; u.role = OLD_ROLES[u.role]; ch = true; } }); return ch; };
if (normUsers() && users.length) writeJSON(USERS_FILE, users);
function syncFromDisk() {
  const b = stamp(USERS_FILE); if (b !== usersStamp) { users = readJSON(USERS_FILE, []); normUsers(); usersStamp = b; }
  const c = stamp(ORGS_FILE); if (c !== orgsStamp) { orgs = readJSON(ORGS_FILE, orgs); orgsStamp = c; }
}
const saveUsers = () => { writeJSON(USERS_FILE, users); usersStamp = stamp(USERS_FILE); };
const saveOrgs = () => { writeJSON(ORGS_FILE, orgs); orgsStamp = stamp(ORGS_FILE); };
const orgById = id => orgs.find(o => o.id === id);
/* the kind of system an organization works in: «Все сервисы» (all) or «Управление заявками» (requests) */
const ORG_TYPES = ['all', 'requests'];
const orgType = u => { const o = u && orgById(u.orgId); return o && o.type === 'requests' ? 'requests' : 'all'; };
const REQ_ROLES = ['admin', 'head', 'worker'];
// «time» — late and/or left early in one mark (the old «late» and «early» are still read)
const STAFF_MARKS = ['sick', 'vacation', 'time', 'late', 'early', 'absent'];
const workCalOf = () => { const c = db.workCal && typeof db.workCal === 'object' ? db.workCal : {}; return { from: c.from || '09:00', to: c.to || '18:00', off: c.off || [], work: c.work || [] }; };
/* «ФКУ Упрдор»: systems of a request, replaced equipment, monthly report documents */
const UPR = require('./upr-reports.js');
const UPR_SYS = Object.keys(UPR.SYSTEMS);
const REPORTS = new Map();
const reqCfgOf = () => { const c = db.reqCfg && typeof db.reqCfg === 'object' ? db.reqCfg : {}; return { tz: c.tz || 'Europe/Moscow', contract: { ...UPR.DEFAULT_CONTRACT, ...(c.contract || {}), prices: { ...UPR.DEFAULT_CONTRACT.prices, ...((c.contract || {}).prices || {}) } }, tg: c.tg || {}, devToken: c.devToken || '' }; };
/* a message to the Telegram chat of the organization (when the administrator set it up); never blocks the request */
function reqNotify(text) {
  const tg = reqCfgOf().tg; if (!tg.token || !tg.chat) return;
  const body = JSON.stringify({ chat_id: tg.chat, text: ((tg.prefix ? tg.prefix + ': ' : '') + text).slice(0, 4000) });
  try {
    const rq = require('node:https').request({ host: 'api.telegram.org', path: `/bot${encodeURIComponent(tg.token)}/sendMessage`, method: 'POST', timeout: 8000, headers: { 'Content-Type': 'application/json', 'Content-Length': Buffer.byteLength(body) } }, r => r.resume());
    rq.on('error', e => console.error('Telegram:', e.message)); rq.on('timeout', () => rq.destroy()); rq.end(body);
  } catch (e) { console.error('Telegram:', e.message); }
}
/* tabs and sub-tabs of «Все сервисы»: an organization and a user keep a list of the HIDDEN ones (new sections are visible by default) */
const SECTIONS = { works: ['works', 'labels'], stock: ['stock', 'inc', 'wo', 'pay'], cps: [], staff: [], staffp: [], plan: [], dt: [], devs: [], notes: ['task', 'shared', 'draw'], transport: ['cars', 'parts'], refs: [] };
const SECTION_KEYS = Object.entries(SECTIONS).flatMap(([k, subs]) => [k, ...subs.map(x => k + ':' + x)]);
const cleanHide = a => [...new Set((Array.isArray(a) ? a : []).filter(k => SECTION_KEYS.includes(k)))];
// what is hidden for a user: hidden for the organization or for him; a hidden tab hides its sub-tabs
const hiddenFor = u => { const o = u && orgById(u.orgId); return [...new Set([...((o && o.hide) || []), ...((u && u.hide) || [])])]; };
const sees = (u, key) => { const H = hiddenFor(u), top = key.split(':')[0]; return !H.includes(key) && !H.includes(top); };
// a request is seen by its author, its executor, the administrator and the manager
const reqSees = (u, r) => HEAD(u) || r.by === u.id || r.assignee === u.id;
/* serial numbers of labels: the text of a number and the index of every number already printed in the organization */
const serialStr = (t, n) => (t.serial.prefix || '') + String(n).padStart(t.serial.digits || 1, '0') + (t.serial.suffix || '');
function labelSerials(){
  if (db.labelSerials && typeof db.labelSerials === 'object') return db.labelSerials;
  const S = db.labelSerials = {};
  for (const [id, t] of Object.entries(db.labels || {})) for (const x of t.prints || []) {
    if (x.manual && !S[x.manual]) S[x.manual] = { l: id, at: x.at, by: x.by, manual: true };
    else if (x.from !== undefined && !x.reprint && x.count) for (let n = x.from; n < x.from + x.count; n++) { const sn = serialStr(t, n); if (!S[sn]) S[sn] = { l: id, at: x.at, by: x.by }; }
  }
  return S;
}
/* values read by a barcode scanner into labels ({scan}): value → where, when and with which serial number it was printed first */
function labelScans(){
  if (!db.labelScans || typeof db.labelScans !== 'object') db.labelScans = {};
  return db.labelScans;
}
/* where every file of the organization is used: file id → up to five places */
function fileUsage(){
  const used = new Map(), add = (id, what) => { if (!id || !db.files[id]) return; const L = used.get(id) || []; if (L.length < 5 && !L.includes(what)) L.push(what); used.set(id, L); };
    for (const i of Object.values(db.invoices || {})) { add(i.file && i.file.id, `Счёт № ${i.number || '—'}`); add(i.receipt && i.receipt.id, `Чек к счёту № ${i.number || '—'}`); const w = i.income && i.income.waybill; if (w) add(w.file && w.file.id, `Накладная № ${w.number || '—'} (счёт № ${i.number || '—'})`); }
    for (const r of Object.values(db.receipts || {})) add(r.file && r.file.id, `Накладная № ${r.number || '—'}`);
    for (const j of Object.values(db.jobs || {})) {
      for (const f of j.docs || []) add(f.id, `Работа № ${j.no || ''} · ${j.title || ''}`);
      for (const x of j.buy || []) for (const f of x.files || []) add(f.id, `Купить · работа № ${j.no || ''}`);
      for (const pl of j.places || []) for (const v of Object.values(pl.photos || {})) for (const f of [].concat(v || [])) add(f && (f.id || f), `Фото точки · работа № ${j.no || ''}`);
    }
    for (const o of Object.values(db.orders || {})) { for (const f of o.specs || []) add(f.id, `Заказ ${o.number || ''}`); for (const p2 of o.products || []) for (const f of p2.files || []) add(f.id, `Изделие ${p2.name || ''} · заказ ${o.number || ''}`); }
    for (const n of db.notes || []) for (const f of n.files || []) add(f.id, n.type === 'shared' ? 'Общая задача' : 'Заметка');
    for (const d of Object.values(db.devs || {})) for (const f of d.files || []) add(f.id, `Разработка № ${d.no || ''} · ${d.name || ''}`);
    for (const t of Object.values(db.labels || {})) for (const x of t.items || []) if (x.img) add(x.img.id, `Этикетка «${t.name}»`);
    for (const r of Object.values(db.requests || {})) for (const f of [...(r.files || []), ...(r.doneFiles || [])]) add(f.id, `Заявка № ${r.no || ''}`);
    for (const d of db.reqDocs || []) if (d.file) add(d.file.id, `Инструкция «${d.title}»`);
    for (const r of db.refs || []) for (const f of r.files || []) add(f.id, `Справочник «${r.title || ''}»`);
    for (const t of db.trips || []) for (const f of t.files || []) add(f.id, `Путевой лист ${t.date || ''}`);
    for (const c of db.checks || []) for (const f of c.files || []) add(f.id, c.kind === 'fuel' ? 'Чек заправки' : `Чек покупки · ${c.seller || ''}`);
    for (const v of Object.values(db.vehicles || {})) for (const d of v.docs || []) if (d.file) add(d.file.id, `Транспорт ${v.name || ''} · ${d.title || ''}`);
    for (const c of Object.values(db.counterparties || {})) for (const k of ['files', 'docs', 'contracts']) for (const f of [].concat(c[k] || [])) add(f && (f.file ? f.file.id : f.id), `Контрагент ${c.name || ''}`);
  return used;
}
/* «Потенциальные разработки»: the author and the administrator manage a development; the author chooses who sees it
   and who may add data to it (fields, documents, links, comments) */
const devManage = (u, d) => d.by === u.id || u.role === 'admin';
const devEdit = (u, d) => devManage(u, d) || (d.editors || []).includes(u.id);
const devSees = (u, d) => devEdit(u, d) || (d.viewers || []).includes(u.id);

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
  if (!u || u.blocked || String(u.ver || 0) !== parts[2] || contractorExpired(u)) return null;
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
    if (contractorExpired(u)) return fail(res, 403, `Срок доступа подрядчика истёк ${u.accessUntil.split('-').reverse().join('.')}. Обратитесь к администратору`);
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
  if (p[1] === 'stats') return statsApi(req, res, m, user);
  if (p[1] === 'prefs' && m === 'PUT') { user.prefs = cleanPrefs(await readJsonBody(req) || {}); saveUsers(); return send(res, 200, { ok: true, prefs: user.prefs }); }
  // the system administrator manages organizations, backups and the server, not the work of an organization
  if (user.sys && !['rev', 'password'].includes(p[1])) return fail(res, 403, 'Администратор системы управляет организациями. Для работы с данными войдите администратором организации');
  // «Сотрудник» and «Подрядчик» see and change only the work given to them
  // in the requests system an employee makes and does requests and attaches files to them
  if (FIELD(user) && !['rev', 'data', 'password', 'jobs', 'overtime', 'checks', 'trips'].includes(p[1]) && !(orgType(user) === 'requests' && ['requests', 'files'].includes(p[1]))
    && !(p[1] === 'devs' || p[1] === 'notes' || p[1] === 'files')) return fail(res, 403, 'Недостаточно прав');
  if (p[1] === 'users') {
    if (user.role !== 'admin') return fail(res, 403, 'Управлять пользователями может только администратор');
    const target = p[2] && orgUsers().find(u => u.id === p[2]);
    if (m === 'GET' && !p[2]) return send(res, 200, orgUsers().map(adminUser));
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req);
      const err = validateUser(b, true); if (err) return fail(res, 400, err);
      if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
      if (orgType(user) === 'requests' && !REQ_ROLES.includes(b.role)) return fail(res, 400, 'В системе заявок роли: администратор, руководитель, сотрудник');
      if (b.role === 'contractor' && !/^\d{4}-\d{2}-\d{2}$/.test(String(b.accessUntil || ''))) return fail(res, 400, 'Для подрядчика укажите, до какой даты у него доступ');
      const nu = addUser(String(b.login), b.role, String(b.name).trim(), String(b.password), user.orgId);
      if (b.role === 'contractor') nu.accessUntil = String(b.accessUntil);
      nu.hide = cleanHide(b.hide); saveUsers();
      return send(res, 200, adminUser(nu));
    }
    if (!target) return fail(res, 404, 'Пользователь не найден');
    if (target.sys && !user.sys) return fail(res, 403, 'Учётную запись администратора системы меняет только он сам');
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      if (b.role !== undefined) {
        if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
        if (orgType(user) === 'requests' && !REQ_ROLES.includes(b.role)) return fail(res, 400, 'В системе заявок роли: администратор, руководитель, сотрудник');
        if (target.id === user.id && b.role !== 'admin') return fail(res, 400, 'Нельзя снять роль администратора с самого себя');
        target.role = b.role;
      }
      if (b.accessUntil !== undefined || b.role !== undefined) {
        if (target.role === 'contractor') {
          const d = String(b.accessUntil ?? target.accessUntil ?? '');
          if (!/^\d{4}-\d{2}-\d{2}$/.test(d)) return fail(res, 400, 'Для подрядчика укажите, до какой даты у него доступ');
          target.accessUntil = d;
        } else delete target.accessUntil;
      }
      if (b.hide !== undefined) target.hide = cleanHide(b.hide);
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
    // points written into works before they were marked on the map get the mark
    if (db.dt && Array.isArray(db.dt.points) && db.dt.points.some(x => x.need)) {
      const nd = new Map(db.dt.points.filter(x => x.need).map(x => [x.no, x.need])); let ch = false;
      for (const j of Object.values(db.jobs || {})) for (const pl of j.places || []) if (pl.dtNo && !pl.need && nd.has(pl.dtNo)) { pl.need = nd.get(pl.dtNo); ch = true; }
      if (ch) saveDb();
    }
    // production is part of «Работы»: an order without a work gets one
    if (HEAD(user)) { let ch = false; const linked = new Set(Object.values(db.jobs || {}).map(j => j.orderId).filter(Boolean));
      for (const [oid, o] of Object.entries(db.orders || {})) if (!linked.has(oid) && !o.jobId) {
        const id = newId(), st = o.status === 'closed' ? 'done' : o.status === 'work' ? 'work' : 'new';
        db.jobs[id] = { kind: 'prod', title: o.title || o.number || 'Заказ', customerId: o.customerId || null, due: o.deadline || '', description: '', docs: [], photoSpec: [], workers: [], places: [], status: st, report: '',
          no: Math.max(0, ...Object.values(db.jobs).map(j => j.no || 0)) + 1, orderId: oid, leaderId: null, createdBy: user.id, createdAt: o.createdAt || new Date().toISOString(), fromOrder: true };
        o.jobId = id; ch = true; }
      if (ch) saveDb(); }
    // works with production made before orders were created for them
    if (HEAD(user)) { let ch = false; for (const [jid, j] of Object.entries(db.jobs || {})) if (ensureJobOrder(j, jid, user)) ch = true; if (ch) saveDb(); }
    const out = { rev: db.rev, users: Object.fromEntries(orgUsers().map(u => [u.id, u.name])), meta: db.meta,
      // the system administrator does not work with the organization's data: he is not offered as staff
      staff: orgUsers().filter(u => !u.blocked && !u.sys).map(u => ({ id: u.id, name: u.name, role: u.role })) };
    // a worker gets only the points assigned to him; points without an executor only when he is the job's only worker
    const mine = j => ({ ...j, places: (j.places || []).filter(x => x.assignee ? x.assignee === user.id : (j.workers || []).length === 1) });
    COLLECTIONS.forEach(c => { out[c] = FIELD(user) ? (c === 'jobs' ? listOf(c).filter(j => (j.workers || []).includes(user.id)).map(mine) : []) : listOf(c); });
    if (orgType(user) === 'requests') {
      out.requests = Object.entries(db.requests || {}).map(([id, r]) => ({ id, ...r })).filter(r => reqSees(user, r));
      out.reqUsers = orgUsers().filter(u => !u.blocked && !u.sys).map(u => ({ id: u.id, name: u.name, role: u.role }));
      out.reqDocs = Array.isArray(db.reqDocs) ? db.reqDocs : [];
      out.devReadings = Array.isArray(db.devReadings) ? db.devReadings.slice(-10).reverse() : [];
    }
    out.devs = sees(user, 'devs') ? Object.entries(db.devs || {}).map(([id, d]) => ({ id, ...d })).filter(d => devSees(user, d)) : [];
    out.labels = FIELD(user) || !sees(user, 'works:labels') ? [] : Object.entries(db.labels || {}).map(([id, t]) => ({ id, ...t }));
    // printed serial numbers — the page warns about a repeat while the number is typed
    if (!FIELD(user) && out.labels.length) { const S = labelSerials(), SC = labelScans(); out.labelSerials = Object.fromEntries(Object.entries(S).slice(-20000).map(([k, v]) => [k, [v.l, v.at, v.by]]));
      out.labelScans = Object.fromEntries(Object.entries(SC).slice(-20000).map(([k, v]) => [k, [v.l, v.at, v.by, v.serial || '']])); }
    out.receipts = FIELD(user) || !sees(user, 'stock:inc') ? [] : Object.entries(db.receipts || {}).map(([id, r]) => ({ id, ...r }));
    if (FIELD(user)) { out.meta = {}; out.staff = []; }
    // irregular working hours: an employee sees his own entries, a manager sees everyone's
    out.overtime = (Array.isArray(db.overtime) ? db.overtime : []).filter(x => HEAD(user) || x.by === user.id);
    // the marks of the manager (sick leave, vacation, late, left early, absence) and the working schedule
    out.staffMarks = (Array.isArray(db.staffMarks) ? db.staffMarks : []).filter(x => HEAD(user) || x.user === user.id);
    out.workCal = workCalOf();
    // «Справочники»: a manager sees all; the others — the open ones and those he is chosen for
    if (orgType(user) !== 'requests' && sees(user, 'refs')) out.refs = (Array.isArray(db.refs) ? db.refs : []).filter(r => HEAD(user) || !r.restricted || (r.viewers || []).includes(user.id));
    // «Загрузить чек»: an employee sees his own receipts, a manager and the accountant see everyone's; the vehicles to choose for a refuelling
    if (orgType(user) !== 'requests') {
      out.checks = (Array.isArray(db.checks) ? db.checks : []).filter(x => HEAD(user) || user.role === 'accountant' || x.by === user.id);
      out.trips = (Array.isArray(db.trips) ? db.trips : []).filter(x => HEAD(user) || user.role === 'accountant' || x.by === user.id);
      out.vehBrief = Object.entries(db.vehicles || {}).map(([id, v]) => ({ id, name: v.name, plate: v.plate || '' })).sort((a, b) => a.name.localeCompare(b.name, 'ru'));
    }
    // «Транспорт»: the vehicles of the company with maintenance and documents, and the spare parts — for managers
    if (HEAD(user) && orgType(user) !== 'requests') {
      out.vehicles = sees(user, 'transport:cars') || sees(user, 'transport:parts') ? Object.entries(db.vehicles || {}).map(([id, v]) => ({ id, ...v })) : [];
      out.parts = sees(user, 'transport:parts') ? (Array.isArray(db.parts) ? db.parts : []) : [];
    }
    if (FIELD(user)) out.notes = (db.notes || []).filter(n => n.type === 'shared' && n.assignee === user.id);
    else if (sees(user, 'notes')) out.notes = (db.notes || []).filter(n => n.by === user.id || (n.type === 'shared' && ((n.share || []).includes(user.id) || n.assignee === user.id)));
    return send(res, 200, out);
  }
  // hidden sections: their data is not given and their actions are refused
  { const need = { devs: 'devs', labels: 'works:labels', receipts: 'stock:inc', notes: 'notes', 'stock-acct': 'stock:stock' }[p[1]];
    if (need && !user.sys && !sees(user, need)) return fail(res, 403, 'Этот раздел для вас закрыт'); }
  if (p[1] === 'devs') {
    if (orgType(user) === 'requests') return fail(res, 403, 'Разработки есть только в системе «Все сервисы»');
    if (!db.devs || typeof db.devs !== 'object') db.devs = {};
    const D = db.devs, now = new Date().toISOString();
    const txt = (v, n) => String(v || '').trim().slice(0, n);
    const cleanFiles = a => (Array.isArray(a) ? a : []).filter(f => f && db.files[f.id]).slice(0, 200).map(f => ({ id: f.id, name: String(f.name || db.files[f.id].name).slice(0, 200), type: db.files[f.id].type, size: db.files[f.id].size, at: f.at || db.files[f.id].at, by: f.by || db.files[f.id].by }));
    const cleanLinks = a => (Array.isArray(a) ? a : []).slice(0, 100).map(l => ({ id: String(l && l.id || newId()).slice(0, 20), title: txt(l && l.title, 200), url: txt(l && l.url, 1000) }))
      .filter(l => /^https?:\/\/[^\s]+$/i.test(l.url)).map(l => ({ ...l, title: l.title || l.url }));
    const people = a => [...new Set((Array.isArray(a) ? a : []).filter(id => orgUsers().some(u => u.id === id && !u.sys)))].slice(0, 200);
    const fields = (b, d) => { for (const [k, n] of [['name', 200], ['short', 1000], ['cost', 200], ['compCost', 1000], ['desc', 10000], ['features', 5000], ['needs', 5000]]) if (b[k] !== undefined) d[k] = txt(b[k], n);
      if (b.files !== undefined) d.files = cleanFiles(b.files); if (b.links !== undefined) d.links = cleanLinks(b.links); };
    const access = (b, d) => { if (b.editors !== undefined) d.editors = people(b.editors).filter(id => id !== d.by);
      if (b.viewers !== undefined) d.viewers = people(b.viewers).filter(id => id !== d.by && !(d.editors || []).includes(id)); };
    const out = (id, d) => ({ ok: true, dev: { id, ...d }, rev: db.rev });
    if (m === 'GET' && !p[2]) return send(res, 200, Object.entries(D).map(([id, d]) => ({ id, ...d })).filter(d => devSees(user, d)));
    if (m === 'POST' && !p[2]) {
      if (FIELD(user)) return fail(res, 403, 'Создавать разработки может администратор, руководитель или бухгалтер');
      const b = await readJsonBody(req);
      if (!txt(b.name, 200)) return fail(res, 400, 'Укажите наименование проекта');
      const id = newId(), d = { no: Math.max(0, ...Object.values(D).map(x => x.no || 0)) + 1, by: user.id, at: now, files: [], links: [], comments: [], viewers: [], editors: [] };
      fields(b, d); access(b, d); D[id] = d; saveDb();
      return send(res, 200, out(id, d));
    }
    const d = p[2] && D[p[2]];
    if (!d || !devSees(user, d)) return fail(res, 404, 'Разработка не найдена — обновите страницу');
    if (p[3] === 'comments') {
      if (!devEdit(user, d)) return fail(res, 403, 'Добавлять данные к разработке могут только те, кому это разрешено');
      d.comments = Array.isArray(d.comments) ? d.comments : [];
      if (m === 'POST') { const b = await readJsonBody(req), t = txt(b.text, 4000); if (!t) return fail(res, 400, 'Пустой комментарий');
        d.comments.push({ id: newId(), by: user.id, at: now, text: t }); d.updatedAt = now; d.updatedBy = user.id; saveDb(); return send(res, 200, out(p[2], d)); }
      if (m === 'DELETE' && p[4]) { const c = d.comments.find(x => x.id === p[4]); if (!c) return fail(res, 404, 'Комментарий не найден');
        if (c.by !== user.id && !devManage(user, d)) return fail(res, 403, 'Удалить можно только свой комментарий');
        d.comments = d.comments.filter(x => x !== c); saveDb(); return send(res, 200, out(p[2], d)); }
      return fail(res, 405, 'Метод не поддерживается');
    }
    if (m === 'PATCH' && p.length === 3) {
      if (!devEdit(user, d)) return fail(res, 403, 'Добавлять данные к разработке могут только те, кому это разрешено');
      const b = await readJsonBody(req);
      if ((b.viewers !== undefined || b.editors !== undefined) && !devManage(user, d)) return fail(res, 403, 'Кто видит разработку, выбирает её автор или администратор');
      if (b.name !== undefined && !txt(b.name, 200)) return fail(res, 400, 'Укажите наименование проекта');
      fields(b, d); access(b, d); d.updatedAt = now; d.updatedBy = user.id; saveDb();
      return send(res, 200, out(p[2], d));
    }
    if (m === 'DELETE' && p.length === 3) {
      if (!devManage(user, d)) return fail(res, 403, 'Удалить разработку может её автор или администратор');
      delete D[p[2]]; saveDb(); return send(res, 200, { ok: true, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* label templates for production: size in millimetres, elements (text with fields, barcode of the serial number) and the serial counter;
     the next serial number is handed out by the server, so two people never print the same one */
  if (p[1] === 'labels') {
    if (!db.labels || typeof db.labels !== 'object') db.labels = {};
    const L = db.labels, now = new Date().toISOString();
    const num = (v, lo, hi, d) => { const n = Number(v); return Number.isFinite(n) ? Math.min(hi, Math.max(lo, Math.round(n * 10) / 10)) : d; };
    const cleanTpl = (b, old = {}) => {
      const ref = b.ref && ((b.ref.type === 'order' && db.orders[b.ref.id]) || (b.ref.type === 'job' && db.jobs[b.ref.id])) ? { type: b.ref.type, id: b.ref.id } : null;
      const sr = b.serial || {};
      return { name: String(b.name || old.name || 'Этикетка').trim().slice(0, 120) || 'Этикетка', w: num(b.w, 10, 300, 58), h: num(b.h, 10, 300, 40), ref,
        // printing: the turn of the label on the printer's tape and a shift to hit the label exactly
        rot: [0, 90, 180, 270].includes(Number(b.rot)) ? Number(b.rot) : 0, dx: num(b.dx, -30, 30, 0), dy: num(b.dy, -30, 30, 0),
        serial: { prefix: String(sr.prefix || '').slice(0, 30), suffix: String(sr.suffix || '').slice(0, 30), digits: num(sr.digits, 1, 12, 6) | 0,
          next: old.serial ? old.serial.next : Math.max(0, Math.floor(Number(sr.next) || 1)) },
        items: (Array.isArray(b.items) ? b.items : []).slice(0, 40).filter(x => x && ['text', 'barcode', 'line', 'box', 'qr', 'image'].includes(x.type) && (x.type !== 'image' || (x.img && db.files[x.img.id]))).map(x => ({
          id: String(x.id || newId()).slice(0, 20), type: x.type, text: String(x.text || '').slice(0, 300), x: num(x.x, -50, 300, 2), y: num(x.y, -50, 300, 2),
          w: num(x.w, 0.2, 300, 30), h: num(x.h, 0.2, 300, 8), size: num(x.size, 3, 120, 10), bold: !!x.bold, align: ['left', 'center', 'right'].includes(x.align) ? x.align : 'left',
          // a QR code: what it holds — fields joined by a separator, a typed text, or a typed text with fields
          ...(x.type === 'qr' ? { mode: ['fields', 'text', 'mix'].includes(x.mode) ? x.mode : 'fields', fields: (Array.isArray(x.fields) ? x.fields : []).filter(k => ['serial', 'scan', 'name', 'order', 'customer', 'date'].includes(k)).slice(0, 6),
            // the elements of the label (by their numbers) whose printed values go into the code
            ...(Array.isArray(x.els) ? { els: x.els.map(e => String(e).slice(0, 20)).slice(0, 40) } : {}),
            sep: String(x.sep ?? ';').slice(0, 5), ec: ['L', 'M', 'Q', 'H'].includes(x.ec) ? x.ec : 'M' } : {}),
          // a picture: an uploaded file, its proportions, black-and-white or in colour
          ...(x.type === 'image' ? { img: { id: x.img.id, name: String(x.img.name || db.files[x.img.id].name).slice(0, 200) }, ar: num(x.ar, 0.01, 100, 1), lock: x.lock !== false, bw: x.bw !== false } : {}) })) };
    };
    if (m === 'POST' && !p[2]) {
      if (!canEdit(user)) return fail(res, 403, 'Создавать этикетки может руководитель или администратор');
      const id = newId(); L[id] = { ...cleanTpl(await readJsonBody(req)), prints: [], createdAt: now, createdBy: user.id };
      saveDb(); return send(res, 200, { ok: true, id, label: { id, ...L[id] }, rev: db.rev });
    }
    const t = p[2] && L[p[2]];
    if (!t) return fail(res, 404, 'Этикетка не найдена — обновите страницу');
    if (m === 'PUT' && p.length === 3) {
      if (!canEdit(user)) return fail(res, 403, 'Менять этикетки может руководитель или администратор');
      const b = await readJsonBody(req);
      Object.assign(t, cleanTpl(b, t), { updatedAt: now, updatedBy: user.id });
      // the counter is changed on purpose only: «Следующий номер»
      if (b.serial && b.serial.setNext !== undefined) { const n = Math.floor(Number(b.serial.setNext)); if (!(n >= 0 && n < 1e12)) return fail(res, 400, 'Неверный номер'); t.serial.next = n; t.prints.push({ at: now, by: user.id, set: n }); }
      saveDb(); return send(res, 200, { ok: true, label: { id: p[2], ...t }, rev: db.rev });
    }
    // every printed serial number of the organization: serial → where and when it was printed first
    const S = labelSerials();
    const mark = (sn, extra = {}) => { if (!S[sn]) S[sn] = { l: p[2], at: now, by: user.id, ...extra }; };
    // the value from the scanner: unique too — a repeat only on purpose (force)
    const SC = labelScans(), fmtAt = at => new Date(at).toLocaleString('ru-RU', { timeZone: process.env.TZ || 'Europe/Moscow' });
    const scanDup = (scan, force) => { const was = scan && SC[scan]; if (!was || force) return null; const u = users.find(x => x.id === was.by), tl = L[was.l];
      return { error: `Значение со сканера «${scan}» уже печаталось ${fmtAt(was.at)}${was.serial ? ' с номером ' + was.serial : ''}${u ? ', ' + u.name : ''}${tl ? ` (этикетка «${tl.name}»)` : ''}`, dupScan: { scan, ...was, label: tl ? tl.name : '' } }; };
    const dateOf = b => /^\d{4}-\d{2}-\d{2}$/.test(b.date || '') ? b.date : undefined;
    const markScan = (scan, sn) => { if (!scan) return; if (!SC[scan]) SC[scan] = { l: p[2], at: now, by: user.id, serial: sn }; else SC[scan].repeats = (SC[scan].repeats || 0) + 1; if (S[sn] && !S[sn].scan) S[sn].scan = scan; };
    // «Печать следующей»: the next free number(s) — numbers already printed (by hand or before the counter was moved back) are skipped
    if (m === 'POST' && p[3] === 'next') {
      const b = await readJsonBody(req), count = Math.min(500, Math.max(1, Math.floor(Number(b.count) || 1))), scan = String(b.scan || '').trim().slice(0, 200);
      if (scan && count > 1) return fail(res, 400, 'Со значением со сканера печатается одна этикетка — уберите количество или значение');
      const sd = scanDup(scan, b.force); if (sd) return send(res, 409, sd);
      const nums = [], skipped = []; let n = t.serial.next;
      while (nums.length < count && n < t.serial.next + count + 10000) { const sn = serialStr(t, n); if (S[sn]) skipped.push(sn); else { nums.push(n); mark(sn); } n++; }
      if (nums.length < count) return fail(res, 409, 'Не удалось подобрать свободные номера — проверьте префикс и счётчик');
      t.serial.next = nums[nums.length - 1] + 1;
      const serials = nums.map(x => serialStr(t, x));
      markScan(scan, serials[0]); const date = dateOf(b); if (date) serials.forEach(sn => { if (S[sn] && !S[sn].date) S[sn].date = date; });
      t.prints = (t.prints || []).concat({ at: now, by: user.id, from: nums[0], count, scan: scan || undefined, date, list: serials.length > 1 && nums[nums.length - 1] - nums[0] + 1 !== count ? serials : undefined, skipped: skipped.length ? skipped.slice(0, 50) : undefined }).slice(-300);
      saveDb(); return send(res, 200, { ok: true, from: nums[0], count, nums, serials, skipped, next: t.serial.next, rev: db.rev });
    }
    // a serial number typed by hand: printed if it was never printed before; a repeat only on purpose (force)
    if (m === 'POST' && p[3] === 'manual') {
      const b = await readJsonBody(req), sn = String(b.serial || '').trim().slice(0, 60), scan = String(b.scan || '').trim().slice(0, 200);
      if (!sn) return fail(res, 400, 'Введите серийный номер');
      const sd = scanDup(scan, b.force); if (sd) return send(res, 409, sd);
      const was = S[sn];
      if (was && !b.force) { const tl = L[was.l], u = users.find(x => x.id === was.by);
        return send(res, 409, { error: `Номер ${sn} уже печатался ${new Date(was.at).toLocaleString('ru-RU', { timeZone: process.env.TZ || 'Europe/Moscow' })}${u ? ', ' + u.name : ''}${tl ? ` (этикетка «${tl.name}»)` : ''}`, dup: { serial: sn, ...was, label: tl ? tl.name : '' } }); }
      mark(sn, { manual: true }); markScan(scan, sn); const date = dateOf(b); if (date && S[sn] && !S[sn].date) S[sn].date = date;
      t.manual = [sn, ...(t.manual || []).filter(x => x !== sn)].slice(0, 200);
      t.prints = (t.prints || []).concat({ at: now, by: user.id, manual: sn, scan: scan || undefined, date, ...(was ? { reprint: true } : {}) }).slice(-300);
      saveDb(); return send(res, 200, { ok: true, serial: sn, repeat: !!was, rev: db.rev });
    }
    // reprint of a number already printed: only written into the log
    if (m === 'POST' && p[3] === 'reprint') {
      const b = await readJsonBody(req), sn = b.serial !== undefined ? String(b.serial).trim() : serialStr(t, Math.floor(Number(b.n)));
      if (!S[sn]) return fail(res, 400, `Номер ${sn} ещё не печатался`);
      t.prints = (t.prints || []).concat({ at: now, by: user.id, manual: sn, reprint: true, scan: S[sn].scan || undefined, date: S[sn].date }).slice(-300);
      saveDb(); return send(res, 200, { ok: true, serial: sn, scan: S[sn].scan || '', date: S[sn].date || '', rev: db.rev });
    }
    if (m === 'DELETE' && p.length === 3) {
      if (!canEdit(user)) return fail(res, 403, 'Удалить этикетку может руководитель или администратор');
      delete L[p[2]]; saveDb(); return send(res, 200, { ok: true, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Управление заявками»: a user makes a request and chooses who does it; the executor takes it and marks it done;
     the author cancels it or sends it back to work; the administrator and the manager see and change everything */
  if (p[1] === 'requests') {
    if (orgType(user) !== 'requests') return fail(res, 403, 'Заявки есть только в системе «Управление заявками»');
    if (!db.requests || typeof db.requests !== 'object') db.requests = {};
    const R = db.requests, boss = HEAD(user), now = new Date().toISOString();
    const okUser = id => !!id && orgUsers().some(u => u.id === id && !u.blocked && !u.sys);
    const cleanFiles = a => (Array.isArray(a) ? a : []).filter(f => f && db.files[f.id]).slice(0, 30).map(f => ({ id: f.id, name: String(f.name || db.files[f.id].name).slice(0, 200), type: db.files[f.id].type }));
    const out = (id, r) => ({ ok: true, request: { id, ...r }, rev: db.rev });
    if (m === 'GET' && !p[2]) return send(res, 200, Object.entries(R).map(([id, r]) => ({ id, ...r })).filter(r => reqSees(user, r)));
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req), text = String(b.text || '').trim().slice(0, 4000);
      // the title is the first line of the description when it is not given
      const title = (String(b.title || '').trim() || text.split('\n')[0]).slice(0, 200);
      if (!title) return fail(res, 400, 'Опишите проблему');
      if (b.system !== undefined && b.system !== '' && !UPR_SYS.includes(b.system)) return fail(res, 400, 'Выберите систему');
      if (b.assignee && !okUser(b.assignee)) return fail(res, 400, 'Исполнитель не найден');
      const id = newId(), no = Math.max(0, ...Object.values(R).map(r => r.no || 0)) + 1;
      R[id] = { no, title, text, system: b.system || '', due: /^\d{4}-\d{2}-\d{2}$/.test(b.due || '') ? b.due : '', urgent: !!b.urgent,
        assignee: b.assignee || null, files: cleanFiles(b.files), status: 'new', by: user.id, at: now, comments: [], history: [{ at: now, by: user.id, act: 'created', to: b.assignee || null }] };
      saveDb();
      reqNotify(`Новая заявка №${no}${b.system ? ' (' + UPR.SYSTEMS[b.system] + ')' : ''}.\n${text || title}\nЗаявитель: ${user.name}${R[id].files.length ? `\nФото и файлов: ${R[id].files.length}` : ''}`);
      return send(res, 200, out(id, R[id]));
    }
    const r = p[2] && R[p[2]];
    if (!r || !reqSees(user, r)) return fail(res, 404, 'Заявка не найдена — обновите страницу');
    const author = r.by === user.id, executor = r.assignee === user.id;
    if (p[3] === 'comments' && m === 'POST') {
      const b = await readJsonBody(req), t = String(b.text || '').trim().slice(0, 2000);
      if (!t) return fail(res, 400, 'Пустой комментарий');
      r.comments = Array.isArray(r.comments) ? r.comments : [];
      r.comments.push({ id: newId(), by: user.id, at: now, text: t }); r.updatedAt = now;
      saveDb();
      return send(res, 200, out(p[2], r));
    }
    if (m === 'PATCH' && p.length === 3) {
      const b = await readJsonBody(req), act = b.action, note = String(b.note || '').trim().slice(0, 2000);
      const log = (a, extra = {}) => { r.history = Array.isArray(r.history) ? r.history : []; r.history.push({ at: now, by: user.id, act: a, ...(note ? { note } : {}), ...extra }); r.updatedAt = now; };
      if (act === 'take') {
        if (!(executor || boss || (!r.assignee))) return fail(res, 403, 'Взять в работу может исполнитель заявки');
        if (r.status !== 'new') return fail(res, 409, 'Заявка уже в работе или закрыта');
        if (!r.assignee) r.assignee = user.id;
        r.status = 'work'; r.takenAt = now; log('take');
      } else if (act === 'done' || act === 'reject') {
        // «Выполнена» or «Отклонена»: what was done (or why it is rejected), the replaced equipment and the photos of the result
        if (!(executor || boss)) return fail(res, 403, 'Закрыть заявку может исполнитель заявки');
        if (!['new', 'work'].includes(r.status)) return fail(res, 409, 'Заявка уже закрыта');
        if (note.length < 3) return fail(res, 400, act === 'done' ? 'Опишите, что было сделано' : 'Напишите причину отклонения');
        let repl = [];
        if (act === 'done' && Array.isArray(b.repl)) {
          if (b.repl.length > 15) return fail(res, 400, 'Слишком много замен (не более 15)');
          for (const [i, x] of b.repl.entries()) {
            const cat = String(x && x.category || '').trim(), nw = String(x && x.newSerial || '').trim().slice(0, 100), old = String(x && x.oldSerial || '').trim().slice(0, 100), eq = String(x && x.equipment || '').trim().slice(0, 200);
            if (!UPR.EQUIPMENT.includes(cat)) return fail(res, 400, `Замена № ${i + 1}: выберите оборудование из списка`);
            if (!nw || !old) return fail(res, 400, `Замена № ${i + 1}: укажите серийные номера нового и старого оборудования`);
            repl.push({ category: cat, equipment: eq || cat, newSerial: nw, oldSerial: old });
          }
        }
        r.status = act; r.doneAt = now; r.doneBy = user.id; r.doneNote = note; r.repl = repl; r.doneFiles = cleanFiles(b.files); log(act);
        reqNotify(`Заявка №${r.no} ${act === 'done' ? 'закрыта' : 'отклонена'}${r.system ? ' (' + UPR.SYSTEMS[r.system] + ')' : ''}.\nОтвет исполнителя: ${note.slice(0, 700)}${repl.length ? '\nЗамен оборудования: ' + repl.length : ''}\nИсполнитель: ${user.name}`);
      } else if (act === 'photos') {
        // more photos to an open request: its author, executor or a manager
        if (!(author || executor || boss)) return fail(res, 403, 'Добавить фото может автор или исполнитель заявки');
        if (!['new', 'work'].includes(r.status)) return fail(res, 409, 'Заявка уже закрыта');
        const add = cleanFiles(b.files); if (!add.length) return fail(res, 400, 'Выберите фото');
        r.files = cleanFiles([...(r.files || []), ...add]); log('photos');
      } else if (act === 'dates') {
        // the administrator corrects the date of creation and closing
        if (user.role !== 'admin') return fail(res, 403, 'Только администратор может менять даты');
        const at = Date.parse(b.at), dn = b.doneAt ? Date.parse(b.doneAt) : null;
        if (!Number.isFinite(at)) return fail(res, 400, 'Укажите корректную дату создания');
        const closed = ['done', 'reject', 'cancel'].includes(r.status);
        if (closed && !Number.isFinite(dn)) return fail(res, 400, 'У закрытой заявки должна быть дата закрытия');
        if (closed && dn < at) return fail(res, 400, 'Дата закрытия раньше даты создания');
        r.at = new Date(at).toISOString(); if (closed) { const k = r.status === 'cancel' ? 'cancelAt' : 'doneAt'; r[k] = new Date(dn).toISOString(); }
        log('dates');
      } else if (act === 'reopen') {
        if (!(author || boss)) return fail(res, 403, 'Вернуть заявку в работу может её автор');
        if (!['done', 'cancel', 'reject'].includes(r.status)) return fail(res, 409, 'Заявка не закрыта');
        r.status = r.assignee ? 'work' : 'new'; r.doneAt = null; r.doneBy = null; log('reopen');
      } else if (act === 'cancel') {
        if (!(author || boss)) return fail(res, 403, 'Отменить заявку может её автор');
        if (!['new', 'work'].includes(r.status)) return fail(res, 409, 'Заявка уже закрыта');
        r.status = 'cancel'; r.cancelAt = now; log('cancel');
      } else if (act === 'assign') {
        if (!(boss || (author && r.status === 'new'))) return fail(res, 403, 'Сменить исполнителя может руководитель или автор, пока заявка не в работе');
        if (b.assignee && !okUser(b.assignee)) return fail(res, 400, 'Исполнитель не найден');
        if (!['new', 'work'].includes(r.status)) return fail(res, 409, 'Заявка закрыта');
        r.assignee = b.assignee || null; if (!r.assignee) r.status = 'new'; log('assign', { to: r.assignee });
      } else if (act === 'edit') {
        if (!(boss || (author && r.status === 'new'))) return fail(res, 403, 'Изменить заявку может автор, пока её не взяли в работу');
        if (b.title !== undefined) { const t = String(b.title).trim().slice(0, 200); if (!t) return fail(res, 400, 'Напишите, что нужно сделать'); r.title = t; }
        if (b.text !== undefined) r.text = String(b.text).trim().slice(0, 4000);
        if (b.due !== undefined) r.due = /^\d{4}-\d{2}-\d{2}$/.test(b.due || '') ? b.due : '';
        if (b.urgent !== undefined) r.urgent = !!b.urgent;
        if (b.files !== undefined) r.files = cleanFiles(b.files);
        if (b.system !== undefined) { if (b.system && !UPR_SYS.includes(b.system)) return fail(res, 400, 'Выберите систему'); r.system = b.system || ''; }
        log('edit');
      } else return fail(res, 400, 'Неизвестное действие');
      saveDb();
      return send(res, 200, out(p[2], r));
    }
    if (m === 'DELETE' && p.length === 3) {
      if (!(boss || (author && r.status === 'new' && !(r.comments || []).length))) return fail(res, 403, 'Удалить можно свою заявку, пока её не взяли в работу, — иначе отмените её');
      delete R[p[2]]; saveDb();
      return send(res, 200, { ok: true, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Справочники»: a manager adds files or text, says what it belongs to (a work, a name typed by hand, or general information)
     and who sees it (everyone or chosen employees); the others only read */
  if (p[1] === 'refs') {
    if (user.sys || orgType(user) === 'requests') return fail(res, 403, 'Недоступно');
    if (!HEAD(user)) return fail(res, 403, 'Справочники ведёт руководитель или администратор');
    if (!sees(user, 'refs')) return fail(res, 403, 'Этот раздел для вас закрыт');
    if (!Array.isArray(db.refs)) db.refs = [];
    const R = db.refs, now = new Date().toISOString(), txt = (v, n) => String(v ?? '').trim().slice(0, n);
    const clean = b => {
      const title = txt(b.title, 300), text = txt(b.text, 20000);
      const files = (Array.isArray(b.files) ? b.files : []).filter(f => f && db.files[f.id]).slice(0, 50).map(f => ({ id: f.id, name: db.files[f.id].name, type: db.files[f.id].type, size: db.files[f.id].size }));
      if (!title) return 'Напишите название справочника';
      if (!text && !files.length) return 'Загрузите файл или внесите текст';
      const s0 = b.scope || {}; let scope;
      if (s0.type === 'job') { const j = db.jobs[s0.jobId]; if (!j) return 'Выберите проект'; scope = { type: 'job', jobId: s0.jobId, name: `№ ${j.no || ''} · ${j.title || ''}` }; }
      else if (s0.type === 'other') { const name = txt(s0.name, 200); if (!name) return 'Впишите, к чему относится справочник'; scope = { type: 'other', name }; }
      else scope = { type: 'common', name: 'Общая информация' };
      const restricted = !!b.restricted, viewers = restricted ? [...new Set((Array.isArray(b.viewers) ? b.viewers : []).filter(id => orgUsers().some(u => u.id === id && !u.sys)))] : [];
      if (restricted && !viewers.length) return 'Выберите сотрудников, которые видят справочник';
      return { title, text, files, scope, restricted, viewers };
    };
    if (m === 'POST' && !p[2]) { const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v); const x = { id: newId(), ...v, at: now, by: user.id }; R.push(x); saveDb(); return send(res, 200, { ok: true, ref: x, rev: db.rev }); }
    const x = p[2] && R.find(e => e.id === p[2]); if (!x) return fail(res, 404, 'Справочник не найден — обновите страницу');
    if (m === 'PUT') { const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v); Object.assign(x, v, { updatedAt: now, updatedBy: user.id }); saveDb(); return send(res, 200, { ok: true, ref: x, rev: db.rev }); }
    if (m === 'DELETE') { db.refs = R.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Путевые листы»: an employee uploads the photo of a waybill and says which work it belongs to (and the vehicle, if he likes) */
  if (p[1] === 'trips') {
    if (user.sys || orgType(user) === 'requests') return fail(res, 403, 'Недоступно');
    if (!Array.isArray(db.trips)) db.trips = [];
    const T = db.trips;
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req);
      const files = (Array.isArray(b.files) ? b.files : []).filter(f => f && db.files[f.id]).slice(0, 10).map(f => ({ id: f.id, name: db.files[f.id].name, type: db.files[f.id].type }));
      if (!files.length) return fail(res, 400, 'Загрузите фото путевого листа');
      const j = b.jobId && db.jobs[b.jobId];
      if (!j) return fail(res, 400, 'Выберите, к какой работе относится путевой лист');
      if (FIELD(user) && !onJob(user, j)) return fail(res, 403, 'Это не ваша работа');
      if (b.vehicleId && !(db.vehicles || {})[b.vehicleId]) return fail(res, 400, 'Транспорт не найден');
      const x = { id: newId(), by: user.id, at: new Date().toISOString(), date: /^\d{4}-\d{2}-\d{2}$/.test(b.date || '') ? b.date : localDate(), jobId: b.jobId, vehicleId: b.vehicleId || null, note: String(b.note || '').trim().slice(0, 1000), files };
      T.push(x); saveDb();
      return send(res, 200, { ok: true, trip: x, rev: db.rev });
    }
    const x = p[2] && T.find(e => e.id === p[2]);
    if (!x || !(x.by === user.id || HEAD(user))) return fail(res, 404, 'Путевой лист не найден — обновите страницу');
    if (m === 'DELETE') { db.trips = T.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Загрузить чек»: a refuelling (photo of the receipt, the vehicle) and a purchase (the work, photo, date, seller, goods with quantity and price, sum) */
  if (p[1] === 'checks') {
    if (user.sys || orgType(user) === 'requests') return fail(res, 403, 'Недоступно');
    if (!Array.isArray(db.checks)) db.checks = [];
    const C = db.checks, now = new Date().toISOString(), txt = (v, n) => String(v ?? '').trim().slice(0, n), D = /^\d{4}-\d{2}-\d{2}$/;
    const money = v => { if (v === '' || v == null) return null; const n = Number(String(v).replace(/\s/g, '').replace(',', '.')); return Number.isFinite(n) && n >= 0 ? Math.round(n * 100) / 100 : NaN; };
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req), kind = b.kind === 'fuel' ? 'fuel' : b.kind === 'buy' ? 'buy' : '';
      if (!kind) return fail(res, 400, 'Выберите: заправка или покупка');
      const files = (Array.isArray(b.files) ? b.files : []).filter(f => f && db.files[f.id]).slice(0, 10).map(f => ({ id: f.id, name: db.files[f.id].name, type: db.files[f.id].type }));
      if (!files.length) return fail(res, 400, 'Загрузите фото или картинку чека');
      const date = D.test(b.date || '') ? b.date : localDate();
      const x = { id: newId(), kind, by: user.id, at: now, date, files, note: txt(b.note, 1000) };
      if (kind === 'fuel') {
        if (!b.vehicleId || !(db.vehicles || {})[b.vehicleId]) return fail(res, 400, 'Выберите, какой транспорт заправлен');
        const sum = money(b.sum), liters = money(b.liters);
        if (Number.isNaN(sum) || Number.isNaN(liters)) return fail(res, 400, 'Сумма и литры — числа');
        Object.assign(x, { vehicleId: b.vehicleId, sum, liters });
      } else {
        const job = b.jobId && db.jobs[b.jobId], work = txt(b.work, 200);
        if (!job && !work) return fail(res, 400, 'Укажите, на какой вид работ покупка');
        const seller = txt(b.seller, 300); if (!seller) return fail(res, 400, 'Укажите, у кого куплено');
        const items = [];
        for (const [i, it] of (Array.isArray(b.items) ? b.items : []).slice(0, 100).entries()) {
          const name = txt(it && it.name, 300), qty = money(it && it.qty), price = money(it && it.price);
          if (!name && qty == null && price == null) continue;
          if (!name) return fail(res, 400, `Строка ${i + 1}: что куплено`);
          if (qty == null || Number.isNaN(qty) || qty <= 0) return fail(res, 400, `Строка ${i + 1}: количество`);
          if (price == null || Number.isNaN(price)) return fail(res, 400, `Строка ${i + 1}: цена`);
          items.push({ name, qty, unit: txt(it.unit, 20), price });
        }
        if (!items.length) return fail(res, 400, 'Укажите, что куплено: наименование, количество и цену');
        const calc = Math.round(items.reduce((a, it) => a + it.qty * it.price, 0) * 100) / 100, sum = money(b.sum);
        if (Number.isNaN(sum)) return fail(res, 400, 'Сумма — число');
        Object.assign(x, { jobId: job ? b.jobId : null, work: job ? '' : work, seller, items, sum: sum == null ? calc : sum });
      }
      C.push(x); saveDb();
      return send(res, 200, { ok: true, check: x, rev: db.rev });
    }
    const x = p[2] && C.find(e => e.id === p[2]);
    if (!x || !(x.by === user.id || HEAD(user))) return fail(res, 404, 'Чек не найден — обновите страницу');
    if (m === 'DELETE') { db.checks = C.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Транспорт» (managers): a vehicle — name, number, VIN, year, mileage, note; its maintenance (date, mileage, what was done)
     and documents (work orders for repairs and so on); spare parts — number, description, link, the vehicle they fit */
  if (p[1] === 'vehicles' || p[1] === 'parts') {
    if (!HEAD(user)) return fail(res, 403, 'Транспорт ведёт руководитель или администратор');
    if (orgType(user) === 'requests') return fail(res, 403, 'Транспорт есть только в системе «Все сервисы»');
    if (!sees(user, p[1] === 'parts' ? 'transport:parts' : 'transport:cars')) return fail(res, 403, 'Этот раздел для вас закрыт');
    if (!db.vehicles || typeof db.vehicles !== 'object') db.vehicles = {};
    if (!Array.isArray(db.parts)) db.parts = [];
    const V = db.vehicles, now = new Date().toISOString(), txt = (v, n) => String(v ?? '').trim().slice(0, n);
    const D = /^\d{4}-\d{2}-\d{2}$/, km = v => v === '' || v == null ? null : Number.isFinite(Number(v)) && Number(v) >= 0 ? Math.round(Number(v)) : NaN;
    const link = v => { const u = txt(v, 1000); return !u || /^https?:\/\/\S+$/i.test(u) ? u : null; };
    const done = (body = { ok: true }) => { saveDb(); return send(res, 200, { ...body, rev: db.rev }); };
    if (p[1] === 'parts') {
      const clean = b => {
        const number = txt(b.number, 100), name = txt(b.name, 1000), l = link(b.link);
        if (!number && !name) return 'Укажите номер или описание запчасти';
        if (l === null) return 'Ссылка должна начинаться с http:// или https://';
        if (b.vehicleId && !V[b.vehicleId]) return 'Транспорт не найден';
        return { number, name, link: l, vehicleId: b.vehicleId || null, note: txt(b.note, 500) };
      };
      if (m === 'POST' && !p[2]) { const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v); const x = { id: newId(), ...v, at: now, by: user.id }; db.parts.push(x); return done({ ok: true, part: x }); }
      const x = p[2] && db.parts.find(e => e.id === p[2]); if (!x) return fail(res, 404, 'Запчасть не найдена — обновите страницу');
      if (m === 'PUT') { const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v); Object.assign(x, v, { updatedAt: now, updatedBy: user.id }); return done({ ok: true, part: x }); }
      if (m === 'DELETE') { db.parts = db.parts.filter(e => e !== x); return done(); }
      return fail(res, 405, 'Метод не поддерживается');
    }
    const cleanV = (b, old = {}) => {
      const name = txt(b.name ?? old.name, 200); if (!name) return 'Укажите транспорт (марка, модель)';
      const mileage = km(b.mileage ?? old.mileage); if (Number.isNaN(mileage)) return 'Пробег — число километров';
      const year = b.year === undefined ? old.year || '' : txt(b.year, 4); if (year && !/^\d{4}$/.test(year)) return 'Год выпуска — четыре цифры';
      const toEvery = km(b.toEvery ?? old.toEvery); if (Number.isNaN(toEvery)) return 'Интервал ТО — число километров';
      return { name, plate: txt(b.plate ?? old.plate, 20).toUpperCase(), vin: txt(b.vin ?? old.vin, 17).toUpperCase(), year, mileage, toEvery, driver: txt(b.driver ?? old.driver, 200), note: txt(b.note ?? old.note, 2000) };
    };
    if (m === 'POST' && !p[2]) { const v = cleanV(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v); const id = newId(); V[id] = { ...v, to: [], docs: [], at: now, by: user.id }; return done({ ok: true, vehicle: { id, ...V[id] } }); }
    const v = p[2] && V[p[2]]; if (!v) return fail(res, 404, 'Транспорт не найден — обновите страницу');
    const out = () => done({ ok: true, vehicle: { id: p[2], ...v } });
    if (m === 'PATCH' && p.length === 3) { const c = cleanV(await readJsonBody(req), v); if (typeof c === 'string') return fail(res, 400, c); Object.assign(v, c, { updatedAt: now, updatedBy: user.id }); return out(); }
    if (m === 'DELETE' && p.length === 3) { delete V[p[2]]; db.parts.forEach(x => { if (x.vehicleId === p[2]) x.vehicleId = null; }); return done(); }
    if (p[3] === 'to') {
      v.to = Array.isArray(v.to) ? v.to : [];
      if (m === 'POST' && !p[4]) {
        const b = await readJsonBody(req), date = String(b.date || ''), mileage = km(b.mileage);
        if (!D.test(date)) return fail(res, 400, 'Укажите дату ТО');
        if (mileage === null || Number.isNaN(mileage)) return fail(res, 400, 'Укажите пробег на ТО');
        v.to.push({ id: newId(), date, mileage, work: txt(b.work, 2000), cost: txt(b.cost, 30), at: now, by: user.id });
        v.to.sort((a, c) => a.date.localeCompare(c.date) || a.mileage - c.mileage);
        if (!(v.mileage >= mileage)) v.mileage = mileage;
        return out();
      }
      if (m === 'DELETE' && p[4]) { v.to = v.to.filter(x => x.id !== p[4]); return out(); }
    }
    if (p[3] === 'docs') {
      v.docs = Array.isArray(v.docs) ? v.docs : [];
      if (m === 'POST' && !p[4]) {
        const b = await readJsonBody(req), f = b.file && db.files[b.file.id];
        if (!f) return fail(res, 400, 'Выберите файл');
        v.docs.push({ id: newId(), title: txt(b.title, 200) || f.name, date: D.test(b.date || '') ? b.date : '', file: { id: b.file.id, name: f.name, type: f.type, size: f.size }, at: now, by: user.id });
        return out();
      }
      if (m === 'DELETE' && p[4]) { v.docs = v.docs.filter(x => x.id !== p[4]); return out(); }
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* the manager marks an employee: sick leave and vacation (a period), late and left early (a day and a time), absence (a day) */
  if (p[1] === 'staff-marks') {
    if (!HEAD(user)) return fail(res, 403, 'Отметки ставит руководитель или администратор');
    if (!Array.isArray(db.staffMarks)) db.staffMarks = [];
    const M = db.staffMarks, D = /^\d{4}-\d{2}-\d{2}$/, T = /^([01]\d|2[0-3]):[0-5]\d$/;
    const clean = b => {
      const type = String(b.type || '');
      if (!STAFF_MARKS.includes(type)) return 'Выберите, что отметить';
      if (!orgUsers().some(u => u.id === b.user && !u.sys)) return 'Сотрудник не найден';
      const from = String(b.from || ''), range = type === 'sick' || type === 'vacation', to = range ? String(b.to || from) : from;
      if (!D.test(from) || Number.isNaN(Date.parse(from))) return 'Укажите дату';
      if (range && (!D.test(to) || to < from)) return 'Дата окончания раньше начала';
      const time = type === 'late' || type === 'early' ? String(b.time || '') : '';
      if ((type === 'late' || type === 'early') && !T.test(time)) return type === 'late' ? 'Укажите, во сколько пришёл' : 'Укажите, во сколько ушёл';
      const tin = type === 'time' ? String(b.tin || '') : '', tout = type === 'time' ? String(b.tout || '') : '';
      if (type === 'time') {
        if (!tin && !tout) return 'Укажите, во сколько пришёл или во сколько ушёл';
        if ((tin && !T.test(tin)) || (tout && !T.test(tout))) return 'Неверное время';
        if (tin && tout && tout <= tin) return 'Время ухода раньше времени прихода';
      }
      return { user: b.user, type, from, to, time, tin, tout, note: String(b.note || '').trim().slice(0, 1000) };
    };
    if (m === 'POST' && !p[2]) {
      const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v);
      const x = { id: newId(), ...v, by: user.id, at: new Date().toISOString() }; M.push(x); saveDb();
      return send(res, 200, { ok: true, mark: x, rev: db.rev });
    }
    const x = p[2] && M.find(e => e.id === p[2]);
    if (!x) return fail(res, 404, 'Отметка не найдена — обновите страницу');
    if (m === 'PUT') { const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v); Object.assign(x, v, { updatedAt: new Date().toISOString(), updatedBy: user.id }); saveDb(); return send(res, 200, { ok: true, mark: x, rev: db.rev }); }
    if (m === 'DELETE') { db.staffMarks = M.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* the working schedule of the organization: the hours of a working day and the exceptions of the calendar */
  if (p[1] === 'workcal' && m === 'PUT') {
    if (!HEAD(user)) return fail(res, 403, 'График меняет руководитель или администратор');
    const b = await readJsonBody(req), T = /^([01]\d|2[0-3]):[0-5]\d$/, D = /^\d{4}-\d{2}-\d{2}$/;
    if (!T.test(b.from || '') || !T.test(b.to || '') || b.to <= b.from) return fail(res, 400, 'Укажите начало и окончание рабочего дня');
    const dates = a => [...new Set((Array.isArray(a) ? a : []).filter(d => D.test(d)))].sort().slice(0, 400);
    const off = dates(b.off), work = dates(b.work).filter(d => !off.includes(d));
    db.workCal = { from: b.from, to: b.to, off, work }; saveDb();
    return send(res, 200, { ok: true, workCal: db.workCal, rev: db.rev });
  }
  /* «Ненормированный рабочий день»: an employee enters the date, the start and the end of his working day and a comment;
     the manager sees the entries in «Сотрудники». The end before the start means the day went past midnight. */
  if (p[1] === 'overtime') {
    if (user.sys) return fail(res, 403, 'Недоступно');
    if (!Array.isArray(db.overtime)) db.overtime = [];
    const O = db.overtime, T = /^([01]\d|2[0-3]):[0-5]\d$/;
    const clean = b => {
      const date = String(b.date || ''), from = String(b.from || ''), to = String(b.to || ''), note = String(b.note || '').trim().slice(0, 1000);
      if (!/^\d{4}-\d{2}-\d{2}$/.test(date) || Number.isNaN(Date.parse(date))) return 'Укажите дату';
      if (date > localDate(new Date(Date.now() + 864e5))) return 'Дата не может быть в будущем';
      if (!T.test(from)) return 'Укажите время начала';
      if (!T.test(to)) return 'Укажите время окончания';
      if (from === to) return 'Время начала и окончания совпадают';
      return { date, from, to, note };
    };
    if (m === 'POST' && !p[2]) {
      const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v);
      const x = { id: newId(), by: user.id, ...v, at: new Date().toISOString() };
      O.push(x); saveDb();
      return send(res, 200, { ok: true, entry: x, rev: db.rev });
    }
    const x = p[2] && O.find(e => e.id === p[2]);
    if (!x || !(x.by === user.id || HEAD(user))) return fail(res, 404, 'Запись не найдена — обновите страницу');
    if (m === 'PUT') {
      // the employee himself or a manager (the manager corrects what was entered)
      if (x.by !== user.id && !HEAD(user)) return fail(res, 403, 'Изменить запись может сотрудник или руководитель');
      const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v);
      Object.assign(x, v, { updatedAt: new Date().toISOString(), ...(x.by !== user.id ? { updatedBy: user.id } : {}) }); saveDb();
      return send(res, 200, { ok: true, entry: x, rev: db.rev });
    }
    if (m === 'DELETE') { db.overtime = O.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Инструкции» of a requests organization: everyone reads, the administrator adds and removes */
  if (p[1] === 'req-docs') {
    if (orgType(user) !== 'requests') return fail(res, 403, 'Инструкции есть только в системе «Управление заявками»');
    if (user.role !== 'admin') return fail(res, 403, 'Инструкции добавляет администратор');
    if (!Array.isArray(db.reqDocs)) db.reqDocs = [];
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req), title = String(b.title || '').trim().slice(0, 200), f = b.file && db.files[b.file.id];
      if (!title) return fail(res, 400, 'Напишите название');
      if (!f) return fail(res, 400, 'Выберите файл');
      const d = { id: newId(), title, file: { id: b.file.id, name: f.name, type: f.type, size: f.size }, at: new Date().toISOString(), by: user.id };
      db.reqDocs.push(d); saveDb();
      return send(res, 200, { ok: true, doc: d, rev: db.rev });
    }
    if (m === 'DELETE' && p[2]) { db.reqDocs = db.reqDocs.filter(d => d.id !== p[2]); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* settings of a requests organization (the administrator): the contract for the reports, the time zone, Telegram, the key of the devices */
  if (p[1] === 'req-cfg') {
    if (orgType(user) !== 'requests' || user.role !== 'admin') return fail(res, 403, 'Настройки меняет администратор');
    if (m === 'GET') return send(res, 200, reqCfgOf());
    if (m === 'PUT') {
      const b = await readJsonBody(req), c = reqCfgOf(), money = v => /^\d{1,9}([.,]\d{1,2})?$/.test(String(v ?? '').trim()) ? String(v).trim().replace(',', '.') : null;
      if (b.contract) {
        const k = b.contract, prices = {};
        for (const s of UPR_SYS) { const v = money(k.prices && k.prices[s]); if (v === null) return fail(res, 400, 'Цена за день: число, например 365.28'); prices[s] = v; }
        if (!/^\d{4}-\d{2}-\d{2}$/.test(k.date || '')) return fail(res, 400, 'Укажите дату контракта');
        const vat = Number(k.vat); if (!(vat >= 0 && vat <= 100)) return fail(res, 400, 'Ставка НДС от 0 до 100');
        const prev = k.prevTotal === '' || k.prevTotal == null ? '' : money(k.prevTotal); if (prev === null) return fail(res, 400, 'Оказано до периода: число или пусто');
        c.contract = { no: String(k.no || '').trim().slice(0, 60), date: k.date, prices, vat, prevTotal: prev };
      }
      if (b.tz !== undefined) { try { new Intl.DateTimeFormat('ru', { timeZone: String(b.tz) }); c.tz = String(b.tz); } catch { return fail(res, 400, 'Неизвестный часовой пояс'); } }
      if (b.tg) c.tg = { token: b.tg.token === undefined ? (c.tg.token || '') : String(b.tg.token).trim().slice(0, 100), chat: String(b.tg.chat || '').trim().slice(0, 40), prefix: String(b.tg.prefix || '').trim().slice(0, 60) };
      if (b.newDevToken) c.devToken = require('node:crypto').randomBytes(18).toString('base64url');
      db.reqCfg = c; saveDb();
      return send(res, 200, { ok: true, cfg: c, rev: db.rev });
    }
    if (m === 'POST' && p[2] === 'tg-test') { if (!reqCfgOf().tg.token || !reqCfgOf().tg.chat) return fail(res, 400, 'Укажите токен бота и чат'); reqNotify('Проверка уведомлений: связь с системой заявок работает.'); return send(res, 200, { ok: true }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Отчётная документация»: 7 Word documents for a month — the requests created in the month and the replaced equipment */
  if (p[1] === 'req-report' && m === 'POST') {
    if (orgType(user) !== 'requests' || user.role !== 'admin') return fail(res, 403, 'Отчёты формирует администратор');
    const b = await readJsonBody(req), c = reqCfgOf(), tz = c.tz;
    if (!/^\d{4}-(0[1-9]|1[0-2])$/.test(b.period || '')) return fail(res, 400, 'Выберите отчётный месяц');
    if (!/^\d{4}-\d{2}-\d{2}$/.test(b.docDate || '') || Number.isNaN(Date.parse(b.docDate))) return fail(res, 400, 'Укажите дату документов');
    const [y, mo] = b.period.split('-').map(Number), skipped = [];
    const tickets = [], repl = [];
    for (const r of Object.values(db.requests || {})) {
      if (r.status === 'cancel') continue;
      if (!UPR_SYS.includes(r.system)) { skipped.push(r.no); continue; }
      const closed = ['done', 'reject'].includes(r.status) && r.doneAt ? UPR.localStamp(r.doneAt, tz) : null;
      const eq = (r.repl || []).map(x => x.equipment);
      tickets.push({ number: r.no, system: r.system, description: (r.text || r.title || '').trim(), created: UPR.localStamp(r.at, tz), closed, answer: r.doneNote || '', equipment: eq.join('; '), overdue: !!(r.due && (closed ? closed.slice(0, 10) : UPR.localStamp(new Date().toISOString(), tz).slice(0, 10)) > r.due) });
      for (const x of r.repl || []) repl.push({ date: closed ? closed.slice(0, 10) : UPR.localStamp(r.doneAt || r.at, tz).slice(0, 10), system: r.system, category: x.category, equipment: x.equipment, ticket: r.no, newSerial: x.newSerial, oldSerial: x.oldSerial });
    }
    let out;
    try {
      out = UPR.generate({ year: y, month: mo, docDate: b.docDate, contractNo: c.contract.no, contractDate: c.contract.date, prices: c.contract.prices, vat: c.contract.vat,
        prevTotal: c.contract.prevTotal, penalty: '0', letterNo: String(b.letterNo || '').trim().slice(0, 40) || '___/' + String(y).slice(2) }, tickets, repl);
    } catch (e) { console.error('Отчёт:', e); return fail(res, 500, 'Не удалось сформировать документы: ' + e.message); }
    const inPeriod = skipped.filter(no => { const r = Object.values(db.requests).find(x => x.no === no); return r && UPR.localStamp(r.at, tz).slice(0, 7) === b.period; });
    if (inPeriod.length) out.warnings.unshift(`Без системы, не вошли в отчёт: заявки № ${inPeriod.join(', ')}`);
    const name = `Отчетная документация ${b.period}.zip`, key = require('node:crypto').randomBytes(12).toString('base64url');
    // the archive waits 15 minutes for its download by a plain link (the browser keeps the file name)
    const now = Date.now(); for (const [k, v] of REPORTS) if (v.until < now) REPORTS.delete(k);
    REPORTS.set(key, { buf: out.zip, name, user: user.id, until: now + 15 * 60e3 });
    return send(res, 200, { ok: true, url: `/api/req-report/${key}`, name, warnings: out.warnings, totals: out.totals, files: out.files.map(f => f.name) });
  }
  if (p[1] === 'req-report' && m === 'GET' && p[2]) {
    const x = REPORTS.get(p[2]);
    if (!x || x.user !== user.id || x.until < Date.now()) return fail(res, 404, 'Документы устарели — сформируйте заново');
    return send(res, 200, x.buf, { 'Content-Type': 'application/zip', 'Content-Disposition': `attachment; filename="report.zip"; filename*=UTF-8''${encodeURIComponent(x.name)}` });
  }
  /* «Мои задачи»: a personal to-do list — each administrator sees and changes only his own notes */
  /* «Мои задачи»: personal tasks («task»), notes with drawings and pictures («memo») and shared tasks («shared»):
     a shared task is seen by the users chosen by its author; they can write comments */
  if (p[1] === 'notes') {
    if (!Array.isArray(db.notes)) db.notes = [];
    const N = db.notes;
    // a shared task is seen by its author, the chosen users and its executor; an employee (field staff) sees only the tasks assigned to him
    const sees = n => FIELD(user) ? n.type === 'shared' && n.assignee === user.id : n.by === user.id || (n.type === 'shared' && ((n.share || []).includes(user.id) || n.assignee === user.id));
    const okAssignee = id => !!id && orgUsers().some(u => u.id === id && !u.sys && !u.blocked);
    const dueOk = v => /^\d{4}-\d{2}-\d{2}$/.test(v || '') ? v : '';
    const cleanFiles = a => (Array.isArray(a) ? a : []).filter(f => f && db.files[f.id]).slice(0, 30).map(f => ({ id: f.id, name: String(f.name || db.files[f.id].name).slice(0, 200), type: db.files[f.id].type, at: db.files[f.id].at }));
    const cleanShare = a => [...new Set((Array.isArray(a) ? a : []).filter(id => id !== user.id && orgUsers().some(u => u.id === id && !FIELD(u) && !u.sys)))].slice(0, 50);
    if (m === 'GET' && !p[2]) return send(res, 200, N.filter(sees));
    if (m === 'POST' && !p[2]) {
      if (FIELD(user)) return fail(res, 403, 'Создавать задачи сотрудник не может');
      const b = await readJsonBody(req), text = String(b.text || '').trim().slice(0, 4000), type = ['task', 'memo', 'shared'].includes(b.type) ? b.type : 'task';
      if (!text && !(b.files || []).length) return fail(res, 400, 'Напишите текст');
      if (b.assignee && !okAssignee(b.assignee)) return fail(res, 400, 'Исполнитель не найден');
      if (type === 'shared' && !cleanShare(b.share).length && !b.assignee) return fail(res, 400, 'Выберите исполнителя или тех, кто увидит общую задачу');
      const n = { id: newId(), type, text, done: false, urgent: !!b.urgent, at: new Date().toISOString(), by: user.id, files: cleanFiles(b.files) };
      if (type === 'shared') { n.share = cleanShare(b.share); n.comments = []; n.assignee = b.assignee || null; n.due = dueOk(b.due); }
      if (n.urgent) n.urgentAt = n.at;
      N.unshift(n); saveDb();
      return send(res, 200, { ok: true, note: n, rev: db.rev });
    }
    const n = p[2] && N.find(x => x.id === p[2] && sees(x));
    if (!n) return fail(res, 404, 'Задача не найдена — обновите страницу');
    const own = n.by === user.id;
    // comments on a shared task: everyone who sees it
    if (p[3] === 'comments') {
      n.comments = Array.isArray(n.comments) ? n.comments : [];
      if (m === 'POST') { const b = await readJsonBody(req), t = String(b.text || '').trim().slice(0, 2000); if (!t) return fail(res, 400, 'Пустой комментарий');
        const c = { id: newId(), by: user.id, at: new Date().toISOString(), text: t }; n.comments.push(c); saveDb(); return send(res, 200, { ok: true, note: n, rev: db.rev }); }
      if (m === 'DELETE' && p[4]) { const c = n.comments.find(x => x.id === p[4]); if (!c) return fail(res, 404, 'Комментарий не найден'); if (c.by !== user.id && !own) return fail(res, 403, 'Удалить можно только свой комментарий');
        n.comments = n.comments.filter(x => x !== c); saveDb(); return send(res, 200, { ok: true, note: n, rev: db.rev }); }
      return fail(res, 405, 'Метод не поддерживается');
    }
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      // participants of a shared task may tick it done; everything else is for its author
      if (!own && Object.keys(b).some(k => k !== 'done')) return fail(res, 403, 'Изменить общую задачу может её автор');
      if (b.text !== undefined) { const t = String(b.text).trim().slice(0, 4000); if (!t && !(n.files || []).length) return fail(res, 400, 'Напишите текст'); n.text = t; n.editedAt = new Date().toISOString(); }
      // urgent: the task goes to the top of the list and is shown in red
      if (b.urgent !== undefined) { n.urgent = !!b.urgent; n.urgentAt = n.urgent ? new Date().toISOString() : null; }
      if (b.files !== undefined) n.files = cleanFiles(b.files);
      if (b.assignee !== undefined && n.type === 'shared') { if (b.assignee && !okAssignee(b.assignee)) return fail(res, 400, 'Исполнитель не найден'); n.assignee = b.assignee || null; }
      if (b.due !== undefined && n.type === 'shared') n.due = dueOk(b.due);
      if (b.share !== undefined && n.type === 'shared') { const sh = cleanShare(b.share); if (!sh.length && !n.assignee) return fail(res, 400, 'Выберите исполнителя или тех, кто увидит общую задачу'); n.share = sh; }
      if (b.done !== undefined) { n.done = !!b.done; n.doneAt = n.done ? new Date().toISOString() : null; n.doneBy = n.done ? user.id : null; }
      saveDb();
      return send(res, 200, { ok: true, note: n, rev: db.rev });
    }
    if (m === 'DELETE') { if (!own) return fail(res, 403, 'Удалить общую задачу может её автор'); N.splice(N.indexOf(n), 1); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
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
  /* «Карта объектов»: objects with coordinates from a spreadsheet; which of them stand on the MKAD, the TTK or an overpass
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
      if (!canEdit(user)) return fail(res, 403, 'Отмечать проверку может администратор');
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
      if (!canEdit(user)) return fail(res, 403, 'Назначать исполнителя может администратор');
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
      // the same points already written into works get the same executor
      let inJobs = 0;
      for (const j of Object.values(db.jobs)) for (const pl of j.places || []) if (pl.dtNo && nos.has(pl.dtNo)) {
        if (who) { pl.assignee = who.id; if (!(j.workers || []).includes(who.id) && FIELD(who)) j.workers = [...(j.workers || []), who.id]; } else delete pl.assignee;
        inJobs++;
      }
      saveDb();
      return send(res, 200, { ok: true, count: n, inJobs, rev: db.rev });
    }
    /* own marks: a name and a colour; deleting one removes it from the points */
    if (p[2] === 'needs') {
      if (!canEdit(user)) return fail(res, 403, 'Создавать пометки может администратор или руководитель');
      db.meta.dtNeeds = Array.isArray(db.meta.dtNeeds) ? db.meta.dtNeeds : [];
      if (m === 'POST' && !p[3]) {
        const b = await readJsonBody(req), name = String(b.name || '').trim().slice(0, 60), color = HEX(b.color);
        if (!name) return fail(res, 400, 'Укажите название пометки');
        if (!color) return fail(res, 400, 'Выберите цвет');
        if (db.meta.dtNeeds.some(x => x.name.toLowerCase() === name.toLowerCase())) return fail(res, 409, 'Такая пометка уже есть');
        const n = { id: 'c_' + newId().replace(/[^A-Za-z0-9]/g, '').slice(0, 10), name, color, at: new Date().toISOString(), by: user.id };
        db.meta.dtNeeds.push(n); saveDb();
        return send(res, 200, { ok: true, need: n, rev: db.rev });
      }
      const n = p[3] && db.meta.dtNeeds.find(x => x.id === p[3]);
      if (!n) return fail(res, 404, 'Пометка не найдена');
      if (m === 'PATCH') {
        const b = await readJsonBody(req);
        if (b.name !== undefined) { const nm = String(b.name).trim().slice(0, 60); if (!nm) return fail(res, 400, 'Укажите название пометки'); n.name = nm; }
        if (b.color !== undefined) { const c = HEX(b.color); if (!c) return fail(res, 400, 'Выберите цвет'); n.color = c; }
        saveDb(); return send(res, 200, { ok: true, need: n, rev: db.rev });
      }
      if (m === 'DELETE') {
        db.meta.dtNeeds = db.meta.dtNeeds.filter(x => x.id !== n.id); let k = 0;
        for (const x of (db.dt && db.dt.points) || []) if (x.need === n.id) { delete x.need; delete x.needAt; delete x.needBy; k++; }
        for (const j of Object.values(db.jobs)) for (const pl of j.places || []) if (pl.need === n.id) delete pl.need;
        saveDb(); return send(res, 200, { ok: true, cleared: k, rev: db.rev });
      }
      return fail(res, 405, 'Метод не поддерживается');
    }
    /* a mark about what the work at a point needs: special vehicles or own fencing; goes to the same points in works */
    if (m === 'PATCH' && p[2] === 'need') {
      if (!canEdit(user)) return fail(res, 403, 'Ставить пометки может администратор или руководитель');
      const b = await readJsonBody(req), P = db.dt && db.dt.points;
      if (!P) return fail(res, 409, 'Точек нет');
      const need = String(b.need || '');
      if (need && !isNeed(need)) return fail(res, 400, 'Неизвестная пометка');
      const nos = new Set((Array.isArray(b.nos) ? b.nos : []).map(String));
      if (!nos.size) return fail(res, 400, 'Не выбрано ни одной точки');
      const at = new Date().toISOString(); let n = 0;
      for (const x of P) if (nos.has(x.no)) { if (need) Object.assign(x, { need, needAt: at, needBy: user.id }); else { delete x.need; delete x.needAt; delete x.needBy; } n++; }
      for (const j of Object.values(db.jobs)) for (const pl of j.places || []) if (pl.dtNo && nos.has(pl.dtNo)) { if (need) pl.need = need; else delete pl.need; }
      saveDb();
      return send(res, 200, { ok: true, count: n, rev: db.rev });
    }
    /* a point added by hand on the map, and removing a point */
    if (m === 'POST' && p[2] === 'point') {
      if (!canEdit(user)) return fail(res, 403, 'Добавлять точки может администратор');
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
    /* several points at once (the selection) */
    if (m === 'POST' && p[2] === 'delete') {
      if (!canEdit(user)) return fail(res, 403, 'Удалять точки может администратор или руководитель');
      const b = await readJsonBody(req), nos = new Set((Array.isArray(b.nos) ? b.nos : []).map(String));
      if (!db.dt || !nos.size) return fail(res, 400, 'Не выбрано ни одной точки');
      const n0 = db.dt.points.length; db.dt.points = db.dt.points.filter(x => !nos.has(x.no)); saveDb();
      return send(res, 200, { ok: true, count: n0 - db.dt.points.length, rev: db.rev });
    }
    /* «Сбросить карту»: every point leaves the map; the works keep theirs */
    if (m === 'POST' && p[2] === 'reset') {
      if (!canEdit(user)) return fail(res, 403, 'Сбросить карту может администратор или руководитель');
      const n = db.dt ? db.dt.points.length : 0;
      db.dt = { points: [], file: '', at: new Date().toISOString(), by: user.id, classifiedAt: null, radius: null, source: '', resetAt: new Date().toISOString(), resetBy: user.id, resetCount: n };
      saveDb();
      return send(res, 200, { ok: true, count: n, rev: db.rev });
    }
    /* the points of a work back on the map (after a reset): object number, place, marks, executor */
    if (m === 'POST' && p[2] === 'restore') {
      if (!canEdit(user)) return fail(res, 403, 'Недостаточно прав');
      const b = await readJsonBody(req), j = db.jobs[String(b.jobId || '')];
      if (!j) return fail(res, 404, 'Работа не найдена');
      if (!db.dt) db.dt = { points: [], file: '', at: new Date().toISOString(), by: user.id, classifiedAt: null, radius: null, source: '' };
      const have = new Set(db.dt.points.map(x => x.no)); let n = 0;
      for (const pl of j.places || []) {
        if (!pl.dtNo || have.has(pl.dtNo)) continue;
        db.dt.points.push({ no: pl.dtNo, lat: pl.lat, lng: pl.lng, cats: (pl.cats || []).slice(), road: pl.road || '', bridge: '', dist: null,
          ...(pl.assignee ? { assignee: pl.assignee } : {}), ...(isNeed(pl.need) ? { need: pl.need } : {}), restoredFrom: j.id });
        have.add(pl.dtNo); n++;
      }
      saveDb();
      return send(res, 200, { ok: true, count: n, rev: db.rev });
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
    if (user.role !== 'admin') return fail(res, 403, 'Загружать выгрузку из 1С может только администратор');
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

  /* «Администрирование» → «Начальные остатки»: a table from 1C; the quantity becomes both the actual and the accounting balance */
  if (p[1] === 'stock-initial' && m === 'POST') {
    if (user.role !== 'admin') return fail(res, 403, 'Загружать начальные остатки может только администратор');
    const b = await readJsonBody(req);
    const rows = Array.isArray(b.rows) ? b.rows.slice(0, 20000) : [];
    const agg = new Map();
    for (const r of rows) {
      const name = String(r.name || '').trim(), sku = String(r.sku || '').trim(), qty = Number(r.qty);
      if (!name || !Number.isFinite(qty) || qty < 0) continue;
      const key = sku ? 'a:' + normName(sku) : 'n:' + normName(name);
      const cur = agg.get(key) || { name, sku, unit: String(r.unit || '').trim(), qty: 0 };
      cur.qty = r3(cur.qty + qty); agg.set(key, cur);
    }
    if (!agg.size) return fail(res, 400, 'В файле не найдено строк с наименованием и количеством');
    const items = Object.entries(db.stock);
    const bySku = new Map(items.filter(([, it]) => it.sku).map(([id, it]) => [normName(it.sku), id]));
    const byName = new Map(items.map(([id, it]) => [normName(it.name), id]));
    const now = new Date().toISOString(), file = String(b.file || '').slice(0, 200), seen = new Set();
    let matched = 0, created = 0;
    for (const r of agg.values()) {
      let id = (r.sku && bySku.get(normName(r.sku))) || byName.get(normName(r.name));
      if (!id) { id = newId(); created++; db.stock[id] = { name: r.name, sku: r.sku, unit: r.unit || 'шт', location: '', minQty: 0, note: 'Добавлено из начальных остатков 1С', qty: 0, moves: [], acctQty: 0, createdAt: now, createdBy: user.id }; }
      else if (!seen.has(id)) matched++;
      const it = db.stock[id], q = seen.has(id) ? r3((Number(it.qty) || 0) + r.qty) : r.qty;
      it.qty = q; it.acctQty = q; seen.add(id);
      it.moves = Array.isArray(it.moves) ? it.moves : [];
      it.moves.push({ id: newId(), type: 'init', qty: r.qty, acct: true, acctBalance: q, balance: q, note: 'Начальный остаток из 1С' + (file ? ' (' + file + ')' : ''), by: user.id, at: now });
      it.updatedAt = now; it.updatedBy = user.id;
    }
    db.meta.initial = { at: now, by: user.id, file, rows: agg.size, matched, created };
    saveDb();
    return send(res, 200, db.meta.initial);
  }
  /* «Администрирование» → «Файлы»: every uploaded file of the organization and where it is used; unused files may be deleted */
  if (p[1] === 'admin-files') {
    if (user.role !== 'admin') return fail(res, 403, 'Файлами управляет только администратор');
    const used = fileUsage();
    if (m === 'GET' && p.length === 2) {
      const list = Object.entries(db.files).map(([id, f]) => ({ id, name: f.name, type: f.type, size: f.size || 0, at: f.at || null, by: f.by || null, used: used.get(id) || [] }))
        .sort((a, b) => String(b.at || '').localeCompare(String(a.at || '')));
      return send(res, 200, list);
    }
    // the server checks again that a file is used nowhere; «all unused» leaves files younger than a day (they may be in a form not saved yet)
    const drop = id => { delete db.files[id]; try { fs.unlinkSync(path.join(filesDir(), id)); } catch {} };
    if (m === 'DELETE' && p[2] && p.length === 3) {
      if (!db.files[p[2]]) return fail(res, 404, 'Файл не найден — обновите список');
      if (used.has(p[2])) return fail(res, 409, 'Файл используется: ' + used.get(p[2]).join(', ') + '. Удалить можно только неиспользуемый файл');
      const size = db.files[p[2]].size || 0; drop(p[2]); saveDb();
      return send(res, 200, { ok: true, deleted: 1, size, rev: db.rev });
    }
    if (m === 'POST' && p[2] === 'delete-unused') {
      const day = Date.now() - 864e5; let n = 0, size = 0, young = 0;
      for (const [id, f] of Object.entries(db.files)) { if (used.has(id)) continue; if (f.at && Date.parse(f.at) > day) { young++; continue; } size += f.size || 0; drop(id); n++; }
      if (n) saveDb();
      return send(res, 200, { ok: true, deleted: n, size, young, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* saving the write-off list: only when every line is covered by the accounting balances */
  if ((p[1] === 'orders' || p[1] === 'jobs') && p[3] === 'writeoff' && m === 'POST') {
    if (!canEdit(user)) return fail(res, 403, 'Сохранить список для списания может администратор или руководитель');
    const o = woDoc(p[1], p[2]); if (!o) return fail(res, 404, p[1] === 'jobs' ? 'Работа не найдена' : 'Заказ не найден');
    const b = await readJsonBody(req), map = {};
    for (const [k, v] of Object.entries(b.map || {})) if (/^(id|n):/.test(k) && db.stock[v]) map[k] = v;
    const lines = writeoffLines(o, map);
    if (!lines.length) return fail(res, 400, p[1] === 'jobs' ? 'В работе нет материалов' : 'В изделиях заказа нет компонентов');
    const bad = lines.filter(L => L.source !== 'acct');
    if (bad.length) return fail(res, 409, 'Не хватает в бухгалтерских остатках: ' + bad.slice(0, 5).map(L => L.name).join(', ') + (bad.length > 5 ? ` и ещё ${bad.length - 5}` : '') + '. Замените номенклатуру или обновите остатки');
    const target = p[1] === 'jobs' ? db.jobs[p[2]] : o, at = new Date().toISOString(), prev = woTaken(target), next = {};
    lines.forEach(L => { next[L.stockId] = r3((next[L.stockId] || 0) + L.need); });
    const what = p[1] === 'jobs' ? `работе № ${target.no || ''} · ${target.title || ''}` : `заказу ${o.number || ''} · ${o.title || ''}`;
    for (const sid of new Set([...Object.keys(prev), ...Object.keys(next)])) {
      const it = db.stock[sid], d = r3((next[sid] || 0) - (prev[sid] || 0)); if (!it || !d) continue;
      it.acctQty = r3((Number(it.acctQty) || 0) - d);
      it.moves = Array.isArray(it.moves) ? it.moves : [];
      it.moves.push({ id: newId(), type: 'wo', qty: d, acct: true, acctBalance: it.acctQty, balance: Number(it.qty) || 0, orderId: p[1] === 'orders' ? p[2] : (target.orderId || null), note: (prev[sid] ? 'Изменён список для списания по ' : 'Списание по ') + what, by: user.id, at });
      it.updatedAt = at; it.updatedBy = user.id;
    }
    target.woMap = map;
    target.writeoff = { at, by: user.id, applied: true, lines: lines.map(L => ({ stockId: L.stockId, name: L.name, sku: L.sku, unit: L.unit, qty: L.need })) };
    saveDb();
    return send(res, 200, { ok: true, writeoff: target.writeoff, rev: db.rev });
  }
  /* write-off list for an order: Excel with highlighting */
  if ((p[1] === 'orders' || p[1] === 'jobs') && p[3] === 'writeoff.xlsx' && m === 'GET') {
    const o = woDoc(p[1], p[2]);
    if (!o) return fail(res, 404, 'Не найдено');
    const buf = writeoffXlsx(o);
    const name = `Списание ${o.number || ''} ${o.title || ''}`.replace(/[\\/:*?"<>|]+/g, ' ').trim().slice(0, 90) + '.xlsx';
    res.writeHead(200, { ...SEC_HEADERS, 'Content-Type': 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
      'Content-Disposition': `attachment; filename="writeoff.xlsx"; filename*=UTF-8''${encodeURIComponent(name)}`, 'Content-Length': buf.length, 'Cache-Control': 'no-store' });
    return res.end(buf);
  }

  if (p[1] === 'invoices-zip' && m === 'GET') {
    if (!canPay(user) && !canEdit(user)) return fail(res, 403, 'Скачивать архив счетов может бухгалтер, руководитель или администратор');
    return sendInvoicesZip(res, user, url.searchParams.get('order') || '');
  }

  if (p[1] === 'files' && m === 'POST') {
    // every user of an organization uploads files: photos of points, receipts («Загрузить чек»), documents
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
    // a receipt goes to the accounting balance too; an issue («Расход») changes only the actual one
    if (b.type === 'in') it.acctQty = r3((Number(it.acctQty) || 0) + qty);
    it.moves = Array.isArray(it.moves) ? it.moves : [];
    const mv = { id: newId(), type: b.type, ...(b.type === 'in' ? { acct: true, acctBalance: it.acctQty } : {}), qty, orderId: b.orderId || null, note: String(b.note || '').slice(0, 500), by: user.id, at: new Date().toISOString(), balance: it.qty };
    it.moves.push(mv);
    it.updatedAt = mv.at; it.updatedBy = user.id;
    saveDb();
    return send(res, 200, { ok: true, qty: it.qty, move: mv });
  }

  /* receipt to the warehouse: made on the basis of an uploaded waybill (накладная) — from an invoice («Приход по счёту»)
     or on its own («Приход по накладной»); posted with its own button, cancelled by a manager or admin */
  /* a receipt as an Excel file for 1C: «Поступление (акты, накладные, УПД)» → «Товары» → «Загрузить» → «Из файла» */
  if (m === 'GET' && ((p[1] === 'invoices' && p[3] === 'income.xlsx') || (p[1] === 'receipts' && p[3] === 'receipt.xlsx')) && p.length === 4) {
    if (FIELD(user)) return fail(res, 403, 'Недостаточно прав');
    let doc;
    if (p[1] === 'invoices') {
      const inv = db.invoices[p[2]]; if (!inv) return fail(res, 404, 'Счёт не найден');
      const wb = inv.income && inv.income.waybill;
      doc = { lines: inv.income ? inv.income.lines : inv.items || [], number: wb ? wb.number : inv.number, date: wb ? wb.date : inv.date, kind: wb ? 'Накладная' : 'Счёт' + (inv.income && inv.income.edo ? ' (документы в ЭДО)' : ''),
        supplier: (wb && wb.supplier) || inv.supplier, inn: (wb && wb.inn) || inv.supplierInn || '', invoice: `№ ${inv.number || '—'}${inv.date ? ' от ' + ruDate(inv.date) : ''}`, orderId: inv.orderId, income: inv.income };
    } else {
      const r = (db.receipts || {})[p[2]]; if (!r) return fail(res, 404, 'Приход не найден');
      doc = { lines: r.lines, number: r.number, date: r.date, kind: 'Накладная', supplier: r.supplier, inn: r.inn || '', invoice: '', orderId: r.orderId, income: r };
    }
    const buf = receiptXlsx(doc);
    const name = `Поступление ${doc.number || ''} ${doc.date ? ruDate(doc.date) : ''} ${doc.supplier || ''}`.replace(/[\\/:*?"<>|]+/g, ' ').replace(/\s+/g, ' ').trim().slice(0, 100) + '.xlsx';
    res.writeHead(200, { ...SEC_HEADERS, 'Content-Type': 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
      'Content-Disposition': `attachment; filename="receipt.xlsx"; filename*=UTF-8''${encodeURIComponent(name)}`, 'Content-Length': buf.length, 'Cache-Control': 'no-store' });
    return res.end(buf);
  }
  if (p[1] === 'invoices' && p[3] === 'income' && p.length === 4) {
    const inv = db.invoices[p[2]];
    if (!inv) return fail(res, 404, 'Счёт не найден');
    if (m === 'POST') {
      if (!canMoveStock(user)) return fail(res, 403, 'Недостаточно прав');
      if (inv.income) return fail(res, 409, 'Приход по этому счёту уже оприходован');
      // the basis: an uploaded waybill, or the invoice itself when the documents come through ЭДО
      const b = await readJsonBody(req), edo = !!b.edo, wb = edo ? null : cleanWaybill(b.waybill);
      if (!wb && !edo) return fail(res, 400, 'Загрузите накладную или отметьте «Документы в ЭДО» — тогда приход делается на основании счёта');
      const lines = cleanItems(b.lines).filter(x => x.qty > 0);
      if (!lines.length) return fail(res, 400, 'Нет строк с количеством');
      const label = edo ? `счёту № ${inv.number || '—'}${inv.date ? ' от ' + inv.date.split('-').reverse().join('.') : ''}${inv.supplier ? ', ' + inv.supplier : ''} (документы в ЭДО)` : waybillLabel(wb, inv.supplier) + ` (счёт № ${inv.number || '—'})`;
      const r = postIncome(lines, label, { orderId: inv.orderId || null, invoiceId: p[2] }, user);
      inv.items = r.out.map(({ moveId, ...x }) => x);
      inv.income = { at: r.at, by: user.id, lines: r.out, ...(edo ? { edo: true } : { waybill: wb }) };
      fillOrderSuppliers(inv);
      saveDb();
      return send(res, 200, { ok: true, lines: r.out.length, created: r.created, rev: db.rev });
    }
    if (m === 'DELETE') {
      if (!canEdit(user)) return fail(res, 403, 'Отменить приход может менеджер или администратор');
      if (!inv.income) return fail(res, 409, 'Приход не оприходован');
      const err = rollbackIncome(inv.income.lines, user); if (err) return fail(res, 409, err);
      delete inv.income; inv.updatedAt = new Date().toISOString(); inv.updatedBy = user.id;
      saveDb();
      return send(res, 200, { ok: true, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'receipts') {
    if (!db.receipts || typeof db.receipts !== 'object') db.receipts = {};
    if (m === 'POST' && !p[2]) {
      if (!canMoveStock(user)) return fail(res, 403, 'Недостаточно прав');
      const b = await readJsonBody(req), wb = cleanWaybill(b.waybill);
      if (!wb) return fail(res, 400, 'Загрузите накладную — приход делается на её основании');
      if (!wb.number) return fail(res, 400, 'Укажите номер накладной');
      const lines = cleanItems(b.lines).filter(x => x.qty > 0);
      if (!lines.length) return fail(res, 400, 'Нет строк с количеством');
      const orderId = b.orderId && db.orders[b.orderId] ? b.orderId : null, id = newId();
      const r = postIncome(lines, waybillLabel(wb), { orderId, receiptId: id }, user);
      db.receipts[id] = { ...wb, orderId, lines: r.out, at: r.at, by: user.id };
      if (wb.supplier) { const sup = ensureSupplier(wb.supplier, wb.inn, user, `Добавлен по накладной № ${wb.number || '—'}`); if (sup.id) db.receipts[id].supplierId = sup.id; }
      saveDb();
      return send(res, 200, { ok: true, id, lines: r.out.length, created: r.created, rev: db.rev });
    }
    const rc = p[2] && db.receipts[p[2]];
    if (!rc) return fail(res, 404, 'Приход не найден');
    if (m === 'DELETE') {
      if (!canEdit(user)) return fail(res, 403, 'Отменить приход может менеджер или администратор');
      const err = rollbackIncome(rc.lines, user); if (err) return fail(res, 409, err);
      delete db.receipts[p[2]];
      saveDb();
      return send(res, 200, { ok: true, rev: db.rev });
    }
    return fail(res, 405, 'Метод не поддерживается');
  }

  /* a worker's report at a point of a job: the photos the job asks for, extra photos and a comment */
  /* lists of a work: «Что нужно сделать» (todo) and «Что нужно купить» (buy, with links and pictures);
     each item is changed on its own, so two people adding to a list do not overwrite each other */
  if (p[1] === 'jobs' && p[3] === 'list' && ['todo', 'buy'].includes(p[4])) {
    const j = db.jobs[p[2]]; if (!j) return fail(res, 404, 'Работа не найдена');
    if (!(mayEditJob(user, j) || onJob(user, j))) return fail(res, 403, 'Список работы меняют руководитель, администратор и участники работы');
    const k = p[4], now = new Date().toISOString(), L = j[k] = Array.isArray(j[k]) ? j[k] : [];
    const links = a => (Array.isArray(a) ? a : []).slice(0, 20).map(l => ({ url: String(l && l.url || '').trim().slice(0, 1000), title: String(l && l.title || '').trim().slice(0, 200) }))
      .filter(l => /^https?:\/\/\S+$/i.test(l.url)).map(l => ({ ...l, title: l.title || l.url }));
    const files = a => (Array.isArray(a) ? a : []).filter(f => f && db.files[f.id]).slice(0, 20).map(f => ({ id: f.id, name: String(f.name || db.files[f.id].name).slice(0, 200), type: db.files[f.id].type }));
    const out = () => { j.updatedAt = now; j.updatedBy = user.id; saveDb(); return send(res, 200, { ok: true, list: L, rev: db.rev }); };
    if (m === 'POST' && p.length === 5) {
      const b = await readJsonBody(req), text = String(b.text || '').trim().slice(0, 2000);
      if (!text && !(b.links || []).length && !(b.files || []).length) return fail(res, 400, 'Напишите, что нужно');
      L.push({ id: newId(), text, done: false, at: now, by: user.id, ...(k === 'buy' ? { links: links(b.links), files: files(b.files) } : {}) });
      return out();
    }
    const it = p[5] && L.find(x => x.id === p[5]); if (!it) return fail(res, 404, 'Пункт не найден — обновите страницу');
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      if (b.text !== undefined) { const t = String(b.text).trim().slice(0, 2000); if (!t && !(it.links || []).length && !(it.files || []).length) return fail(res, 400, 'Пустой пункт — удалите его'); it.text = t; }
      if (b.done !== undefined) { it.done = !!b.done; it.doneAt = it.done ? now : null; it.doneBy = it.done ? user.id : null; }
      if (k === 'buy' && b.links !== undefined) it.links = links(b.links);
      if (k === 'buy' && b.files !== undefined) it.files = files(b.files);
      it.editedAt = now; it.editedBy = user.id;
      return out();
    }
    if (m === 'DELETE') { L.splice(L.indexOf(it), 1); return out(); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'jobs' && p[3] === 'places' && p[4]) {
    const j = db.jobs[p[2]]; if (!j) return fail(res, 404, 'Работа не найдена');
    const pl = (j.places || []).find(x => x.id === p[4]); if (!pl) return fail(res, 404, 'Точка не найдена');
    const mayReport = mayEditJob(user, j) || ((j.workers || []).includes(user.id) && (pl.assignee ? pl.assignee === user.id : (j.workers || []).length === 1)) || j.leaderId === user.id;
    if (!mayReport) return fail(res, 403, 'Это не ваша точка');
    const touch = () => { pl.reportAt = new Date().toISOString(); pl.reportBy = user.id; j.updatedAt = pl.reportAt; j.updatedBy = user.id; };
    pl.photos = pl.photos || {};
    // a closed point: the worker may correct it for 24 hours; after that — and always for other people's points — only the administrator.
    // «Руководитель» sees closed points but does not change them
    const adm = user.role === 'admin';
    if (pl.doneAt && m !== 'GET' && !adm) {
      if (HEAD(user) && pl.doneBy !== user.id) return fail(res, 403, 'Изменять и удалять выполненные точки может администратор');
      if (Date.now() - Date.parse(pl.doneAt) > 864e5) return fail(res, 409, 'Прошло больше суток после закрытия точки — изменить данные может администратор');
    }
    if (p[5] === 'done' && m === 'POST') {
      const b = await readJsonBody(req), notWorking = !!b.notWorking;
      const missing = (j.photoSpec || []).filter(n => !pl.photos[n]);
      if (missing.length) return fail(res, 400, 'Не хватает фото: ' + missing.join(', '));   // photos are required even when the device does not work
      const at = new Date().toISOString(), first = !pl.doneAt;
      Object.assign(pl, { notWorking, comment: String(b.comment ?? pl.comment ?? '').slice(0, 4000) });
      if (first) { pl.doneAt = at; pl.doneBy = user.id; } else { pl.editedAt = at; pl.editedBy = user.id; }
      touch();
      // the job follows its points: in work after the first one, done when every point is closed
      const all = j.places || [], left = all.filter(x => !x.doneAt).length;
      if (!left && j.status !== 'done') Object.assign(j, { status: 'done', doneAt: at, doneBy: user.id });
      else if (left && (j.status === 'new' || j.status === 'wait')) Object.assign(j, { status: 'work', startedAt: at, startedBy: user.id });
      saveDb();
      return send(res, 200, { ok: true, place: pl, left, status: j.status, rev: db.rev });
    }
    /* the administrator deletes what was done at a point: photos, comment and the mark go, the point is again
       in the list of the employee it is assigned to */
    if (p[5] === 'done' && m === 'DELETE') {
      if (!adm) return fail(res, 403, 'Удалить выполнение точки может администратор');
      const ph = pl.photos || {}, files = [...Object.entries(ph).filter(([k]) => k !== '_extra').map(([, f]) => f), ...(ph._extra || [])];
      for (const f of files) if (f && f.id && db.files[f.id]) { delete db.files[f.id]; try { fs.unlinkSync(path.join(filesDir(), f.id)); } catch {} }
      ['doneAt', 'doneBy', 'notWorking', 'comment', 'editedAt', 'editedBy', 'reportAt', 'reportBy'].forEach(k => delete pl[k]); pl.photos = {};
      pl.clearedAt = new Date().toISOString(); pl.clearedBy = user.id;
      if (j.status === 'done') { j.status = 'work'; j.doneAt = null; j.doneBy = null; }
      j.updatedAt = pl.clearedAt; j.updatedBy = user.id;
      saveDb();
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
      if (FIELD(user)) return fail(res, 403, 'Недостаточно прав');
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
      if (c.by !== user.id && !HEAD(user)) return fail(res, 403, 'Удалить можно только свой комментарий');
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
      const wantSt = data.status;
      data = cleanJob({ ...data, status: undefined, report: undefined }); data._st = wantSt;
      if (!data.title) return fail(res, 400, 'Укажите название проекта');
      data.kind = data.kind || 'mount'; data.workers = data.workers || []; data.docs = data.docs || [];
      data.status = ['new', 'wait', 'work'].includes(data._st) ? data._st : 'new'; delete data._st; data.report = ''; data.places = data.places || [];
      jobWorkersFromPlaces(data);
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
    if (col === 'jobs') { delete data.orderId; ensureJobOrder(data, nid, user); }
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
      // photos of a point taken for a list item that was renamed or removed become extra photos
      if (c.photoSpec) { const keep = new Set(c.photoSpec); for (const pl of (c.places || j.places || [])) { const src = (j.places || []).find(x => x.id === pl.id) || pl; const ph = src.photos; if (!ph) continue; for (const k of Object.keys(ph)) if (k !== '_extra' && !keep.has(k)) { ph._extra = [...(ph._extra || []), { ...ph[k], name: k + ' — ' + (ph[k].name || 'фото') }].slice(-20); delete ph[k]; } } }
      if (c.places) { const old = new Map((j.places || []).map(x => [x.id, x])); c.places.forEach(x => { const o = old.get(x.id); if (o) ['photos', 'comment', 'reportAt', 'reportBy', 'doneAt', 'doneBy', 'notWorking', 'editedAt', 'editedBy'].forEach(k => { if (o[k] !== undefined) x[k] = o[k]; }); }); }
      const other = ck.filter(k => !JOB_WORKER_FIELDS.includes(k));
      if (other.length ? !mayEditJob(user, j) : !(mayEditJob(user, j) || onJob(user, j))) return fail(res, 403, 'Недостаточно прав');
      if ('title' in c && !c.title) return fail(res, 400, 'Укажите название проекта');
      if ('status' in c) {
        if (!JOB_STATUS.includes(c.status)) return fail(res, 400, 'Неизвестный статус');
        const t = new Date().toISOString();
        if (c.status === 'work' && !j.startedAt) { c.startedAt = t; c.startedBy = user.id; }
        c.doneAt = c.status === 'done' ? t : null; c.doneBy = c.status === 'done' ? user.id : null;
      }
      delete c.orderId;   // the order of a work is made and kept by the server
      Object.assign(j, c, { updatedAt: new Date().toISOString(), updatedBy: user.id });
      if (c.places) jobWorkersFromPlaces(j);
      ensureJobOrder(j, id, user, c);
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
    // a deleted order of a work is not made again automatically
    if (col === 'orders') for (const j of Object.values(db.jobs || {})) if (j.orderId === id) { j.orderId = null; j.noOrder = true; }
    if (col === 'jobs' && d.orderId && db.orders[d.orderId] && db.orders[d.orderId].jobId === id) delete db.orders[d.orderId].jobId;
    delete db[col][id]; saveDb();
    return send(res, 200, { ok: true, rev: db.rev });
  }
  return fail(res, 405, 'Метод не поддерживается');
}
/* ---------- organizations: only the system administrator ---------- */
const ORG_ID = /^[a-z0-9][a-z0-9-]{1,30}$/;
const orgOut = o => {
  const st = orgState(o), us = users.filter(u => u.orgId === o.id);
  return { id: o.id, name: o.name, type: o.type === 'requests' ? 'requests' : 'all', hide: o.hide || [], until: o.until || '', blocked: !!o.blocked, blockNote: o.blockNote || '', note: o.note || '', createdAt: o.createdAt || null,
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
    const org = { id, name, type: ORG_TYPES.includes(b.type) ? b.type : 'all', hide: cleanHide(b.hide), until, blocked: false, note: String(b.note || '').slice(0, 1000), createdAt: new Date().toISOString(), createdBy: user.id };
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
    if (b.type !== undefined) { if (!ORG_TYPES.includes(b.type)) return fail(res, 400, 'Неизвестный тип системы'); o.type = b.type; }
    if (b.hide !== undefined) o.hide = cleanHide(b.hide);
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
      if (b.name !== undefined) { if (!String(b.name).trim()) return fail(res, 400, 'Укажите имя'); t.name = String(b.name).trim().slice(0, 120); }
      if (b.login !== undefined) {
        const login = String(b.login).trim().toLowerCase();
        if (!/^[a-z0-9._-]{2,40}$/.test(login)) return fail(res, 400, 'Логин: от 2 символов, латиница, цифры, точка, дефис или подчёркивание');
        if (users.some(u => u.login === login && u.id !== t.id)) return fail(res, 400, 'Такой логин уже есть');
        t.login = login;
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
/* the workers of a work are the people its points are assigned to */
function jobWorkersFromPlaces(j) {
  const ids = new Set(j.workers || []);
  for (const pl of j.places || []) if (pl.assignee) { const u = users.find(x => x.id === pl.assignee); if (u && FIELD(u)) ids.add(u.id); }
  j.workers = [...ids];
}

/* ---------- server load for the system administrator ---------- */
const reqLog = [];               // request times of the last 10 minutes
const lastSeen = new Map();      // user id → time of the last request
const startedAt = Date.now();
let reqTotal = 0;
function countRequest(u) {
  const t = Date.now(); reqTotal++; reqLog.push(t);
  while (reqLog.length && reqLog[0] < t - 600e3) reqLog.shift();
  if (u) lastSeen.set(u.id, t);
}
const dirSize = dir => { let n = 0, c = 0; try { for (const f of fs.readdirSync(dir, { withFileTypes: true })) if (f.isFile()) { n += fs.statSync(path.join(dir, f.name)).size; c++; } } catch {} return { bytes: n, count: c }; };
let cpuPrev = process.cpuUsage(), cpuAt = Date.now(), cpuPct = 0;
setInterval(() => { const u = process.cpuUsage(cpuPrev), dt = (Date.now() - cpuAt) * 1000; cpuPct = dt ? Math.round((u.user + u.system) / dt * 1000) / 10 : 0; cpuPrev = process.cpuUsage(); cpuAt = Date.now(); }, 5000).unref();
async function statsApi(req, res, m, user) {
  if (!user.sys) return fail(res, 403, 'Статистику сервера видит только администратор системы');
  if (m !== 'GET') return fail(res, 405, 'Метод не поддерживается');
  const mem = process.memoryUsage(), now = Date.now();
  let disk = null; try { const st = fs.statfsSync(DATA_DIR); disk = { total: st.blocks * st.bsize, free: st.bavail * st.bsize }; } catch {}
  const per = orgs.map(o => {
    const e = orgEntry(o.id), d = e.db, files = dirSize(e.files);
    let dbBytes = 0; try { dbBytes = fs.statSync(e.file).size; } catch {}
    const us = users.filter(u => u.orgId === o.id);
    return { id: o.id, name: o.name, state: orgState(o).blocked ? 'blocked' : 'active', users: us.length, online: us.filter(u => now - (lastSeen.get(u.id) || 0) < 300e3).length,
      orders: Object.keys(d.orders || {}).length, jobs: Object.keys(d.jobs || {}).length, points: (d.dt && d.dt.points || []).length,
      places: Object.values(d.jobs || {}).reduce((a, j) => a + (j.places || []).length, 0), files: files.count, filesBytes: files.bytes, dbBytes };
  });
  const backups = dirSize(BACKUP_DIR);
  return send(res, 200, {
    at: new Date().toISOString(), version: APP_VERSION, node: process.version, platform: `${os.type()} ${os.release()}`, host: os.hostname(),
    uptime: { process: Math.round((now - startedAt) / 1000), system: Math.round(os.uptime()) },
    memory: { rss: mem.rss, heapUsed: mem.heapUsed, heapTotal: mem.heapTotal, external: mem.external, total: os.totalmem(), free: os.freemem() },
    cpu: { cores: os.cpus().length, model: (os.cpus()[0] || {}).model || '', load: os.loadavg(), process: cpuPct },
    disk, data: { orgs: per.reduce((a, o) => a + o.dbBytes + o.filesBytes, 0), backups: backups.bytes, backupFiles: backups.count },
    requests: { total: reqTotal, perMin: reqLog.filter(t => t > now - 60e3).length, per10Min: reqLog.length },
    users: { total: users.length, online: [...lastSeen.values()].filter(t => now - t < 300e3).length },
    orgs: per,
  });
}
const publicUser = u => ({ id: u.id, login: u.login, name: u.name, role: u.role, roleName: ROLES[u.role] });
/* personal settings of a user: theme, text size, start page, what the map shows and in which colours */
const HEX = v => /^#[0-9a-f]{6}$/i.test(String(v || '')) ? String(v).toLowerCase() : null;
function cleanPrefs(b){
  const o = {};
  if (['system', 'light', 'dark', 'telecom', 'pink', 'engineer', 'upr', 'anime'].includes(b.theme)) o.theme = b.theme;
  if ([1, 1.1, 1.2, 1.35].includes(Number(b.scale))) o.scale = Number(b.scale);
  if (['pin', 'dot'].includes(b.marker)) o.marker = b.marker;
  if (['type', 'need', 'person'].includes(b.dtColor)) o.dtColor = b.dtColor;
  if (/^[a-z]{2,10}$/.test(String(b.start || ''))) o.start = String(b.start);
  if (b.dtShow && typeof b.dtShow === 'object') o.dtShow = Object.fromEntries(Object.entries(b.dtShow).filter(([k]) => /^[a-z_]{2,20}$/.test(k)).slice(0, 30).map(([k, v]) => [k, !!v]));
  if (b.colors && typeof b.colors === 'object') o.colors = Object.fromEntries(Object.entries(b.colors).filter(([k, v]) => /^[a-z_]{2,20}$/.test(k) && HEX(v)).slice(0, 30).map(([k, v]) => [k, HEX(v)]));
  return o;
}
/* Map background: OpenStreetMap by default, another tile source can be set in sed.env */
const MAP = {
  tiles: process.env.MAP_TILES || 'https://tile.openstreetmap.org/{z}/{x}/{y}.png',
  attribution: process.env.MAP_ATTRIBUTION || '&copy; <a href="https://www.openstreetmap.org/copyright" target="_blank" rel="noopener">OpenStreetMap</a>',
  subdomains: process.env.MAP_SUBDOMAINS || 'abc',
  maxZoom: Number(process.env.MAP_MAX_ZOOM || 19),
};
const meInfo = u => { const o = orgById(u.orgId), st = orgState(o); return { ...publicUser(u), prefs: u.prefs || {}, map: MAP, sys: !!u.sys, hide: u.sys ? [] : hiddenFor(u), org: o ? { id: o.id, name: o.name, until: o.until || '', type: orgType(u), hide: o.hide || [] } : null, orgWarn: st.warn || '' }; };
const adminUser = u => ({ ...publicUser(u), sys: !!u.sys, hide: u.hide || [], accessUntil: u.accessUntil || '', expired: !!contractorExpired(u), blocked: !!u.blocked, lastLoginAt: u.lastLoginAt || null, createdAt: u.createdAt || null });

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
/* The write-off list of an order is taken from the accounting balances (1С). A line whose position is not in the balances
   or whose balance is short is «red»; the nomenclature of a line can be replaced (o.woMap: original line key → stock id). */
// a work's materials look like one product of quantity 1 for the write-off list
const woDoc = (col, id) => { const x = db[col] && db[col][id]; if (!x) return null; return col === 'jobs' ? { ...x, number: 'работа № ' + (x.no || ''), products: [{ name: x.title, qty: 1, components: x.materials || [] }] } : x; };
const woTaken = o => { const t = {}; if (o && o.writeoff && o.writeoff.applied) for (const L of o.writeoff.lines || []) if (L.stockId) t[L.stockId] = r3((t[L.stockId] || 0) + (Number(L.qty) || 0)); return t; };
function writeoffLines(o, mapOverride) {
  const taken = woTaken(o);
  const byName = new Map(Object.entries(db.stock).map(([id, it]) => [normName(it.name), id]));
  const map = mapOverride || o.woMap || {};
  const lines = new Map();
  for (const p of o.products || []) {
    const k = Number(p.qty) || 0;
    for (const c of p.components || []) {
      const sid0 = (c.stockId && db.stock[c.stockId]) ? c.stockId : byName.get(normName(c.name));
      if (!sid0 && !String(c.name || '').trim()) continue;
      const key0 = sid0 ? 'id:' + sid0 : 'n:' + normName(c.name);
      const sid = map[key0] && db.stock[map[key0]] ? map[key0] : sid0;
      const it = sid ? db.stock[sid] : null;
      const key = sid ? 'id:' + sid : key0;
      const L = lines.get(key) || { key, keys: [], name: it ? it.name : c.name, sku: it ? it.sku || '' : '', unit: (it && it.unit) || c.unit || 'шт', need: 0, acct: it ? r3((Number(it.acctQty) || 0) + (taken[sid] || 0)) : 0, real: it ? Number(it.qty) || 0 : 0, inStock: !!it, stockId: sid || null, replaced: false, products: [] };
      if (!L.keys.includes(key0)) L.keys.push(key0);
      if (sid !== sid0) L.replaced = true;
      L.need = Math.round((L.need + (Number(c.qty) || 0) * k) * 1000) / 1000;
      if (p.name && !L.products.includes(p.name)) L.products.push(p.name);
      lines.set(key, L);
    }
  }
  return [...lines.values()].map(L => {
    const source = !L.inStock ? 'none' : L.acct >= L.need - 1e-9 ? 'acct' : 'short';
    const shortage = source === 'acct' ? 0 : Math.round((L.need - (L.inStock ? L.acct : 0)) * 1000) / 1000;
    return { ...L, source, shortage };
  }).sort((a, b) => a.name.localeCompare(b.name, 'ru'));
}
const SOURCE_LABEL = { acct: 'Хватает', short: 'Не хватает', none: 'Нет в бухгалтерских остатках' };
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
const xlsxBuffer = (sheetName, rows, widths) => xlsxBook([{ name: sheetName, rows, widths }]);
function xlsxSheet(rows, widths) {
  const sheetRows = rows.map((r, ri) => `<row r="${ri + 1}">` + r.map((c, ci) => {
    if (c == null) return '';
    const ref = colName(ci) + (ri + 1), cell = typeof c === 'object' ? c : { v: c };
    const st = cell.s ? ` s="${cell.s}"` : '';
    if (typeof cell.v === 'number') return `<c r="${ref}"${st}><v>${cell.v}</v></c>`;
    return `<c r="${ref}"${st} t="inlineStr"><is><t xml:space="preserve">${xmlEsc(cell.v)}</t></is></c>`;
  }).join('') + '</row>').join('');
  const cols = widths ? '<cols>' + widths.map((w, i) => `<col min="${i + 1}" max="${i + 1}" width="${w}" customWidth="1"/>`).join('') + '</cols>' : '';
  return `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><worksheet xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main">${cols}<sheetData>${sheetRows}</sheetData></worksheet>`;
}
/* sheets: [{ name, rows, widths }] */
function xlsxBook(sheets) {
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
    { name: '[Content_Types].xml', data: `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Types xmlns="http://schemas.openxmlformats.org/package/2006/content-types"><Default Extension="rels" ContentType="application/vnd.openxmlformats-package.relationships+xml"/><Default Extension="xml" ContentType="application/xml"/><Override PartName="/xl/workbook.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.sheet.main+xml"/>${sheets.map((x, i) => `<Override PartName="/xl/worksheets/sheet${i + 1}.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.worksheet+xml"/>`).join('')}<Override PartName="/xl/styles.xml" ContentType="application/vnd.openxmlformats-officedocument.spreadsheetml.styles+xml"/></Types>` },
    { name: '_rels/.rels', data: '<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships"><Relationship Id="rId1" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/officeDocument" Target="xl/workbook.xml"/></Relationships>' },
    { name: 'xl/workbook.xml', data: `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><workbook xmlns="http://schemas.openxmlformats.org/spreadsheetml/2006/main" xmlns:r="http://schemas.openxmlformats.org/officeDocument/2006/relationships"><sheets>${sheets.map((x, i) => `<sheet name="${xmlEsc(x.name).slice(0, 31)}" sheetId="${i + 1}" r:id="rId${i + 1}"/>`).join('')}</sheets></workbook>` },
    { name: 'xl/_rels/workbook.xml.rels', data: `<?xml version="1.0" encoding="UTF-8" standalone="yes"?><Relationships xmlns="http://schemas.openxmlformats.org/package/2006/relationships">${sheets.map((x, i) => `<Relationship Id="rId${i + 1}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/worksheet" Target="worksheets/sheet${i + 1}.xml"/>`).join('')}<Relationship Id="rId${sheets.length + 1}" Type="http://schemas.openxmlformats.org/officeDocument/2006/relationships/styles" Target="styles.xml"/></Relationships>` },
    { name: 'xl/styles.xml', data: styles },
    ...sheets.map((x, i) => ({ name: `xl/worksheets/sheet${i + 1}.xml`, data: xlsxSheet(x.rows, x.widths) })),
  ];
  return zipStore(files);
}
/* sheet «Товары»: one header row and the goods — the form 1C reads with «Загрузить из файла» (columns are recognized by their headers);
   names are taken from the warehouse position, which carries the 1C name after the balances import; sheet «Реквизиты»: the document */
function receiptXlsx(d) {
  const lines = (d.lines || []).filter(x => x && x.name);
  const nameOf = x => { const it = x.stockId && db.stock[x.stockId]; return it ? it.name : x.name; };
  const skuOf = x => { const it = x.stockId && db.stock[x.stockId]; return (it && it.sku) || x.sku || ''; };
  const sumOf = x => Number(x.sum) > 0 ? r2(x.sum) : r2((Number(x.qty) || 0) * (Number(x.price) || 0));
  const head = ['№', 'Артикул', 'Номенклатура', 'Единица', 'Количество', 'Цена', 'Сумма', 'Наименование в накладной'].map(v => ({ v, s: 1 }));
  const goods = [head, ...lines.map((x, i) => [{ v: i + 1, s: 3 }, { v: skuOf(x), s: 2 }, { v: nameOf(x), s: 2 }, { v: x.unit || 'шт', s: 2 }, { v: Number(x.qty) || 0, s: 3 },
    { v: Number(x.price) || 0, s: 3 }, { v: sumOf(x), s: 3 }, { v: x.name !== nameOf(x) ? x.name : '', s: 2 }])];
  const cp = d.inn ? null : Object.values(db.counterparties || {}).find(c => normName(c.name) === normName(d.supplier));
  const o = d.orderId && db.orders[d.orderId], u = d.income && d.income.by && users.find(x => x.id === d.income.by);
  const total = r2(lines.reduce((a, x) => a + sumOf(x), 0));
  const info = [
    [{ v: 'Поступление товаров', s: 10 }],
    [],
    ['Основание', d.kind],
    ['Номер входящего документа', d.number || ''],
    ['Дата входящего документа', d.date ? ruDate(d.date) : ''],
    ['Поставщик (контрагент)', d.supplier || ''],
    ['ИНН поставщика', d.inn || (cp && cp.inn) || ''],
    ...(d.invoice ? [['Счёт поставщика', d.invoice]] : []),
    ...(o ? [['Заказ', `${o.number || ''} · ${o.title || ''}`]] : []),
    ['Строк', lines.length],
    ['Сумма по строкам', total],
    ['Оприходовано на склад', d.income && d.income.at ? new Date(d.income.at).toLocaleString('ru-RU', { timeZone: process.env.TZ || 'Europe/Moscow' }) + (u ? ', ' + u.name : '') : 'ещё не оприходовано'],
    [],
    ['Как загрузить в 1С:Бухгалтерию 8:'],
    ['1. Покупки → Поступление (акты, накладные, УПД) → Поступление → Товары (накладная, УПД).'],
    ['2. Заполните контрагента, номер и дату входящего документа с этого листа.'],
    ['3. На вкладке «Товары» нажмите «Загрузить» (или «Ещё» → «Загрузить из файла») и выберите этот файл — данные на листе «Товары».'],
    ['4. Проверьте сопоставление номенклатуры и ставку НДС, проведите документ.'],
  ];
  return xlsxBook([{ name: 'Товары', rows: goods, widths: [5, 16, 50, 9, 12, 13, 14, 40] }, { name: 'Реквизиты', rows: info, widths: [30, 60] }]);
}
/* the write-off list as an Excel file for 1C: sheet «Товары» — one header row and the materials (1С:Бухгалтерия 8:
   «Требование-накладная» → «Материалы» → «Загрузить» → «Из файла»; columns are recognized by their headers);
   «Реквизиты» — what it is for and how to load; «Проверка остатков» — the coloured check against the accounting balances */
function writeoffXlsx(o) {
  const lines = writeoffLines(o);
  const fmt = iso => iso ? new Date(iso).toLocaleString('ru-RU', { timeZone: process.env.TZ || 'Europe/Moscow' }) : 'не загружались';
  const job = /^работа/.test(o.number || ''), cp = o.customerId && db.counterparties[o.customerId];
  const ord = job && o.orderId && db.orders[o.orderId];
  const wb = o.writeoff, u = wb && users.find(x => x.id === wb.by);
  // the lines of the saved list when it is saved (that is what was taken off the books), otherwise the current ones
  const out = wb && Array.isArray(wb.lines) && wb.lines.length ? wb.lines.map(L => { const it = L.stockId && db.stock[L.stockId]; return { name: it ? it.name : L.name, sku: (it && it.sku) || L.sku || '', unit: (it && it.unit) || L.unit || 'шт', qty: Number(L.qty) || 0 }; })
    : lines.map(L => ({ name: L.name, sku: L.sku || '', unit: L.unit || 'шт', qty: L.need }));
  const goods = [['№', 'Артикул', 'Номенклатура', 'Единица', 'Количество'].map(v => ({ v, s: 1 })),
    ...out.map((L, i) => [{ v: i + 1, s: 3 }, { v: L.sku, s: 2 }, { v: L.name, s: 2 }, { v: L.unit, s: 2 }, { v: L.qty, s: 3 }])];
  const bad = lines.filter(L => L.source !== 'acct');
  const info = [
    [{ v: 'Списание материалов', s: 10 }],
    [],
    ['Основание', job ? `Работа ${String(o.number || '').replace(/^работа\s*/, '')} · ${o.title || ''}` : `Заказ на производство ${o.number || ''} · ${o.title || ''}`],
    ...(ord ? [['Заказ на производство', `${ord.number || ''} · ${ord.title || ''}`]] : []),
    ...(cp || o.customer ? [['Заказчик', cp ? cp.name : o.customer]] : []),
    ['Список для списания', wb ? `сохранён ${fmt(wb.at)}${u ? ', ' + u.name : ''}` : 'ещё не сохранён — в файле текущие строки'],
    ['Строк', out.length],
    ['Бухгалтерские остатки', db.meta.acct ? `из 1С ${fmt(db.meta.acct.at)}${db.meta.acct.file ? ' (' + db.meta.acct.file + ')' : ''}` : 'выгрузка 1С не загружалась'],
    ...(bad.length ? [['Внимание', `не хватает в бухгалтерских остатках: ${bad.length} — см. лист «Проверка остатков»`]] : []),
    ['Сформирован', fmt(new Date().toISOString())],
    [],
    ['Как загрузить в 1С:Бухгалтерию 8:'],
    ['1. Производство → Требования-накладные (для монтажа — Склад → Списание товаров) → Создать.'],
    ['2. Укажите склад и счёт затрат; в комментарии — основание с этого листа.'],
    ['3. На вкладке «Материалы» («Товары») нажмите «Загрузить» (или «Ещё» → «Загрузить из файла») и выберите этот файл — данные на листе «Товары».'],
    ['4. Проверьте сопоставление номенклатуры и проведите документ.'],
  ];
  const st = { acct: [4, 5], short: [8, 9], none: [8, 9] };
  const check = [
    ['№', 'Наименование', 'Артикул', 'Ед.', 'Списать', 'Бух. остаток', 'Факт. остаток', 'Состояние', 'Не хватает', 'Изделия'].map(v => ({ v, s: 1 })),
    ...lines.map((L, i) => { const [ts, ns] = st[L.source]; return [
      { v: i + 1, s: ns }, { v: L.name, s: ts }, { v: L.sku, s: ts }, { v: L.unit, s: ts }, { v: L.need, s: ns },
      L.inStock ? { v: L.acct, s: ns } : { v: '—', s: ts }, L.inStock ? { v: L.real, s: ns } : { v: '—', s: ts },
      { v: SOURCE_LABEL[L.source], s: ts }, L.shortage ? { v: L.shortage, s: ns } : { v: '', s: ts }, { v: L.products.join(', '), s: ts }]; }),
    [],
    [{ v: 'Хватает бухгалтерского остатка', s: 4 }],
    [{ v: 'Позиции нет в бухгалтерских остатках или её не хватает', s: 8 }],
  ];
  return xlsxBook([{ name: 'Товары', rows: goods, widths: [5, 16, 50, 9, 12] }, { name: 'Реквизиты', rows: info, widths: [30, 70] }, { name: 'Проверка остатков', rows: check, widths: [5, 42, 16, 7, 11, 13, 13, 30, 12, 30] }]);
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
    // the page carries the version it was served with, so an old page left open on a phone knows to reload itself
    if (rel === '/index.html') buf = Buffer.from(buf.toString('utf8').split('__APP_VERSION__').join(APP_VERSION));
    res.writeHead(200, {
      ...SEC_HEADERS,
      'Content-Type': MIME[path.extname(fp)] || 'application/octet-stream',
      'Cache-Control': rel === '/index.html' ? 'no-store' : 'no-cache',
    });
    res.end(buf);
  });
}

/* the readings of the power monitor: building and server room power (true — «в режиме»), the battery (raw value of the device, 840 and more — full) and the signal;
   a reading with the same state only refreshes the time of the last one */
const DEV_POWER = { 1: [false, false], 2: [true, true], 3: [false, true], 4: [true, false] };
async function devIn(req, res, url, key) {
  const c = reqCfgOf();
  if (!c.devToken || key !== c.devToken) return fail(res, 403, 'Неверный ключ устройства');
  let b = Object.fromEntries(url.searchParams);
  if (req.method === 'POST') { try { b = { ...b, ...(await readJsonBody(req)) }; } catch { return fail(res, 400, 'Ожидается JSON'); } }
  else if (req.method !== 'GET') return fail(res, 405, 'Метод не поддерживается');
  const bool = v => v === undefined || v === '' ? null : ['1', 'true', 'on', 'yes'].includes(String(v).toLowerCase());
  const num = v => v === undefined || v === '' || !Number.isFinite(Number(v)) ? null : Number(v);
  const pw = DEV_POWER[Number(b.power)] || [bool(b.building), bool(b.server)];
  const rd = { building: pw[0], server: pw[1], battery: num(b.battery), signal: num(b.signal) };
  if (rd.building === null && rd.server === null && rd.battery === null && rd.signal === null) return fail(res, 400, 'Нет данных: power (1–4) или building/server, battery, signal');
  if (!Array.isArray(db.devReadings)) db.devReadings = [];
  const L = db.devReadings, last = L[L.length - 1], now = new Date().toISOString(), full = x => x === null ? null : x >= 840;
  if (last && last.building === rd.building && last.server === rd.server && full(last.battery) === full(rd.battery)) Object.assign(last, rd, { upd: now });
  else { L.push({ no: (last ? last.no : 0) + 1, ...rd, at: now, upd: now }); if (L.length > 500) L.splice(0, L.length - 500); }
  saveDb();
  return send(res, 200, { ok: true });
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
      // a device of a requests organization reports the power of the building and the server room (no session: the key of the organization)
      if (url.pathname.startsWith('/api/dev-in/')) {
        const [, , , orgId, key] = url.pathname.split('/');
        const o = orgById(orgId);
        if (!o || o.type !== 'requests' || !key) return fail(res, 404, 'Не найдено');
        return await als.run(orgEntry(orgId), async () => devIn(req, res, url, key));
      }
      if (url.pathname.startsWith('/api/') || url.pathname.startsWith('/files/')) {
        // every request works inside the data of the signed-in user's organization
        const su = sessionUser(req), org = su && orgById(su.orgId) ? su.orgId : MAIN_ORG;
        countRequest(su);
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

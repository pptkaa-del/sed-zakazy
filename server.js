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
const { spawn } = require('node:child_process');

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
// the presentation of the system (PDF) — downloaded by the system administrator from his menu
const PRESENTATION_FILE = path.join(__dirname, 'docs', 'presentation.pdf');
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
  office:     'Сотрудник офиса', // the same rights as «Руководитель»
  accountant: 'Бухгалтер',
  worker:     'Сотрудник',
  contractor: 'Подрядчик',
  executor:   'Исполнитель',   // only in «Управление заявками»
};
/* «Сотрудник» and «Подрядчик» work in the field: only their points; a contractor's access ends on a set date */
const FIELD = u => u && (u.role === 'worker' || u.role === 'contractor');
const contractorExpired = u => u && u.role === 'contractor' && u.accessUntil && localDateNow() > u.accessUntil;
function localDateNow() { const d = new Date(); return `${d.getFullYear()}-${String(d.getMonth() + 1).padStart(2, '0')}-${String(d.getDate()).padStart(2, '0')}`; }
const PAY_FIELDS = ['status', 'paidAt', 'payNo', 'paidAmount', 'paidBy', 'receipt'];
// «Руководитель» works like the administrator but neither marks invoices paid nor manages users
const HEAD = u => u && (u.role === 'admin' || u.role === 'head' || u.role === 'office');
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
// «Задействован транспорт» of a task of the plan: only the vehicles of the organization
const taskVehicles = a => [...new Set((Array.isArray(a) ? a : []).map(String))].filter(id => db.vehicles && db.vehicles[id]).slice(0, 30);
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
  // «Эксплуатация» — a work of requests: each request has an executor and a vehicle
  if ('kind' in d) out.kind = ['prod', 'mount', 'both', 'ops'].includes(d.kind) ? d.kind : 'mount';
  // a priority work goes to the top of the list
  if ('priority' in d) out.priority = !!d.priority;
  // the group of a work («Группы» in «Работы»)
  if ('groupId' in d) out.groupId = d.groupId && (db.jobGroups || []).some(g => g.id === d.groupId) ? String(d.groupId) : null;
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
  // a personal minimum of points a day for chosen workers of the work (instead of the common one)
  if ('minByWorker' in d) out.minByWorker = Object.fromEntries(Object.entries(d.minByWorker && typeof d.minByWorker === 'object' ? d.minByWorker : {})
    .filter(([id, v]) => users.some(u => u.id === id) && Number(v) > 0).slice(0, 500).map(([id, v]) => [id, Math.min(10000, Math.round(Number(v)))]));
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
// «Изменения» of a work: who changed what and when; the last 300 entries
const short = v => v == null ? '' : Array.isArray(v) ? (v.length ? String(v.length) : '') : typeof v === 'object' ? JSON.stringify(v).slice(0, 200) : String(v).slice(0, 300);
function jobLog(j, user, e){ if (!j) return; j.history = (Array.isArray(j.history) ? j.history : []).concat({ at: new Date().toISOString(), by: user.id, ...e }).slice(-300); }
function diffOf(old, patch, skip = []){ return Object.keys(patch).filter(k => !skip.includes(k) && JSON.stringify(old[k] ?? null) !== JSON.stringify(patch[k] ?? null)).map(k => ({ f: k, from: short(old[k]), to: short(patch[k]) })); }
const jobToOrderSt = st => st === 'done' ? 'closed' : st === 'work' ? 'work' : 'new';
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
// «Этикетки для модемов» moved into «Дополнительные модули»: a hidden «refs:sn» becomes a hidden «refs:mods»
const hideMoved = h => { if (Array.isArray(h) && h.includes('refs:sn')) { const i = h.indexOf('refs:sn'); h.splice(i, 1); if (!h.includes('refs:mods')) h.push('refs:mods'); return true; } return false; };
const normUsers = () => { let ch = false; users.forEach(u => { if (!u.orgId) { u.orgId = MAIN_ORG; ch = true; } if (OLD_ROLES[u.role]) { u.wasRole = u.role; u.role = OLD_ROLES[u.role]; ch = true; } if (hideMoved(u.hide)) ch = true; }); return ch; };
if (normUsers() && users.length) writeJSON(USERS_FILE, users);
if (Array.isArray(orgs) && orgs.reduce((a, o) => hideMoved(o.hide) || a, false)) writeJSON(ORGS_FILE, orgs);
function syncFromDisk() {
  const b = stamp(USERS_FILE); if (b !== usersStamp) { users = readJSON(USERS_FILE, []); normUsers(); usersStamp = b; }
  const c = stamp(ORGS_FILE); if (c !== orgsStamp) { orgs = readJSON(ORGS_FILE, orgs); orgsStamp = c; }
}
const saveUsers = () => { writeJSON(USERS_FILE, users); usersStamp = stamp(USERS_FILE); };
const saveOrgs = () => { writeJSON(ORGS_FILE, orgs); orgsStamp = stamp(ORGS_FILE); };
/* «Написать администратору»: a user of an organization writes to its administrators, an administrator of an organization — to the system
   administrator. One thread per user: { kind: 'admin' | 'sys', orgId, uid, msgs: [{ id, by, text, at }], userRead, staffRead } */
const CHAT_FILE = path.join(DATA_DIR, 'chat.json');
let chat = null, chatStamp;
const chatDb = () => { const st = stamp(CHAT_FILE); if (!chat || st !== chatStamp) { chat = readJSON(CHAT_FILE, { threads: {} }); if (!chat.threads) chat.threads = {}; if (!chat.files) chat.files = {}; chatStamp = st; } return chat; };
// the attachments of the conversations: DATA_DIR/chat-files/<id>; { name, type, size, at, by, thread } in chat.files
const CHAT_FILES = path.join(DATA_DIR, 'chat-files');
const saveChat = () => { writeJSON(CHAT_FILE, chat); chatStamp = stamp(CHAT_FILE); };
/* «Запросить пробный доступ» on the login page: the requests go to the system administrator (tab «Запросы доступа») */
const TRIALS_FILE = path.join(DATA_DIR, 'trials.json');
let trials = null, trialsStamp;
const trialsDb = () => { const st = stamp(TRIALS_FILE); if (!trials || st !== trialsStamp) { trials = readJSON(TRIALS_FILE, []); if (!Array.isArray(trials)) trials = []; trialsStamp = st; } return trials; };
const saveTrials = () => { writeJSON(TRIALS_FILE, trials); trialsStamp = stamp(TRIALS_FILE); };
const TRIAL_TYPES = { all: 'Все сервисы', requests: 'Управление заявками', transport: 'Транспортная организация', ip: 'ИП / самозанятый' };
const trialsNew = () => trialsDb().filter(x => x.status === 'new').length;
const isOrgAdmin = u => u && u.role === 'admin' && !u.sys;
// the thread a user writes in himself: to the administrators of his organization or (an administrator) to the system administrator
const chatMine = u => !u || u.sys ? null : isOrgAdmin(u) ? { kind: 'sys', key: `sys:${u.orgId}:${u.id}` } : { kind: 'admin', key: `admin:${u.orgId}:${u.id}` };
// who answers in a thread: the administrators of the organization / the system administrators
const chatStaff = (u, th) => !!u && !u.blocked && (th.kind === 'admin' ? isOrgAdmin(u) && u.orgId === th.orgId : !!u.sys);
const chatOwn = (u, th) => !!u && th.uid === u.id && th.orgId === u.orgId;
const url_dl = req => /[?&]dl=1\b/.test(req.url || '');
const chatUnread = u => { if (!u) return 0; let n = 0; for (const th of Object.values(chatDb().threads)) {
  if (chatOwn(u, th)) n += th.msgs.filter(x => x.by !== u.id && x.at > (th.userRead || '')).length;
  else if (chatStaff(u, th)) n += th.msgs.filter(x => x.by === th.uid && x.at > (th.staffRead || '')).length; } return n; };
async function chatApi(req, res, p, m, user) {
  const C = chatDb(), uName = id => users.find(u => u.id === id)?.name || 'Пользователь', mine = chatMine(user);
  const fileOf = id => { const f = C.files[id]; return f ? { id, name: f.name, type: f.type, size: f.size } : null; };
  const pubMsg = th => x => ({ id: x.id, by: x.by, name: uName(x.by), staff: x.by !== th.uid, text: x.text, at: x.at, files: (x.files || []).map(fileOf).filter(Boolean) });
  const canTh = key => { const th = C.threads[key]; return !!th && (chatOwn(user, th) || chatStaff(user, th)); };
  // a file is uploaded first, then sent with the message; files not sent within a day are removed
  if (p[2] === 'upload' && m === 'POST') {
    let name = 'файл'; try { name = decodeURIComponent(String(req.headers['x-filename'] || 'файл')); } catch {}
    name = name.replace(/[\\/\r\n"]/g, '_').slice(0, 200) || 'файл';
    const buf = await readBody(req, MAX_FILE); if (!buf.length) return fail(res, 400, 'Пустой файл');
    const type = String(req.headers['content-type'] || 'application/octet-stream').split(';')[0].trim().toLowerCase();
    fs.mkdirSync(CHAT_FILES, { recursive: true });
    const day = new Date(Date.now() - 864e5).toISOString();
    for (const [fid, f] of Object.entries(C.files)) if (!f.thread && f.at < day) { delete C.files[fid]; try { fs.unlinkSync(path.join(CHAT_FILES, fid)); } catch {} }
    const id = newId(); fs.writeFileSync(path.join(CHAT_FILES, id), buf);
    C.files[id] = { name, type, size: buf.length, at: new Date().toISOString(), by: user.id, thread: null }; saveChat();
    return send(res, 200, fileOf(id));
  }
  if (p[2] === 'f' && p[3] && m === 'GET') {
    const id = p[3], f = C.files[id];
    if (!/^[\w-]+$/.test(id) || !f || !(f.thread ? canTh(f.thread) : f.by === user.id)) return fail(res, 404, 'Файл не найден');
    const fp = path.join(CHAT_FILES, id); if (!fs.existsSync(fp)) return fail(res, 404, 'Файл не найден');
    const inline = INLINE.has(f.type), enc = encodeURIComponent(f.name);
    res.writeHead(200, { ...SEC_HEADERS, 'Content-Type': inline ? f.type + (f.type.startsWith('text/') ? '; charset=utf-8' : '') : 'application/octet-stream', 'Content-Length': f.size,
      'Content-Disposition': `${inline && !url_dl(req) ? 'inline' : 'attachment'}; filename="${enc}"; filename*=UTF-8''${enc}`, 'Content-Security-Policy': "default-src 'none'; img-src 'self'; style-src 'unsafe-inline'; sandbox", 'Cache-Control': 'private, no-cache' });
    return fs.createReadStream(fp).pipe(res);
  }
  const body = m === 'POST' ? await readJsonBody(req) : null;
  if (m === 'GET' && !p[2]) {
    const inbox = Object.entries(C.threads).filter(([, th]) => chatStaff(user, th) && th.msgs.length).map(([key, th]) => { const last = th.msgs[th.msgs.length - 1], o = users.find(u => u.id === th.uid);
      return { key, kind: th.kind, uid: th.uid, name: uName(th.uid), role: o ? ROLES[o.role] : '', org: orgById(th.orgId)?.name || '', last: last.at, lastText: (last.text || ((last.files || []).length ? '📎 файл' : '')).slice(0, 120), lastBy: last.by === th.uid ? 'user' : 'staff', unread: th.msgs.filter(x => x.by === th.uid && x.at > (th.staffRead || '')).length }; })
      .sort((a, b) => b.last.localeCompare(a.last));
    const th = mine && C.threads[mine.key];
    const staffCount = mine ? (mine.kind === 'admin' ? users.filter(u => isOrgAdmin(u) && u.orgId === user.orgId && !u.blocked).length : users.filter(u => u.sys && !u.blocked).length) : 0;
    return send(res, 200, { mine: mine ? { ...mine, staffCount, unread: th ? th.msgs.filter(x => x.by !== user.id && x.at > (th.userRead || '')).length : 0 } : null, inbox, canInbox: isOrgAdmin(user) || !!user.sys, unread: chatUnread(user) });
  }
  if (p[2] !== 't' || !p[3]) return fail(res, 404, 'Не найдено');
  const key = decodeURIComponent(p[3]); let th = C.threads[key];
  const own = mine && mine.key === key;
  if (!th && own) th = { kind: mine.kind, orgId: user.orgId, uid: user.id, msgs: [], userRead: '', staffRead: '' };
  if (!th || !(own || chatOwn(user, th) || chatStaff(user, th))) return fail(res, 404, 'Переписка не найдена');
  const asOwner = own || chatOwn(user, th), now = new Date().toISOString();
  if (m === 'GET') {
    const was = asOwner ? th.userRead : th.staffRead;
    if (C.threads[key] && th.msgs.length && th.msgs[th.msgs.length - 1].at > (was || '')) { if (asOwner) th.userRead = now; else th.staffRead = now; saveChat(); }
    const o = users.find(u => u.id === th.uid);
    return send(res, 200, { key, kind: th.kind, owner: { id: th.uid, name: uName(th.uid), role: o ? ROLES[o.role] : '', org: orgById(th.orgId)?.name || '' }, asOwner, msgs: th.msgs.map(pubMsg(th)) });
  }
  if (m === 'POST') {
    const text = String(body?.text ?? '').trim().slice(0, 4000);
    const files = [...new Set((Array.isArray(body?.files) ? body.files : []).map(String))].filter(id => C.files[id] && C.files[id].by === user.id && !C.files[id].thread).slice(0, 20);
    if (!text && !files.length) return fail(res, 400, 'Напишите сообщение или прикрепите файл');
    if (th.msgs.length >= 2000) th.msgs = th.msgs.slice(-1500);
    files.forEach(id => { C.files[id].thread = key; });
    th.msgs.push({ id: newId(), by: user.id, text, at: now, ...(files.length ? { files } : {}) }); if (asOwner) th.userRead = now; else th.staffRead = now;
    C.threads[key] = th; saveChat(); return send(res, 200, { ok: true, msg: pubMsg(th)(th.msgs[th.msgs.length - 1]) });
  }
  return fail(res, 405, 'Метод не поддерживается');
}
const orgById = id => orgs.find(o => o.id === id);
/* the kind of system an organization works in: «Все сервисы» (all) or «Управление заявками» (requests) */
// «Все сервисы», «Управление заявками», «Транспортная организация» (спецтехника и грузоперевозки)
// «ИП / самозанятый» (ip): договоры, счета, налог 6 %, сканы документов
const ORG_TYPES = ['all', 'requests', 'transport', 'ip'];
const IP_ROLES = ['admin', 'head', 'accountant'];
const orgType = u => { const o = u && orgById(u.orgId); return o && ORG_TYPES.includes(o.type) ? o.type : 'all'; };
const REQ_ROLES = ['admin', 'head', 'executor', 'worker'];
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
const SECTIONS = { works: ['works'], prodscr: [], stock: ['stock', 'inc', 'wo', 'pay', 'checks', 'trips'], cps: [], staff: [], staffp: [], plan: [], dt: [], devs: [], notes: ['task', 'shared'], transport: ['cars', 'parts'], refs: ['list', 'draw', 'vault', 'labels', 'netshare', 'ssh', 'mods'] };
const SECTION_KEYS = Object.entries(SECTIONS).flatMap(([k, subs]) => [k, ...subs.map(x => k + ':' + x)]);
const cleanHide = a => [...new Set((Array.isArray(a) ? a : []).filter(k => SECTION_KEYS.includes(k)))];
// what is hidden for a user: hidden for the organization or for him; a hidden tab hides its sub-tabs
const hiddenFor = u => { const o = u && orgById(u.orgId); return [...new Set([...((o && o.hide) || []), ...((u && u.hide) || [])])]; };
const sees = (u, key) => { const H = hiddenFor(u), top = key.split(':')[0]; return !H.includes(key) && !H.includes(top); };
// a request is seen by its author, the executors («Исполнитель» sees all, new ones too), the administrator and the manager
const REQ_EXEC = u => HEAD(u) || (u && u.role === 'executor');
const reqSees = (u, r) => REQ_EXEC(u) || r.by === u.id || r.assignee === u.id;
/* the equipment of a requests organization: the administrator keeps the list; an item is general (everyone) or fixed to chosen users */
const eqSees = (u, e) => REQ_EXEC(u) || !(e.owners || []).length || (e.owners || []).includes(u.id);
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
    for (const o of Object.values(db.tOrders || {})) for (const f of o.docs || []) add(f.id, `Заказ № ${o.no || ''}`);
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
/* «SSH-консоль»: the manager or the administrator keeps his servers and commands (encrypted, only for himself) and connects;
   the server of the program runs the OpenSSH client («ssh -tt»), its output goes to the browser as a stream (SSE), the keys come back by POST */
const SSH_BIN = process.env.SSH_BIN || 'ssh';
const SSH_SESS = new Map();   // sid → a running connection
try { for (const f of fs.readdirSync(path.join(DATA_DIR, 'ssh-tmp'))) fs.unlinkSync(path.join(DATA_DIR, 'ssh-tmp', f)); } catch {}
const sshTmp = () => { const d = path.join(DATA_DIR, 'ssh-tmp'); fs.mkdirSync(d, { recursive: true, mode: 0o700 }); return d; };
const sshHome = () => { const d = path.join(DATA_DIR, 'ssh-home'); fs.mkdirSync(path.join(d, '.ssh'), { recursive: true, mode: 0o700 }); return d; };
function sshEmit(S, ev, data) { const msg = (ev ? `event: ${ev}\n` : '') + (ev ? '' : `id: ${S.seq}\n`) + `data: ${data}\n\n`; for (const r of S.subs) { try { r.write(msg); } catch {} } }
function sshPush(S, buf) {
  S.seq++; const b64 = buf.toString('base64'); S.chunks.push([S.seq, b64]); S.size += b64.length;
  while (S.size > 2e6 && S.chunks.length > 1) S.size -= S.chunks.shift()[1].length;   // the last ~1.5 MB of the output for a reconnect
  sshEmit(S, null, b64);
}
function sshCleanup(S) { for (const f of S.tmp) { try { fs.unlinkSync(f); } catch {} } S.tmp = []; }
function sshClose(S, why) { if (S.closed) return; S.why = why || ''; sshCleanup(S); try { process.kill(-S.proc.pid, 'SIGTERM'); } catch { try { S.proc.kill('SIGTERM'); } catch {} } setTimeout(() => { if (!S.closed) { try { process.kill(-S.proc.pid, 'SIGKILL'); } catch {} } }, 3000).unref(); }
setInterval(() => { const now = Date.now();
  for (const [sid, S] of SSH_SESS) {
    if (!S.closed && !S.subs.size && now - S.last > 30 * 60e3) sshClose(S, 'нет активности 30 минут');
    if (S.closed && now - S.closedAt > 10 * 60e3) SSH_SESS.delete(sid);
  } }, 60e3).unref();
function sshStart(user, srv, cols, rows) {
  const host = String(srv.host || '').trim(), login = String(srv.user || '').trim(), port = Number(srv.port) || 22;
  if (!/^[A-Za-z0-9.:\[\]_-]+$/.test(host) || host.startsWith('-')) throw new Error('Неверный адрес сервера');
  if (!/^[A-Za-z0-9._@\\-]+$/.test(login) || login.startsWith('-')) throw new Error('Неверное имя пользователя');
  if (!(port >= 1 && port <= 65535)) throw new Error('Неверный порт');
  const c = Math.max(20, Math.min(400, Math.round(Number(cols) || 120))), r = Math.max(5, Math.min(200, Math.round(Number(rows) || 32)));
  const tmp = [], args = ['-tt', '-o', 'StrictHostKeyChecking=accept-new', '-o', 'UserKnownHostsFile=' + path.join(DATA_DIR, 'ssh_known_hosts'), '-o', 'ServerAliveInterval=30', '-o', 'ConnectTimeout=15', '-p', String(port)];
  const env = { PATH: process.env.PATH || '/usr/bin:/bin', HOME: sshHome(), TERM: 'xterm-256color', LANG: 'C.UTF-8' };
  if (srv.auth === 'key' && srv.key) {
    const f = path.join(sshTmp(), 'k-' + crypto.randomBytes(8).toString('hex')); fs.writeFileSync(f, String(srv.key).replace(/\r\n/g, '\n').trim() + '\n', { mode: 0o600 }); tmp.push(f);
    args.push('-i', f, '-o', 'IdentitiesOnly=yes', '-o', 'PreferredAuthentications=publickey');
    if (srv.password) { const a = path.join(sshTmp(), 'a-' + crypto.randomBytes(8).toString('hex') + '.sh'); fs.writeFileSync(a, '#!/bin/sh\nprintf \'%s\\n\' "$SED_SSH_PW"\n', { mode: 0o700 }); tmp.push(a); Object.assign(env, { SSH_ASKPASS: a, SSH_ASKPASS_REQUIRE: 'force', DISPLAY: ':0', SED_SSH_PW: String(srv.password) }); }
  } else if (srv.password) {
    // the password is given by an askpass script from the environment of this process only (it is not written to a file)
    const a = path.join(sshTmp(), 'a-' + crypto.randomBytes(8).toString('hex') + '.sh'); fs.writeFileSync(a, '#!/bin/sh\nprintf \'%s\\n\' "$SED_SSH_PW"\n', { mode: 0o700 }); tmp.push(a);
    Object.assign(env, { SSH_ASKPASS: a, SSH_ASKPASS_REQUIRE: 'force', DISPLAY: ':0', SED_SSH_PW: String(srv.password) });
    args.push('-o', 'PreferredAuthentications=password,keyboard-interactive', '-o', 'NumberOfPasswordPrompts=1', '-o', 'PubkeyAuthentication=no');
  }
  args.push('--', login + '@' + host);
  // Linux and other Unix servers: the size of the terminal of the browser (ssh without a local terminal cannot pass it)
  if (srv.os !== 'other') args.push(`stty cols ${c} rows ${r} 2>/dev/null; exec "\${SHELL:-/bin/sh}" -l`);
  const proc = spawn(SSH_BIN, args, { env, stdio: ['pipe', 'pipe', 'pipe'], detached: true });
  const sid = crypto.randomBytes(12).toString('base64url');
  const S = { sid, uid: user.id, orgId: user.orgId, srvId: srv.id || '', name: srv.name || host, host, proc, chunks: [], size: 0, seq: 0, subs: new Set(), last: Date.now(), closed: false, code: null, tmp, at: new Date().toISOString() };
  SSH_SESS.set(sid, S);
  proc.stdout.on('data', b => sshPush(S, b)); proc.stderr.on('data', b => { if (!S.hostKey && /REMOTE HOST IDENTIFICATION HAS CHANGED|Host key verification failed/.test(b.toString())) S.hostKey = true; sshPush(S, b); });
  proc.on('error', e => { sshPush(S, Buffer.from(e.code === 'ENOENT' ? '\r\n[На сервере программы не установлен клиент SSH (OpenSSH). Установите пакет openssh-client.]\r\n' : '\r\n[Ошибка запуска ssh: ' + e.message + ']\r\n')); });
  proc.on('close', code => { S.closed = true; S.closedAt = Date.now(); S.code = code; sshCleanup(S); sshEmit(S, 'exit', JSON.stringify({ code, why: S.why || '', hostKey: !!S.hostKey, srvId: S.srvId })); for (const r of S.subs) { try { r.end(); } catch {} } S.subs.clear(); });
  // the key and the askpass script are needed only at the login
  setTimeout(() => { for (const f of S.tmp) { try { fs.unlinkSync(f); } catch {} } S.tmp = []; }, 60e3).unref();
  return S;
}
/* «Сетевая папка»: a file server in another network runs a small agent (public/netshare/) on its own 127.0.0.1 and opens a reverse SSH tunnel
   «ssh -N -R 127.0.0.1:<port>:127.0.0.1:<agent port> user@<this server>»; the program asks the agent through 127.0.0.1:<port> for the list of files.
   NETSHARE_HOST — where the tunnels end (127.0.0.1; in Docker — the address of the host), NETSHARE_PORTS — the allowed ports of the tunnels. */
const NS_HOST = process.env.NETSHARE_HOST || '127.0.0.1';
const NS_PORTS = (() => { const m = String(process.env.NETSHARE_PORTS || '20000-20999').match(/^(\d+)-(\d+)$/); return m ? [Number(m[1]), Number(m[2])] : [20000, 20999]; })();
const nsSees = (u, x) => HEAD(u) || !x.restricted || (x.viewers || []).includes(u.id);
const nsPublic = x => ({ id: x.id, name: x.name, root: x.root, port: x.port, restricted: !!x.restricted, viewers: x.viewers || [], at: x.at, by: x.by });
// a GET to the agent through the tunnel; the answer must be the JSON of the agent
function nsAgent(x, pth, q){
  return new Promise(resolve => {
    const token = (vaultDec(x.token) || {}).t || '';
    const rq = http.get({ host: NS_HOST, port: x.port, path: pth + '?' + new URLSearchParams(q).toString(), headers: { 'X-Token': token, Host: 'localhost' }, timeout: 10000 }, r => {
      const ch = []; let n = 0;
      r.on('data', c => { n += c.length; if (n > 8e6) { rq.destroy(); return resolve({ ok: false, error: 'Слишком большой ответ агента' }); } ch.push(c); });
      r.on('end', () => { try { const j = JSON.parse(Buffer.concat(ch).toString('utf8')); resolve(j && typeof j === 'object' ? j : { ok: false, error: 'Неверный ответ агента' }); } catch { resolve({ ok: false, error: 'Ответ не похож на агента «Сетевая папка» — проверьте порт' }); } });
    });
    rq.on('timeout', () => { rq.destroy(); resolve({ ok: false, error: 'Агент не ответил за 10 секунд' }); });
    rq.on('error', e => resolve({ ok: false, offline: true, error: e.code === 'ECONNREFUSED' ? 'Нет подключения: туннель не открыт или агент не запущен' : 'Нет подключения: ' + e.code }));
  });
}
/* «Личное хранилище»: the entries of a user are kept encrypted (AES-256-GCM) with a key derived from secret.key */
const VAULT_KEY = crypto.createHash('sha256').update(Buffer.concat([secret, Buffer.from('sed-vault-v1')])).digest();
const vaultEnc = obj => { const iv = crypto.randomBytes(12), c = crypto.createCipheriv('aes-256-gcm', VAULT_KEY, iv); const e = Buffer.concat([c.update(JSON.stringify(obj), 'utf8'), c.final()]); return 'v1:' + Buffer.concat([iv, c.getAuthTag(), e]).toString('base64'); };
const vaultDec = s => { try { const b = Buffer.from(String(s).slice(3), 'base64'), d = crypto.createDecipheriv('aes-256-gcm', VAULT_KEY, b.subarray(0, 12)); d.setAuthTag(b.subarray(12, 28)); return JSON.parse(Buffer.concat([d.update(b.subarray(28)), d.final()]).toString('utf8')); } catch { return null; } };

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
/* the system administrator «as the administrator of the main organization» (the switch in his header): while it is on, he is seen
   as an ordinary administrator of his organization — the data, the users, every section; the changes he makes go to his own record */
const actingViews = new WeakMap();
const asActing = u => {
  if (!u || !u.sys || !u.actAsOrg) return u;
  let v = actingViews.get(u);
  if (!v) { v = new Proxy(u, { get: (t, k) => k === 'sys' ? false : k === 'role' ? 'admin' : k === 'actingSys' ? true : t[k] }); actingViews.set(u, v); }
  return v;
};
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
  return asActing(u);
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
    return send(res, 200, meInfo(asActing(u)), { 'Set-Cookie': cookie(req, makeSession(u), SESSION_DAYS * 86400) });
  }
  // a request for a trial access — without a session; a hidden field catches robots, an address may send 5 an hour
  if (p[1] === 'trial' && m === 'POST') {
    const b = await readJsonBody(req) || {}, t = (v, n) => String(v ?? '').trim().slice(0, n), key = 'trial|' + clientIp(req), now = Date.now();
    const a = (attempts.get(key) || []).filter(x => now - x < 3600e3); attempts.set(key, a);
    if (a.length >= 5) return fail(res, 429, 'Слишком много запросов с этого адреса. Попробуйте через час.');
    if (t(b.website, 200)) return send(res, 200, { ok: true });
    const x = { org: t(b.org, 200), type: TRIAL_TYPES[b.type] ? b.type : '', name: t(b.name, 200), phone: t(b.phone, 40), email: t(b.email, 200).toLowerCase(), comment: t(b.comment, 2000) };
    if (!x.org) return fail(res, 400, 'Укажите название организации');
    if (!x.type) return fail(res, 400, 'Выберите тип системы');
    if (!x.name) return fail(res, 400, 'Укажите имя контактного лица');
    if (x.phone.replace(/\D/g, '').length < 6) return fail(res, 400, 'Укажите номер телефона');
    if (!/^[^@\s]+@[^@\s]+\.[^@\s]+$/.test(x.email)) return fail(res, 400, 'Укажите почту, например name@company.ru');
    const L = trialsDb(); if (L.length >= 5000) L.splice(0, L.length - 4000);
    L.push({ id: newId(), at: new Date().toISOString(), ...x, ip: clientIp(req), status: 'new' }); saveTrials(); a.push(now);
    return send(res, 200, { ok: true });
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
    return send(res, 200, meInfo(asActing(u)), { 'Set-Cookie': cookie(req, makeSession(u), SESSION_DAYS * 86400) });
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
  if (p[1] === 'chat') return chatApi(req, res, p, m, user);
  // the switch of the system administrator: «Интерфейс основной организации» ↔ «Администратор системы»
  if (p[1] === 'sys-mode' && m === 'POST') {
    const real = users.find(x => x.id === user.id);
    if (!real || !real.sys) return fail(res, 403, 'Переключение есть только у администратора системы');
    const b = await readJsonBody(req) || {}; real.actAsOrg = !!b.org; saveUsers();
    return send(res, 200, meInfo(asActing(real)));
  }
  if (p[1] === 'prefs' && m === 'PUT') { user.prefs = cleanPrefs(await readJsonBody(req) || {}); saveUsers(); return send(res, 200, { ok: true, prefs: user.prefs }); }
  // the system administrator manages organizations, backups and the server, not the work of an organization
  if (p[1] === 'presentation.pdf' && m === 'GET') {
    if (!user.sys) return fail(res, 403, 'Презентацию скачивает администратор системы');
    let st; try { st = fs.statSync(PRESENTATION_FILE); } catch { return fail(res, 404, 'Файл презентации не найден на сервере'); }
    const name = encodeURIComponent('Управление предприятием — презентация.pdf');
    res.writeHead(200, { ...SEC_HEADERS, 'Content-Type': 'application/pdf', 'Content-Length': st.size, 'Content-Disposition': `attachment; filename="presentation.pdf"; filename*=UTF-8''${name}`, 'Cache-Control': 'private, no-cache' });
    return fs.createReadStream(PRESENTATION_FILE).pipe(res);
  }
  if (user.sys && !['rev', 'password', 'trials'].includes(p[1])) return fail(res, 403, 'Администратор системы управляет организациями. Для работы с данными войдите администратором организации');
  // «Сотрудник» and «Подрядчик» see and change only the work given to them
  // in the requests system an employee makes and does requests and attaches files to them
  if ((FIELD(user) || user.role === 'executor') && !['rev', 'data', 'password', 'jobs', 'overtime', 'checks', 'trips', 'tor', 'vault', 'netshare', 'snmap', 'cal'].includes(p[1]) && !(orgType(user) === 'requests' && ['requests', 'files'].includes(p[1]))
    && !(p[1] === 'devs' || p[1] === 'notes' || p[1] === 'files')) return fail(res, 403, 'Недостаточно прав');
  if (p[1] === 'users') {
    if (user.role !== 'admin') return fail(res, 403, 'Управлять пользователями может только администратор');
    const target = p[2] && orgUsers().find(u => u.id === p[2]);
    if (m === 'GET' && !p[2]) return send(res, 200, orgUsers().map(adminUser));
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req);
      const err = validateUser(b, true); if (err) return fail(res, 400, err);
      if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
      if (orgType(user) === 'ip' && !IP_ROLES.includes(b.role)) return fail(res, 400, 'В организации «ИП / самозанятый» роли: администратор, руководитель, бухгалтер');
      if (orgType(user) === 'requests' ? !REQ_ROLES.includes(b.role) : b.role === 'executor') return fail(res, 400, orgType(user) === 'requests' ? 'В системе заявок роли: администратор, руководитель, исполнитель, пользователь' : 'Роль «Исполнитель» есть только в системе заявок');
      if (b.role === 'contractor' && !/^\d{4}-\d{2}-\d{2}$/.test(String(b.accessUntil || ''))) return fail(res, 400, 'Для подрядчика укажите, до какой даты у него доступ');
      const nu = addUser(String(b.login), b.role, String(b.name).trim(), String(b.password), user.orgId);
      if (b.role === 'contractor') nu.accessUntil = String(b.accessUntil);
      // made from a counterparty «Подрядчик» — the link is kept (the card of the counterparty lists its users)
      if (b.cpId && db.counterparties[b.cpId]) { nu.cpId = String(b.cpId); saveUsers(); }
      nu.hide = cleanHide(b.hide); saveUsers();
      return send(res, 200, adminUser(nu));
    }
    if (!target) return fail(res, 404, 'Пользователь не найден');
    if (target.sys && !user.sys) return fail(res, 403, 'Учётную запись администратора системы меняет только он сам');
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      if (b.role !== undefined) {
        if (!ROLES[b.role]) return fail(res, 400, 'Неизвестная роль');
        if (orgType(user) === 'ip' && !IP_ROLES.includes(b.role)) return fail(res, 400, 'В организации «ИП / самозанятый» роли: администратор, руководитель, бухгалтер');
        if (orgType(user) === 'requests' ? !REQ_ROLES.includes(b.role) : b.role === 'executor') return fail(res, 400, orgType(user) === 'requests' ? 'В системе заявок роли: администратор, руководитель, исполнитель, пользователь' : 'Роль «Исполнитель» есть только в системе заявок');
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
  if (p[1] === 'rev' && m === 'GET') return send(res, 200, { rev: db.rev, version: APP_VERSION, chat: chatUnread(user), ...(user.sys ? { trials: trialsNew() } : {}) });
  // «Запросы доступа»: the system administrator sees the requests, marks them (new / done / rejected), writes a note, deletes
  if (p[1] === 'trials') {
    if (!user.sys) return fail(res, 403, 'Запросы доступа видит администратор системы');
    const L = trialsDb();
    if (m === 'GET' && !p[2]) return send(res, 200, { list: L.slice().reverse(), types: TRIAL_TYPES });
    const x = p[2] && L.find(e => e.id === p[2]); if (!x) return fail(res, 404, 'Запрос не найден — обновите страницу');
    if (m === 'PATCH') { const b = await readJsonBody(req) || {};
      if (b.status !== undefined) { if (!['new', 'done', 'rejected'].includes(b.status)) return fail(res, 400, 'Неизвестный статус'); x.status = b.status; x.handledAt = new Date().toISOString(); x.handledBy = user.id; }
      if (b.note !== undefined) x.note = String(b.note).slice(0, 2000);
      if (b.orgId !== undefined) x.orgId = String(b.orgId).slice(0, 40);
      saveTrials(); return send(res, 200, { ok: true, item: x }); }
    if (m === 'DELETE') { trials = L.filter(e => e !== x); saveTrials(); return send(res, 200, { ok: true }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'data' && m === 'GET') {
    // points written into works before they were marked on the map get the mark
    if (db.dt && Array.isArray(db.dt.points) && db.dt.points.some(x => x.need)) {
      const nd = new Map(db.dt.points.filter(x => x.need).map(x => [x.no, x.need])); let ch = false;
      for (const j of Object.values(db.jobs || {})) for (const pl of j.places || []) if (pl.dtNo && !pl.need && nd.has(pl.dtNo)) { pl.need = nd.get(pl.dtNo); ch = true; }
      if (ch) saveDb();
    }
    // the order of a production work follows the status of the work (they could part before)
    { let ch = false; for (const j of Object.values(db.jobs || {})) { const o = j.orderId && db.orders[j.orderId]; if (o && o.status !== jobToOrderSt(j.status)) { o.status = jobToOrderSt(j.status); ch = true; } } if (ch) saveDb(); }
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
      // the equipment the user sees, with the history of its problems (from all requests: what happened and what was done)
      const RQ = Object.values(db.requests || {});
      out.reqEquip = (Array.isArray(db.reqEquip) ? db.reqEquip : []).filter(e => eqSees(user, e)).map(e => ({ ...e,
        hist: RQ.filter(r => r.eqId === e.id).sort((a, b) => String(b.at).localeCompare(String(a.at))).map(r => ({ no: r.no, at: r.at, title: r.title, text: r.text, status: r.status, by: r.by, assignee: r.assignee || null, takenAt: r.takenAt || null, doneAt: r.doneAt || null, doneBy: r.doneBy || null, doneNote: r.doneNote || '', repl: r.repl || [] })) }));
      out.devReadings = Array.isArray(db.devReadings) ? db.devReadings.slice(-10).reverse() : [];
    }
    out.devs = sees(user, 'devs') ? Object.entries(db.devs || {}).map(([id, d]) => ({ id, ...d })).filter(d => devSees(user, d)) : [];
    out.labels = FIELD(user) || !sees(user, 'refs:labels') ? [] : Object.entries(db.labels || {}).map(([id, t]) => ({ id, ...t }));
    // printed serial numbers — the page warns about a repeat while the number is typed
    if (!FIELD(user) && out.labels.length) { const S = labelSerials(), SC = labelScans(); out.labelSerials = Object.fromEntries(Object.entries(S).slice(-20000).map(([k, v]) => [k, [v.l, v.at, v.by]]));
      out.labelScans = Object.fromEntries(Object.entries(SC).slice(-20000).map(([k, v]) => [k, [v.l, v.at, v.by, v.serial || '']])); }
    out.receipts = FIELD(user) || !sees(user, 'stock:inc') ? [] : Object.entries(db.receipts || {}).map(([id, r]) => ({ id, ...r }));
    if (FIELD(user)) { out.meta = {}; out.staff = []; }
    // irregular working hours: an employee sees his own entries, a manager sees everyone's
    out.overtime = (Array.isArray(db.overtime) ? db.overtime : []).filter(x => HEAD(user) || x.by === user.id);
    // the marks of the manager (sick leave, vacation, late, left early, absence) and the working schedule
    out.staffMarks = (Array.isArray(db.staffMarks) ? db.staffMarks : []).filter(x => HEAD(user) || x.user === user.id);
    // the monthly ratings 1–5 the manager gives: a manager sees all, an employee only his own
    out.staffRatings = (Array.isArray(db.staffRatings) ? db.staffRatings : []).filter(x => HEAD(user) || x.user === user.id);
    out.workCal = workCalOf();
    // «Справочники»: a manager sees all; the others — the open ones and those he is chosen for
    // «Сетевая папка»: the connections the user may browse (without the key of the agent)
    if (orgType(user) !== 'requests' && sees(user, 'refs:netshare')) out.netshares = (Array.isArray(db.netshares) ? db.netshares : []).filter(x => nsSees(user, x)).map(nsPublic);
    if (orgType(user) !== 'requests' && sees(user, 'refs:list')) out.refs = (Array.isArray(db.refs) ? db.refs : []).filter(r => HEAD(user) || !r.restricted || (r.viewers || []).includes(user.id));
    // «Загрузить чек»: an employee sees his own receipts, a manager and the accountant see everyone's; the vehicles to choose for a refuelling
    if (orgType(user) !== 'requests') {
      // «Учётка → Чеки / Путевые листы» can be hidden for an office user; field staff and a transport organization always have their own
      const ckOff = k => !FIELD(user) && orgType(user) !== 'transport' && !sees(user, 'stock:' + k);
      out.checks = ckOff('checks') ? [] : (Array.isArray(db.checks) ? db.checks : []).filter(x => HEAD(user) || user.role === 'accountant' || x.by === user.id);
      out.trips = ckOff('trips') ? [] : (Array.isArray(db.trips) ? db.trips : []).filter(x => HEAD(user) || user.role === 'accountant' || x.by === user.id);
      // a transport organization: the orders (rent of special vehicles, cargo); a driver gets his own
      if (orgType(user) === 'transport') {
        out.tOrders = Object.entries(db.tOrders || {}).map(([id, x]) => ({ id, ...x })).filter(x => HEAD(user) || user.role === 'accountant' || x.driverId === user.id);
      }
      out.vehBrief = Object.entries(db.vehicles || {}).map(([id, v]) => ({ id, name: v.name, plate: v.plate || '' })).sort((a, b) => a.name.localeCompare(b.name, 'ru'));
    }
    // «Транспорт»: the vehicles of the company with maintenance and documents, and the spare parts — for managers
    if (HEAD(user) && orgType(user) !== 'requests') {
      out.vehicles = sees(user, 'transport:cars') || sees(user, 'transport:parts') ? Object.entries(db.vehicles || {}).map(([id, v]) => ({ id, ...v })) : [];
      out.parts = sees(user, 'transport:parts') ? (Array.isArray(db.parts) ? db.parts : []) : [];
    }
    out.jobGroups = Array.isArray(db.jobGroups) ? db.jobGroups : [];
    // «Экран производства» for an employee or a contractor (they get only their own works): the productions to view — a short copy, nothing to change
    if (FIELD(user) && sees(user, 'prodscr')) {
      const J = listOf('jobs').filter(j => ['prod', 'both'].includes(j.kind) && j.orderId && db.orders[j.orderId]);
      out.prodScr = { jobs: J.map(j => { const P = j.places || [], c = P.filter(x => x.doneAt).length;
          return { id: j.id, no: j.no, title: j.title, kind: j.kind, status: j.status, due: j.due || '', priority: !!j.priority, groupId: j.groupId || null, orderId: j.orderId, custName: (db.counterparties[j.customerId] || {}).name || '', places: [], progress: P.length ? Math.round(c / P.length * 100) : j.progress ?? null }; }),
        orders: J.map(j => { const o = db.orders[j.orderId]; return { id: j.orderId, number: o.number, deadline: o.deadline || '', products: (o.products || []).map(p => ({ id: p.id, name: p.name, qty: p.qty, unit: p.unit, note: p.note, components: p.components || [], files: p.files || [] })) }; }) };
    }
    if (FIELD(user)) out.notes = (db.notes || []).filter(n => n.type === 'shared' && n.assignee === user.id);
    else if (sees(user, 'notes')) out.notes = (db.notes || []).filter(n => n.by === user.id || (n.type === 'shared' && ((n.share || []).includes(user.id) || n.assignee === user.id)));
    return send(res, 200, out);
  }
  // hidden sections: their data is not given and their actions are refused
  { const need = { devs: 'devs', labels: 'refs:labels', receipts: 'stock:inc', notes: 'notes', 'stock-acct': 'stock:stock' }[p[1]];
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
        // not sent (an older page) — the saved value stays; it was reset to 0 on every save before
        rot: b.rot === undefined ? (Number(old.rot) || 0) : [0, 90, 180, 270].includes(Number(b.rot)) ? Number(b.rot) : 0,
        flip: b.flip === undefined ? !!old.flip : !!b.flip,
        scale: b.scale === undefined ? (Number(old.scale) || 100) : num(b.scale, 30, 200, 100),
        sx: b.sx === undefined ? (Number(old.sx) || 100) : num(b.sx, 30, 200, 100),
        sy: b.sy === undefined ? (Number(old.sy) || 100) : num(b.sy, 30, 200, 100),
        dx: b.dx === undefined ? (Number(old.dx) || 0) : num(b.dx, -30, 30, 0), dy: b.dy === undefined ? (Number(old.dy) || 0) : num(b.dy, -30, 30, 0),
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
      const eq = b.eqId ? (db.reqEquip || []).find(e => e.id === b.eqId) : null;
      if (b.eqId && (!eq || !eqSees(user, eq))) return fail(res, 400, 'Оборудование не найдено');
      const id = newId(), no = Math.max(0, ...Object.values(R).map(r => r.no || 0)) + 1;
      R[id] = { no, title, text, eqId: eq ? eq.id : null, system: b.system || (eq && eq.system) || '', due: /^\d{4}-\d{2}-\d{2}$/.test(b.due || '') ? b.due : '', urgent: !!b.urgent,
        assignee: b.assignee || null, files: cleanFiles(b.files), status: 'new', by: user.id, at: now, comments: [], history: [{ at: now, by: user.id, act: 'created', to: b.assignee || null }] };
      saveDb();
      reqNotify(`Новая заявка №${no}${eq ? ' · ' + eq.name + (eq.invNo ? ' (инв. ' + eq.invNo + ')' : '') : ''}${R[id].system ? ' (' + UPR.SYSTEMS[R[id].system] + ')' : ''}.\n${title}${text && text !== title ? '\n' + text : ''}\nЗаявитель: ${user.name}${R[id].files.length ? `\nФото и файлов: ${R[id].files.length}` : ''}`);
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
        if (!REQ_EXEC(user)) return fail(res, 403, 'Приступить к выполнению может исполнитель');
        if (r.status !== 'new') return fail(res, 409, 'Заявка уже в работе или закрыта');
        r.assignee = user.id;
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
        if (b.eqId !== undefined) { const eq = b.eqId ? (db.reqEquip || []).find(e => e.id === b.eqId) : null; if (b.eqId && !eq) return fail(res, 400, 'Оборудование не найдено'); r.eqId = eq ? eq.id : null; }
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
  /* «SSH-консоль»: servers and commands of the user (encrypted), connections */
  if (p[1] === 'ssh') {
    if (orgType(user) === 'requests' || !HEAD(user) || !sees(user, 'refs:ssh')) return fail(res, 403, 'SSH-консоль доступна руководителю и администратору');
    if (!db.sshVault || typeof db.sshVault !== 'object') db.sshVault = {};
    const V = db.sshVault[user.id] = db.sshVault[user.id] || { servers: [], cmds: [] }, now = new Date().toISOString(), t = (v, n) => String(v ?? '').slice(0, n);
    const srvOf = x => ({ id: x.id, at: x.at, ...(vaultDec(x.data) || {}) });
    // «Кто ещё видит»: the owner chooses the other users of the SSH console; they connect and run commands, but cannot change them or see the password or key
    const canSsh = u => u && !u.sys && !u.blocked && HEAD(u) && sees(u, 'refs:ssh');
    const cleanShare = a => [...new Set((Array.isArray(a) ? a : []).map(String))].filter(id => id !== user.id && canSsh(orgUsers().find(u => u.id === id)));
    const meta = (x, owner) => owner === user.id ? { share: Array.isArray(x.share) ? x.share : [] } : { shared: true, owner };
    const srvPublic = (x, owner = user.id) => { const v = srvOf(x); return { id: v.id, name: v.name, host: v.host, port: v.port, user: v.user, auth: v.auth, os: v.os, hasPassword: !!v.password, hasKey: !!v.key, ...meta(x, owner) }; };
    const cmdOf = (x, owner = user.id) => ({ id: x.id, at: x.at, ...(vaultDec(x.data) || {}), ...meta(x, owner) });
    const sharedTo = kind => Object.entries(db.sshVault).filter(([uid]) => uid !== user.id && orgUsers().some(u => u.id === uid)).flatMap(([uid, W]) => (W[kind] || []).filter(x => (x.share || []).includes(user.id)).map(x => [x, uid]));
    const mine = S => S && S.uid === user.id && S.orgId === user.orgId;
    if (m === 'GET' && !p[2]) return send(res, 200, { servers: [...V.servers.map(x => srvPublic(x)), ...sharedTo('servers').map(([x, uid]) => srvPublic(x, uid))], cmds: [...V.cmds.map(x => cmdOf(x)), ...sharedTo('cmds').map(([x, uid]) => cmdOf(x, uid))], sessions: [...SSH_SESS.values()].filter(mine).map(S => ({ sid: S.sid, name: S.name, closed: S.closed, at: S.at })) });
    if (p[2] === 'servers') {
      const x = p[3] && V.servers.find(e => e.id === p[3]);
      if (m === 'DELETE' && x) { V.servers = V.servers.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
      // «👁 Показать пароль» in the card of the server: only to the one who added it (those it is shared with never get it)
      if (m === 'GET' && p[4] === 'secret') { if (!x) return fail(res, 403, 'Пароль сервера видит только тот, кто его добавил'); return send(res, 200, { password: srvOf(x).password || '' }); }
      // «Забыть ключ сервера»: after a reinstall the server has a new host key and ssh refuses it; the owner removes the remembered one,
      // the next connection remembers the new key
      if (m === 'POST' && p[4] === 'forget-key') {
        if (!x) return fail(res, 403, 'Забыть ключ может только тот, кто добавил сервер');
        const v = srvOf(x), host = String(v.host || '').replace(/^\[|\]$/g, ''), port = Number(v.port) || 22, file = path.join(DATA_DIR, 'ssh_known_hosts');
        if (!/^[A-Za-z0-9.:_-]+$/.test(host) || host.startsWith('-')) return fail(res, 400, 'Неверный адрес сервера');
        if (!fs.existsSync(file)) return send(res, 200, { ok: true, removed: 0 });
        const names = [host, `[${host}]:${port}`], before = fs.readFileSync(file, 'utf8');
        const run = n => new Promise(ok => { const k = spawn(process.env.SSH_KEYGEN_BIN || 'ssh-keygen', ['-f', file, '-R', n], { stdio: 'ignore' }); k.on('error', () => ok(false)); k.on('close', c => ok(c === 0)); });
        let tool = true; for (const n of names) tool = (await run(n)) && tool;
        // without ssh-keygen: the plain (not hashed) lines of this host
        if (!tool) { const L = fs.readFileSync(file, 'utf8').split('\n'); fs.writeFileSync(file, L.filter(l => !l.trim() || l.startsWith('#') || !l.split(/\s+/)[0].split(',').some(h => names.includes(h))).join('\n')); }
        try { fs.unlinkSync(file + '.old'); } catch {}
        const after = fs.readFileSync(file, 'utf8'), removed = before.split('\n').filter(Boolean).length - after.split('\n').filter(Boolean).length;
        return send(res, 200, { ok: true, removed });
      }
      if (m === 'POST' || m === 'PUT') {
        const b = await readJsonBody(req), old = x ? srvOf(x) : {};
        const v = { name: t(b.name, 200).trim(), host: t(b.host, 255).trim(), port: Number(b.port) || 22, user: t(b.user, 100).trim(), auth: b.auth === 'key' ? 'key' : 'password', os: b.os === 'other' ? 'other' : 'linux',
          password: b.password != null && b.password !== '' ? t(b.password, 500) : b.clearPassword ? '' : old.password || '', key: b.key != null && String(b.key).trim() ? t(b.key, 20000) : old.key || '' };
        if (!v.host) return fail(res, 400, 'Укажите адрес сервера'); if (!/^[A-Za-z0-9.:\[\]_-]+$/.test(v.host) || v.host.startsWith('-')) return fail(res, 400, 'Адрес сервера: только буквы, цифры, точки, двоеточия и дефисы');
        if (!v.user) return fail(res, 400, 'Укажите пользователя'); if (!/^[A-Za-z0-9._@\\-]+$/.test(v.user) || v.user.startsWith('-')) return fail(res, 400, 'Пользователь: только латиница, цифры, точка, дефис, @ и \\');
        if (!(v.port >= 1 && v.port <= 65535)) return fail(res, 400, 'Порт — от 1 до 65535');
        if (v.auth === 'key' && !v.key) return fail(res, 400, 'Вставьте закрытый ключ');
        if (!v.name) v.name = v.user + '@' + v.host;
        if (p[3] && !x) return fail(res, 403, 'Этот сервер добавил другой пользователь — изменить его может только он');
        if (x) { x.data = vaultEnc(v); x.updatedAt = now; } else { if (V.servers.length >= 200) return fail(res, 400, 'Слишком много серверов'); V.servers.push({ id: newId(), at: now, data: vaultEnc(v) }); }
        const it = x || V.servers[V.servers.length - 1]; if (b.share !== undefined) it.share = cleanShare(b.share);
        saveDb(); return send(res, 200, { ok: true, server: srvPublic(it), rev: db.rev });
      }
      return fail(res, 404, 'Сервер не найден');
    }
    if (p[2] === 'cmds') {
      const x = p[3] && V.cmds.find(e => e.id === p[3]);
      if (m === 'DELETE' && x) { V.cmds = V.cmds.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
      if (m === 'POST' || m === 'PUT') {
        const b = await readJsonBody(req), v = { title: t(b.title, 200).trim(), cmd: t(b.cmd, 10000), serverId: t(b.serverId, 40) || '' };
        if (!v.cmd.trim()) return fail(res, 400, 'Напишите команду'); if (!v.title) v.title = v.cmd.split('\n')[0].slice(0, 80);
        if (p[3] && !x) return fail(res, 403, 'Эту команду добавил другой пользователь — изменить её может только он');
        if (x) { x.data = vaultEnc(v); x.updatedAt = now; } else { if (V.cmds.length >= 500) return fail(res, 400, 'Слишком много команд'); V.cmds.push({ id: newId(), at: now, data: vaultEnc(v) }); }
        const it = x || V.cmds[V.cmds.length - 1]; if (b.share !== undefined) it.share = cleanShare(b.share);
        saveDb(); return send(res, 200, { ok: true, cmd: cmdOf(it), rev: db.rev });
      }
      return fail(res, 404, 'Команда не найдена');
    }
    if (p[2] === 'connect' && m === 'POST') {
      const b = await readJsonBody(req), x = V.servers.find(e => e.id === b.serverId) || sharedTo('servers').map(([e]) => e).find(e => e.id === b.serverId); if (!x) return fail(res, 404, 'Сервер не найден');
      if ([...SSH_SESS.values()].filter(S => mine(S) && !S.closed).length >= 5) return fail(res, 400, 'Открыто уже 5 подключений — закройте лишние');
      try { const S = sshStart(user, srvOf(x), b.cols, b.rows); return send(res, 200, { ok: true, sid: S.sid, name: S.name }); } catch (e) { return fail(res, 400, e.message); }
    }
    if (p[2] === 's' && p[3]) {
      const S = SSH_SESS.get(p[3]); if (!mine(S)) return fail(res, 404, 'Подключение не найдено — подключитесь заново');
      if (p[4] === 'stream' && m === 'GET') {
        res.writeHead(200, { 'Content-Type': 'text/event-stream; charset=utf-8', 'Cache-Control': 'no-store', 'X-Accel-Buffering': 'no', Connection: 'keep-alive' });
        const since = Number(req.headers['last-event-id'] || url.searchParams.get('since') || 0);
        res.write('retry: 2000\n\n'); for (const [i, b64] of S.chunks) if (i > since) res.write(`id: ${i}\ndata: ${b64}\n\n`);
        if (S.closed) { res.write(`event: exit\ndata: ${JSON.stringify({ code: S.code, why: S.why || '', hostKey: !!S.hostKey, srvId: S.srvId })}\n\n`); return res.end(); }
        S.subs.add(res); S.last = Date.now();
        const ping = setInterval(() => { try { res.write(': ping\n\n'); } catch {} }, 25e3);
        req.on('close', () => { clearInterval(ping); S.subs.delete(res); S.last = Date.now(); });
        return;
      }
      if (p[4] === 'input' && m === 'POST') { const b = await readJsonBody(req); if (S.closed) return fail(res, 409, 'Соединение закрыто'); const d = String(b.d ?? ''); if (d.length > 100000) return fail(res, 400, 'Слишком много текста за раз'); S.proc.stdin.write(d); S.last = Date.now(); return send(res, 200, { ok: true }); }
      if (p[4] === 'close' && m === 'POST') { sshClose(S, 'закрыто пользователем'); if (S.closed) SSH_SESS.delete(S.sid); return send(res, 200, { ok: true }); }
    }
    return fail(res, 404, 'Не найдено');
  }
  /* «Сетевая папка»: the administrator and the manager set up the connections; the chosen users browse the tree of folders */
  if (p[1] === 'netshare') {
    if (orgType(user) === 'requests' || !sees(user, 'refs:netshare')) return fail(res, 403, 'Этот раздел для вас закрыт');
    if (!Array.isArray(db.netshares)) db.netshares = [];
    const N = db.netshares, txt = (v, n) => String(v ?? '').trim().slice(0, n);
    const clean = (b, old) => {
      const name = txt(b.name, 200); if (!name) return 'Напишите название подключения';
      const root = txt(b.root, 500); if (!root) return 'Укажите диск или папку на сервере, например D:\\ или /srv/share';
      const port = Number(b.port); if (!Number.isInteger(port) || port < NS_PORTS[0] || port > NS_PORTS[1]) return `Порт туннеля — от ${NS_PORTS[0]} до ${NS_PORTS[1]}`;
      if (N.some(e => e.port === port && e !== old)) return 'Этот порт уже занят другим подключением';
      const viewers = [...new Set((Array.isArray(b.viewers) ? b.viewers : []).filter(id => orgUsers().some(u => u.id === id && !u.sys)))];
      return { name, root, port, restricted: !!b.restricted, viewers };
    };
    if (m === 'GET' && !p[2]) return send(res, 200, N.filter(x => nsSees(user, x)).map(nsPublic));
    if (m === 'POST' && !p[2]) {
      if (!HEAD(user)) return fail(res, 403, 'Подключения настраивает руководитель или администратор');
      const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v);
      const t = crypto.randomBytes(24).toString('base64url'), x = { id: newId(), ...v, token: vaultEnc({ t }), at: new Date().toISOString(), by: user.id };
      N.push(x); saveDb(); return send(res, 200, { ok: true, share: nsPublic(x), token: t, rev: db.rev });
    }
    const x = p[2] && N.find(e => e.id === p[2]);
    if (!x || !nsSees(user, x)) return fail(res, 404, 'Подключение не найдено — обновите страницу');
    if (p[3] === 'list' && m === 'GET') {
      const sub = String(url.searchParams.get('path') || '').slice(0, 2000);
      if (sub.split(/[\\/]/).includes('..')) return fail(res, 400, 'Недопустимый путь');
      const r = await nsAgent(x, '/list', { root: x.root, path: sub });
      if (!r.ok) return fail(res, r.offline ? 502 : 400, r.error || 'Агент вернул ошибку');
      const entries = (Array.isArray(r.entries) ? r.entries : []).slice(0, 5000).map(e => ({ name: String(e.name || '').slice(0, 500), dir: !!e.dir, size: Number.isFinite(e.size) ? e.size : null, mtime: typeof e.mtime === 'string' ? e.mtime.slice(0, 40) : null }));
      return send(res, 200, { ok: true, path: sub, total: Number(r.total) || entries.length, entries });
    }
    if (p[3] === 'ping' && m === 'GET') { const r = await nsAgent(x, '/ping', {}); return send(res, 200, { ok: !!r.ok && r.agent === 'sed-netshare', host: r.ok ? String(r.host || '').slice(0, 100) : '', platform: r.ok ? String(r.platform || '').slice(0, 20) : '', error: r.ok ? '' : r.error }); }
    if (!HEAD(user)) return fail(res, 403, 'Подключения настраивает руководитель или администратор');
    if (p[3] === 'token' && m === 'GET') return send(res, 200, { token: (vaultDec(x.token) || {}).t || '' });
    if (p[3] === 'token' && m === 'POST') { const t = crypto.randomBytes(24).toString('base64url'); x.token = vaultEnc({ t }); saveDb(); return send(res, 200, { ok: true, token: t, rev: db.rev }); }
    if (m === 'PUT' && p.length === 3) { const v = clean(await readJsonBody(req), x); if (typeof v === 'string') return fail(res, 400, v); Object.assign(x, v, { updatedAt: new Date().toISOString() }); saveDb(); return send(res, 200, { ok: true, share: nsPublic(x), rev: db.rev }); }
    if (m === 'DELETE' && p.length === 3) { db.netshares = N.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Личное хранилище»: passwords and notes of the user himself — nobody else (not even the administrator) reads them */
  if (p[1] === 'vault') {
    if (orgType(user) === 'requests' || !sees(user, 'refs:vault')) return fail(res, 403, 'Этот раздел для вас закрыт');
    if (!db.vault || typeof db.vault !== 'object') db.vault = {};
    const V = db.vault[user.id] = db.vault[user.id] || { pw: [], notes: [] }, kind = p[2], now = new Date().toISOString();
    if (!Array.isArray(V.contacts)) V.contacts = [];
    const open = x => ({ id: x.id, at: x.at, updatedAt: x.updatedAt || null, ...(vaultDec(x.data) || { title: '(не удалось прочитать)' }) });
    if (m === 'GET' && !p[2]) return send(res, 200, { pw: V.pw.map(open), notes: V.notes.map(open), contacts: V.contacts.map(open) });
    if (!['pw', 'notes', 'contacts'].includes(kind)) return fail(res, 404, 'Не найдено');
    const L = V[kind], t = (v, n) => String(v ?? '').slice(0, n);
    const clean = b => kind === 'contacts'
      ? (t(b.name, 200).trim() || t(b.phone, 60).trim() ? { name: t(b.name, 200).trim(), phone: t(b.phone, 60).trim(), note: t(b.note, 2000) } : 'Укажите ФИО или номер телефона')
      : kind === 'pw'
      ? (t(b.title, 200).trim() ? { title: t(b.title, 200).trim(), login: t(b.login, 300), pass: t(b.pass, 500), url: t(b.url, 500).trim(), note: t(b.note, 2000) } : 'Напишите, от чего этот логин и пароль')
      : (() => { const pics = (Array.isArray(b.pics) ? b.pics : []).filter(x => typeof x === 'string' && x.length <= 1.6e6 && /^data:image\/(png|jpeg|webp);base64,[A-Za-z0-9+/=]+$/.test(x)).slice(0, 6);
          // pictures (from «Рисовалка») are kept inside the note, encrypted with it — so nobody else sees them, not even in «Файлы»
          return t(b.title, 200).trim() || t(b.text, 20000).trim() || pics.length ? { title: t(b.title, 200).trim(), text: t(b.text, 20000), ...(pics.length ? { pics } : {}) } : 'Заметка пустая'; })();
    if (m === 'POST' && !p[3]) {
      if (L.length >= 2000) return fail(res, 400, 'Слишком много записей');
      const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v);
      const x = { id: newId(), at: now, data: vaultEnc(v) }; L.push(x); saveDb(); return send(res, 200, { ok: true, item: open(x), rev: db.rev });
    }
    const x = p[3] && L.find(e => e.id === p[3]); if (!x) return fail(res, 404, 'Запись не найдена — обновите страницу');
    if (m === 'PUT') { const b = await readJsonBody(req); if (kind === 'notes' && b.pics === undefined) b.pics = (vaultDec(x.data) || {}).pics;   // a save without «pics» keeps the pictures
      const v = clean(b); if (typeof v === 'string') return fail(res, 400, v); x.data = vaultEnc(v); x.updatedAt = now; saveDb(); return send(res, 200, { ok: true, item: open(x), rev: db.rev }); }
    if (m === 'DELETE') { V[kind] = L.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Этикетки для модемов»: IMEI and SN of a device (from the scanner) with the ICCID of its SIM card; each number may be recorded only once */
  /* «ИП / самозанятый»: договоры, счета, доходы для налога, сканы документов и реквизиты — all in the database of the organization */
  if (p[1] === 'ip') {
    if (orgType(user) !== 'ip') return fail(res, 403, 'Этот раздел есть только у организации «ИП / самозанятый»');
    if (!db.ip || typeof db.ip !== 'object') db.ip = {};
    const I = db.ip; ['contracts', 'invoices', 'incomes', 'docs'].forEach(k => { if (!Array.isArray(I[k])) I[k] = []; });
    if (!I.profile) I.profile = { status: 'ip', taxRate: 6 }; if (!I.contrib || typeof I.contrib !== 'object') I.contrib = {};
    const ed = HEAD(user) || user.role === 'accountant', t = (v, n) => String(v ?? '').trim().slice(0, n), now = new Date().toISOString();
    const day = v => /^\d{4}-\d{2}-\d{2}$/.test(String(v || '')) ? String(v) : '';
    const amt = v => { const x = Math.round(Number(String(v ?? '').replace(/\s/g, '').replace(',', '.')) * 100) / 100; return isFinite(x) && x >= 0 ? x : 0; };
    const out = () => { saveDb(); return send(res, 200, { ok: true, ip: I, rev: db.rev }); };
    if (m === 'GET' && !p[2]) return send(res, 200, { ip: I });
    if (!ed) return fail(res, 403, 'Изменять может администратор, руководитель или бухгалтер');
    if (p[2] === 'profile' && m === 'PUT') {
      const b = await readJsonBody(req) || {};
      I.profile = { status: b.status === 'sz' ? 'sz' : 'ip', name: t(b.name, 300), inn: t(b.inn, 12), ogrnip: t(b.ogrnip, 15), address: t(b.address, 500), city: t(b.city, 100), phone: t(b.phone, 60), email: t(b.email, 200),
        bank: t(b.bank, 300), bik: t(b.bik, 9), account: t(b.account, 20), corr: t(b.corr, 20), taxRate: Math.min(20, Math.max(0, Number(b.taxRate) || 6)) };
      return out();
    }
    // «Страховые взносы» of a quarter: the tax of an ИП is reduced by them
    if (p[2] === 'contrib' && m === 'PUT') { const b = await readJsonBody(req) || {}, key = String(b.key || ''); if (!/^\d{4}-Q[1-4]$/.test(key)) return fail(res, 400, 'Неверный период'); I.contrib[key] = amt(b.sum); return out(); }
    const kinds = { contracts: 'Договор', invoices: 'Счёт', incomes: 'Доход', docs: 'Документ' }, k = p[2];
    if (!kinds[k]) return fail(res, 404, 'Не найдено');
    const L = I[k];
    // the next number within the year of the document
    const nextNo = date => { const y = String(date || localDateNow()).slice(0, 4), ns = L.filter(x => String(x.date || '').startsWith(y)).map(x => parseInt(String(x.no || '').split(/[-/]/).pop(), 10) || 0); return String((ns.length ? Math.max(...ns) : 0) + 1); };
    const clean = (b, old) => {
      if (k === 'contracts') {
        const date = day(b.date) || localDateNow();
        const v = { no: t(b.no, 40) || old?.no || nextNo(date), date, kind: t(b.kind, 100) || 'оказания услуг', client: t(b.client, 300), clientInn: t(b.clientInn, 12), clientType: b.clientType === 'person' ? 'person' : 'company',
          clientAddress: t(b.clientAddress, 500), clientRep: t(b.clientRep, 300), subject: t(b.subject, 5000), sum: amt(b.sum), until: day(b.until), payment: t(b.payment, 3000), status: ['draft', 'active', 'closed'].includes(b.status) ? b.status : 'active' };
        return v.client ? v : 'Укажите заказчика';
      }
      if (k === 'invoices') {
        const date = day(b.date) || localDateNow();
        const lines = (Array.isArray(b.lines) ? b.lines : []).slice(0, 100).map(l => ({ name: t(l.name, 500), qty: amt(l.qty) || 1, unit: t(l.unit, 20) || 'шт', price: amt(l.price) })).filter(l => l.name);
        const v = { no: t(b.no, 40) || old?.no || nextNo(date), date, contractId: t(b.contractId, 40), client: t(b.client, 300), clientInn: t(b.clientInn, 12), clientType: b.clientType === 'person' ? 'person' : 'company', lines,
          total: Math.round(lines.reduce((a, l) => a + l.qty * l.price, 0) * 100) / 100, due: day(b.due), paid: !!b.paid, paidAt: b.paid ? day(b.paidAt) || localDateNow() : '', note: t(b.note, 2000) };
        if (!v.client) return 'Укажите плательщика';
        return lines.length ? v : 'Добавьте хотя бы одну строку';
      }
      if (k === 'incomes') { const v = { date: day(b.date) || localDateNow(), sum: amt(b.sum), from: b.from === 'person' ? 'person' : 'company', comment: t(b.comment, 500) }; return v.sum > 0 ? v : 'Укажите сумму'; }
      const v = { kind: ['contract', 'invoice', 'act', 'check', 'supp', 'other'].includes(b.kind) ? b.kind : 'other', title: t(b.title, 300), date: day(b.date) || localDateNow(), contractId: t(b.contractId, 40), invoiceId: t(b.invoiceId, 40),
        files: (Array.isArray(b.files) ? b.files : []).filter(f => f && db.files[f.id]).slice(0, 20).map(f => ({ id: f.id, name: db.files[f.id].name, type: db.files[f.id].type, size: db.files[f.id].size })) };
      return v.files.length ? v : 'Прикрепите файл';
    };
    if (m === 'POST' && !p[3]) {
      if (L.length >= 20000) return fail(res, 400, 'Слишком много записей');
      const v = clean(await readJsonBody(req) || {}); if (typeof v === 'string') return fail(res, 400, v);
      L.push({ id: newId(), ...v, at: now, by: user.id }); return out();
    }
    const x = p[3] && L.find(e => e.id === p[3]); if (!x) return fail(res, 404, kinds[k] + ' не найден — обновите страницу');
    if (m === 'PUT') { const v = clean(await readJsonBody(req) || {}, x); if (typeof v === 'string') return fail(res, 400, v); Object.assign(x, v, { updatedAt: now, updatedBy: user.id }); return out(); }
    if (m === 'DELETE') { I[k] = L.filter(e => e !== x); return out(); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'snmap') {
    if (orgType(user) === 'requests' || !sees(user, 'refs:mods')) return fail(res, 403, 'Этот раздел для вас закрыт');
    if (!Array.isArray(db.snmap)) db.snmap = [];
    const L = db.snmap, F = { imei: 'IMEI', sn: 'SN', iccid: 'ICCID', ip: 'IP-адрес' }, num = v => String(v ?? '').replace(/\s+/g, '').toUpperCase().slice(0, 40);
    const ipOk = v => /^(25[0-5]|2[0-4]\d|1?\d?\d)(\.(25[0-5]|2[0-4]\d|1?\d?\d)){3}$/.test(v) || (/^[0-9A-F:]+$/.test(v) && v.includes(':') && v.length >= 3);
    const pub = x => ({ id: x.id, imei: x.imei, sn: x.sn, iccid: x.iccid, ip: x.ip || '', at: x.at, by: x.by, updatedAt: x.updatedAt || null });
    const dup = (k, v, self) => v && L.find(e => e !== self && e[k] === v);
    if (m === 'GET' && !p[2]) return send(res, 200, { list: L.map(pub) });
    // «Доступ для другого сервера»: the manager turns it on, sees and copies the key, issues a new one or turns it off
    if (p[2] === 'api-key') {
      if (!HEAD(user)) return fail(res, 403, 'Доступ для другого сервера настраивает руководитель или администратор');
      const A = db.snmapApi, info = () => db.snmapApi ? { enabled: true, key: vaultDec(db.snmapApi.key) || '', at: db.snmapApi.at, by: db.snmapApi.by, lastUsedAt: db.snmapApi.lastUsedAt || null, lastIp: db.snmapApi.lastIp || '', orgId: user.orgId } : { enabled: false, orgId: user.orgId };
      if (m === 'GET') return send(res, 200, info());
      if (m === 'POST') { const k = crypto.randomBytes(24).toString('base64url'); db.snmapApi = { key: vaultEnc(k), hash: snHash(k).toString('hex'), at: new Date().toISOString(), by: user.id }; saveDb(); return send(res, 200, info()); }
      if (m === 'DELETE') { if (A) { db.snmapApi = null; saveDb(); } return send(res, 200, info()); }   // «delete» does not reach the database through the proxy
      return fail(res, 405, 'Метод не поддерживается');
    }
    // «Прошить модем»: the configurations of the modem (.ini of the utility of the manufacturer) — kept encrypted: they hold the command password of the modem;
    // everybody of the module reads them (to flash a modem), the manager or the administrator adds and deletes
    if (p[2] === 'cfg') {
      if (!Array.isArray(db.snmapCfg)) db.snmapCfg = [];
      const C = db.snmapCfg, cpub = x => ({ id: x.id, name: x.name, text: vaultDec(x.text) || '', at: x.at, by: x.by });
      if (m === 'GET') return send(res, 200, { list: C.map(cpub) });
      if (!HEAD(user)) return fail(res, 403, 'Конфигурации добавляет руководитель или администратор');
      if (m === 'POST' && !p[3]) {
        const b = await readJsonBody(req) || {}, name = String(b.name || '').trim().slice(0, 60), text = String(b.text || '').slice(0, 200000);
        if (!name) return fail(res, 400, 'Укажите название конфигурации'); if (!/^\s*\[[^\]]+\]/m.test(text)) return fail(res, 400, 'Это не файл конфигурации (.ini)');
        if (C.length >= 50) return fail(res, 400, 'Слишком много конфигураций');
        const old = C.find(x => x.name.toLowerCase() === name.toLowerCase()), v = { name, text: vaultEnc(text), at: new Date().toISOString(), by: user.id };
        if (old) Object.assign(old, v); else C.push({ id: newId(), ...v });
        saveDb(); return send(res, 200, { list: C.map(cpub) });
      }
      if (m === 'DELETE' && p[3]) { db.snmapCfg = C.filter(x => x.id !== p[3]); saveDb(); return send(res, 200, { list: db.snmapCfg.map(cpub) }); }
      return fail(res, 405, 'Метод не поддерживается');
    }
    if (m === 'POST' && !p[2]) {
      const b = await readJsonBody(req) || {}, x = { imei: num(b.imei), sn: num(b.sn), iccid: num(b.iccid), ip: num(b.ip) };
      if (x.ip && !ipOk(x.ip)) return fail(res, 400, 'IP-адрес — например 10.0.0.1');
      for (const k of Object.keys(F)) { if (!x[k]) return fail(res, 400, 'Не указан ' + F[k]); const d = dup(k, x[k]); if (d) return fail(res, 409, `${F[k]} ${x[k]} уже записан (${new Date(d.at).toLocaleDateString('ru-RU')})`); }
      if (L.length >= 100000) return fail(res, 400, 'Слишком много записей');
      const it = { id: newId(), ...x, at: new Date().toISOString(), by: user.id }; L.push(it); saveDb(); return send(res, 200, { ok: true, item: pub(it), rev: db.rev });
    }
    const x = p[2] && L.find(e => e.id === p[2]); if (!x) return fail(res, 404, 'Запись не найдена — обновите страницу');
    if (m === 'PUT') {
      const b = await readJsonBody(req) || {}, upd = {};
      for (const k of Object.keys(F)) if (b[k] !== undefined) { const v = num(b[k]); if (!v) return fail(res, 400, F[k] + ' не может быть пустым'); if (k === 'ip' && !ipOk(v)) return fail(res, 400, 'IP-адрес — например 10.0.0.1'); const d = dup(k, v, x); if (d) return fail(res, 409, `${F[k]} ${v} уже записан в другой строке`); upd[k] = v; }
      Object.assign(x, upd, { updatedAt: new Date().toISOString() }); saveDb(); return send(res, 200, { ok: true, item: pub(x), rev: db.rev });
    }
    if (m === 'DELETE') { if (!HEAD(user) && x.by !== user.id) return fail(res, 403, 'Удалить строку может тот, кто её записал, или руководитель'); db.snmap = L.filter(e => e !== x); saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'refs') {
    if (user.sys || orgType(user) === 'requests') return fail(res, 403, 'Недоступно');
    if (!HEAD(user)) return fail(res, 403, 'Справочники ведёт руководитель или администратор');
    if (!sees(user, 'refs:list')) return fail(res, 403, 'Этот раздел для вас закрыт');
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
  /* «Заказы» of a transport organization: rent of special vehicles or a cargo transport — the client, the date and time, the route,
     the vehicle and the driver, the rate (hour / shift / trip / km), planned and actual quantity, the sum, the status, the payment, documents.
     Managers create and change; the accountant marks the payment; the driver starts and finishes his own orders. */
  if (p[1] === 'tor') {
    if (orgType(user) !== 'transport') return fail(res, 403, 'Заказы есть только у транспортной организации');
    if (!db.tOrders || typeof db.tOrders !== 'object') db.tOrders = {};
    const O = db.tOrders, now = new Date().toISOString(), txt = (v, n) => String(v ?? '').trim().slice(0, n);
    const D = /^\d{4}-\d{2}-\d{2}$/, T = /^([01]\d|2[0-3]):[0-5]\d$/;
    const num = v => { if (v === '' || v == null) return null; const n = Number(String(v).replace(/\s/g, '').replace(',', '.')); return Number.isFinite(n) && n >= 0 ? Math.round(n * 100) / 100 : NaN; };
    const files = a => (Array.isArray(a) ? a : []).filter(f => f && db.files[f.id]).slice(0, 50).map(f => ({ id: f.id, name: db.files[f.id].name, type: db.files[f.id].type, size: db.files[f.id].size, at: f.at || db.files[f.id].at }));
    const total = x => { const q = x.factQty != null ? x.factQty : x.planQty; return x.sumManual != null ? x.sumManual : q != null && x.price != null ? Math.round(q * x.price * 100) / 100 : null; };
    const out = (id, x) => { x.sum = total(x); saveDb(); return send(res, 200, { ok: true, order: { id, ...x }, rev: db.rev }); };
    const log = (x, act, extra = {}) => { x.history = Array.isArray(x.history) ? x.history : []; x.history.push({ at: now, by: user.id, act, ...extra }); x.updatedAt = now; };
    const clean = (b, old = {}) => {
      const kind = ['rent', 'cargo'].includes(b.kind) ? b.kind : old.kind || 'cargo';
      const date = b.date !== undefined ? String(b.date || '') : old.date || '';
      if (!D.test(date)) return 'Укажите дату';
      const t1 = b.timeFrom !== undefined ? String(b.timeFrom || '') : old.timeFrom || '', t2 = b.timeTo !== undefined ? String(b.timeTo || '') : old.timeTo || '';
      if ((t1 && !T.test(t1)) || (t2 && !T.test(t2))) return 'Время — в формате 09:00';
      const dateTo = b.dateTo !== undefined ? (D.test(b.dateTo || '') ? b.dateTo : '') : old.dateTo || '';
      if (dateTo && dateTo < date) return 'Дата окончания раньше даты начала';
      const clientId = b.clientId !== undefined ? (b.clientId && db.counterparties[b.clientId] ? b.clientId : null) : old.clientId || null;
      const clientName = txt(b.clientName ?? old.clientName, 200);
      if (!clientId && !clientName) return 'Укажите клиента';
      const vehicleId = b.vehicleId !== undefined ? (b.vehicleId || null) : old.vehicleId || null;
      if (vehicleId && !(db.vehicles || {})[vehicleId]) return 'Транспорт не найден';
      const driverId = b.driverId !== undefined ? (b.driverId || null) : old.driverId || null;
      if (driverId && !orgUsers().some(u => u.id === driverId && !u.sys)) return 'Водитель не найден';
      const unit = ['hour', 'shift', 'trip', 'km'].includes(b.unit) ? b.unit : old.unit || (kind === 'rent' ? 'hour' : 'trip');
      const price = b.price !== undefined ? num(b.price) : old.price ?? null, planQty = b.planQty !== undefined ? num(b.planQty) : old.planQty ?? null;
      const sumManual = b.sumManual !== undefined ? num(b.sumManual) : old.sumManual ?? null;
      if ([price, planQty, sumManual].some(Number.isNaN)) return 'Цена, количество и сумма — числа';
      return { kind, date, dateTo, timeFrom: t1, timeTo: t2, clientId, clientName: clientId ? db.counterparties[clientId].name : clientName, phone: txt(b.phone ?? old.phone, 60),
        from: txt(b.from ?? old.from, 300), to: txt(b.to ?? old.to, 300), cargo: txt(b.cargo ?? old.cargo, 1000), vehicleId, driverId, unit, price, planQty, sumManual, note: txt(b.note ?? old.note, 2000) };
    };
    if (m === 'POST' && !p[2]) {
      if (!HEAD(user)) return fail(res, 403, 'Заказы создаёт руководитель или диспетчер');
      const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v);
      const id = newId(), no = Math.max(0, ...Object.values(O).map(x => x.no || 0)) + 1;
      O[id] = { no, ...v, status: v.driverId && v.vehicleId ? 'assigned' : 'new', paid: false, factQty: null, docs: [], at: now, by: user.id, history: [] };
      log(O[id], 'created');
      return out(id, O[id]);
    }
    const x = p[2] && O[p[2]];
    if (!x || !(HEAD(user) || user.role === 'accountant' || x.driverId === user.id)) return fail(res, 404, 'Заказ не найден — обновите страницу');
    if (m === 'PATCH' && p.length === 3) {
      const b = await readJsonBody(req), act = b.action, driver = x.driverId === user.id;
      if (act === 'edit') {
        if (!HEAD(user)) return fail(res, 403, 'Изменять заказ может руководитель или диспетчер');
        const v = clean(b, x); if (typeof v === 'string') return fail(res, 400, v);
        Object.assign(x, v); if (x.status === 'new' && x.driverId && x.vehicleId) x.status = 'assigned'; log(x, 'edit');
      } else if (act === 'start') {
        if (!(driver || HEAD(user))) return fail(res, 403, 'Начать может водитель заказа');
        if (!['new', 'assigned'].includes(x.status)) return fail(res, 409, 'Заказ уже выполняется или закрыт');
        x.status = 'work'; x.startAt = now; log(x, 'start');
      } else if (act === 'done') {
        if (!(driver || HEAD(user))) return fail(res, 403, 'Завершить может водитель заказа');
        if (['done', 'cancel'].includes(x.status)) return fail(res, 409, 'Заказ уже закрыт');
        const q = num(b.factQty); if (q === null || Number.isNaN(q)) return fail(res, 400, x.unit === 'km' ? 'Укажите, сколько километров' : x.unit === 'trip' ? 'Укажите, сколько рейсов' : x.unit === 'shift' ? 'Укажите, сколько смен' : 'Укажите, сколько часов');
        x.factQty = q; x.status = 'done'; x.doneAt = now; x.doneBy = user.id; x.doneNote = txt(b.note, 1000);
        x.docs = files([...(x.docs || []), ...(Array.isArray(b.files) ? b.files : [])]); log(x, 'done', { qty: q });
      } else if (act === 'cancel') {
        if (!HEAD(user)) return fail(res, 403, 'Отменить может руководитель или диспетчер');
        x.status = 'cancel'; log(x, 'cancel', { note: txt(b.note, 500) });
      } else if (act === 'reopen') {
        if (!HEAD(user)) return fail(res, 403, 'Вернуть в работу может руководитель или диспетчер');
        x.status = x.startAt ? 'work' : x.driverId && x.vehicleId ? 'assigned' : 'new'; x.doneAt = null; log(x, 'reopen');
      } else if (act === 'paid') {
        if (!(HEAD(user) || user.role === 'accountant')) return fail(res, 403, 'Оплату отмечает бухгалтер или руководитель');
        x.paid = !!b.paid; x.paidAt = x.paid ? now : null; log(x, x.paid ? 'paid' : 'unpaid');
      } else if (act === 'docs') {
        if (!(driver || HEAD(user) || user.role === 'accountant')) return fail(res, 403, 'Нет доступа');
        x.docs = files(b.files); log(x, 'docs');
      } else return fail(res, 400, 'Неизвестное действие');
      return out(p[2], x);
    }
    if (m === 'DELETE' && p.length === 3) { if (!HEAD(user)) return fail(res, 403, 'Удалить заказ может руководитель'); delete O[p[2]]; saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
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
      const tr = orgType(user) === 'transport', j = !tr && b.jobId && db.jobs[b.jobId], to = tr && b.orderId && (db.tOrders || {})[b.orderId];
      if (tr ? !to : !j) return fail(res, 400, tr ? 'Выберите, к какому заказу относится путевой лист' : 'Выберите, к какой работе относится путевой лист');
      if (FIELD(user) && (tr ? to.driverId !== user.id : !onJob(user, j))) return fail(res, 403, tr ? 'Это не ваш заказ' : 'Это не ваша работа');
      if (b.vehicleId && !(db.vehicles || {})[b.vehicleId]) return fail(res, 400, 'Транспорт не найден');
      const x = { id: newId(), by: user.id, at: new Date().toISOString(), date: /^\d{4}-\d{2}-\d{2}$/.test(b.date || '') ? b.date : localDate(), jobId: tr ? null : b.jobId, orderId: tr ? b.orderId : null, vehicleId: b.vehicleId || null, note: String(b.note || '').trim().slice(0, 1000), files };
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
  /* the rating of an employee for a month: 1 — отлынивал … 3 — работал нормально … 5 — вкалывал; 0 removes it */
  if (p[1] === 'staff-ratings' && m === 'PUT') {
    if (!HEAD(user)) return fail(res, 403, 'Оценки ставит руководитель или администратор');
    const b = await readJsonBody(req), score = Number(b.score), ym = String(b.ym || '');
    if (!/^\d{4}-(0[1-9]|1[0-2])$/.test(ym)) return fail(res, 400, 'Укажите месяц');
    if (!orgUsers().some(u => u.id === b.user && !u.sys)) return fail(res, 400, 'Сотрудник не найден');
    if (!(Number.isInteger(score) && score >= 0 && score <= 5)) return fail(res, 400, 'Оценка — от 1 до 5');
    if (!Array.isArray(db.staffRatings)) db.staffRatings = [];
    db.staffRatings = db.staffRatings.filter(x => !(x.user === b.user && x.ym === ym));
    let x = null;
    if (score) { x = { user: b.user, ym, score, note: String(b.note || '').trim().slice(0, 500), by: user.id, at: new Date().toISOString() }; db.staffRatings.push(x); }
    saveDb(); return send(res, 200, { ok: true, rating: x, rev: db.rev });
  }
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
  /* «Оборудование» of a requests organization: the administrator (and a manager) adds, changes and removes */
  if (p[1] === 'req-equip') {
    if (orgType(user) !== 'requests') return fail(res, 403, 'Оборудование есть только в системе «Управление заявками»');
    if (!HEAD(user)) return fail(res, 403, 'Список оборудования ведёт администратор');
    if (!Array.isArray(db.reqEquip)) db.reqEquip = [];
    const E = db.reqEquip, now = new Date().toISOString(), txt = (v, n) => String(v ?? '').trim().slice(0, n);
    const clean = b => {
      const name = txt(b.name, 200); if (!name) return 'Напишите название оборудования';
      const invNo = txt(b.invNo, 60);
      if (invNo && E.some(e => e.invNo && e.invNo.toLowerCase() === invNo.toLowerCase() && e.id !== b._id)) return 'Такой инвентарный номер уже есть';
      if (b.system && !UPR_SYS.includes(b.system)) return 'Неизвестная система';
      const owners = [...new Set((Array.isArray(b.owners) ? b.owners : []).filter(id => orgUsers().some(u => u.id === id && !u.sys)))];
      return { name, invNo, place: txt(b.place, 200), system: b.system || '', owners, note: txt(b.note, 1000) };
    };
    if (m === 'POST' && !p[2]) { const v = clean(await readJsonBody(req)); if (typeof v === 'string') return fail(res, 400, v); const x = { id: newId(), ...v, at: now, by: user.id }; E.push(x); saveDb(); return send(res, 200, { ok: true, eq: x, rev: db.rev }); }
    const x = p[2] && E.find(e => e.id === p[2]); if (!x) return fail(res, 404, 'Оборудование не найдено — обновите страницу');
    if (m === 'PUT') { const v = clean({ ...(await readJsonBody(req)), _id: x.id }); if (typeof v === 'string') return fail(res, 400, v); Object.assign(x, v, { updatedAt: now }); saveDb(); return send(res, 200, { ok: true, eq: x, rev: db.rev }); }
    if (m === 'DELETE') { db.reqEquip = E.filter(e => e !== x); for (const r of Object.values(db.requests || {})) if (r.eqId === x.id) { r.eqName = x.name + (x.invNo ? ' (инв. ' + x.invNo + ')' : ''); r.eqId = null; } saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
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
  /* «Мой календарь»: the own entries of a user — a date, a time (from–to, may be empty), what, a comment; nobody else sees them */
  if (p[1] === 'cal') {
    if (!db.cal || typeof db.cal !== 'object') db.cal = {};
    const L = Array.isArray(db.cal[user.id]) ? db.cal[user.id] : (db.cal[user.id] = []);
    const t = (v, n) => String(v ?? '').trim().slice(0, n), tm = v => /^([01]\d|2[0-3]):[0-5]\d$/.test(String(v || '')) ? String(v) : '';
    const clean = b => { const v = { date: /^\d{4}-\d{2}-\d{2}$/.test(String(b.date || '')) ? String(b.date) : '', time: tm(b.time), timeTo: tm(b.timeTo), title: t(b.title, 300), comment: t(b.comment, 5000), done: !!b.done };
      if (!v.date) return 'Укажите дату'; if (!v.title && !v.comment) return 'Напишите, что запланировано, или комментарий'; if (v.timeTo && v.time && v.timeTo < v.time) return 'Время окончания раньше начала'; return v; };
    const out = () => { saveDb(); return send(res, 200, { list: L }); };
    if (m === 'GET' && !p[2]) return send(res, 200, { list: L });
    if (m === 'POST' && !p[2]) { if (L.length >= 5000) return fail(res, 400, 'Слишком много записей'); const v = clean(await readJsonBody(req) || {}); if (typeof v === 'string') return fail(res, 400, v); L.push({ id: newId(), ...v, at: new Date().toISOString() }); return out(); }
    const x = p[2] && L.find(e => e.id === p[2]); if (!x) return fail(res, 404, 'Запись не найдена — обновите страницу');
    if (m === 'PUT') { const v = clean({ ...x, ...(await readJsonBody(req) || {}) }); if (typeof v === 'string') return fail(res, 400, v); Object.assign(x, v, { editedAt: new Date().toISOString() }); return out(); }
    if (m === 'DELETE') { db.cal[user.id] = L.filter(e => e !== x); saveDb(); return send(res, 200, { list: db.cal[user.id] }); }
    return fail(res, 405, 'Метод не поддерживается');
  }
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
      // the comments of the points stay (they are kept on the server only, the file does not bring them)
      const pc = new Map(((db.dt && db.dt.points) || []).filter(x => (x.comments || []).length).map(x => [x.no, x.comments]));
      points.forEach(x => { if (pc.has(x.no)) x.comments = pc.get(x.no); });
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
    /* the comments of a point: anybody who sees the map writes; the author or a manager deletes */
    if (p[2] === 'comment') {
      const b = await readJsonBody(req) || {}, pt = db.dt && (db.dt.points || []).find(x => x.no === String(b.no || ''));
      if (!pt) return fail(res, 404, 'Точка не найдена — обновите страницу');
      pt.comments = Array.isArray(pt.comments) ? pt.comments : [];
      if (m === 'POST') { const text = String(b.text || '').trim().slice(0, 2000); if (!text) return fail(res, 400, 'Напишите комментарий'); if (pt.comments.length >= 500) return fail(res, 400, 'Слишком много комментариев');
        pt.comments.push({ id: newId(), text, by: user.id, at: new Date().toISOString() }); saveDb(); return send(res, 200, { ok: true, comments: pt.comments, rev: db.rev }); }
      if (m === 'DELETE') { const c = pt.comments.find(x => x.id === b.id); if (!c) return fail(res, 404, 'Комментарий не найден');
        if (c.by !== user.id && !canEdit(user)) return fail(res, 403, 'Удалить может автор или руководитель');
        pt.comments = pt.comments.filter(x => x !== c); saveDb(); return send(res, 200, { ok: true, comments: pt.comments, rev: db.rev }); }
      return fail(res, 405, 'Метод не поддерживается');
    }
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
        // a new position: the quantity of the file goes to the accounting and to the actual balance
        const q0 = r3(Math.max(0, r.qty));
        db.stock[nid] = { name: r.name, sku: r.sku, unit: r.unit || 'шт', location: '', minQty: 0, note: 'Добавлено из выгрузки 1С', qty: q0, acctQty: r.qty, createdAt: now, createdBy: user.id,
          moves: q0 > 0 ? [{ id: newId(), type: 'init', qty: q0, acct: true, acctBalance: r.qty, balance: q0, note: 'Новая позиция из выгрузки 1С' + (b.file ? ' (' + String(b.file).slice(0, 200) + ')' : ''), by: user.id, at: now }] : [] };
        seen.add(nid); created++;
      } else skipped++;
    }
    let zeroed = 0;
    for (const [id, it] of items) if (!seen.has(id)) { if (Number(it.acctQty)) zeroed++; it.acctQty = 0; }   // not in the export: nothing on the books
    db.meta.acct = { at: now, by: user.id, file: String(b.file || '').slice(0, 200), rows: agg.size, matched, created, skipped, zeroed };
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
    // the balances were already loaded: a repeated upload updates the accounting balance of every line of the file,
    // the positions not in the file get 0 on the books, the actual balance of the existing positions stays
    const again = !!(db.meta.acct || db.meta.initial);
    let matched = 0, created = 0, zeroed = 0;
    for (const r of agg.values()) {
      let id = (r.sku && bySku.get(normName(r.sku))) || byName.get(normName(r.name));
      if (id && again) { const it = db.stock[id]; if (!seen.has(id)) { matched++; it.acctQty = r.qty; } else it.acctQty = r3((Number(it.acctQty) || 0) + r.qty); seen.add(id); it.updatedAt = now; it.updatedBy = user.id; continue; }
      if (!id) { id = newId(); created++; db.stock[id] = { name: r.name, sku: r.sku, unit: r.unit || 'шт', location: '', minQty: 0, note: 'Добавлено из начальных остатков 1С', qty: 0, moves: [], acctQty: 0, createdAt: now, createdBy: user.id }; }
      else if (!seen.has(id)) matched++;
      const it = db.stock[id], q = seen.has(id) ? r3((Number(it.qty) || 0) + r.qty) : r.qty;
      it.qty = q; it.acctQty = q; seen.add(id);
      it.moves = Array.isArray(it.moves) ? it.moves : [];
      it.moves.push({ id: newId(), type: 'init', qty: r.qty, acct: true, acctBalance: q, balance: q, note: 'Начальный остаток из 1С' + (file ? ' (' + file + ')' : ''), by: user.id, at: now });
      it.updatedAt = now; it.updatedBy = user.id;
    }
    if (again) for (const [id, it] of items) if (!seen.has(id) && Number(it.acctQty)) { it.acctQty = 0; zeroed++; }
    db.meta.initial = { at: now, by: user.id, file, rows: agg.size, matched, created, again, zeroed };
    if (again) db.meta.acct = { at: now, by: user.id, file, rows: agg.size, matched, created, skipped: 0, zeroed };
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
    const r = woApply(p[1], p[2], map, user); if (r.error) return fail(res, 400, r.error);
    saveDb();
    return send(res, 200, { ok: true, writeoff: r.writeoff, rev: db.rev });
  }
  /* the draft of a write-off list: kept on every change until «Сохранить»; «Вернуть как было» deletes it.
     full — the lines «на весь объём» being edited (orders), map — the replaced nomenclature */
  if ((p[1] === 'orders' || p[1] === 'jobs') && p[3] === 'wodraft' && (m === 'PUT' || m === 'DELETE')) {
    if (!canEdit(user)) return fail(res, 403, 'Список для списания ведёт администратор или руководитель');
    const target = db[p[1]] && db[p[1]][p[2]]; if (!target) return fail(res, 404, p[1] === 'jobs' ? 'Работа не найдена' : 'Заказ не найден');
    if (m === 'DELETE') { delete target.woDraft; saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    const b = await readJsonBody(req), d = { at: new Date().toISOString(), by: user.id };
    if (Array.isArray(b.full)) d.full = b.full.slice(0, 1000).map(x => ({ id: String(x && x.id || newId()).slice(0, 40), stockId: x && x.stockId && db.stock[x.stockId] ? x.stockId : null, name: String(x && x.name || '').slice(0, 300), unit: String(x && x.unit || '').slice(0, 20), qty: String((x && x.qty) ?? '').slice(0, 30), per: String((x && x.per) ?? '').slice(0, 30) }));
    if (b.units !== undefined) d.units = String(b.units ?? '').slice(0, 30);
    if (b.map && typeof b.map === 'object') { d.map = {}; for (const [k, v] of Object.entries(b.map)) if (/^(id|n):/.test(k) && db.stock[v]) d.map[k] = v; }
    if (!d.full && !d.map) { delete target.woDraft; saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    target.woDraft = d; saveDb(); return send(res, 200, { ok: true, woDraft: d, rev: db.rev });
  }
  /* the write-off list «на весь объём» of an order (production): the materials for the whole volume instead of the products */
  if ((p[1] === 'orders' || p[1] === 'jobs') && p[3] === 'wofull' && (m === 'PUT' || m === 'DELETE')) {
    if (!canEdit(user)) return fail(res, 403, 'Список для списания ведёт администратор или руководитель');
    const o = db[p[1]] && db[p[1]][p[2]]; if (!o) return fail(res, 404, p[1] === 'jobs' ? 'Работа не найдена' : 'Заказ не найден');
    if (m === 'DELETE') { delete o.woFull; if (o.woDraft) { delete o.woDraft.full; if (!o.woDraft.map) delete o.woDraft; } saveDb(); return send(res, 200, { ok: true, rev: db.rev }); }
    const b = await readJsonBody(req), lines = [];
    for (const [i, x] of (Array.isArray(b.lines) ? b.lines : []).slice(0, 1000).entries()) {
      const name = String(x && x.name || '').trim().slice(0, 300), qty = Number(x && x.qty);
      if (!name && !(qty > 0)) continue;
      if (!name) return fail(res, 400, `Строка ${i + 1}: укажите номенклатуру`);
      if (!(qty > 0) || qty > 1e9) return fail(res, 400, `Строка ${i + 1}: укажите количество больше нуля`);
      const sid = x.stockId && db.stock[x.stockId] && normName(db.stock[x.stockId].name) === normName(name) ? x.stockId : (Object.entries(db.stock).find(([, it]) => normName(it.name) === normName(name)) || [])[0] || null;
      const per = Number(x.per); lines.push({ id: String(x.id || newId()).slice(0, 40), stockId: sid, name: sid ? db.stock[sid].name : name, unit: String((sid && db.stock[sid].unit) || x.unit || 'шт').slice(0, 20), qty: r3(qty), ...(x.per != null && x.per !== '' && per > 0 && per <= 1e9 ? { per: r3(per) } : {}) });
    }
    if (!lines.length) return fail(res, 400, 'Добавьте хотя бы одну строку');
    const units = Number(b.units); o.woFull = { lines, ...(units > 0 && units <= 1e9 ? { units: r3(units) } : {}), at: new Date().toISOString(), by: user.id };
    if (o.woDraft) { delete o.woDraft.full; if (!o.woDraft.map) delete o.woDraft; }
    // the write-off is already saved — it follows the list at once
    let reapplied = null;
    if (o.writeoff && o.writeoff.applied) { const r = woApply(p[1], p[2], o.woMap || {}, user); if (!r.error) reapplied = r.writeoff; }
    saveDb();
    return send(res, 200, { ok: true, woFull: o.woFull, writeoff: reapplied, rev: db.rev });
  }
  /* write-off list for an order: Excel with highlighting */
  if ((p[1] === 'orders' || p[1] === 'jobs') && p[3] === 'writeoff-table.xlsx' && m === 'GET') {
    const o = woDoc(p[1], p[2]); if (!o) return fail(res, 404, 'Не найдено');
    const buf = writeoffPlainXlsx(o), name = `Таблица списания ${o.number || ''} ${o.title || ''}`.replace(/[\\/:*?"<>|]+/g, ' ').trim().slice(0, 90) + '.xlsx';
    res.writeHead(200, { ...SEC_HEADERS, 'Content-Type': 'application/vnd.openxmlformats-officedocument.spreadsheetml.sheet',
      'Content-Disposition': `attachment; filename="writeoff-table.xlsx"; filename*=UTF-8''${encodeURIComponent(name)}`, 'Content-Length': buf.length, 'Cache-Control': 'no-store' });
    return res.end(buf);
  }
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
    // a receipt goes to the accounting balance too; an issue («Расход») and the starting quantity of a new position («+ Позиция») change only the actual one
    const toAcct = b.type === 'in' && b.acct !== false;
    if (toAcct) it.acctQty = r3((Number(it.acctQty) || 0) + qty);
    it.moves = Array.isArray(it.moves) ? it.moves : [];
    const mv = { id: newId(), type: b.type, ...(toAcct ? { acct: true, acctBalance: it.acctQty } : {}), qty, orderId: b.orderId || null, note: String(b.note || '').slice(0, 500), by: user.id, at: new Date().toISOString(), balance: it.qty };
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
  /* «Что взять с собой»: the manager makes the checklist of a work; every employee of the work ticks what he has packed — each for himself */
  if (p[1] === 'jobs' && p[3] === 'kit') {
    const j = db.jobs[p[2]]; if (!j) return fail(res, 404, 'Работа не найдена');
    const L = j.kit = Array.isArray(j.kit) ? j.kit : [], now = new Date().toISOString(), ed = mayEditJob(user, j);
    const out = () => { j.updatedAt = now; saveDb(); return send(res, 200, { ok: true, kit: L, rev: db.rev }); };
    if (m === 'POST' && p.length === 4) {
      if (!ed) return fail(res, 403, 'Чек-лист составляет руководитель или администратор');
      const b = await readJsonBody(req) || {}, texts = (Array.isArray(b.texts) ? b.texts : [b.text]).map(t => String(t || '').trim().slice(0, 300)).filter(Boolean).slice(0, 100);
      if (!texts.length) return fail(res, 400, 'Напишите, что взять');
      if (L.length + texts.length > 200) return fail(res, 400, 'Слишком много пунктов');
      texts.forEach(text => L.push({ id: newId(), text, at: now, by: user.id, got: {} }));
      return out();
    }
    // «Снять мои отметки» — before the next trip
    if (m === 'POST' && p[4] === 'reset') { if (!(onJob(user, j) || ed)) return fail(res, 403, 'Недостаточно прав'); L.forEach(x => { if (x.got) delete x.got[user.id]; }); return out(); }
    const it = p[4] && L.find(x => x.id === p[4]); if (!it) return fail(res, 404, 'Пункт не найден — обновите страницу');
    if (m === 'POST' && p[5] === 'got') {
      if (!(onJob(user, j) || ed)) return fail(res, 403, 'Отмечать могут участники работы');
      const b = await readJsonBody(req) || {}; it.got = it.got && typeof it.got === 'object' ? it.got : {};
      if (b.got) it.got[user.id] = now; else delete it.got[user.id];
      return out();
    }
    if (!ed) return fail(res, 403, 'Чек-лист меняет руководитель или администратор');
    if (m === 'PATCH') { const b = await readJsonBody(req) || {}, t = String(b.text ?? '').trim().slice(0, 300); if (!t) return fail(res, 400, 'Пустой пункт — удалите его'); it.text = t; it.editedAt = now; return out(); }
    if (m === 'DELETE') { L.splice(L.indexOf(it), 1); return out(); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  /* «Эксплуатация»: the requests of a work — what to do, by when, the executor (he becomes a worker of the work and sees it) and the vehicle, the state */
  /* «Группы» of works: a name; a work has «groupId»; a deleted group leaves its works without a group */
  if (p[1] === 'jobgroups') {
    if (!canEdit(user)) return fail(res, 403, 'Группы меняет руководитель или администратор');
    const G = db.jobGroups = Array.isArray(db.jobGroups) ? db.jobGroups : [], nm = v => String(v ?? '').trim().slice(0, 100);
    const out = () => { saveDb(); return send(res, 200, { ok: true, jobGroups: G, rev: db.rev }); };
    const same = (n, self) => G.find(g => g !== self && g.name.toLowerCase() === n.toLowerCase());
    if (m === 'POST' && !p[2]) { const n = nm((await readJsonBody(req) || {}).name); if (!n) return fail(res, 400, 'Укажите название группы'); if (same(n)) return fail(res, 400, 'Такая группа уже есть'); if (G.length >= 500) return fail(res, 400, 'Слишком много групп');
      G.push({ id: newId(), name: n, at: new Date().toISOString(), by: user.id }); return out(); }
    const g = p[2] && G.find(x => x.id === p[2]); if (!g) return fail(res, 404, 'Группа не найдена — обновите страницу');
    if (m === 'PATCH') { const n = nm((await readJsonBody(req) || {}).name); if (!n) return fail(res, 400, 'Укажите название группы'); if (same(n, g)) return fail(res, 400, 'Такая группа уже есть'); g.name = n; return out(); }
    if (m === 'DELETE') { G.splice(G.indexOf(g), 1); for (const j of Object.values(db.jobs || {})) if (j.groupId === g.id) j.groupId = null; return out(); }
    return fail(res, 405, 'Метод не поддерживается');
  }
  if (p[1] === 'jobs' && p[3] === 'reqs') {
    const j = db.jobs[p[2]]; if (!j) return fail(res, 404, 'Работа не найдена');
    const own = it => it && it.assignee === user.id;
    const L = j.reqs = Array.isArray(j.reqs) ? j.reqs : [], now = new Date().toISOString();
    const t = (v, n) => String(v ?? '').trim().slice(0, n), day = v => /^\d{4}-\d{2}-\d{2}$/.test(String(v || '')) ? String(v) : '';
    const who = v => v && orgUsers().some(u => u.id === v) ? String(v) : '';
    const veh = v => taskVehicles(v ? [v] : [])[0] || '';
    const out = () => { j.updatedAt = now; j.updatedBy = user.id; saveDb(); return send(res, 200, { ok: true, reqs: L, workers: j.workers || [], rev: db.rev }); };
    const addWorker = id => { if (id && !(j.workers || []).includes(id)) j.workers = [...(j.workers || []), id]; };
    if (m === 'POST' && !p[4]) {
      if (!mayEditJob(user, j)) return fail(res, 403, 'Заявки добавляет руководитель или администратор');
      const b = await readJsonBody(req) || {}, text = t(b.text, 3000); if (!text) return fail(res, 400, 'Напишите, что нужно сделать');
      if (L.length >= 5000) return fail(res, 400, 'Слишком много заявок');
      const x = { id: newId(), no: (L.reduce((a, r) => Math.max(a, r.no || 0), 0) + 1), text, address: t(b.address, 500), due: day(b.due), assignee: who(b.assignee), vehicle: veh(b.vehicle), status: 'new', comment: t(b.comment, 3000), at: now, by: user.id };
      L.push(x); addWorker(x.assignee); jobLog(j, user, { t: 'req', act: 'add', no: x.no, text: x.text.slice(0, 300) }); return out();
    }
    const it = p[4] && L.find(x => x.id === p[4]); if (!it) return fail(res, 404, 'Заявка не найдена — обновите страницу');
    if (m === 'PATCH') {
      if (!(mayEditJob(user, j) || own(it))) return fail(res, 403, 'Заявку меняет руководитель, администратор или её исполнитель');
      const b = await readJsonBody(req) || {}, head = mayEditJob(user, j);
      if (head) { if (b.text !== undefined) { const v = t(b.text, 3000); if (!v) return fail(res, 400, 'Пустая заявка — удалите её'); it.text = v; }
        if (b.address !== undefined) it.address = t(b.address, 500); if (b.due !== undefined) it.due = day(b.due);
        if (b.assignee !== undefined) { it.assignee = who(b.assignee); addWorker(it.assignee); } if (b.vehicle !== undefined) it.vehicle = veh(b.vehicle); }
      if (b.comment !== undefined) it.comment = t(b.comment, 3000);
      if (b.status !== undefined && ['new', 'work', 'done'].includes(b.status)) { it.status = b.status; it.doneAt = b.status === 'done' ? now : null; it.doneBy = b.status === 'done' ? user.id : null; }
      it.editedAt = now; it.editedBy = user.id; jobLog(j, user, { t: 'req', act: 'edit', no: it.no, text: String(it.text || '').slice(0, 300), ch: Object.keys(b).filter(k => ['text', 'address', 'due', 'assignee', 'vehicle', 'comment', 'status'].includes(k)).map(k => ({ f: k, to: short(b[k]) })) }); return out();
    }
    if (m === 'DELETE') { if (!mayEditJob(user, j)) return fail(res, 403, 'Удаляет руководитель или администратор'); jobLog(j, user, { t: 'req', act: 'del', no: it.no, text: String(it.text || '').slice(0, 300) }); L.splice(L.indexOf(it), 1); return out(); }
    return fail(res, 405, 'Метод не поддерживается');
  }
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
      jobLog(j, user, { t: 'list', k, act: 'add', text: text.slice(0, 300) });
      return out();
    }
    const it = p[5] && L.find(x => x.id === p[5]); if (!it) return fail(res, 404, 'Пункт не найден — обновите страницу');
    if (m === 'PATCH') {
      const b = await readJsonBody(req);
      if (b.text !== undefined) { const t = String(b.text).trim().slice(0, 2000); if (!t && !(it.links || []).length && !(it.files || []).length) return fail(res, 400, 'Пустой пункт — удалите его'); it.text = t; }
      if (b.text !== undefined && String(b.text).trim() !== it.text) jobLog(j, user, { t: 'list', k, act: 'edit', text: String(b.text).trim().slice(0, 300), from: String(it.text || '').slice(0, 300) });
      if (b.done !== undefined && !!b.done !== !!it.done) jobLog(j, user, { t: 'list', k, act: b.done ? 'done' : 'undone', text: String(it.text || '').slice(0, 300) });
      if (b.done !== undefined) { it.done = !!b.done; it.doneAt = it.done ? now : null; it.doneBy = it.done ? user.id : null; }
      if (k === 'buy' && b.links !== undefined) it.links = links(b.links);
      if (k === 'buy' && b.files !== undefined) it.files = files(b.files);
      it.editedAt = now; it.editedBy = user.id;
      return out();
    }
    if (m === 'DELETE') { jobLog(j, user, { t: 'list', k, act: 'del', text: String(it.text || '').slice(0, 300) }); L.splice(L.indexOf(it), 1); return out(); }
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
    if (col === 'tasks') data.vehicles = taskVehicles(data.vehicles);
    if (col === 'invoices') {
      // an invoice belongs to an order, or to a work (a mounting work has no order); a work with production gives its order
      const job = data.jobId && db.jobs[data.jobId]; if (!job) data.jobId = null;
      if (!data.orderId && job && job.orderId && db.orders[job.orderId]) data.orderId = job.orderId;
      if (data.orderId && !db.orders[data.orderId]) return fail(res, 400, 'Заказ не найден');
      if (!data.orderId && !job) return fail(res, 400, 'Выберите заказ или работу');
      if (!data.orderId) data.orderId = null;
      data.projectId = data.orderId ? db.orders[data.orderId].projectId || null : null;
      data.status = 'topay'; [...PAY_FIELDS.slice(1), ...SEEN_FIELDS].forEach(f => delete data[f]);
      delete data.income; data.items = cleanItems(data.items);
    }
    let cpCreated = false;
    if (col === 'invoices') { const sup = ensureSupplier(data.supplier, data.supplierInn, user, `Добавлен по счёту № ${data.number || '—'}`); data.supplierId = sup.id; cpCreated = sup.created; }
    const nid = newId(); db[col][nid] = data;
    if (col === 'jobs') { delete data.orderId; ensureJobOrder(data, nid, user); jobLog(data, user, { t: 'created' }); }
    if (col === 'tasks' && db.jobs[data.jobId]) jobLog(db.jobs[data.jobId], user, { t: 'task', act: 'add', title: data.title, kind: data.kind, start: data.start, end: data.end });
    const linesFilled = col === 'invoices' ? fillOrderSuppliers(data) : 0;
    saveDb();
    return send(res, 200, { id: nid, rev: db.rev, cpCreated, linesFilled });
  }
  if (!id || !db[col][id]) return fail(res, 404, 'Запись не найдена');

  if (m === 'PATCH') {
    const patch = clean(await readJsonBody(req));
    delete patch.createdBy; delete patch.createdAt;
    if (col === 'orders' || col === 'counterparties') delete patch.comments;   // comments go through their own endpoint
    if (col === 'stock') { delete patch.qty; delete patch.moves; delete patch.acctQty; }
    if (col === 'tasks' && patch.vehicles !== undefined) patch.vehicles = taskVehicles(patch.vehicles);   // balances change only through moves and the 1C import
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
      { const ch = diffOf(j, c, ['history', 'updatedAt', 'updatedBy', 'doneAt', 'doneBy', 'startedAt', 'startedBy', 'woDraft']); if (ch.length) jobLog(j, user, { t: 'job', ch }); }
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
    if (col === 'invoices' && (patch.orderId !== undefined || patch.jobId !== undefined)) {
      if (patch.jobId !== undefined && patch.jobId && !db.jobs[patch.jobId]) return fail(res, 400, 'Работа не найдена');
      const jobId = patch.jobId !== undefined ? patch.jobId || null : db[col][id].jobId || null;
      if (patch.jobId !== undefined) patch.jobId = jobId;
      if (patch.orderId) { if (!db.orders[patch.orderId]) return fail(res, 400, 'Заказ не найден'); patch.projectId = db.orders[patch.orderId].projectId || null; }
      else if (patch.orderId !== undefined) { if (!jobId) return fail(res, 400, 'Выберите заказ или работу'); patch.orderId = null; patch.projectId = null; }
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
    if (col === 'orders') { const ch = diffOf(db.orders[id], patch, ['updatedAt', 'updatedBy', 'products', 'components', 'specs', 'woDraft', 'woMap', 'woFull']); const j = Object.values(db.jobs || {}).find(x => x.orderId === id); if (ch.length && j) jobLog(j, user, { t: 'order', ch }); }
    if (col === 'tasks') { const t = db.tasks[id], ch = diffOf(t, patch, ['updatedAt', 'updatedBy', 'contractorsNote']); if (ch.length && db.jobs[t.jobId || patch.jobId]) jobLog(db.jobs[t.jobId || patch.jobId], user, { t: 'task', act: 'edit', title: t.title, kind: t.kind, ch }); }
    Object.assign(db[col][id], patch, { updatedAt: new Date().toISOString(), updatedBy: user.id });
    // a production work and its order have one status: the work's («Выполнена» — the order is closed)
    if (col === 'jobs' && 'status' in patch) { const o = db.jobs[id].orderId && db.orders[db.jobs[id].orderId]; if (o) o.status = jobToOrderSt(patch.status); }
    if (col === 'orders' && 'status' in patch) { const j = Object.values(db.jobs || {}).find(x => x.orderId === id); if (j && jobToOrderSt(j.status) !== patch.status) j.status = patch.status === 'closed' ? 'done' : patch.status === 'work' ? 'work' : (j.status === 'wait' ? 'wait' : 'new'); }
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
    if (col === 'jobs' && listOf('invoices').some(i => i.jobId === id && !i.orderId)) return fail(res, 409, 'По работе есть счета — сначала удалите их');
    if (col === 'counterparties' && listOf('orders').some(o => o.customerId === id)) return fail(res, 409, 'Контрагент указан заказчиком в заказах');
    if (col === 'invoices' && d.status === 'paid') return fail(res, 409, 'Оплаченный счёт удалить нельзя');
    if (col === 'invoices' && d.income) return fail(res, 409, 'По счёту оприходован товар на склад. Сначала отмените приход');
    // a deleted order of a work is not made again automatically
    if (col === 'orders') for (const j of Object.values(db.jobs || {})) if (j.orderId === id) { j.orderId = null; j.noOrder = true; }
    if (col === 'jobs' && d.orderId && db.orders[d.orderId] && db.orders[d.orderId].jobId === id) delete db.orders[d.orderId].jobId;
    if (col === 'tasks' && db.jobs[d.jobId]) jobLog(db.jobs[d.jobId], user, { t: 'task', act: 'del', title: d.title, kind: d.kind, start: d.start, end: d.end });
    delete db[col][id]; saveDb();
    return send(res, 200, { ok: true, rev: db.rev });
  }
  return fail(res, 405, 'Метод не поддерживается');
}
/* ---------- organizations: only the system administrator ---------- */
const ORG_ID = /^[a-z0-9][a-z0-9-]{1,30}$/;
const orgOut = o => {
  const st = orgState(o), us = users.filter(u => u.orgId === o.id);
  return { id: o.id, name: o.name, type: ORG_TYPES.includes(o.type) ? o.type : 'all', hide: o.hide || [], until: o.until || '', blocked: !!o.blocked, blockNote: o.blockNote || '', note: o.note || '', createdAt: o.createdAt || null,
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
  if (['system', 'light', 'dark', 'telecom', 'pink', 'engineer', 'upr', 'anime', 'xp', 'w98'].includes(b.theme)) o.theme = b.theme;
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
const meInfo = u => { const o = orgById(u.orgId), st = orgState(o); return { ...publicUser(u), actingSys: !!u.actingSys, prefs: u.prefs || {}, map: MAP, sys: !!u.sys, hide: u.sys ? [] : hiddenFor(u), org: o ? { id: o.id, name: o.name, until: o.until || '', type: orgType(u), hide: o.hide || [] } : null, orgWarn: st.warn || '' }; };
const adminUser = u => ({ ...publicUser(u), cpId: u.cpId || null, sys: !!u.sys, hide: u.hide || [], accessUntil: u.accessUntil || '', expired: !!contractorExpired(u), blocked: !!u.blocked, lastLoginAt: u.lastLoginAt || null, createdAt: u.createdAt || null });

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
// the write-off list «на весь объём» of an order: when it has lines the products of the order are not counted
const woFullOn = o => !!(o && o.woFull && Array.isArray(o.woFull.lines) && o.woFull.lines.length);
const woProducts = o => woFullOn(o) ? [{ name: 'Весь объём', qty: 1, components: o.woFull.lines }] : (o.products || []);
/* writes the list off the books: the difference with what was written off before goes as a move of every position;
   short lines — as much as there is on the books */
function woApply(col, id, map, user) {
  const o = woDoc(col, id); if (!o) return { error: 'Не найдено' };
    const lines = writeoffLines(o, map);
    if (!lines.length) return { error: col === 'jobs' ? 'В работе нет материалов' : 'В изделиях заказа нет компонентов' };
    if (!lines.some(L => L.take > 0)) return { error: 'Нечего списывать: ни одной позиции нет в бухгалтерских остатках' };
    // lines that are short are written off as much as there is on the books (the rest is «не хватает»)
    const target = col === 'jobs' ? db.jobs[id] : o, at = new Date().toISOString(), prev = woTaken(target), next = {};
    lines.forEach(L => { if (L.stockId && L.take > 0) next[L.stockId] = r3((next[L.stockId] || 0) + L.take); });
    const what = col === 'jobs' ? `работе № ${target.no || ''} · ${target.title || ''}` : `заказу ${o.number || ''} · ${o.title || ''}`;
    for (const sid of new Set([...Object.keys(prev), ...Object.keys(next)])) {
      const it = db.stock[sid], d = r3((next[sid] || 0) - (prev[sid] || 0)); if (!it || !d) continue;
      it.acctQty = r3((Number(it.acctQty) || 0) - d);
      it.moves = Array.isArray(it.moves) ? it.moves : [];
      it.moves.push({ id: newId(), type: 'wo', qty: d, acct: true, acctBalance: it.acctQty, balance: Number(it.qty) || 0, orderId: col === 'orders' ? id : (target.orderId || null), note: (prev[sid] ? 'Изменён список для списания по ' : 'Списание по ') + what, by: user.id, at });
      it.updatedAt = at; it.updatedBy = user.id;
    }
    target.woMap = map;
    if (target.woDraft) { delete target.woDraft.map; if (!target.woDraft.full) delete target.woDraft; }
    target.writeoff = { at, by: user.id, applied: true, lines: lines.map(L => ({ stockId: L.stockId, name: L.name, sku: L.sku, unit: L.unit, qty: L.take, need: L.need })) };
    saveDb();
  return { writeoff: target.writeoff };
}
function writeoffLines(o, mapOverride) {
  const taken = woTaken(o);
  const byName = new Map(Object.entries(db.stock).map(([id, it]) => [normName(it.name), id]));
  const map = mapOverride || o.woMap || {};
  const lines = new Map();
  for (const p of woProducts(o)) {
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
    // what will be written off: the quantity, but not more than the accounting balance
    const take = L.inStock ? r3(Math.max(0, Math.min(L.need, L.acct))) : 0;
    return { ...L, source, shortage, take };
  });   // in the order the lines were added to the list (not by name)
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
<numFmts count="1"><numFmt numFmtId="164" formatCode="General"/></numFmts>
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
  const sumOf = x => Number(x.sum) > 0 ? r2(x.sum) : r2((Number(x.qty) || 0) * (Number(x.price) || 0));
  const head = ['№', 'Номенклатура', 'Единица', 'Количество', 'Цена', 'Сумма', 'Наименование в накладной'].map(v => ({ v, s: 1 }));
  const goods = [head, ...lines.map((x, i) => [{ v: i + 1, s: 3 }, { v: nameOf(x), s: 2 }, { v: x.unit || 'шт', s: 2 }, { v: Number(x.qty) || 0, s: 3 },
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
  return xlsxBook([{ name: 'Товары', rows: goods, widths: [5, 50, 9, 12, 13, 14, 40] }, { name: 'Реквизиты', rows: info, widths: [30, 60] }]);
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
  const out = (wb && Array.isArray(wb.lines) && wb.lines.length ? woSavedOrdered(o, lines).map(L => { const it = L.stockId && db.stock[L.stockId]; return { name: it ? it.name : L.name, sku: (it && it.sku) || L.sku || '', unit: (it && it.unit) || L.unit || 'шт', qty: Number(L.qty) || 0 }; })
    : lines.map(L => ({ name: L.name, sku: L.sku || '', unit: L.unit || 'шт', qty: L.take }))).filter(L => L.qty > 0);
  const goods = [['№', 'Номенклатура', 'Единица', 'Количество'].map(v => ({ v, s: 1 })),
    ...out.map((L, i) => [{ v: i + 1, s: 3 }, { v: L.name, s: 2 }, { v: L.unit, s: 2 }, { v: L.qty, s: 3 }])];
  const bad = lines.filter(L => L.source !== 'acct');
  const info = [
    [{ v: 'Списание материалов', s: 10 }],
    [],
    ['Основание', job ? `Работа ${String(o.number || '').replace(/^работа\s*/, '')} · ${o.title || ''}` : `Заказ на производство ${o.number || ''} · ${o.title || ''}`],
    ...(ord ? [['Заказ на производство', `${ord.number || ''} · ${ord.title || ''}`]] : []),
    ...(cp || o.customer ? [['Заказчик', cp ? cp.name : o.customer]] : []),
    ...(woFullOn(o) ? [['Состав списка', 'на весь объём (изделия заказа не учитываются)']] : []),
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
    ['№', 'Наименование', 'Ед.', 'Нужно списать', 'Спишется', 'Бух. остаток', 'Факт. остаток', 'Состояние', 'Не хватает', 'Изделия'].map(v => ({ v, s: 1 })),
    ...lines.map((L, i) => { const [ts, ns] = st[L.source]; return [
      { v: i + 1, s: ns }, { v: L.name, s: ts }, { v: L.unit, s: ts }, { v: L.need, s: ns }, { v: L.take, s: ns },
      L.inStock ? { v: L.acct, s: ns } : { v: '—', s: ts }, L.inStock ? { v: L.real, s: ns } : { v: '—', s: ts },
      { v: SOURCE_LABEL[L.source], s: ts }, L.shortage ? { v: L.shortage, s: ns } : { v: '', s: ts }, { v: L.products.join(', '), s: ts }]; }),
    [],
    [{ v: 'Хватает бухгалтерского остатка', s: 4 }],
    [{ v: 'Позиции нет в бухгалтерских остатках или её не хватает', s: 8 }],
  ];
  return xlsxBook([{ name: 'Товары', rows: goods, widths: [5, 50, 9, 12] }, { name: 'Реквизиты', rows: info, widths: [30, 70] }, { name: 'Проверка остатков', rows: check, widths: [5, 42, 7, 13, 11, 13, 13, 30, 12, 30] }]);
}

/* the plain table of a write-off: what had to be written off, what is written off (not more than the books), what is short */
// the lines of a saved write-off in the order of the list (older saves were sorted by name)
function woSavedOrdered(o, lines) {
  const pos = new Map(lines.map((L, i) => [L.stockId || 'n:' + normName(L.name), i]));
  return o.writeoff.lines.map((L, i) => ({ L, k: pos.has(L.stockId || 'n:' + normName(L.name)) ? pos.get(L.stockId || 'n:' + normName(L.name)) : 1e6 + i })).sort((a, b) => a.k - b.k).map(x => x.L);
}
// the saved write-off does not match the list any more (lines added, removed or changed after «Сохранить список»)
function woStale(o, lines) {
  if (!(o.writeoff && o.writeoff.applied)) return false;
  const a = woTaken(o), b = {}; lines.forEach(L => { if (L.stockId && L.take > 0) b[L.stockId] = r3((b[L.stockId] || 0) + L.take); });
  return [...new Set([...Object.keys(a), ...Object.keys(b)])].some(k => Math.abs((a[k] || 0) - (b[k] || 0)) > 1e-9);
}
function writeoffPlainXlsx(o) {
  const lines = writeoffLines(o), wb = o.writeoff, saved = !!(wb && wb.applied && Array.isArray(wb.lines)), took = saved ? woTaken(o) : {};
  const fmt = iso => iso ? new Date(iso).toLocaleString('ru-RU', { timeZone: process.env.TZ || 'Europe/Moscow' }) : '';
  // exactly the lines of the list, in its order; «Списано» — what the saved write-off took (or what will be taken)
  // by the current list and the books (with what this order already took): exactly what the window shows
  const rows = lines.map(L => ({ name: L.name, unit: L.unit || 'шт', need: L.need, got: L.take, short: r3(Math.max(0, L.need - L.take)) }));
  const what = /^работа/.test(o.number || '') ? `Работа ${String(o.number || '').replace(/^работа\s*/, '')} · ${o.title || ''}` : `Заказ ${o.number || ''} · ${o.title || ''}`;
  const t = [
    [{ v: 'Списание материалов — ' + what, s: 10 }],
    [saved ? `Списание сохранено ${fmt(wb.at)}` : 'Список ещё не сохранён — в столбце «Списано» показано, сколько спишется'],
    [],
    ['№', 'Номенклатура', 'Ед.', 'Нужно списать', 'Списано', 'Не хватает'].map(v => ({ v, s: 1 })),
    ...rows.map((x, i) => [{ v: i + 1, s: x.short ? 9 : 3 }, { v: x.name, s: x.short ? 8 : 2 }, { v: x.unit, s: x.short ? 8 : 2 }, { v: x.need, s: x.short ? 9 : 3 }, { v: x.got, s: x.short ? 9 : 3 }, x.short ? { v: x.short, s: 9 } : { v: '', s: 2 }]),
  ];
  return xlsxBook([{ name: 'Списание', rows: t, widths: [5, 60, 7, 15, 13, 13] }]);
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
/* the rows of «Этикетки для модемов» as JSON; the key goes in «Authorization: Bearer …» (or ?key=…); ?since=<time> — only rows added or changed after it */
const snHash = t => crypto.createHash('sha256').update(String(t)).digest();
const snRow = x => ({ imei: x.imei, sn: x.sn, iccid: x.iccid, ip: x.ip || '', at: x.at, updatedAt: x.updatedAt || x.at });
async function snExport(req, res, url, o) {
  const st = orgState(o); if (st.blocked) return fail(res, 423, st.message);
  const A = db.snmapApi, m = String(req.headers.authorization || '').match(/^Bearer\s+(\S+)$/i), key = m ? m[1] : url.searchParams.get('key') || '';
  const throttleKey = 'snexp|' + clientIp(req);
  if (throttled(throttleKey)) return fail(res, 429, 'Слишком много неверных ключей. Подождите 10 минут.');
  if (!A || !A.hash || !key || !crypto.timingSafeEqual(snHash(key), Buffer.from(A.hash, 'hex'))) { attempts.get(throttleKey).push(Date.now()); return fail(res, 401, 'Неверный ключ доступа'); }
  const since = url.searchParams.get('since'), L = (Array.isArray(db.snmap) ? db.snmap : []).map(snRow).filter(x => !since || String(x.updatedAt) > since);
  // when and from where it was last used (without a new revision — the open pages need not reload)
  A.lastUsedAt = new Date().toISOString(); A.lastIp = clientIp(req); { const e = ctx(); writeJSON(e.file, e.db); e.stamp = stamp(e.file); }
  return send(res, 200, { organization: o.name, generatedAt: new Date().toISOString(), count: L.length, items: L });
}
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
      // «Этикетки для модемов» for another server: GET /api/sn-export/<organization> with the key of the organization (no session)
      if (url.pathname.startsWith('/api/sn-export/')) {
        const orgId = url.pathname.split('/')[3] || '', o = orgById(orgId);
        if (!o || req.method !== 'GET') return fail(res, 404, 'Не найдено');
        return await als.run(orgEntry(orgId), async () => snExport(req, res, url, o));
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

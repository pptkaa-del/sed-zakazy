'use strict';
/* «ФКУ Упрдор»: the monthly report documents of a requests organization — 7 Word files made from the templates
   in upr-templates/*.docx with {{MARKERS}}; the tables with a variable number of rows (the daily sheet, the requests,
   the replaced equipment) are filled by code. No dependencies: a docx is a ZIP of XML parts. */
const fs = require('node:fs');
const path = require('node:path');
const zlib = require('node:zlib');

const TEMPLATES = path.join(__dirname, 'upr-templates');

/* the systems: key → name; the order in the documents */
const SYSTEMS = { voice: 'Система голосового оповещения', sms: 'Система sms-оповещения', video: 'Система видеонаблюдения', acs: 'Система контроля и управления доступом' };
const SYS_ORDER = ['voice', 'sms', 'video', 'acs'];
/* the equipment as in the table of Appendix 4 (the defect list) */
const EQUIPMENT = ['Контроллер СКУД', 'Считыватель бесконтактный', 'Кнопка выхода', 'Замок электромагнитный',
  'Блок бесперебойного питания', 'Устройство разблокировки двери Smartec St-er115', 'Аккумуляторная батарея 3 Ач',
  'Преобразователь интерфейсов RS-485/RS-232', 'Реле мониторинга и управления серверным оборудованием',
  'IP видеокамера внутренняя', 'IP видеокамера внешняя', 'Шлюз IP',
  'Громкоговоритель настенный 6/3Вт 100В', 'Громкоговоритель потолочный 6/3Вт/100В'];
const DEFAULT_CONTRACT = { no: '100076398126100092', date: '2026-07-13', prices: { voice: '365.28', sms: '5.47', video: '1314.40', acs: '1572.18' }, vat: 22 };

const MONTHS_GEN = ['января', 'февраля', 'марта', 'апреля', 'мая', 'июня', 'июля', 'августа', 'сентября', 'октября', 'ноября', 'декабря'];
const MONTHS_NOM = ['январь', 'февраль', 'март', 'апрель', 'май', 'июнь', 'июль', 'август', 'сентябрь', 'октябрь', 'ноябрь', 'декабрь'];

/* ---------- ZIP ---------- */
const CRC = (() => { const t = new Int32Array(256); for (let n = 0; n < 256; n++) { let c = n; for (let k = 0; k < 8; k++) c = c & 1 ? 0xEDB88320 ^ (c >>> 1) : c >>> 1; t[n] = c; } return t; })();
const crc32 = b => { let c = -1; for (let i = 0; i < b.length; i++) c = CRC[(c ^ b[i]) & 0xFF] ^ (c >>> 8); return (c ^ -1) >>> 0; };
function unzip(buf) {
  let e = buf.length - 22;
  while (e >= 0 && buf.readUInt32LE(e) !== 0x06054b50) e--;
  if (e < 0) throw new Error('Шаблон повреждён (не ZIP)');
  const n = buf.readUInt16LE(e + 10); let o = buf.readUInt32LE(e + 16);
  const out = [];
  for (let i = 0; i < n; i++) {
    const method = buf.readUInt16LE(o + 10), csize = buf.readUInt32LE(o + 20), nl = buf.readUInt16LE(o + 28), xl = buf.readUInt16LE(o + 30), cl = buf.readUInt16LE(o + 32), lo = buf.readUInt32LE(o + 42);
    const name = buf.slice(o + 46, o + 46 + nl).toString('utf8');
    const start = lo + 30 + buf.readUInt16LE(lo + 26) + buf.readUInt16LE(lo + 28), raw = buf.slice(start, start + csize);
    if (!name.endsWith('/')) out.push({ name, data: method === 0 ? raw : zlib.inflateRawSync(raw) });
    o += 46 + nl + xl + cl;
  }
  return out;
}
function zip(entries, deflate = true) {
  const now = new Date();
  const t = ((now.getHours() << 11) | (now.getMinutes() << 5) | (now.getSeconds() >> 1)) & 0xFFFF;
  const d = (((now.getFullYear() - 1980) << 9) | ((now.getMonth() + 1) << 5) | now.getDate()) & 0xFFFF;
  const parts = [], central = []; let offset = 0;
  for (const e of entries) {
    const name = Buffer.from(e.name, 'utf8'), raw = Buffer.isBuffer(e.data) ? e.data : Buffer.from(e.data, 'utf8'), crc = crc32(raw);
    const data = deflate ? zlib.deflateRawSync(raw, { level: 6 }) : raw, method = deflate ? 8 : 0;
    const h = Buffer.alloc(30);
    h.writeUInt32LE(0x04034b50, 0); h.writeUInt16LE(20, 4); h.writeUInt16LE(0x0800, 6); h.writeUInt16LE(method, 8); h.writeUInt16LE(t, 10); h.writeUInt16LE(d, 12);
    h.writeUInt32LE(crc, 14); h.writeUInt32LE(data.length, 18); h.writeUInt32LE(raw.length, 22); h.writeUInt16LE(name.length, 26);
    const c = Buffer.alloc(46);
    c.writeUInt32LE(0x02014b50, 0); c.writeUInt16LE(20, 4); c.writeUInt16LE(20, 6); c.writeUInt16LE(0x0800, 8); c.writeUInt16LE(method, 10); c.writeUInt16LE(t, 12); c.writeUInt16LE(d, 14);
    c.writeUInt32LE(crc, 16); c.writeUInt32LE(data.length, 20); c.writeUInt32LE(raw.length, 24); c.writeUInt16LE(name.length, 28); c.writeUInt32LE(offset, 42);
    parts.push(h, name, data); central.push(c, name); offset += 30 + name.length + data.length;
  }
  const cd = Buffer.concat(central), end = Buffer.alloc(22);
  end.writeUInt32LE(0x06054b50, 0); end.writeUInt16LE(entries.length, 8); end.writeUInt16LE(entries.length, 10); end.writeUInt32LE(cd.length, 12); end.writeUInt32LE(offset, 16);
  return Buffer.concat([...parts, cd, end]);
}

/* ---------- a minimal XML tree: elements { name, attrs: [[k, v]], kids }, text nodes are raw (still escaped) strings ---------- */
function parseXml(s) {
  const root = { name: '#root', attrs: [], kids: [] }, stack = [root]; let i = 0;
  while (i < s.length) {
    const lt = s.indexOf('<', i);
    if (lt < 0) { stack[stack.length - 1].kids.push(s.slice(i)); break; }
    if (lt > i) stack[stack.length - 1].kids.push(s.slice(i, lt));
    if (s.startsWith('<?', lt)) { const e = s.indexOf('?>', lt); root.kids.push({ raw: s.slice(lt, e + 2) }); i = e + 2; continue; }
    if (s.startsWith('<!--', lt)) { const e = s.indexOf('-->', lt); stack[stack.length - 1].kids.push({ raw: s.slice(lt, e + 3) }); i = e + 3; continue; }
    if (s.startsWith('<![CDATA[', lt)) { const e = s.indexOf(']]>', lt); stack[stack.length - 1].kids.push({ raw: s.slice(lt, e + 3) }); i = e + 3; continue; }
    if (s[lt + 1] === '/') { const e = s.indexOf('>', lt); stack.pop(); i = e + 1; continue; }
    // an opening tag: quoted attribute values may hold '>'
    let j = lt + 1, q = null;
    for (; j < s.length; j++) { const c = s[j]; if (q) { if (c === q) q = null; } else if (c === '"' || c === "'") q = c; else if (c === '>') break; }
    let body = s.slice(lt + 1, j); const self = body.endsWith('/'); if (self) body = body.slice(0, -1);
    const m = body.match(/^([^\s/]+)/), el = { name: m[1], attrs: [], kids: [] };
    for (const a of body.slice(m[1].length).matchAll(/([^\s=]+)\s*=\s*("([^"]*)"|'([^']*)')/g)) el.attrs.push([a[1], a[3] ?? a[4]]);
    stack[stack.length - 1].kids.push(el);
    if (!self) stack.push(el);
    i = j + 1;
  }
  return root;
}
const serXml = n => typeof n === 'string' ? n : n.raw !== undefined ? n.raw : n.name === '#root' ? n.kids.map(serXml).join('')
  : `<${n.name}${n.attrs.map(([k, v]) => ` ${k}="${v}"`).join('')}${n.kids.length ? `>${n.kids.map(serXml).join('')}</${n.name}>` : '/>'}`;
const unesc = s => s.replace(/&(#x[0-9a-f]+|#\d+|amp|lt|gt|quot|apos);/gi, (_, e) => e[0] === '#' ? String.fromCodePoint(e[1].toLowerCase() === 'x' ? parseInt(e.slice(2), 16) : parseInt(e.slice(1), 10)) : { amp: '&', lt: '<', gt: '>', quot: '"', apos: "'" }[e.toLowerCase()]);
const esc = s => String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;').replace(/[\u0000-\u0008\u000B\u000C\u000E-\u001F]/g, '');
const els = n => n.kids.filter(k => typeof k === 'object' && k.name);
const kids = (n, name) => els(n).filter(k => k.name === name);
const kid = (n, name) => els(n).find(k => k.name === name);
function* walk(n, name) { for (const k of els(n)) { if (k.name === name) yield k; yield* walk(k, name); } }
const attr = (n, k) => (n.attrs.find(a => a[0] === k) || [])[1];
const setAttr = (n, k, v) => { const a = n.attrs.find(x => x[0] === k); if (a) a[1] = v; else n.attrs.push([k, v]); };
const clone = n => typeof n === 'string' ? n : { ...n, attrs: n.attrs ? n.attrs.map(a => [...a]) : undefined, kids: n.kids ? n.kids.map(clone) : undefined };
const el = (name, attrs = [], ks = []) => ({ name, attrs, kids: ks });

/* ---------- Word: runs, paragraphs, cells, rows ---------- */
function runText(r) {
  let t = '';
  for (const k of els(r)) {
    if (k.name === 'w:t') t += unesc(k.kids.filter(x => typeof x === 'string').join(''));
    else if (k.name === 'w:tab' || k.name === 'w:ptab') t += '\t';
    else if (k.name === 'w:br' || k.name === 'w:cr') t += '\n';
    else if (k.name === 'w:noBreakHyphen') t += '-';
  }
  return t;
}
const CONTENT = new Set(['w:t', 'w:tab', 'w:ptab', 'w:br', 'w:cr', 'w:noBreakHyphen', 'w:softHyphen', 'w:sym', 'w:delText']);
function setRunText(r, text) {
  r.kids = r.kids.filter(k => !(typeof k === 'object' && CONTENT.has(k.name)));
  String(text).split(/(\t|\n)/).forEach(part => {
    if (part === '\t') r.kids.push(el('w:tab'));
    else if (part === '\n') r.kids.push(el('w:br'));
    else if (part) r.kids.push(el('w:t', /^\s|\s$/.test(part) ? [['xml:space', 'preserve']] : [], [esc(part)]));
  });
}
const runs = p => kids(p, 'w:r');
const parText = p => runs(p).map(runText).join('');
// the text of a paragraph as Word shows it: runs inside hyperlinks too
const parFullText = p => els(p).map(k => k.name === 'w:r' ? runText(k) : k.name === 'w:hyperlink' ? parFullText(k) : '').join('');
function replaceInPar(p, old, nw) {
  const rs = runs(p), full = rs.map(runText).join(''), i = full.indexOf(old);
  if (i < 0) return false;
  const j = i + old.length; let pos = 0, first = true;
  for (const r of rs) {
    const t = runText(r), a = pos, b = pos + t.length; pos = b;
    if (b <= i || a >= j) continue;
    const s = Math.max(i, a) - a, e = Math.min(j, b) - a;
    if (first) { setRunText(r, t.slice(0, s) + nw + t.slice(e)); first = false; } else setRunText(r, t.slice(0, s) + t.slice(e));
  }
  return true;
}
function fillTokens(body, values) {
  for (const p of walk(body, 'w:p')) {
    for (const tok of new Set([...parText(p).matchAll(/\{\{(\w+)\}\}/g)].map(m => m[1]))) {
      if (!(tok in values)) throw new Error(`Нет значения для маркера {{${tok}}}`);
      while (replaceInPar(p, `{{${tok}}}`, String(values[tok])));
    }
  }
  const left = [...walk(body, 'w:p')].flatMap(p => parFullText(p).match(/\{\{\w+\}\}/g) || []);
  if (left.length) throw new Error('Незаполненные маркеры: ' + left.join(', '));
}
const tables = body => { const out = []; (function f(n) { for (const k of els(n)) { if (k.name === 'w:tbl') out.push(k); else f(k); } })(body); return out; };
const rows = tbl => kids(tbl, 'w:tr');
// the cells of a row by the columns of the grid: a cell spanning N columns comes N times
function cells(tr) {
  const out = [];
  for (const k of els(tr)) {
    const tcs = k.name === 'w:tc' ? [k] : k.name === 'w:sdt' ? [...walk(k, 'w:tc')] : [];
    for (const tc of tcs) { const span = Number(attr(kid(kid(tc, 'w:tcPr') || el('x'), 'w:gridSpan') || el('x'), 'w:val')) || 1; for (let s = 0; s < span; s++) out.push(tc); }
  }
  return out;
}
const cellText = tc => kids(tc, 'w:p').map(parText).join('\n');
function setCell(tc, text) {
  const ps = kids(tc, 'w:p'), p = ps[0], rs = runs(p);
  if (rs.length) { setRunText(rs[0], text); rs.slice(1).forEach(r => setRunText(r, '')); }
  else { const r = el('w:r'); setRunText(r, text); p.kids.push(r); }
  for (const x of ps.slice(1)) tc.kids.splice(tc.kids.indexOf(x), 1);
}
// keeps the first `keep` rows, the others become n copies of the template row
function rebuildRows(tbl, keep, n, tmpl) {
  const rs = rows(tbl), t = clone(tmpl || rs[keep]);
  for (const r of rs.slice(keep)) tbl.kids.splice(tbl.kids.indexOf(r), 1);
  return Array.from({ length: n }, () => { const r = clone(t); tbl.kids.push(r); return r; });
}

/* ---------- a document ---------- */
function openDoc(name) {
  const parts = unzip(fs.readFileSync(path.join(TEMPLATES, name)));
  const get = n => parts.find(x => x.name === n);
  const doc = parseXml(get('word/document.xml').data.toString('utf8'));
  const body = kid(kid(doc, 'w:document'), 'w:body');
  return { parts, doc, body, get, tables: tables(body) };
}
function saveDoc(d) {
  d.get('word/document.xml').data = Buffer.from(serXml(d.doc), 'utf8');
  for (const [n, x] of d.extra || []) d.get(n).data = Buffer.from(serXml(x), 'utf8');
  return zip(d.parts);
}
/* the act is printed in Times New Roman everywhere: runs, styles, headers and footers */
function forceFont(d, font = 'Times New Roman') {
  const fix = rpr => {
    let rf = kid(rpr, 'w:rFonts');
    if (!rf) { rf = el('w:rFonts'); const rs = kid(rpr, 'w:rStyle'); rpr.kids.splice(rs ? rpr.kids.indexOf(rs) + 1 : 0, 0, rf); }
    rf.attrs = ['ascii', 'hAnsi', 'cs', 'eastAsia'].map(a => ['w:' + a, font]);
  };
  const fixTree = root => {
    for (const r of walk(root, 'w:r')) if (!kid(r, 'w:rPr')) r.kids.unshift(el('w:rPr'));
    for (const rpr of walk(root, 'w:rPr')) fix(rpr);
  };
  d.extra = d.extra || [];
  fixTree(d.doc);
  for (const p of d.parts) if (/^word\/(header|footer)\d*\.xml$/.test(p.name)) { const x = parseXml(p.data.toString('utf8')); fixTree(x); d.extra.push([p.name, x]); }
  const sp = d.get('word/styles.xml');
  if (sp) {
    const x = parseXml(sp.data.toString('utf8')), styles = kid(x, 'w:styles'); fixTree(x);
    const dd = kid(styles, 'w:docDefaults');
    if (dd) {
      let rpd = kid(dd, 'w:rPrDefault'); if (!rpd) { rpd = el('w:rPrDefault'); dd.kids.unshift(rpd); }
      let rpr = kid(rpd, 'w:rPr'); if (!rpr) { rpr = el('w:rPr'); rpd.kids.push(rpr); }
      fix(rpr);
    }
    for (const st of kids(styles, 'w:style')) {
      if (['paragraph', 'table', 'character'].includes(attr(st, 'w:type')) && !kid(st, 'w:rPr') && attr(st, 'w:default') === '1') {
        const rpr = el('w:rPr'), ppr = kid(st, 'w:pPr');
        if (ppr) st.kids.splice(st.kids.indexOf(ppr) + 1, 0, rpr); else st.kids.push(rpr);
        fix(rpr);
      }
    }
    d.extra.push(['word/styles.xml', x]);
  }
}

/* ---------- numbers and words ---------- */
const ONES_M = ['', 'один', 'два', 'три', 'четыре', 'пять', 'шесть', 'семь', 'восемь', 'девять'];
const ONES_F = ['', 'одна', 'две', 'три', 'четыре', 'пять', 'шесть', 'семь', 'восемь', 'девять'];
const TEENS = ['десять', 'одиннадцать', 'двенадцать', 'тринадцать', 'четырнадцать', 'пятнадцать', 'шестнадцать', 'семнадцать', 'восемнадцать', 'девятнадцать'];
const TENS = ['', '', 'двадцать', 'тридцать', 'сорок', 'пятьдесят', 'шестьдесят', 'семьдесят', 'восемьдесят', 'девяносто'];
const HUND = ['', 'сто', 'двести', 'триста', 'четыреста', 'пятьсот', 'шестьсот', 'семьсот', 'восемьсот', 'девятьсот'];
const trip = (n, fem) => { const r = n % 100; return [HUND[Math.floor(n / 100)], ...(r >= 10 && r < 20 ? [TEENS[r - 10]] : [TENS[Math.floor(r / 10)], (fem ? ONES_F : ONES_M)[r % 10]])].filter(Boolean); };
const plural = (n, a, b, c) => { n %= 100; if (n >= 11 && n <= 19) return c; n %= 10; return n === 1 ? a : n >= 2 && n <= 4 ? b : c; };
function words(n) {
  if (!n) return 'ноль';
  const m = Math.floor(n / 1e6), t = Math.floor(n / 1000) % 1000, r = n % 1000, w = [];
  if (m) w.push(...trip(m), plural(m, 'миллион', 'миллиона', 'миллионов'));
  if (t) w.push(...trip(t, true), plural(t, 'тысяча', 'тысячи', 'тысяч'));
  if (r) w.push(...trip(r));
  return w.join(' ');
}
/* money is kept in kopecks (integers) */
const toK = v => { const s = String(v ?? '0').trim().replace(',', '.'); if (!/^-?\d+(\.\d+)?$/.test(s)) return 0; const [a, b = ''] = s.replace('-', '').split('.'); const k = Number(a) * 100 + Number((b + '00').slice(0, 2)) + (Number(b[2] || 0) >= 5 ? 1 : 0); return s.startsWith('-') ? -k : k; };
const fix2 = k => `${k < 0 ? '-' : ''}${Math.floor(Math.abs(k) / 100)}.${String(Math.abs(k) % 100).padStart(2, '0')}`;
const fmtA = k => fix2(k).replace('.', ',');                                                   // 10958,40
const fmtB = k => fix2(k).replace(/\B(?=(\d{3})+(?!\d))(?=\d*\.)/g, ' ').replace('.', ',');     // 10 958,40
const phrase = k => { const r = Math.floor(k / 100), c = k % 100, w = words(r); return [fix2(k), `(${w[0].toUpperCase() + w.slice(1)}) ${plural(r, 'рубль', 'рубля', 'рублей')} ${String(c).padStart(2, '0')} ${plural(c, 'копейка', 'копейки', 'копеек')}`]; };
const penText = k => { const r = Math.floor(k / 100), c = k % 100; return `${r} (${words(r)}) ${plural(r, 'рубль', 'рубля', 'рублей')} ${c} ${plural(c, 'копейка', 'копейки', 'копеек')}`; };

/* ---------- dates: plain { y, m, d } and day numbers ---------- */
const ymd = s => { const [y, m, d] = String(s).slice(0, 10).split('-').map(Number); return { y, m, d }; };
const dayNo = x => Date.UTC(x.y, x.m - 1, x.d) / 864e5;
const fromNo = n => { const t = new Date(n * 864e5); return { y: t.getUTCFullYear(), m: t.getUTCMonth() + 1, d: t.getUTCDate() }; };
const p2 = n => String(n).padStart(2, '0');
const dq = x => `«${p2(x.d)}» ${MONTHS_GEN[x.m - 1]} ${x.y} г.`;
const dtxt = x => `${p2(x.d)} ${MONTHS_GEN[x.m - 1]} ${x.y} г.`;
const dnum = x => `${p2(x.d)}.${p2(x.m)}.${x.y}`;
const iso = x => `${x.y}-${p2(x.m)}-${p2(x.d)}`;
/* a moment as local wall-clock time in the time zone of the organization: 'YYYY-MM-DD HH:MM' */
function localStamp(isoStr, tz) {
  const p = Object.fromEntries(new Intl.DateTimeFormat('en-CA', { timeZone: tz, year: 'numeric', month: '2-digit', day: '2-digit', hour: '2-digit', minute: '2-digit', hourCycle: 'h23' })
    .formatToParts(new Date(isoStr)).map(x => [x.type, x.value]));
  return `${p.year}-${p.month}-${p.day} ${p.hour}:${p.minute}`;
}

/* ---------- the calculation ---------- */
function compute(cfg) {
  const price = Object.fromEntries(SYS_ORDER.map(k => [k, toK(cfg.prices[k])]));
  const ps = { y: cfg.year, m: cfg.month, d: 1 }, pe = fromNo(dayNo({ y: cfg.month === 12 ? cfg.year + 1 : cfg.year, m: cfg.month === 12 ? 1 : cfg.month + 1, d: 1 }) - 1);
  const cd = ymd(cfg.contractDate), start = Math.max(dayNo(ps), dayNo(cd));
  const days = []; for (let n = start; n <= dayNo(pe); n++) days.push(fromNo(n));
  const n = days.length, sums = Object.fromEntries(SYS_ORDER.map(k => [k, price[k] * n]));
  const total = SYS_ORDER.reduce((s, k) => s + sums[k], 0), dayTotal = SYS_ORDER.reduce((s, k) => s + price[k], 0);
  const prev = cfg.prevTotal != null && cfg.prevTotal !== '' ? toK(cfg.prevTotal) : dayTotal * Math.max(dayNo(ps) - dayNo(cd), 0);
  const penalty = toK(cfg.penalty), payable = total - penalty, vr = Number(cfg.vat) || 0;
  const vat = x => { const q = x * vr, d = 100 + vr; return Math.floor((2 * q + d) / (2 * d)); };
  return { price, days, n, sums, total, dayTotal, cum: prev + total, penalty, payable, vat: vat(total), payableVat: vat(payable), ps, pe };
}

/* ---------- the documents ---------- */
function commonTokens(cfg, c) {
  const cd = ymd(cfg.contractDate), dd = ymd(cfg.docDate);
  return {
    PERIOD_FROM: dq(c.ps), PERIOD_TO: dq(c.pe), PERIOD_FROM_NUM: dnum(c.ps), PERIOD_TO_NUM: dnum(c.pe),
    CONTRACT_NO: cfg.contractNo, CONTRACT_DATE_Q: dq(cd), CONTRACT_DATE_TEXT: dtxt(cd), CONTRACT_DATE_NUM: dnum(cd),
    DOC_DATE_Q: dq(dd), DOC_DATE_TEXT: dtxt(dd), DOC_DATE_COMPACT: dtxt(dd).replace(' г.', 'г.'),
    LETTER_NO: cfg.letterNo, MAINT_DATE: dnum(cfg.maintDate ? ymd(cfg.maintDate) : c.pe), VAT_RATE: cfg.vat,
  };
}
function buildAct(cfg, c, tok) {
  const d = openDoc('act.docx');
  for (const t of d.tables.slice(0, 2)) rows(t).slice(1, 5).forEach((r, i) => { const k = SYS_ORDER[i], cs = cells(r); setCell(cs[2], String(c.n)); setCell(cs[3], fmtA(c.price[k])); setCell(cs[4], fmtA(c.sums[k])); });
  for (const [key, v] of [['CUM', c.cum], ['TOTAL', c.total], ['VAT', c.vat], ['PAYABLE', c.payable], ['PAYABLE_VAT', c.payableVat]]) [tok[key + '_NUM'], tok[key + '_WORDS']] = phrase(v);
  tok.PENALTY_TEXT = penText(c.penalty);
  fillTokens(d.body, tok);
  forceFont(d);
  return d;
}
function buildInfo(cfg, c, tok) {
  const d = openDoc('info_sheet.docx'), [t1, t2] = [d.tables[1], d.tables[2]];
  rows(t1).slice(1, 5).forEach((r, i) => { const k = SYS_ORDER[i], cs = cells(r); setCell(cs[1], fmtA(c.price[k])); setCell(cs[cs.length - 1], fmtB(c.sums[k])); });
  { const cs = cells(rows(t1)[5]); setCell(cs[cs.length - 1], fmtB(c.total)); }
  const rs = rows(t2), totals = clone(rs[rs.length - 1]);
  rebuildRows(t2, 1, c.n, rs[1]).forEach((r, i) => {
    const cs = cells(r), day = c.days[i];
    setCell(cs[0], dnum(day)); SYS_ORDER.forEach((k, j) => setCell(cs[13 + j], fmtB(c.price[k]))); setCell(cs[17], fmtB(c.dayTotal));
  });
  t2.kids.push(totals);
  { const cs = cells(totals); SYS_ORDER.forEach((k, j) => setCell(cs[13 + j], fmtB(c.sums[k]))); setCell(cs[17], fmtB(c.total)); }
  fillTokens(d.body, tok);
  return d;
}
function buildSimple(name, tok) { const d = openDoc(name); fillTokens(d.body, tok); return d; }
function buildTickets(cfg, c, tok, tickets) {
  const d = openDoc('tickets_report.docx'), T = d.tables, tmpl = clone(rows(T[4])[1]);
  const by = Object.fromEntries(SYS_ORDER.map(k => [k, tickets.filter(t => t.system === k).sort((a, b) => a.created.localeCompare(b.created) || a.number - b.number)]));
  rows(T[1]).slice(1, 5).forEach((r, i) => { const ts = by[SYS_ORDER[i]], cs = cells(r);
    [ts.length, ts.filter(t => t.closed).length, ts.filter(t => !t.closed).length, ts.filter(t => t.overdue).length].forEach((v, j) => setCell(cs[1 + j], String(v))); });
  T.slice(2, 6).forEach((tbl, ti) => {
    const ts = by[SYS_ORDER[ti]], rs = rebuildRows(tbl, 1, Math.max(ts.length, 1), tmpl);
    if (!ts.length) { cells(rs[0]).forEach(tc => setCell(tc, '')); return; }
    rs.forEach((r, i) => { const t = ts[i], done = !!t.closed;
      const vals = [`${i + 1}.`, t.created.slice(0, 10), t.created.slice(11, 16), done ? t.closed : '—', `№${String(t.number).padStart(3, '0')}`,
        done ? 'Исполнена' : 'В работе', done ? 'Работа завершена' : 'В работе', t.description, t.answer || (done ? '' : 'На исполнении'), t.equipment || '—'];
      cells(r).forEach((tc, j) => { if (j < vals.length) setCell(tc, vals[j]); }); });
  });
  Object.assign(tok, { N_VOICE: by.voice.length, N_SMS: by.sms.length, N_VIDEO: by.video.length, N_ACS: by.acs.length });
  fillTokens(d.body, tok);
  return d;
}
function buildDefects(cfg, c, tok, repl) {
  const d = openDoc('defect_list.docx'), T = d.tables, cat = T[1], catRows = rows(cat);
  const names = new Map(catRows.slice(1, -1).map(r => [cellText(cells(r)[1]).trim().toLowerCase(), r]));
  for (const r of names.values()) setCell(cells(r)[2], '0');
  for (const x of repl) {
    const r = names.get(x.category.trim().toLowerCase());
    if (!r) throw new Error(`Неизвестная категория оборудования «${x.category}»`);
    setCell(cells(r)[2], String(Number(cellText(cells(r)[2])) + 1));
  }
  setCell(cells(catRows[catRows.length - 1])[2], String(repl.length));
  const tmpl = clone(rows(T[2])[2]);
  T.slice(2, 6).forEach((tbl, ti) => {
    const k = ['acs', 'video', 'sms', 'voice'][ti], xs = repl.filter(x => x.system === k).sort((a, b) => a.date.localeCompare(b.date) || a.ticket - b.ticket);
    const rs = rebuildRows(tbl, 2, Math.max(xs.length, 1), tmpl);
    if (!xs.length) cells(rs[0]).forEach(tc => setCell(tc, ''));
    xs.forEach((x, i) => { const vals = [dnum(ymd(x.date)), x.equipment, String(x.ticket), x.newSerial, x.oldSerial]; cells(rs[i]).forEach((tc, j) => { if (j < vals.length) setCell(tc, vals[j]); }); });
  });
  fillTokens(d.body, tok);
  return d;
}

/* cfg: { year, month, docDate:'YYYY-MM-DD', contractNo, contractDate, prices:{voice,sms,video,acs}, vat, penalty, letterNo, prevTotal?, maintDate? }
   tickets: [{ number, system:'voice|sms|video|acs', description, created:'YYYY-MM-DD HH:MM', closed:'YYYY-MM-DD HH:MM'|null, answer, equipment, overdue }]
   replacements: [{ date:'YYYY-MM-DD', system, category, equipment, ticket, newSerial, oldSerial }] */
function generate(cfg, tickets = [], replacements = []) {
  const c = compute(cfg), tok = commonTokens(cfg, c), from = iso(c.ps), to = iso(c.pe), doc = cfg.docDate;
  tickets = tickets.filter(t => t.created.slice(0, 10) >= from && t.created.slice(0, 10) <= to);
  replacements = replacements.filter(r => r.date >= from && r.date <= to);
  const warnings = [];
  for (const t of tickets) {
    if (t.closed && t.closed < t.created) warnings.push(`Заявка №${t.number}: дата закрытия ${t.closed} раньше даты создания ${t.created}`);
    if (t.closed && t.closed.slice(0, 10) > doc) warnings.push(`Заявка №${t.number}: дата закрытия ${t.closed} позже даты документов ${doc}`);
    else if (t.closed && t.closed.slice(0, 10) > to) warnings.push(`Заявка №${t.number}: закрыта ${t.closed.slice(0, 10)} — после окончания отчётного периода`);
    if (!t.equipment) warnings.push(`Заявка №${t.number}: не указано оборудование (будет «—»)`);
  }
  const suffix = `(${MONTHS_NOM[cfg.month - 1]} ${cfg.year})`;
  const docs = [
    ['1. Акт сдачи-приемки оказанных услуг', buildAct(cfg, c, { ...tok })],
    ['2. Приложение 1 к Акту сдачи-приемки (информационная справка)', buildInfo(cfg, c, { ...tok })],
    ['3. Приложение 1 к Акту регламентных работ', buildSimple('maintenance_appendix1.docx', { ...tok })],
    ['4. Приложение 2 - Акт регламентных работ', buildSimple('maintenance_act.docx', { ...tok })],
    ['5. Приложение 3 - Отчет о выполнении заявок', buildTickets(cfg, c, { ...tok }, tickets)],
    ['6. Приложение 4 - Дефектная ведомость', buildDefects(cfg, c, { ...tok }, replacements)],
    ['7. Письмо об оказании услуг', buildSimple('letter.docx', { ...tok })],
  ];
  const files = docs.map(([title, d]) => ({ name: `${title} ${suffix}.docx`, data: saveDoc(d) }));
  return { files, zip: zip(files), warnings,
    totals: { days: c.n, total: fix2(c.total), vat: fix2(c.vat), cumulative: fix2(c.cum), payable: fix2(c.payable), tickets: tickets.length, replacements: replacements.length } };
}

module.exports = { generate, SYSTEMS, SYS_ORDER, EQUIPMENT, DEFAULT_CONTRACT, localStamp, MONTHS_NOM };

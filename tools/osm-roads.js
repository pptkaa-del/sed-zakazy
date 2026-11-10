#!/usr/bin/env node
'use strict';
/*
 * Builds public/vendor/osm-moscow/roads.json for the «Замена ДТ» tab: the lines of the MKAD, the TTK
 * and road overpasses (bridges) of Moscow, taken from an OpenStreetMap extract.
 *
 *   node tools/osm-roads.js <extract.osm.pbf> [west,south,east,north]
 *
 * The extract can be e.g. https://download.geofabrik.de/russia/central-fed-district-latest.osm.pbf.
 * Needs osmium-tool (apt install osmium-tool). Data: © OpenStreetMap contributors, ODbL.
 */
const { execFileSync } = require('node:child_process');
const fs = require('node:fs');
const os = require('node:os');
const path = require('node:path');

const [src, box = '36.80,55.10,38.20,56.20'] = process.argv.slice(2);
if (!src) { console.error('Укажите файл выгрузки: node tools/osm-roads.js extract.osm.pbf [w,s,e,n]'); process.exit(1); }
const tmp = fs.mkdtempSync(path.join(os.tmpdir(), 'osm-roads-'));
const T = n => path.join(tmp, n);
const osmium = (...a) => execFileSync('osmium', a, { stdio: ['ignore', 'pipe', 'inherit'], maxBuffer: 1 << 30 });

console.log('Вырезаем область', box);
osmium('extract', '-b', box, src, '-o', T('area.pbf'), '--overwrite');
console.log('Кольца и эстакады…');
osmium('tags-filter', T('area.pbf'),
  'r/ref=МКАД', 'r/name=Московская кольцевая автомобильная дорога', 'r/name=Третье транспортное кольцо', 'r/ref=ТТК',
  'w/ref=МКАД', 'w/name=Московская кольцевая автомобильная дорога', 'w/name=МКАД', 'w/name=Третье транспортное кольцо', 'w/ref=ТТК',
  '-o', T('rings.pbf'), '--overwrite');
osmium('tags-filter', T('area.pbf'), 'w/bridge', '-o', T('bridges.pbf'), '--overwrite');

/* ways with their tags and node coordinates, and relations with their member ways, from OPL text */
function readOpl(file) {
  osmium('cat', file, '-f', 'opl', '-o', T('x.opl'), '--overwrite');
  const nodes = new Map(), ways = new Map(), rels = [];
  const unesc = s => s.replace(/%([0-9a-f]+)%/gi, (_, h) => String.fromCodePoint(parseInt(h, 16)));
  const tags = s => Object.fromEntries((s || '').split(',').filter(Boolean).map(kv => { const i = kv.indexOf('='); return [unesc(kv.slice(0, i)), unesc(kv.slice(i + 1))]; }));
  for (const line of fs.readFileSync(T('x.opl'), 'utf8').split('\n')) {
    if (!line) continue;
    const f = Object.fromEntries(line.split(' ').slice(1).map(x => [x[0], x.slice(1)]));
    const id = line.split(' ')[0];
    if (id[0] === 'n') nodes.set(id.slice(1), [Number(f.y), Number(f.x)]);
    else if (id[0] === 'w') ways.set(id.slice(1), { id: Number(id.slice(1)), tags: tags(f.T), nodes: (f.N || '').split(',').filter(Boolean).map(n => n.slice(1)) });
    else if (id[0] === 'r') rels.push({ tags: tags(f.T), members: (f.M || '').split(',').filter(m => m[0] === 'w').map(m => m.slice(1).split('@')[0]) });
  }
  return { nodes, ways, rels };
}
const HW = /^(motorway|trunk|primary|secondary|tertiary|unclassified|residential|service|motorway_link|trunk_link|primary_link|secondary_link|tertiary_link)$/;
const R = readOpl(T('rings.pbf'));
const isMkad = t => /(^|;)МКАД($|;)/.test(t.ref || '') || /^(МКАД|Московская кольцевая автомобильная дорога)$/.test(t.name || '');
const isTtk = t => /(^|;)ТТК($|;)/.test(t.ref || '') || /Третье транспортное кольцо/.test(t.name || '');
const pick = test => {
  const ids = new Set();
  R.rels.filter(r => test(r.tags)).forEach(r => r.members.forEach(m => ids.add(m)));
  for (const [id, w] of R.ways) if (test(w.tags)) ids.add(id);
  return [...ids].map(id => R.ways.get(id)).filter(w => w && HW.test(w.tags.highway || ''));
};
const mkad = pick(isMkad), ttk = pick(isTtk);
const B = readOpl(T('bridges.pbf'));
const bridges = [...B.ways.values()].filter(w => HW.test(w.tags.highway || '') && w.tags.bridge && w.tags.bridge !== 'no')
  .filter(w => { const n = (w.tags['bridge:name'] || '') + ' ' + (w.tags.name || ''); return /эстакад/i.test(n) || !/(^|[^а-яё])мост(?![а-яё])|мостик/i.test(n); });

/* compact lines: integer micro-degrees, the first point absolute and the rest as differences */
const enc = (w, nodes, keep) => {
  const c = []; let pa = 0, po = 0;
  for (const n of w.nodes) { const p = nodes.get(n); if (!p) continue; const a = Math.round(p[0] * 1e6), o = Math.round(p[1] * 1e6); c.push(a - pa, o - po); pa = a; po = o; }
  const t = {}; keep.forEach(k => { if (w.tags[k]) t[k] = w.tags[k]; });
  return c.length >= 4 ? { i: w.id, t, c } : null;
};
const [W, S, E, N] = box.split(',').map(Number);
let date = '';
try { date = String(execFileSync('osmium', ['fileinfo', '-g', 'header.option.osmosis_replication_timestamp', src])).trim().slice(0, 10); } catch {}
if (!date) date = new Date(fs.statSync(src).mtime).toISOString().slice(0, 10);
const out = {
  source: 'OpenStreetMap', license: '© участники OpenStreetMap, ODbL 1.0 — https://www.openstreetmap.org/copyright', date,
  bbox: [S, W, N, E],
  mkad: mkad.map(w => enc(w, R.nodes, ['name'])).filter(Boolean),
  ttk: ttk.map(w => enc(w, R.nodes, ['name'])).filter(Boolean),
  bridge: bridges.map(w => enc(w, B.nodes, ['name', 'bridge:name'])).filter(Boolean),
};
const dst = path.join(__dirname, '..', 'public', 'vendor', 'osm-moscow', 'roads.json');
fs.mkdirSync(path.dirname(dst), { recursive: true });
fs.writeFileSync(dst, JSON.stringify(out));
fs.writeFileSync(path.join(path.dirname(dst), 'LICENSE.txt'), `Линии МКАД, ТТК и эстакад Москвы для вкладки «Замена ДТ».\nИсточник: OpenStreetMap, выгрузка от ${date}.\n© участники OpenStreetMap. Данные доступны по лицензии Open Database License (ODbL) 1.0: https://www.openstreetmap.org/copyright\nСобрано скриптом tools/osm-roads.js.\n`);
fs.rmSync(tmp, { recursive: true, force: true });
console.log(`Готово: МКАД ${out.mkad.length} линий, ТТК ${out.ttk.length}, эстакад ${out.bridge.length}; ${(fs.statSync(dst).size / 1048576).toFixed(2)} МБ → ${dst}`);

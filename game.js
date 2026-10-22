'use strict';
// Маджонг с лотком: берёшь открытую плитку в лоток, две одинаковые исчезают, лоток полон — проигрыш.
(() => {
const $ = id => document.getElementById(id);
const canvas = $('game'), ctx = canvas.getContext('2d');

const store = {
  get(k, d) { try { const v = localStorage.getItem(k); return v === null ? d : JSON.parse(v); } catch { return d; } },
  set(k, v) { try { localStorage.setItem(k, JSON.stringify(v)); } catch {} },
};

const TRAY_SIZE = 4;
const BOOSTERS = { shuffle: 3, hint: 3, undo: 3 };
const HINT_MAX = 10, PAIRS_PER_HINT = 10;  // +1 подсказка за 10 пар, копятся между уровнями до 10
const SPECIALS = ['🍁', '🌊', '⛰️', '🔥', '🌿', '🌸', '🌙', '☀️', '⭐', '🐉', '🍀', '❄️'];
const TYPE_COUNT = 27 + SPECIALS.length;  // 9 точек + 9 бамбуков + 9 цифр + картинки
const COLORS = { g: '#1f7a4d', r: '#c2362b', b: '#1f4f9c' };
const WORDS = ['ONE', 'TWO', 'THREE', 'FOUR', 'FIVE', 'SIX', 'SEVEN', 'EIGHT', 'NINE'];

let level = store.get('mj_level', 1);
let score = store.get('mj_score', 0);
let soundOn = store.get('mj_sound', true), vibroOn = store.get('mj_vibro', true);

let pairProgress = store.get('mj_pairs', 0), levelStartHints = 0, levelStartPairs = 0;
let tiles = [], tray = [], history = [], boosters = {}, levelStartScore = score;
let busy = false, over = false, hintIds = [], hintUntil = 0;
let W = 0, H = 0, tileW = 40, bounds = null, traySlots = [], trayW = 50, trayBox = null;

const shuffle = a => { for (let i = a.length - 1; i > 0; i--) { const j = Math.random() * (i + 1) | 0; [a[i], a[j]] = [a[j], a[i]]; } return a; };

// ---------- генерация уровня ----------

const overlaps = (a, b) => Math.abs(a.hx - b.hx) < 2 && Math.abs(a.hy - b.hy) < 2;

function levelParams(L) {
  return {
    cols: 6, rows: 7,
    layers: Math.min(3 + Math.floor(L / 2), 7),
    target: Math.min(56 + 8 * (L - 1), 140),
    spread: Math.min(2 + Math.floor((L - 1) / 3), 3),  // сколько незакрытых пар приходится держать в лотке
    types: Math.min(14 + 2 * L, TYPE_COUNT),
  };
}

// Позиции в полуклетках, раскладка симметрична. Нижний слой — столбики со сдвигом,
// верхние слои — плитки вразброс с наплывом на полплитки, каждая опирается на нижний слой.
function makeLayout(L) {
  const { cols, rows, layers, target } = levelParams(L);
  const maxHx = 2 * (cols - 1), maxHy = 2 * (rows - 1) + 1;
  const out = [];
  for (let c = 0; c < Math.ceil(cols / 2); c++) {
    const off = Math.random() < 0.5 ? 0 : 1;
    for (const xx of new Set([c, cols - 1 - c])) {
      for (let r = 0; r < rows; r++) if (Math.random() < 0.92) out.push({ hx: 2 * xx, hy: 2 * r + off, z: 0 });
    }
  }
  const fits = t => !out.some(u => u.z === t.z && overlaps(u, t)) && out.some(u => u.z === t.z - 1 && overlaps(u, t));
  for (let z = 1; z < layers && out.length < target; z++) {
    const cap = out.length + Math.ceil((target - out.length) / (layers - z));
    for (let k = 0; k < 600 && out.length < cap; k++) {
      const t = { hx: Math.random() * (maxHx + 1) | 0, hy: Math.random() * (maxHy + 1) | 0, z };
      const m = { ...t, hx: maxHx - t.hx };
      if (!fits(t)) continue;
      if (t.hx === m.hx) out.push(t);
      else if (!overlaps(t, m) && fits(m)) out.push(t, m);
    }
  }
  if (out.length % 2) { out.sort((a, b) => a.z - b.z); out.pop(); }
  return out;
}

function linkTiles() {
  for (const t of tiles) t.above = tiles.filter(u => u.z > t.z && overlaps(t, u));
}

const isFree = t => t.state === 'board' && t.above.every(u => u.state !== 'board');

// Случайный порядок, в котором плитки можно снимать по одной.
function solveOrder(list) {
  const left = new Set(list), order = [];
  while (left.size) {
    const free = [...left].filter(t => t.above.every(u => !left.has(u)));
    const t = free[Math.random() * free.length | 0];
    order.push(t); left.delete(t);
  }
  return order;
}

// Раздаёт типы так, чтобы уровень гарантированно решался: идём по порядку снятия и держим
// не больше spread «открытых» пар (плиток, ждущих напарника в лотке). forced — типы, уже лежащие в лотке.
function dealTypes(list, forced, pairTypes, spread) {
  const order = solveOrder(list), open = [...forced], queue = [...pairTypes];
  spread = Math.max(spread, forced.length);
  order.forEach((t, i) => {
    const left = order.length - i;
    if (open.length && (open.length >= spread || left <= open.length || Math.random() < 0.45)) {
      t.type = open.splice(Math.random() * open.length | 0, 1)[0];
    } else {
      let q = queue.findIndex(type => !open.includes(type));
      if (q < 0) q = queue.length - 1;
      t.type = queue.splice(q, 1)[0];
      open.push(t.type);
    }
  });
}

function startLevel(restarting = false) {
  tiles = makeLayout(level).map((p, id) => ({ id, ...p, type: 0, state: 'board', x: 0, y: 0, w: 0, a: 1, pop: 0, shake: 0 }));
  linkTiles();
  const pairs = tiles.length / 2;
  const { types, spread } = levelParams(level);
  const pool = shuffle([...Array(TYPE_COUNT).keys()]).slice(0, Math.min(pairs, types));
  dealTypes(tiles, [], shuffle(Array.from({ length: pairs }, (_, i) => pool[i % pool.length])), spread);

  const xs = tiles.map(t => t.hx), ys = tiles.map(t => t.hy);
  bounds = { minX: Math.min(...xs), maxX: Math.max(...xs) + 2, minY: Math.min(...ys), maxY: Math.max(...ys) + 2, maxZ: Math.max(...tiles.map(t => t.z)) };
  const hint = restarting ? levelStartHints : Math.max(boosters.hint ?? store.get('mj_hints', BOOSTERS.hint), BOOSTERS.hint);
  tray = []; history = []; boosters = { ...BOOSTERS, hint };
  levelStartScore = score; levelStartHints = hint; levelStartPairs = pairProgress;
  saveHints();
  busy = false; over = false; hintIds = [];
  hide('overlay');
  layoutScreen();
  for (const t of tiles) { t.x = t.tx; t.y = t.ty; t.w = t.tw; t.a = 0; }  // плитки проявляются
  updateHud(); kick();
}

// ---------- геометрия ----------

function resize() {
  const dpr = window.devicePixelRatio || 1, r = canvas.getBoundingClientRect();
  W = r.width; H = r.height;
  canvas.width = Math.round(W * dpr); canvas.height = Math.round(H * dpr);
  ctx.setTransform(dpr, 0, 0, dpr, 0, 0);
  layoutScreen();
  for (const t of tiles) { t.x = t.tx; t.y = t.ty; t.w = t.tw; }
  kick();
}

function layoutScreen() {
  trayW = Math.min(64, (W - 60) / TRAY_SIZE);
  const gap = trayW * 0.14, total = TRAY_SIZE * trayW + (TRAY_SIZE - 1) * gap, pad = trayW * 0.16;
  const x0 = (W - total) / 2, y0 = pad + 2;
  traySlots = Array.from({ length: TRAY_SIZE }, (_, i) => ({ x: x0 + i * (trayW + gap), y: y0 }));
  trayBox = { x: x0 - pad, y: y0 - pad, w: total + 2 * pad, h: trayW * 1.3 + 2 * pad };
  if (!bounds) return;

  const top = trayBox.y + trayBox.h + 18, availW = W - 8, availH = H - top - 8;
  const spanX = (bounds.maxX - bounds.minX) / 2, spanY = (bounds.maxY - bounds.minY) / 2, z = bounds.maxZ;
  tileW = Math.min(84, availW / (spanX + 0.08 * z + 0.12), availH / (spanY * 1.3 + 0.08 * z + 0.12));
  const d = tileW * 0.08, bw = spanX * tileW + z * d, bh = spanY * tileW * 1.3 + z * d;
  const ox = (W - bw) / 2 + z * d, oy = top + (availH - bh) / 2 + z * d;
  for (const t of tiles) {
    t.bx = ox + (t.hx - bounds.minX) * tileW / 2 - t.z * d;
    t.by = oy + (t.hy - bounds.minY) * tileW * 1.3 / 2 - t.z * d;
  }
  setTargets();
}

function setTargets() {
  for (const t of tiles) if (t.state === 'board') { t.tx = t.bx; t.ty = t.by; t.tw = tileW; }
  tray.forEach((t, i) => { t.tx = traySlots[i].x; t.ty = traySlots[i].y; t.tw = trayW; });
}

// ---------- отрисовка ----------

function rr(x, y, w, h, r) {
  ctx.beginPath();
  ctx.moveTo(x + r, y); ctx.arcTo(x + w, y, x + w, y + h, r); ctx.arcTo(x + w, y + h, x, y + h, r);
  ctx.arcTo(x, y + h, x, y, r); ctx.arcTo(x, y, x + w, y, r); ctx.closePath();
}

const DOTS = {
  1: [[.5, .5, 'r']],
  2: [[.5, .27, 'g'], [.5, .73, 'b']],
  3: [[.22, .2, 'b'], [.5, .5, 'r'], [.78, .8, 'g']],
  4: [[.28, .27, 'b'], [.72, .27, 'g'], [.28, .73, 'g'], [.72, .73, 'b']],
  5: [[.24, .22, 'b'], [.76, .22, 'g'], [.5, .5, 'r'], [.24, .78, 'g'], [.76, .78, 'b']],
  6: [[.3, .18, 'g'], [.7, .18, 'g'], [.3, .5, 'r'], [.7, .5, 'r'], [.3, .82, 'r'], [.7, .82, 'r']],
  7: [[.2, .12, 'g'], [.5, .24, 'g'], [.8, .36, 'g'], [.3, .62, 'r'], [.7, .62, 'r'], [.3, .86, 'r'], [.7, .86, 'r']],
  8: [.13, .38, .62, .87].flatMap(y => [[.3, y, 'b'], [.7, y, 'b']]),
  9: [[.2, 'g'], [.5, 'r'], [.8, 'b']].flatMap(([y, c]) => [[.2, y, c], [.5, y, c], [.8, y, c]]),
};
const DOT_R = { 1: .34, 2: .21, 3: .17, 4: .17, 5: .15, 6: .15, 7: .12, 8: .12, 9: .13 };

const BAMBOO = {
  1: [[.5, .5, 'g']],
  2: [[.5, .27, 'b'], [.5, .73, 'g']],
  3: [[.5, .27, 'b'], [.3, .73, 'g'], [.7, .73, 'g']],
  4: [[.3, .27, 'b'], [.7, .27, 'g'], [.3, .73, 'g'], [.7, .73, 'b']],
  5: [[.2, .27, 'g'], [.8, .27, 'b'], [.5, .5, 'r'], [.2, .73, 'b'], [.8, .73, 'g']],
  6: [.2, .5, .8].flatMap(x => [[x, .27, 'g'], [x, .73, 'b']]),
  7: [[.5, .17, 'r'], ...[.2, .5, .8].flatMap(x => [[x, .5, 'g'], [x, .83, 'b']])],
  8: [.14, .38, .62, .86].flatMap(x => [[x, .27, 'g'], [x, .73, 'b']]),
  9: [[.2, 'g'], [.5, 'r'], [.8, 'b']].flatMap(([x, c]) => [[x, .17, c], [x, .5, c], [x, .83, c]]),
};

function drawFace(type, x, y, w, h) {
  const pad = w * 0.1, fx = x + pad, fy = y + pad * 1.1, fw = w - 2 * pad, fh = h - 2.2 * pad;
  ctx.textAlign = 'center'; ctx.textBaseline = 'middle';
  if (type < 9) {
    const n = type + 1, r = DOT_R[n] * fw;
    for (const [px, py, c] of DOTS[n]) {
      const cx = fx + px * fw, cy = fy + py * fh;
      ctx.fillStyle = COLORS[c]; ctx.beginPath(); ctx.arc(cx, cy, r, 0, 7); ctx.fill();
      ctx.fillStyle = '#fffdf5'; ctx.beginPath(); ctx.arc(cx, cy, r * 0.6, 0, 7); ctx.fill();
      ctx.fillStyle = COLORS[c]; ctx.beginPath(); ctx.arc(cx, cy, r * 0.28, 0, 7); ctx.fill();
    }
  } else if (type < 18) {
    const n = type - 8, rows = new Set(BAMBOO[n].map(p => p[1])).size;
    const sw = (n === 1 ? .28 : .13) * fw, sh = (n === 1 ? .82 : rows === 3 ? .27 : .4) * fh;
    for (const [px, py, c] of BAMBOO[n]) {
      const sx = fx + px * fw - sw / 2, sy = fy + py * fh - sh / 2;
      ctx.fillStyle = COLORS[c]; rr(sx, sy, sw, sh, sw * 0.4); ctx.fill();
      ctx.fillStyle = 'rgba(255,255,255,.55)';
      for (const k of [1 / 3, 2 / 3]) ctx.fillRect(sx + sw * 0.15, sy + sh * k - sh * 0.03, sw * 0.7, sh * 0.06);
    }
  } else if (type < 27) {
    ctx.fillStyle = '#1d5c47'; ctx.font = `bold ${fh * 0.55}px Georgia, serif`;
    ctx.fillText(String(type - 17), fx + fw / 2, fy + fh * 0.38);
    const word = WORDS[type - 18];
    ctx.font = `bold ${fh * 0.2}px sans-serif`;
    const size = fh * 0.2 * Math.min(1, fw * 1.02 / ctx.measureText(word).width);
    ctx.fillStyle = '#c2362b'; ctx.font = `bold ${size}px sans-serif`;
    ctx.fillText(word, fx + fw / 2, fy + fh * 0.82);
  } else {
    ctx.font = `${fw * 0.82}px sans-serif`; ctx.fillStyle = '#000';
    ctx.fillText(SPECIALS[type - 27], fx + fw / 2, fy + fh / 2 + fw * 0.04);
  }
}

function drawTile(t, dim, glow) {
  const w = t.w, h = w * 1.3, side = w * 0.09, r = w * 0.14;
  let x = t.x + (t.shake ? Math.sin(t.shake * 1.7) * w * 0.06 : 0), y = t.y;
  ctx.save();
  ctx.globalAlpha = Math.max(0, t.a);
  if (t.pop) {
    const s = 1 + t.pop;
    ctx.translate(x + w / 2, y + h / 2); ctx.scale(s, s); ctx.translate(-(x + w / 2), -(y + h / 2));
  }
  ctx.fillStyle = 'rgba(0,0,0,.22)'; rr(x + side * 1.8, y + side * 1.8, w, h, r); ctx.fill();
  ctx.fillStyle = '#c99a3c'; rr(x + side, y + side, w, h, r); ctx.fill();
  ctx.fillStyle = '#e8dcbc'; rr(x + side * 0.45, y + side * 0.45, w, h, r); ctx.fill();
  const g = ctx.createLinearGradient(x, y, x, y + h);
  g.addColorStop(0, '#fffdf6'); g.addColorStop(1, '#f0e8d4');
  ctx.fillStyle = g; rr(x, y, w, h, r); ctx.fill();
  drawFace(t.type, x, y, w, h);
  if (dim) { ctx.fillStyle = 'rgba(12,40,28,.38)'; rr(x, y, w, h, r); ctx.fill(); }
  if (glow) {
    ctx.strokeStyle = `rgba(255,214,80,${0.6 + 0.4 * Math.sin(performance.now() / 120)})`;
    ctx.lineWidth = Math.max(3, w * 0.07); rr(x, y, w, h, r); ctx.stroke();
  }
  ctx.restore();
}

function draw() {
  ctx.clearRect(0, 0, W, H);
  ctx.fillStyle = 'rgba(0,0,0,.25)'; rr(trayBox.x, trayBox.y, trayBox.w, trayBox.h, trayW * 0.25); ctx.fill();
  ctx.fillStyle = 'rgba(0,0,0,.2)';
  for (const s of traySlots) { rr(s.x, s.y, trayW, trayW * 1.3, trayW * 0.14); ctx.fill(); }

  const hinting = performance.now() < hintUntil;
  const board = tiles.filter(t => t.state === 'board').sort((a, b) => a.z - b.z || a.hx - b.hx || a.hy - b.hy);
  for (const t of board) drawTile(t, !isFree(t), hinting && hintIds.includes(t.id));
  for (const t of tiles) if (t.state === 'vanish') drawTile(t);
  for (const t of tray) drawTile(t);
}

let raf = 0;
function kick() { if (!raf) raf = requestAnimationFrame(frame); }
function frame() {
  raf = 0;
  let moving = false;
  for (const t of tiles) {
    for (const [k, tk] of [['x', 'tx'], ['y', 'ty'], ['w', 'tw']]) {
      const d = t[tk] - t[k];
      if (Math.abs(d) > 0.3) { t[k] += d * 0.3; moving = true; } else t[k] = t[tk];
    }
    if (t.state === 'vanish') {
      t.a -= 0.07; t.pop += 0.035; moving = true;
      if (t.a <= 0) { t.state = 'gone'; t.pop = 0; }
    } else if (t.state !== 'gone' && t.a < 1) { t.a = Math.min(1, t.a + 0.08); moving = true; }
    if (t.shake > 0) { t.shake--; moving = true; }
  }
  draw();
  if (moving || performance.now() < hintUntil) kick();
}

// ---------- игра ----------

function snapshot() {
  history.push({
    states: tiles.map(t => (t.state === 'vanish' ? 'gone' : t.state)),
    types: tiles.map(t => t.type),
    tray: tray.map(t => t.id),
    score, pairProgress,
  });
}

function saveHints() {
  store.set('mj_hints', boosters.hint);
  store.set('mj_pairs', pairProgress);
}

// Вызывается после каждой собранной пары. На максимуме счётчик стоит на нуле.
function earnHint() {
  if (boosters.hint >= HINT_MAX) pairProgress = 0;
  else if (++pairProgress >= PAIRS_PER_HINT) {
    pairProgress = 0;
    boosters.hint++;
    history[history.length - 1].awarded = true;
    toast('+1 подсказка!');
  }
  saveHints();
}

function take(t) {
  snapshot();
  hintUntil = 0;
  t.state = 'tray';
  const mate = tray.find(u => u.type === t.type);
  if (mate) tray.splice(tray.indexOf(mate) + 1, 0, t); else tray.push(t);
  setTargets(); kick(); sound('tap');
  if (mate) {
    busy = true;
    setTimeout(() => {
      for (const u of [t, mate]) { u.state = 'vanish'; u.a = 1; u.pop = 0; }
      tray = tray.filter(u => u !== t && u !== mate);
      score += 20;
      earnHint();
      setTargets(); updateHud(); kick(); sound('match'); vibrate(20);
      busy = false;
      if (tiles.every(u => u.state === 'gone' || u.state === 'vanish')) win();
    }, 230);
  } else if (tray.length >= TRAY_SIZE) {
    over = true;
    setTimeout(lose, 400);
  }
}

function win() {
  over = true;
  score += 100;
  level++;
  store.set('mj_level', level); store.set('mj_score', score);
  updateHud();
  setTimeout(() => {
    sound('win');
    showOverlay(`Уровень ${level - 1} пройден!`, `Бонус +100<br>Счёт: ${score}`, 'Дальше', startLevel);
  }, 500);
}

function lose() {
  sound('lose'); vibrate(200);
  const canUndo = boosters.undo > 0 && history.length > 0;
  showOverlay('Лоток заполнен', 'Не осталось места для плитки.',
    canUndo ? `Отменить ход (${boosters.undo})` : 'Начать заново',
    canUndo ? undo : restart,
    canUndo ? ['Начать заново', restart] : null);
}

function restart() {
  score = levelStartScore;
  pairProgress = levelStartPairs;
  startLevel(true);
}

function undo() {
  if (busy || !history.length || !boosters.undo) return;
  const h = history.pop();
  tiles.forEach((t, i) => { t.state = h.states[i]; t.type = h.types[i]; t.a = 1; t.pop = 0; });
  tray = h.tray.map(id => tiles[id]);
  score = h.score;
  pairProgress = h.pairProgress;
  if (h.awarded && boosters.hint > 0) boosters.hint--;
  saveHints();
  boosters.undo--;
  over = false; hintUntil = 0;
  hide('overlay');
  setTargets(); updateHud(); kick(); sound('tap');
}

function shuffleBoard() {
  if (busy || over || !boosters.shuffle) return;
  const board = tiles.filter(t => t.state === 'board');
  const forced = tray.map(t => t.type);
  const counts = new Map();
  for (const t of board) counts.set(t.type, (counts.get(t.type) || 0) + 1);
  for (const f of forced) counts.set(f, counts.get(f) - 1);
  const pairTypes = [];
  for (const [type, c] of counts) for (let i = 0; i < c / 2; i++) pairTypes.push(type);
  dealTypes(board, forced, shuffle(pairTypes), levelParams(level).spread);
  for (const t of board) t.a = 0.15;
  boosters.shuffle--; hintUntil = 0;
  updateHud(); kick(); sound('shuffle'); vibrate(30);
}

function hint() {
  if (busy || over || !boosters.hint) return;
  const free = tiles.filter(isFree);
  let ids = null;
  const inTray = free.find(t => tray.some(u => u.type === t.type));
  if (inTray) ids = [inTray.id];
  else {
    const seen = new Map();
    for (const t of free) {
      if (seen.has(t.type)) { ids = [seen.get(t.type).id, t.id]; break; }
      seen.set(t.type, t);
    }
  }
  if (!ids) { toast('Открытых пар нет — попробуйте «Перемешать»'); return; }
  boosters.hint--;
  saveHints();
  hintIds = ids; hintUntil = performance.now() + 2500;
  updateHud(); kick();
}

canvas.addEventListener('pointerdown', e => {
  if (busy || over) return;
  const r = canvas.getBoundingClientRect(), px = e.clientX - r.left, py = e.clientY - r.top;
  const board = tiles.filter(t => t.state === 'board').sort((a, b) => b.z - a.z || b.hx - a.hx || b.hy - a.hy);
  const t = board.find(t => px >= t.tx && px <= t.tx + t.tw && py >= t.ty && py <= t.ty + t.tw * 1.3);
  if (!t) return;
  if (!isFree(t)) { t.shake = 12; sound('bump'); vibrate(15); kick(); return; }
  take(t);
});

// ---------- интерфейс ----------

function updateHud() {
  $('level').textContent = `Уровень ${level}`;
  $('score').textContent = score;
  for (const k of ['shuffle', 'hint', 'undo']) {
    $(k + 'N').textContent = boosters[k];
    $(k + 'Btn').disabled = !boosters[k];
  }
  $('hintLbl').textContent = boosters.hint >= HINT_MAX ? 'Подсказка (макс.)' : `Подсказка ${pairProgress}/${PAIRS_PER_HINT}`;
}

const hide = id => $(id).classList.add('hidden');
const show = id => $(id).classList.remove('hidden');

function showOverlay(title, text, mainLabel, mainFn, second) {
  $('ovTitle').textContent = title;
  $('ovText').innerHTML = text;
  $('ovMain').textContent = mainLabel;
  $('ovMain').onclick = () => { hide('overlay'); mainFn(); };
  $('ovSecond').classList.toggle('hidden', !second);
  if (second) { $('ovSecond').textContent = second[0]; $('ovSecond').onclick = () => { hide('overlay'); second[1](); }; }
  show('overlay');
}

let toastTimer = 0;
function toast(msg) {
  $('toast').textContent = msg; show('toast');
  clearTimeout(toastTimer); toastTimer = setTimeout(() => hide('toast'), 2200);
}

let audio = null;
const SOUNDS = {
  tap: [[660, .05]], bump: [[170, .07]], match: [[880, .07], [1320, .12]],
  shuffle: [[520, .05], [700, .05], [600, .06]],
  win: [[523, .1], [659, .1], [784, .1], [1047, .25]], lose: [[330, .15], [220, .3]],
};
function sound(kind) {
  if (!soundOn) return;
  try {
    audio = audio || new (window.AudioContext || window.webkitAudioContext)();
    let at = audio.currentTime;
    for (const [f, d] of SOUNDS[kind]) {
      const o = audio.createOscillator(), g = audio.createGain();
      o.type = 'triangle'; o.frequency.value = f;
      g.gain.setValueAtTime(0.15, at); g.gain.exponentialRampToValueAtTime(0.001, at + d);
      o.connect(g).connect(audio.destination); o.start(at); o.stop(at + d);
      at += d * 0.8;
    }
  } catch {}
}
function vibrate(ms) { if (vibroOn && navigator.vibrate) try { navigator.vibrate(ms); } catch {} }

$('shuffleBtn').onclick = shuffleBoard;
$('hintBtn').onclick = hint;
$('undoBtn').onclick = undo;
$('menuBtn').onclick = () => show('menu');
$('resumeBtn').onclick = () => hide('menu');
$('restartBtn').onclick = () => { hide('menu'); restart(); };
$('soundToggle').checked = soundOn;
$('vibroToggle').checked = vibroOn;
$('soundToggle').onchange = e => { soundOn = e.target.checked; store.set('mj_sound', soundOn); };
$('vibroToggle').onchange = e => { vibroOn = e.target.checked; store.set('mj_vibro', vibroOn); };

window.addEventListener('resize', resize);
resize();
startLevel();
})();

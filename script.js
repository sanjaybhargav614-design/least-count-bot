// ==== CORE (pure game logic, no DOM). Mirrors least_count_best.cpp. ============

// Settings (same values as the C++ program).
const LIMIT = 200, PENALTY = 40, SHOW_MAX = 6, STALL_TURNS = 60;
const PAR = [
  { bait: 0, pickF: 2.5, margin: 3.0, boundFrom: -1, setupW: 0, oppW: 6 }, // player 0 (you)
  { bait: 0, pickF: 2.5, margin: 3.0, boundFrom: -1, setupW: 0, oppW: 6 }, // player 1 (bot)
];
const RANKS = ["A","2","3","4","5","6","7","8","9","T","J","Q","K"];
const SUITS = ["H","S","D","C"];

// "7H" -> "7", "JK" -> "JK".
function rankOf(c) { return c === "JK" ? "JK" : c.slice(0, -1); }
function suitOf(c) { return c.slice(-1); }

// 52 standard cards plus 2 jokers.
function makeDeck() {
  const d = [];
  for (const r of RANKS) for (const s of SUITS) d.push(r + s);
  d.push("JK", "JK");
  return d;
}
function shuffled(a) {
  const b = a.slice();
  for (let i = b.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [b[i], b[j]] = [b[j], b[i]];
  }
  return b;
}
// A=1, 2-9 face value, T/J/Q/K=10, JK=0, cards of this round's joker rank=0.
function valueOf(c, jr) {
  if (c === "JK") return 0;
  const r = rankOf(c);
  if (r === jr) return 0;
  if (r === "A") return 1;
  if (r === "T" || r === "J" || r === "Q" || r === "K") return 10;
  return parseInt(r, 10);
}
function removeOne(arr, c) {
  const i = arr.indexOf(c);
  if (i < 0) return false;
  arr.splice(i, 1);
  return true;
}
function handTotal(hand) { return hand.reduce((t, c) => t + valueOf(c, G.jokerRank), 0); }
function binom(n, k) {
  if (k < 0 || k > n) return 0;
  if (k > n - k) k = n - k;
  let r = 1;
  for (let i = 1; i <= k; i++) r = r * (n - k + i) / i;
  return r;
}

function newState() {
  return {
    deck: [], openPile: [], hands: [[], []], known: [[], []], bound: [-1, -1],
    setAside: "", jokerRank: "", topOpen: "", roundOver: false, gameOver: false,
    forceShow: false, turnsInRound: 0, turn: 0, player0Opens: true, round: 1, scores: [0, 0],
  };
}
let G = newState();

function setTop() { G.topOpen = G.openPile.length ? G.openPile[G.openPile.length - 1] : ""; }

// Open cards except the top go back into the draw pile; the top stays.
function reshuffle() {
  if (G.openPile.length <= 1) return;
  const top = G.openPile.pop();
  G.deck.push(...G.openPile);
  G.openPile = [top];
  G.deck = shuffled(G.deck);
  setTop();
}
function drawFromDeck() {
  if (G.deck.length === 0) reshuffle();
  if (G.deck.length === 0) return "";
  return G.deck.pop();
}

// Deal a round: 7 each, one open card, one random non-joker set aside.
function dealCore() {
  G.deck = shuffled(makeDeck());
  G.hands = [[], []]; G.known = [[], []]; G.bound = [-1, -1]; G.openPile = [];
  for (let i = 0; i < 7; i++) { G.hands[0].push(G.deck.pop()); G.hands[1].push(G.deck.pop()); }
  G.openPile.push(G.deck.pop());
  setTop();
  let idx;
  do { idx = Math.floor(Math.random() * G.deck.length); } while (G.deck[idx] === "JK");
  G.setAside = G.deck.splice(idx, 1)[0];
  G.jokerRank = rankOf(G.setAside);
  G.roundOver = false; G.forceShow = false; G.turnsInRound = 0;
  G.turn = G.player0Opens ? 0 : 1;
}

// Drop = every card of one rank. The card face-up before the drop stays under it.
function dropGroup(me, cards) {
  const prev = G.topOpen;
  const a = {
    prevOpen: prev, prevIndex: 0, canTake: prev !== "",
    noPick: prev !== "" && rankOf(cards[0]) === rankOf(prev),
  };
  for (const c of cards) {
    removeOne(G.hands[me], c);
    removeOne(G.known[1 - me], c);     // the opponent now sees these cards
    G.openPile.push(c);
  }
  if (a.canTake) a.prevIndex = G.openPile.length - cards.length - 1;
  const y = valueOf(cards[0], G.jokerRank);
  G.bound[me] = a.noPick ? 2 * y : y;
  setTop();
  return a;
}
function takePrevOpen(a) {
  if (!a.canTake || a.prevIndex >= G.openPile.length) return "";
  const c = G.openPile[a.prevIndex];
  G.openPile.splice(a.prevIndex, 1);
  setTop();
  return c;
}

// Cards player `me` cannot see.
function hiddenPool(me) {
  const pool = makeDeck();
  for (const c of G.hands[me]) removeOne(pool, c);
  for (const c of G.openPile) removeOne(pool, c);
  for (const c of G.known[me]) removeOne(pool, c);
  removeOne(pool, G.setAside);
  return pool;
}
function unknownCount(me) { return G.hands[1 - me].length - G.known[me].length; }
function poolAverage(pool) {
  if (!pool.length) return 0;
  return pool.reduce((s, c) => s + valueOf(c, G.jokerRank), 0) / pool.length;
}
function oppBound(me) {
  const from = PAR[me].boundFrom;
  if (from < 0 || G.round <= from) return -1;
  return G.bound[1 - me];
}

// Exact distribution of the opponent's total. Returns winPts and penProb.
function estimateOpponent(me, myT) {
  let pool = hiddenPool(me);
  const m = unknownCount(me);
  const K = handTotal(G.known[me]);
  const ob = oppBound(me);
  if (ob >= 0) {
    const el = pool.filter(c => valueOf(c, G.jokerRank) < ob);
    if (el.length >= m) pool = el;
  }
  const e = { P: 0, E: K, winPts: 0, penProb: 0 };
  const zeroTie = myT === 0;
  if (m <= 0) {
    e.P = K > myT ? 1 : 0;
    if (K > myT) e.winPts = K;
    else if (!(zeroTie && K === 0)) e.penProb = 1;
    return e;
  }
  const H = pool.length;
  const cnt = Array(11).fill(0);
  for (const c of pool) cnt[valueOf(c, G.jokerRank)]++;
  const maxS = 10 * m;
  let ways = Array.from({ length: m + 1 }, () => Array(maxS + 1).fill(0));
  ways[0][0] = 1;
  for (let v = 0; v <= 10; v++) {
    if (!cnt[v]) continue;
    const nxt = Array.from({ length: m + 1 }, () => Array(maxS + 1).fill(0));
    for (let j = 0; j <= m; j++)
      for (let s = 0; s <= maxS; s++) {
        const w = ways[j][s];
        if (!w) continue;
        for (let t = 0; t <= cnt[v] && j + t <= m && s + t * v <= maxS; t++)
          nxt[j + t][s + t * v] += w * binom(cnt[v], t);
      }
    ways = nxt;
  }
  const all = binom(H, m);
  for (let s = 0; s <= maxS; s++) {
    const pr = all > 0 ? ways[m][s] / all : 0;
    const total = K + s;
    if (total > myT) { e.P += pr; e.winPts += total * pr; }
    else if (!(zeroTie && total === 0)) e.penProb += pr;
  }
  e.E = K + m * poolAverage(pool);
  return e;
}
function expectedGain(e) { return e.winPts - PENALTY * e.penProb; }

// Bot pick rule: match first, else take if value < hidden average - pickF.
function botTakesOpen(me, openCard) {
  if (!openCard) return false;
  const r = rankOf(openCard);
  if (G.hands[me].some(c => rankOf(c) === r)) return true;
  const avg = poolAverage(hiddenPool(me));
  return valueOf(openCard, G.jokerRank) < avg - PAR[me].pickF;
}
function opponentHoldsRank(me, rank, pool) {
  if (G.known[me].some(c => rankOf(c) === rank)) return 1;
  if (!pool.length) return 0;
  const nr = pool.filter(c => rankOf(c) === rank).length;
  return Math.min(1, unknownCount(me) * nr / pool.length);
}
// Drop score: points - my pick cost - P(opp holds rank) * their draw cost + 0.5 * setup.
function scoreDrop(me, d, pool, avg) {
  const points = d.cards.reduce((s, c) => s + valueOf(c, G.jokerRank), 0);
  const top = G.topOpen;
  let drawCost = avg;
  if (top) drawCost = Math.min(avg, valueOf(top, G.jokerRank));
  const matches = top !== "" && d.rank === rankOf(top);
  const myPickCost = matches ? 0 : drawCost;
  let setup = 0;
  if (!matches && top) {
    const tr = rankOf(top);
    for (const c of G.hands[me]) if (rankOf(c) === tr) setup += valueOf(c, G.jokerRank);
  }
  return points - myPickCost
       - PAR[me].oppW * opponentHoldsRank(me, d.rank, pool) * drawCost
       + PAR[me].setupW * setup;
}
function getDropOptions(me) {
  const groups = {};
  for (const c of G.hands[me]) (groups[rankOf(c)] = groups[rankOf(c)] || []).push(c);
  const pool = hiddenPool(me);
  const avg = poolAverage(pool);
  return Object.keys(groups).map(r => {
    const d = { rank: r, cards: groups[r], score: 0 };
    d.score = scoreDrop(me, d, pool, avg);
    return d;
  });
}
// Plan B (rounds 1..bait): 6s, then 8s, then 7s. Plan A otherwise: highest score.
function chooseDrop(me) {
  let opts = getDropOptions(me);
  // Never throw away a zero-value card (joker or joker rank) while other cards can be dropped.
  const nonZero = opts.filter(o => o.cards.some(c => valueOf(c, G.jokerRank) > 0));
  if (nonZero.length) opts = nonZero;
  if (G.round <= PAR[me].bait) {
    for (const r of ["6", "8", "7"]) {
      const o = opts.find(x => x.rank === r);
      if (o) return o;
    }
  }
  return opts.reduce((a, b) => (b.score > a.score ? b : a));
}

// Bot turn pieces (also used by the UI so each step can be shown).
function botDrop(me) {
  const d = chooseDrop(me);
  const a = dropGroup(me, d.cards);
  return { drop: d, a };
}
function botPick(me, a) {
  const opp = 1 - me;
  if (botTakesOpen(me, a.prevOpen) && a.canTake) {
    const c = takePrevOpen(a);
    G.hands[me].push(c);
    G.known[opp].push(c);            // the opponent sees we took this card
    return { type: "take", card: c };
  }
  const c = drawFromDeck();
  if (c) G.hands[me].push(c);
  return { type: "draw", card: c };
}
function botShowCheck(me) {
  const t = handTotal(G.hands[me]);
  if (t > SHOW_MAX) return { shows: false, t };
  const est = estimateOpponent(me, t);
  const eg = expectedGain(est);
  return { shows: eg >= PAR[me].margin, t, est, eg };
}

// Round end. Right show: shower 0, other gets their total. Wrong show (tie
// counts as wrong): shower PENALTY, other 0. Both 0: tie, no points.
function endRound(showerIdx) {
  const st = handTotal(G.hands[showerIdx]);
  const ot = handTotal(G.hands[1 - showerIdx]);
  const right = st < ot;
  const tieZero = st === 0 && ot === 0;
  let showerPts = right ? 0 : PENALTY;
  let otherPts = right ? ot : 0;
  if (tieZero) { showerPts = 0; otherPts = 0; }
  G.scores[showerIdx] += showerPts;
  G.scores[1 - showerIdx] += otherPts;
  G.roundOver = true;
  G.round++;
  G.player0Opens = !G.player0Opens;
  if (G.scores[0] >= LIMIT || G.scores[1] >= LIMIT) G.gameOver = true;
  return { st, ot, right, tieZero, showerPts, otherPts };
}

// One full bot turn, no UI (used by the simulation). Order: show, drop, pick.
function botTurnCore(me) {
  const opp = 1 - me;
  G.turnsInRound++;
  if (G.hands[me].length === 0) return endRound(me);
  if (G.forceShow || G.turnsInRound > STALL_TURNS) {
    const myT = handTotal(G.hands[me]), oT = handTotal(G.hands[opp]);
    if (G.forceShow || myT <= oT) return endRound(me);
    G.forceShow = true;
    G.turn = opp;
    return null;
  }
  if (botShowCheck(me).shows) return endRound(me);   // show is checked before the drop
  const { a } = botDrop(me);
  if (!a.noPick) botPick(me, a);
  G.turn = opp;
  return null;
}

// Self-check: exact probability vs brute-force enumeration. Returns worst error.
function selfTest(trials = 300) {
  let worst = 0, checked = 0;
  for (let trial = 0; trial < trials; trial++) {
    G = newState();
    dealCore();
    const idx = shuffled([0, 1, 2, 3, 4, 5, 6]);
    const known = 3 + Math.floor(Math.random() * 4);
    for (let k = 0; k < known; k++) G.known[1].push(G.hands[0][idx[k]]);
    const m = unknownCount(1);
    if (m < 0 || m > 4) continue;
    const myT = Math.floor(Math.random() * 12);
    const e = estimateOpponent(1, myT);
    // brute force over every m-subset of the candidate pool
    const pool = hiddenPool(1);
    const K = handTotal(G.known[1]);
    let bw = 0, bp = 0, n = 0;
    const comb = [];
    (function rec(start, chosen) {
      if (chosen.length === m) {
        n++;
        let s = K;
        for (const i of chosen) s += valueOf(pool[i], G.jokerRank);
        if (s > myT) bw += s;
        else if (!(myT === 0 && s === 0)) bp += 1;
        return;
      }
      for (let i = start; i < pool.length; i++) { chosen.push(i); rec(i + 1, chosen); chosen.pop(); }
    })(0, comb);
    if (n === 0) { bw = 0; bp = 0; }
    else { bw /= n; bp /= n; }
    worst = Math.max(worst, Math.abs(e.winPts - bw), Math.abs(e.penProb - bp));
    checked++;
  }
  return { checked, worst };
}

// Bot-vs-bot simulation, no UI.
function runSim(games) {
  const wins = [0, 0];
  let ties = 0, rounds = 0;
  for (let gi = 0; gi < games; gi++) {
    G = newState();
    while (!G.gameOver) {
      dealCore();
      while (!G.roundOver) botTurnCore(G.turn);
    }
    rounds += G.round - 1;
    if (G.scores[0] < G.scores[1]) wins[0]++;
    else if (G.scores[1] < G.scores[0]) wins[1]++;
    else ties++;
  }
  return { games, wins, ties, avgRounds: rounds / games };
}
// ==== UI (DOM, sound, animation) =============================================
const $ = id => document.getElementById(id);
const SUIT_SYMBOL = { H: "♥", D: "♦", S: "♠", C: "♣" };
const REDUCED = !!(window.matchMedia && window.matchMedia("(prefers-reduced-motion: reduce)").matches);
const sleep = ms => (REDUCED ? Promise.resolve() : new Promise(r => setTimeout(r, ms)));
const rankLabel = r => (r === "T" ? "10" : r);

let phase = "idle";        // idle | showfirst | drop | pick | botwait | over
let busy = false;
let lastAction = null;     // result of the last human drop
let pendingTake = null;    // drop action whose "card under the drop" can still be taken
let lastDropCount = 0;     // cards in the most recent drop group
let dealing = false;       // true while cards are being dealt or collected
let revealBot = false;     // show the bot's hand face up (round over)
let history = [];          // one row per round: { round, you, bot }
let muted = false;
let humanFlying = false;   // a card is flying into your hand: hand order is locked
let suppressClick = false;
let drag = null;
const selected = new Set();

// ---- Sound ------------------------------------------------------------------
let audioCtx = null;
function ctx() {
  if (!audioCtx) audioCtx = new (window.AudioContext || window.webkitAudioContext)();
  if (audioCtx.state === "suspended") audioCtx.resume();
  return audioCtx;
}
function tone(freq, dur, type = "sine", vol = 0.15, when = 0) {
  if (muted) return;
  try {
    const c = ctx();
    const o = c.createOscillator(), g = c.createGain();
    o.type = type; o.frequency.value = freq;
    g.gain.setValueAtTime(vol, c.currentTime + when);
    g.gain.exponentialRampToValueAtTime(0.001, c.currentTime + when + dur);
    o.connect(g).connect(c.destination);
    o.start(c.currentTime + when);
    o.stop(c.currentTime + when + dur + 0.02);
  } catch (e) { /* audio unavailable */ }
}
function noise(dur, vol = 0.2, when = 0) {
  if (muted) return;
  try {
    const c = ctx();
    const len = Math.floor(c.sampleRate * dur);
    const buf = c.createBuffer(1, len, c.sampleRate);
    const d = buf.getChannelData(0);
    for (let i = 0; i < len; i++) d[i] = (Math.random() * 2 - 1) * (1 - i / len);
    const src = c.createBufferSource();
    src.buffer = buf;
    const g = c.createGain();
    g.gain.value = vol;
    src.connect(g).connect(c.destination);
    src.start(c.currentTime + when);
  } catch (e) { /* audio unavailable */ }
}
const SFX = {
  shuffle() { for (let i = 0; i < 10; i++) noise(0.05, 0.22, i * 0.07); },
  deal()    { noise(0.04, 0.18); },
  flip()    { noise(0.05, 0.12); tone(900, 0.04, "sine", 0.05); },
  drop()    { tone(180, 0.09, "triangle", 0.22); noise(0.04, 0.12); },
  take()    { tone(520, 0.07, "sine", 0.15); },
  show()    { tone(660, 0.15); tone(880, 0.25, "sine", 0.15, 0.12); },
  bad()     { tone(140, 0.35, "sawtooth", 0.12); },
  win()     { [523, 659, 784, 1047].forEach((f, i) => tone(f, 0.3, "sine", 0.15, i * 0.12)); },
};

// ---- Cards ------------------------------------------------------------------
function makeCardEl(code, faceUp) {
  const el = document.createElement("div");
  el.dataset.code = code || "";
  el.dataset.up = faceUp && code ? "1" : "";
  if (!faceUp || !code) { el.className = "card back"; return el; }
  const joker = code === "JK";
  const shown = joker ? "JK" : rankLabel(rankOf(code));
  const s = joker ? "" : SUIT_SYMBOL[suitOf(code)];
  const color = joker ? "joker" : (suitOf(code) === "H" || suitOf(code) === "D" ? "red" : "black");
  el.className = "card " + color;
  el.innerHTML = `<span class="corner">${shown}<br>${s}</span>` +
                 `<span class="mid">${joker ? "🃏" : s}</span>` +
                 `<span class="corner bot">${shown}<br>${s}</span>`;
  return el;
}

function log(msg, cls = "") {
  const d = document.createElement("div");
  d.textContent = msg;
  if (cls) d.className = cls;
  const box = $("log");
  box.prepend(d);
  while (box.children.length > 80) box.lastChild.remove();
}
function setStatus(msg, kind = "") {
  const s = $("status");
  s.className = "status " + kind;
  s.textContent = msg;
  if (kind === "think") s.insertAdjacentHTML("beforeend", '<span class="dots"><i></i><i></i><i></i></span>');
}
function showBanner(title, sub, kind) {
  const b = $("banner");
  b.className = kind || "";
  b.innerHTML = `<b></b><span></span>`;
  b.firstChild.textContent = title;
  b.lastChild.textContent = sub;
  void b.offsetWidth;
  b.classList.add("show");
}
function hideBanner() { $("banner").classList.remove("show"); }
function showOver(title, text) {
  $("overTitle").textContent = title;
  $("overText").textContent = text;
  $("over").classList.remove("hidden");
}
function confetti() {
  if (REDUCED) return;
  const colors = ["#f1c40f", "#e74c3c", "#3498db", "#2ecc71", "#9b59b6", "#fff"];
  for (let i = 0; i < 70; i++) {
    const c = document.createElement("div");
    c.className = "confetti";
    c.style.left = Math.random() * 100 + "vw";
    c.style.background = colors[i % colors.length];
    c.style.animationDuration = 2200 + Math.random() * 2200 + "ms";
    c.style.animationDelay = Math.random() * 600 + "ms";
    document.body.appendChild(c);
    setTimeout(() => c.remove(), 5500);
  }
}

// ---- Geometry helpers --------------------------------------------------------
function cardSize() { const r = $("deck").getBoundingClientRect(); return { w: r.width, h: r.height }; }
// Rectangle of one card, centred on an element (so rotated slots and piles give a true card box).
function cardBox(el) {
  const r = el.getBoundingClientRect(), s = cardSize();
  return { left: r.left + (r.width - s.w) / 2, top: r.top + (r.height - s.h) / 2, width: s.w, height: s.h };
}
const hide = el => { if (el) el.style.visibility = "hidden"; };
const lastCardEl = rowId => { const k = $(rowId).lastElementChild; return k ? k.firstElementChild : null; };

// ---- Score table -------------------------------------------------------------
function renderScore() {
  const body = $("scoreBody");
  body.innerHTML = "";
  for (const h of history) {
    const tr = document.createElement("tr");
    tr.innerHTML = `<td>${h.round}</td><td>${h.you}</td><td>${h.bot}</td>`;
    body.appendChild(tr);
  }
  $("totYou").textContent = G.scores[0];
  $("totBot").textContent = G.scores[1];
}

// ---- Rendering --------------------------------------------------------------
function renderInfo() {
  const shownRound = (phase === "over") ? G.round - 1 : G.round;
  const jr = G.jokerRank ? rankLabel(G.jokerRank) : "-";
  $("info").innerHTML =
    `<span class="chip">Round ${Math.max(1, shownRound)}</span>` +
    `<span class="chip joker" title="Cards of this rank are worth 0 this round">Joker rank <b>${jr}</b></span>` +
    `<span class="chip">You <b>${G.scores[0]}</b> : Bot <b>${G.scores[1]}</b></span>` +
    `<span class="chip dim">first to ${LIMIT} loses</span>`;
  $("deckCount").textContent = `Draw: ${G.deck.length}`;
  $("openCount").textContent = `Open: ${G.openPile.length}`;
  const n = G.hands[1].length;
  $("botLabel").textContent = `Bot · ${n} card${n === 1 ? "" : "s"}` + (revealBot ? ` · total ${handTotal(G.hands[1])}` : "");
  const t = handTotal(G.hands[0]);
  const mt = $("myTotal");
  if (dealing || !G.hands[0].length) { mt.textContent = ""; mt.className = ""; return; }
  mt.textContent = `total ${t}` + (t <= SHOW_MAX ? " (you can show)" : "");
  mt.className = t <= SHOW_MAX ? "ok" : "";
}

// Overlap + fan the cards of one row so they always fit on one line.
function layoutRow(row, fan) {
  const slots = [...row.children], n = slots.length;
  if (!n) return;
  const cw = cardSize().w, gap = 6;
  const avail = Math.max(row.clientWidth - 8, cw);
  const step = n > 1 ? Math.min(cw + gap, (avail - cw) / (n - 1)) : 0;
  slots.forEach((s, i) => {
    s.style.zIndex = i;
    if (i > 0) s.style.marginLeft = (step - cw) + "px";
    if (fan && n > 1) {
      const m = i - (n - 1) / 2, rot = m * Math.min(3.2, 22 / n);
      s.dataset.rot = rot.toFixed(2);
      s.style.transform = `translateY(${(m * m * 1.4).toFixed(1)}px) rotate(${rot.toFixed(2)}deg)`;
    }
  });
}

function renderAll() {
  abortDrag();
  renderInfo();

  // Draw pile: a small stack of face-down cards.
  const deckEl = $("deck");
  deckEl.querySelectorAll(".card").forEach(n => n.remove());
  const stack = G.deck.length ? Math.min(5, 1 + Math.floor(G.deck.length / 8)) : 0;
  for (let i = 0; i < stack; i++) {
    const b = makeCardEl(null, false);
    b.style.left = (i * 1.5) + "px"; b.style.top = (-i * 1.5) + "px";
    deckEl.insertBefore(b, $("deckCount"));
  }

  // Bot hand (face down until the round is over).
  const botRow = $("botHand");
  botRow.innerHTML = "";
  G.hands[1].forEach(c => {
    const slot = document.createElement("div"); slot.className = "card-slot";
    slot.appendChild(makeCardEl(c, revealBot)); botRow.appendChild(slot);
  });

  // Open pile: the card under the drop (the one you may take), then the top card.
  const openEl = $("open");
  openEl.querySelectorAll(".card").forEach(n => n.remove());
  const n = G.openPile.length;
  let underCode = "";
  if (pendingTake && pendingTake.canTake && !pendingTake.noPick && pendingTake.prevIndex < n - 1) underCode = G.openPile[pendingTake.prevIndex];
  else if (n > 1) underCode = G.openPile[n - 2];
  if (underCode) {
    const under = makeCardEl(underCode, true);
    under.classList.add("under");
    under.style.left = "5px"; under.style.top = "-5px";
    openEl.insertBefore(under, $("openCount"));
  }
  if (n) {
    const top = makeCardEl(G.topOpen, true);
    top.classList.add("top");
    if (lastDropCount > 1) {
      const badge = document.createElement("span");
      badge.className = "badge";
      badge.textContent = `×${lastDropCount}`;
      top.appendChild(badge);
    }
    openEl.insertBefore(top, $("openCount"));
  }

  // Joker card: the set-aside card, face up, so its rank (worth 0 this round) is always visible.
  const jokerEl = $("joker");
  jokerEl.querySelectorAll(".card").forEach(n => n.remove());
  if (G.setAside) {
    const jc = makeCardEl(G.setAside, true);
    jc.classList.add("wild");
    jokerEl.insertBefore(jc, $("jokerCount"));
  }
  $("jokerCount").textContent = G.setAside ? `Joker: ${rankLabel(G.jokerRank)} = 0 pts` : "";

  // My hand.
  const row = $("myHand");
  row.innerHTML = "";
  G.hands[0].forEach((c, i) => {
    const slot = document.createElement("div"); slot.className = "card-slot";
    const el = makeCardEl(c, true);
    el.tabIndex = 0; el.setAttribute("role", "button");
    el.setAttribute("aria-pressed", selected.has(i) ? "true" : "false");
    if (selected.has(i)) el.classList.add("sel");
    el.addEventListener("click", () => onCardClick(i));
    el.addEventListener("pointerdown", e => onCardPointerDown(e, i, el));
    el.addEventListener("keydown", e => { if (e.key === "Enter" || e.key === " ") { e.preventDefault(); onCardClick(i); } });
    slot.appendChild(el); row.appendChild(slot);
  });

  layoutRow(botRow, false);
  layoutRow(row, true);
  renderScore();
}

function selectionRank() {
  const cards = [...selected].map(i => G.hands[0][i]);
  if (!cards.length) return null;
  return cards.every(c => rankOf(c) === rankOf(cards[0])) ? rankOf(cards[0]) : "";
}

function setButtons() {
  const t = handTotal(G.hands[0]);
  const sr = selectionRank();
  const vis = (id, on) => { $(id).hidden = !on; };
  vis("dropBtn", phase === "drop");
  vis("takeBtn", phase === "pick" && !!lastAction && lastAction.canTake);
  vis("drawBtn", phase === "pick");
  vis("showBtn", phase === "showfirst");
  vis("passBtn", phase === "showfirst");
  vis("nextBtn", phase === "over" && !G.gameOver);
  $("dropBtn").disabled = !(phase === "drop" && !busy && sr);
  $("dropBtn").textContent = selected.size > 1 && sr ? `Drop ${selected.size} cards` : "Drop selected";
  $("takeBtn").disabled = busy;
  $("drawBtn").disabled = busy;
  $("showBtn").disabled = !(phase === "showfirst" && !busy && t <= SHOW_MAX);
  $("passBtn").disabled = !(phase === "showfirst" && !busy);
  $("nextBtn").disabled = !(phase === "over" && !busy && !G.gameOver);
  document.querySelectorAll(".mini").forEach(b => { b.disabled = handLocked() || G.hands[0].length < 2; });
  const canPick = phase === "pick" && !busy;
  $("deck").classList.toggle("glow", canPick);
  $("open").classList.toggle("glow", canPick && !!lastAction && lastAction.canTake);
}

// ---- Animation --------------------------------------------------------------
// One card flies on an arc from one box to another (Web Animations API).
function fly(from, to, code, faceUp, o = {}) {
  if (REDUCED) return Promise.resolve();
  const { dur = 520, delay = 0, endRot = 0 } = o;
  return new Promise(resolve => {
    const c = makeCardEl(code, faceUp);
    c.classList.add("flying");
    c.style.left = from.left + "px"; c.style.top = from.top + "px";
    c.style.width = from.width + "px"; c.style.height = from.height + "px";
    document.body.appendChild(c);
    const dx = to.left - from.left, dy = to.top - from.top;
    const sc = to.width / from.width;
    const lift = Math.min(70, Math.hypot(dx, dy) * 0.14);
    let done = false;
    const finish = () => { if (done) return; done = true; c.remove(); resolve(); };
    const a = c.animate([
      { transform: "translate(0,0) rotate(0deg) scale(1)", offset: 0 },
      { transform: `translate(${dx * 0.55}px,${dy * 0.55 - lift}px) rotate(${endRot / 2}deg) scale(1.1)`, offset: 0.55 },
      { transform: `translate(${dx}px,${dy}px) rotate(${endRot}deg) scale(${sc})`, offset: 1 },
    ], { duration: dur, delay, easing: "cubic-bezier(.3,.7,.2,1)", fill: "both" });
    a.onfinish = finish; a.oncancel = finish;
    setTimeout(finish, dur + delay + 250);
  });
}
// Fly a card into the real element that will show it; the element stays hidden until it lands.
async function flyInto(el, from, code, faceUp, o = {}) {
  if (!el) return;
  const holder = el.parentElement && el.parentElement.classList.contains("card-slot") ? el.parentElement : el;
  const to = cardBox(holder);
  const endRot = parseFloat(holder.dataset.rot || "0");
  if (o.sfx) setTimeout(o.sfx, o.delay || 0);
  await fly(from, to, code, faceUp, { ...o, endRot });
  el.style.visibility = "";
  if (o.flip) el.classList.add("flipin");
  if (o.land) el.classList.add("land");
}
// Dropped cards fly to the top of the open pile; the pile's top card appears on the first landing.
async function dropFlight(cards, boxes) {
  const top = $("open").querySelector(".card.top");
  if (!top) return;
  hide(top);
  const to = cardBox(top);
  const n = cards.length;
  await Promise.all(cards.map((c, i) =>
    fly(boxes[i], to, c, true, { dur: 480, delay: i * 90, endRot: i === n - 1 ? 0 : (i - n + 1) * 4 })
      .then(() => { if (i === 0) top.style.visibility = ""; })));
  top.style.visibility = "";
  top.classList.add("land");
}

async function dealAnimation() {
  renderAll();
  const mine = [...$("myHand").children].map(s => s.firstElementChild);
  const bots = [...$("botHand").children].map(s => s.firstElementChild);
  const open = $("open").querySelector(".card.top");
  const jk = $("joker").querySelector(".card");
  [...mine, ...bots, open, jk].forEach(hide);
  const from = cardBox($("deck"));
  const jobs = [];
  for (let i = 0; i < 7; i++) {
    jobs.push({ el: mine[i], code: G.hands[0][i], flip: true });
    jobs.push({ el: bots[i], code: G.hands[1][i], flip: false });
  }
  jobs.push({ el: open, code: G.topOpen, flip: true });
  jobs.push({ el: jk, code: G.setAside, flip: true });
  SFX.shuffle();
  await Promise.all(jobs.map((j, i) =>
    flyInto(j.el, from, j.code, false, { dur: 430, delay: i * 85, flip: j.flip, sfx: SFX.deal })));
  await sleep(120);
}

// Everything on the table flies back into the draw pile, which then shuffles.
async function collectAnimation() {
  const to = cardBox($("deck"));
  const jobs = [];
  const grab = el => jobs.push({ from: cardBox(el.parentElement.classList.contains("card-slot") ? el.parentElement : el),
                                 code: el.dataset.code, up: el.dataset.up === "1" });
  [...$("myHand").children].forEach(s => grab(s.firstElementChild));
  [...$("botHand").children].forEach(s => grab(s.firstElementChild));
  const openEls = [...$("open").querySelectorAll(".card")];
  openEls.forEach(grab);
  const jokerEls = [...$("joker").querySelectorAll(".card")];
  jokerEls.forEach(grab);
  jokerEls.forEach(n => n.remove());
  $("jokerCount").textContent = "";
  for (let i = 0; i < Math.min(6, Math.max(0, G.openPile.length - openEls.length)); i++)
    jobs.push({ from: cardBox($("open")), code: "", up: false });
  $("myHand").innerHTML = ""; $("botHand").innerHTML = "";
  openEls.forEach(n => n.remove());
  SFX.deal();
  await Promise.all(jobs.map((j, i) => fly(j.from, to, j.code, j.up, { dur: 460, delay: i * 26 })));
  $("deck").classList.add("shuffling");
  SFX.shuffle();
  await sleep(900);
  $("deck").classList.remove("shuffling");
}

// ---- Flow -------------------------------------------------------------------
async function newRound() {
  busy = true; phase = "idle"; selected.clear(); lastAction = null; pendingTake = null; setButtons();
  hideBanner();
  if (G.hands[0].length + G.hands[1].length + G.openPile.length > 0) {
    dealing = true; renderInfo();
    await collectAnimation();
  }
  revealBot = false; lastDropCount = 0;
  dealCore();
  dealing = true;
  setStatus("Dealing…");
  await dealAnimation();
  dealing = false;
  renderAll();
  log(`Round ${G.round}: cards dealt. The joker rank is ${rankLabel(G.jokerRank)}.`);
  busy = false;
  if (G.turn === 1) botTurnUI();
  else startHumanTurnUI();
}

function startHumanTurnUI() {
  G.turnsInRound++;
  phase = "idle";
  if (G.hands[0].length === 0) { log("You have no cards left, so you show."); finishRoundUI(0); return; }
  if (G.forceShow || G.turnsInRound > STALL_TURNS) {
    const myT = handTotal(G.hands[0]), botT = handTotal(G.hands[1]);
    if (G.forceShow || myT <= botT) { log("You must show."); finishRoundUI(0); return; }
    G.forceShow = true;
    log("You pass. The bot must show.");
    G.turn = 1;
    botTurnUI();
    return;
  }
  // Show is decided before the drop.
  if (handTotal(G.hands[0]) <= SHOW_MAX) {
    phase = "showfirst";
    renderInfo(); setButtons();
    setStatus(`Your total is ${handTotal(G.hands[0])}. Show now, or keep playing.`, "you");
    log(`Your total is ${handTotal(G.hands[0])}. Show now, or continue to drop.`);
    return;
  }
  enterDropPhase();
}

function enterDropPhase() {
  phase = "drop";
  selected.clear();
  renderAll(); setButtons();
  setStatus("Your turn: select cards of one rank, then drop them.", "you");
  log("Select cards of one rank, then press Drop selected.");
}

function endHumanTurn() {
  phase = "botwait";
  setButtons();
  G.turn = 1;
  botTurnUI();
}

// Index of each card of `cards` inside hand `me` (handles duplicate cards).
function pickIndices(me, cards) {
  const used = new Set();
  return cards.map(c => {
    const i = G.hands[me].findIndex((x, k) => x === c && !used.has(k));
    used.add(i);
    return i;
  });
}

async function botTurnUI() {
  busy = true; phase = "botwait"; setButtons();
  setStatus("Bot is thinking", "think");
  await sleep(700);
  G.turnsInRound++;
  if (G.hands[1].length === 0) { log("The bot has no cards left, so it shows."); finishRoundUI(1); return; }
  if (G.forceShow || G.turnsInRound > STALL_TURNS) {
    const myT = handTotal(G.hands[0]), botT = handTotal(G.hands[1]);
    if (G.forceShow || botT <= myT) { log("The bot must show."); finishRoundUI(1); return; }
    G.forceShow = true;
    log("The bot passes. You must show.");
    G.turn = 0; busy = false;
    startHumanTurnUI();
    return;
  }

  // 1. Show check, before the drop.
  const sc = botShowCheck(1);
  if (sc.shows) {
    log(`Bot shows with ${sc.t} (chance ${Math.round(sc.est.P * 100)}%).`);
    finishRoundUI(1);
    return;
  }

  // 2. Drop: the cards fly from the bot's row to the open pile.
  const drop = chooseDrop(1);
  const fromBoxes = pickIndices(1, drop.cards).map(i => cardBox($("botHand").children[i]));
  const a = dropGroup(1, drop.cards);
  lastDropCount = drop.cards.length;
  pendingTake = a;
  log(`Bot drops ${drop.cards.length} card(s): ${drop.cards.join(" ")}.`);
  SFX.drop();
  renderAll();
  await dropFlight(drop.cards, fromBoxes);

  // 3. Pick: from under the drop, or from the draw pile, flying into the bot's row.
  if (!a.noPick) {
    await sleep(250);
    const underEl = $("open").querySelector(".card.under");
    const underBox = underEl ? cardBox(underEl) : cardBox($("open"));
    const deckBox = cardBox($("deck"));
    const p = botPick(1, a);
    pendingTake = null;
    renderAll();
    const el = lastCardEl("botHand");
    hide(el);
    if (p.type === "take") {
      SFX.take();
      log("Bot takes the card under its drop.");
      await flyInto(el, underBox, p.card, true, { dur: 480 });
    } else if (p.card) {
      SFX.deal();
      log("Bot draws from the pile.");
      await flyInto(el, deckBox, null, false, { dur: 480 });
    } else if (el) el.style.visibility = "";
  } else {
    pendingTake = null;
    log("Bot's drop matched the open card, so it needs no pick.");
    await sleep(350);
  }

  G.turn = 0; busy = false;
  renderAll();
  startHumanTurnUI();
}

async function finishRoundUI(showerIdx) {
  busy = true; pendingTake = null;
  selected.clear();
  const roundNo = G.round;
  const r = endRound(showerIdx);
  const you = showerIdx === 0 ? r.showerPts : r.otherPts;
  const bot = showerIdx === 1 ? r.showerPts : r.otherPts;
  history.push({ round: roundNo, you, bot });
  phase = "over";
  setButtons();
  setStatus("Revealing hands…");

  // Reveal the bot's hand with a staggered flip.
  revealBot = true;
  renderAll();
  [...$("botHand").children].forEach((s, i) => {
    const el = s.firstElementChild;
    el.style.animationDelay = (i * 70) + "ms";
    el.classList.add("flipin");
  });
  SFX.flip();
  await sleep(450 + G.hands[1].length * 70);

  const who = showerIdx === 0 ? "You" : "The bot";
  const verdict = r.tieZero ? "both hands total 0: tie, no points"
                : r.right ? "right show" : "wrong show (penalty)";
  const myT = handTotal(G.hands[0]), botT = handTotal(G.hands[1]);
  log(`${who} showed: ${verdict}. Your hand ${myT}, bot ${botT}.`, r.tieZero ? "" : (you < bot ? "good" : "bad"));
  log(`Round points: you +${you}, bot +${bot}.`);
  const kind = r.tieZero ? "" : (you < bot ? "good" : "bad");
  const title = r.tieZero ? "Tie: no points"
              : showerIdx === 0 ? (r.right ? "Right show!" : `Wrong show: +${PENALTY} penalty`)
                                : (r.right ? "The bot showed correctly" : "The bot's show failed!");
  showBanner(title, `You ${myT} · Bot ${botT}  →  You +${you}, Bot +${bot}`, kind);
  if (kind === "good") SFX.show(); else if (kind === "bad") SFX.bad();

  renderInfo(); renderScore();
  busy = false;
  setStatus(G.gameOver ? "Game over" : "Round over. Press Next round.", "you");
  setButtons();
  if (G.gameOver) {
    const youWin = G.scores[0] < G.scores[1];
    const tie = G.scores[0] === G.scores[1];
    await sleep(1600);
    if (youWin) { SFX.win(); confetti(); }
    showOver(tie ? "Tie game" : youWin ? "You win!" : "The bot wins",
             `Final scores: you ${G.scores[0]}, bot ${G.scores[1]}.`);
  }
}

// ---- Human actions ----------------------------------------------------------
function onCardClick(i) {
  if (suppressClick) return;
  if (phase !== "drop" || busy) return;
  if (selected.has(i)) selected.delete(i); else selected.add(i);
  renderAll();
  setButtons();
}

async function onDrop() {
  if (phase !== "drop" || busy) return;
  const idx = [...selected].sort((a, b) => a - b);
  const cards = idx.map(i => G.hands[0][i]);
  if (!cards.length || !cards.every(c => rankOf(c) === rankOf(cards[0]))) {
    log("Those cards are not one rank. Select cards of the same rank.", "bad");
    SFX.bad();
    return;
  }
  // Remember where the cards are, then change the state, re-render and animate.
  const boxes = idx.map(i => cardBox($("myHand").children[i].firstElementChild));
  selected.clear();
  busy = true;
  lastAction = dropGroup(0, cards);
  lastDropCount = cards.length;
  pendingTake = lastAction.noPick ? null : lastAction;
  SFX.drop();
  log(`You drop ${cards.length} card(s): ${cards.join(" ")}.`);
  renderAll(); setButtons();
  await dropFlight(cards, boxes);
  busy = false;
  if (lastAction.noPick) {
    pendingTake = null;
    log("Your drop matches the open card, so no pick is needed.", "good");
    renderAll();
    endHumanTurn();
  } else {
    phase = "pick";
    setButtons();
    setStatus("Take the glowing card under your drop, or draw from the pile.", "you");
    log("Now take the card under your drop, or draw from the pile.");
  }
}

async function onTake() {
  if (phase !== "pick" || busy || !lastAction || !lastAction.canTake) return;
  busy = true; humanFlying = true; setButtons();
  const underEl = $("open").querySelector(".card.under");
  const from = underEl ? cardBox(underEl) : cardBox($("open"));
  const c = takePrevOpen(lastAction);
  pendingTake = null;
  if (c) { G.hands[0].push(c); G.known[1].push(c); }   // the bot sees that you took this card
  SFX.take();
  log(`You take ${c} from under your drop.`);
  renderAll();
  const el = lastCardEl("myHand");
  hide(el);
  await flyInto(el, from, c, true, { dur: 480, land: true });
  busy = false; humanFlying = false;
  endHumanTurn();
}

async function onDraw() {
  if (phase !== "pick" || busy) return;
  busy = true; humanFlying = true; setButtons();
  const from = cardBox($("deck"));
  if (G.deck.length === 0 && G.openPile.length > 1) { log("The draw pile is empty: reshuffling."); SFX.shuffle(); }
  pendingTake = null;
  const c = drawFromDeck();
  if (c) G.hands[0].push(c);
  SFX.deal();
  log("You draw from the pile.");
  renderAll();
  if (c) {
    const el = lastCardEl("myHand");
    hide(el);
    await flyInto(el, from, null, false, { dur: 480, flip: true });
  }
  busy = false; humanFlying = false;
  endHumanTurn();
}

function onShow() {
  if (phase !== "showfirst" || busy) return;
  const t = handTotal(G.hands[0]);
  if (t > SHOW_MAX) return;
  log(`You show with ${t}.`);
  finishRoundUI(0);
}
function onContinue() {
  if (phase !== "showfirst" || busy) return;
  log("You do not show. Now drop cards.");
  enterDropPhase();
}

// ---- Reorder your own hand (drag a card, or use the sort buttons) ------------
const handLocked = () => dealing || humanFlying || !G.hands[0].length;

// Apply a new order (array of old indices), keeping selection, and glide the cards into place.
function applyHandOrder(order) {
  const row = $("myHand");
  const old = [...row.children].map(s => ({ code: s.firstElementChild.dataset.code, r: s.firstElementChild.getBoundingClientRect() }));
  const hand = G.hands[0];
  const newSel = new Set();
  order.forEach((orig, pos) => { if (selected.has(orig)) newSel.add(pos); });
  G.hands[0] = order.map(k => hand[k]);
  selected.clear(); newSel.forEach(x => selected.add(x));
  renderAll(); setButtons();
  if (REDUCED) return;
  [...row.children].forEach(s => {
    const el = s.firstElementChild;
    const k = old.findIndex(o => o && o.code === el.dataset.code);
    if (k < 0) return;
    const o = old[k]; old[k] = null;
    const n = el.getBoundingClientRect();
    const dx = o.r.left - n.left, dy = o.r.top - n.top;
    if (Math.abs(dx) + Math.abs(dy) < 1) return;
    el.animate([{ transform: `translate(${dx}px,${dy}px)` }, { transform: "translate(0,0)" }],
               { duration: 380, easing: "cubic-bezier(.22,.8,.24,1)" });
  });
}

function sortHand(mode) {
  if (handLocked()) return;
  const hand = G.hands[0];
  const rankIdx = c => (c === "JK" ? -1 : RANKS.indexOf(rankOf(c)));
  const suitIdx = c => (c === "JK" ? -1 : SUITS.indexOf(suitOf(c)));
  const val = c => valueOf(c, G.jokerRank);
  const keys = {
    rank:   c => [rankIdx(c), suitIdx(c)],
    suit:   c => [suitIdx(c), rankIdx(c)],
    points: c => [val(c), rankIdx(c), suitIdx(c)],
  }[mode];
  const order = hand.map((_, k) => k).sort((a, b) => {
    const ka = keys(hand[a]), kb = keys(hand[b]);
    for (let i = 0; i < ka.length; i++) if (ka[i] !== kb[i]) return ka[i] - kb[i];
    return a - b;
  });
  applyHandOrder(order);
  SFX.flip();
}

function abortDrag() {
  if (!drag) return;
  window.removeEventListener("pointermove", drag.move);
  window.removeEventListener("pointerup", drag.up);
  window.removeEventListener("pointercancel", drag.up);
  drag = null;
}
function onCardPointerDown(e, i, el) {
  if (handLocked() || (e.button !== undefined && e.button !== 0)) return;
  abortDrag();
  const slots = [...$("myHand").children];
  const centers = slots.map(s => { const r = s.getBoundingClientRect(); return r.left + r.width / 2; });
  drag = { i, el, slot: slots[i], slots, centers, target: i, x0: e.clientX, y0: e.clientY, moved: false,
           base: slots.map(s => s.style.transform),
           shift: centers.length > 1 ? Math.abs(centers[1] - centers[0]) : 0 };
  drag.move = ev => {
    const dx = ev.clientX - drag.x0, dy = ev.clientY - drag.y0;
    if (!drag.moved) {
      if (Math.hypot(dx, dy) < 8) return;
      drag.moved = true;
      el.classList.add("dragging");
      drag.slot.style.zIndex = 200;
    }
    el.style.transform = `translate(${dx}px,${dy}px) scale(1.08)`;
    let t = 0, best = Infinity;
    drag.centers.forEach((c, k) => { const d = Math.abs(c - ev.clientX); if (d < best) { best = d; t = k; } });
    drag.target = t;
    drag.slots.forEach((s, k) => {
      if (k === drag.i) return;
      let sh = 0;
      if (drag.i < t && k > drag.i && k <= t) sh = -drag.shift;
      else if (drag.i > t && k >= t && k < drag.i) sh = drag.shift;
      s.style.transform = `translateX(${sh}px) ${drag.base[k]}`;
    });
  };
  drag.up = () => {
    const d = drag;
    abortDrag();
    if (!d.moved) return;
    suppressClick = true;
    setTimeout(() => { suppressClick = false; }, 60);
    const order = G.hands[0].map((_, k) => k);
    const [m] = order.splice(d.i, 1);
    order.splice(d.target, 0, m);
    // Dragged card: start the glide from where it was dropped.
    const dragged = d.el.getBoundingClientRect();
    const moved = d.target !== d.i;
    if (!moved) { renderAll(); setButtons(); return; }
    applyHandOrder(order);
    const el2 = $("myHand").children[d.target].firstElementChild;
    const n = el2.getBoundingClientRect();
    if (!REDUCED) el2.animate([{ transform: `translate(${dragged.left - n.left}px,${dragged.top - n.top}px) scale(1.08)` },
                               { transform: "translate(0,0) scale(1)" }],
                              { duration: 320, easing: "cubic-bezier(.22,.8,.24,1)" });
    SFX.deal();
  };
  window.addEventListener("pointermove", drag.move);
  window.addEventListener("pointerup", drag.up);
  window.addEventListener("pointercancel", drag.up);
}
document.querySelectorAll(".mini").forEach(b => b.addEventListener("click", () => sortHand(b.dataset.sort)));

// ---- Start, buttons, URL modes ----------------------------------------------
function startGame() {
  ctx();
  $("start").classList.add("hidden");
  $("over").classList.add("hidden");
  G = newState();
  history = []; selected.clear();
  lastAction = null; pendingTake = null; lastDropCount = 0; revealBot = false; dealing = false;
  $("log").innerHTML = "";
  hideBanner();
  renderAll(); setButtons();
  newRound();
}
$("startBtn").addEventListener("click", startGame);
$("againBtn").addEventListener("click", startGame);
$("dropBtn").addEventListener("click", onDrop);
$("takeBtn").addEventListener("click", onTake);
$("drawBtn").addEventListener("click", onDraw);
$("showBtn").addEventListener("click", onShow);
$("passBtn").addEventListener("click", onContinue);
$("nextBtn").addEventListener("click", () => { if (!G.gameOver && phase === "over" && !busy) newRound(); });
$("deck").addEventListener("click", onDraw);
$("open").addEventListener("click", onTake);
$("muteBtn").addEventListener("click", () => {
  muted = !muted;
  $("muteBtn").textContent = muted ? "🔇" : "🔊";
});
let resizeTimer = null;
window.addEventListener("resize", () => {
  clearTimeout(resizeTimer);
  resizeTimer = setTimeout(() => { if (!busy && !dealing) renderAll(); }, 120);
});

const params = new URLSearchParams(location.search);
if (params.has("sim")) {
  const r = runSim(parseInt(params.get("sim"), 10) || 1000);
  console.log("Simulation", r);
  $("start").classList.add("hidden");
  log(`Simulation: ${r.games} games, P0 ${r.wins[0]}, P1 ${r.wins[1]}, ties ${r.ties}, avg rounds ${r.avgRounds.toFixed(2)}`);
}
if (params.has("test")) {
  const r = selfTest();
  console.log("Probability self-test", r);
  $("start").classList.add("hidden");
  log(`Probability self-test: ${r.checked} states, worst error ${r.worst.toExponential(2)}`);
}

renderAll();
setButtons();
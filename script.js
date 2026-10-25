// ==== CORE (pure game logic, no DOM). Mirrors least_count_best.cpp. ============
// v3: upgraded Monte Carlo bot (unbiased human show model, fast pools, fixed rollouts,
//     persistent opponent learning). See "UPGRADE" notes inside the MC section.

// Settings (same values as the C++ program, except SHOW_MAX which is now 10).
const LIMIT = 200, PENALTY = 40, SHOW_MAX = 10, STALL_TURNS = 60;
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
const ALL_CARDS = makeDeck();   // constant copy used by the fast hiddenPool
function shuffled(a) {
  const b = a.slice();
  for (let i = b.length - 1; i > 0; i--) {
    const j = Math.floor(Math.random() * (i + 1));
    [b[i], b[j]] = [b[j], b[i]];
  }
  return b;
}
// A=1, 2-9 face value, T/J/Q/K=10, JK=0, cards of this round's joker rank=0.
// Memoised per joker rank (this is called millions of times inside rollouts).
let _vjr = null, _vcache = new Map();
function valueOf(c, jr) {
  if (jr !== _vjr) { _vjr = jr; _vcache = new Map(); }
  let v = _vcache.get(c);
  if (v !== undefined) return v;
  if (c === "JK") v = 0;
  else {
    const r = rankOf(c);
    if (r === jr) v = 0;
    else if (r === "A") v = 1;
    else if (r === "T" || r === "J" || r === "Q" || r === "K") v = 10;
    else v = parseInt(r, 10);
  }
  _vcache.set(c, v);
  return v;
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
    slots: [[], []],
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
  // slots[v][i] = ranks that viewer v knows the opponent's i-th unseen card is NOT.
  G.slots = [0, 1].map(() => Array.from({ length: 7 }, () => new Set()));
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

// Whether a drop is assumed to always contain every card of that rank the dropper holds.
// The bot always does this; the human may drop just one of a pair, so startGame() turns it off.
let ASSUME_FULL_DROPS = true;

// Drop = cards of one rank. The card face-up before the drop stays under it.
function dropGroup(me, cards) {
  const prev = G.topOpen;
  const a = {
    prevOpen: prev, prevIndex: 0, canTake: prev !== "",
    noPick: prev !== "" && rankOf(cards[0]) === rankOf(prev),
  };
  let unseen = 0;
  for (const c of cards) {
    removeOne(G.hands[me], c);
    if (!removeOne(G.known[1 - me], c)) unseen++;   // the opponent now sees these cards
    G.openPile.push(c);
  }
  trackDrop(1 - me, rankOf(cards[0]), unseen, me === 1 || ASSUME_FULL_DROPS);
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

// Cards player `me` cannot see. Count-based removal: no fresh deck, no indexOf per card.
function hiddenPool(me) {
  const rm = new Map();
  const add = c => rm.set(c, (rm.get(c) || 0) + 1);
  for (const c of G.hands[me]) add(c);
  for (const c of G.openPile) add(c);
  for (const c of G.known[me]) add(c);
  add(G.setAside);
  const pool = [];
  for (const c of ALL_CARDS) {
    const n = rm.get(c);
    if (n) rm.set(c, n - 1); else pool.push(c);
  }
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

// Match-first pickup preserves a useful same-rank group for a later drop.
// If there is no match, take a low-value open card only when it beats the draw estimate.
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
// Conservative greedy tie-break: keep the risk-adjusted score as the main signal,
// but do not let a tiny score difference force an obviously weaker point-removal move.
const GREEDY_SCORE_MARGIN = 2.0;
const GREEDY_EXTRA_CARD_BONUS = 0.5;

function groupPointValue(cards) {
  return cards.reduce((sum, c) => sum + valueOf(c, G.jokerRank), 0);
}
function greedyDropValue(drop) {
  return groupPointValue(drop.cards)
       + GREEDY_EXTRA_CARD_BONUS * Math.max(0, drop.cards.length - 1);
}

// Plan B (rounds 1..bait): 6s, then 8s, then 7s. Otherwise use the
// risk-adjusted score, then a greedy tie-break when scores are within 2 points.
function chooseDrop(me) {
  let opts = getDropOptions(me);

  // Keep zero-point jokers/joker-rank cards while any positive-point group exists.
  const nonZero = opts.filter(o => o.cards.some(c => valueOf(c, G.jokerRank) > 0));
  if (nonZero.length) opts = nonZero;

  if (G.round <= PAR[me].bait) {
    for (const r of ["6", "8", "7"]) {
      const o = opts.find(x => x.rank === r);
      if (o) return o;
    }
  }

  const best = opts.reduce((a, b) => (b.score > a.score ? b : a));
  const nearBest = opts.filter(o => best.score - o.score <= GREEDY_SCORE_MARGIN + 1e-9);
  let chosen = nearBest[0] || best;

  for (const option of nearBest.slice(1)) {
    const optionValue = greedyDropValue(option);
    const chosenValue = greedyDropValue(chosen);
    if (optionValue > chosenValue + 1e-9 ||
        (Math.abs(optionValue - chosenValue) <= 1e-9 && option.score > chosen.score)) {
      chosen = option;
    }
  }

  chosen.greedyTieBreak = chosen !== best && chosen.score < best.score - 1e-9;
  chosen.greedyScoreGap = Math.max(0, best.score - chosen.score);
  return chosen;
}

// ==== Challenger strategy (tuned against the original bot) ===================
// This is a heuristic policy, not a mathematically proven optimal solver.
const CHALLENGER_CFG = {
  riskModel: "corrected",
  oppRisk: 1,                 // was 2: keeps the exposure coefficient from going negative for big cards
  pickMargin: 1.5,
  showMargin: 30,
  safeShowPenProb: 0.005,
  groupBonus: 0.5,
  noPickBonus: 2,
  zeroGroupBonus: 1,
  excludeZero: true,
  setupThresholdBonus: 0.5,
  setupW: 0.25,
  leakW: 1,                   // cost of handing the opponent a cheap card to pick up
  leakSoft: 1.2               // how sharply "cheap" is judged
};
const DEFAULT_CFG = { ...CHALLENGER_CFG };   // the original, untrained settings

function exactHoldProbability(me, rank, pool) {
  if (G.known[me].some(c => rankOf(c) === rank)) return 1;
  const m = unknownCount(me), n = pool.length;
  if (m <= 0 || n <= 0) return 0;
  const copies = pool.filter(c => rankOf(c) === rank).length;
  if (copies <= 0) return 0;
  if (n - copies < m) return 1;
  const denom = binom(n, m);
  if (!(denom > 0)) return 0;
  return Math.max(0, Math.min(1, 1 - binom(n - copies, m) / denom));
}

// Returns every drop option, scored and sorted best-first.
function challengerRankDrops(me) {
  let opts = getDropOptions(me);
  const pool = hiddenPool(me);
  const avg = poolAverage(pool);
  const top = G.topOpen;
  const topVal = top ? valueOf(top, G.jokerRank) : avg;
  const hasTopRank = !!top && G.hands[me].some(c => rankOf(c) === rankOf(top));
  const takesTop = !!top && (hasTopRank || topVal < avg - CHALLENGER_CFG.pickMargin);

  if (CHALLENGER_CFG.excludeZero) {
    const nonZero = opts.filter(o => o.cards.some(c => valueOf(c, G.jokerRank) > 0));
    if (nonZero.length) opts = nonZero;
  }

  for (const o of opts) {
    const points = o.cards.reduce((sum, c) => sum + valueOf(c, G.jokerRank), 0);
    const noPick = !!top && o.rank === rankOf(top);
    const exposedValue = valueOf(o.cards[o.cards.length - 1], G.jokerRank);
    const rankProb = exactHoldProbability(me, o.rank, pool);
    const ownPickupCost = noPick ? 0 : (takesTop ? topVal : avg);
    const sizeBonus = CHALLENGER_CFG.groupBonus * Math.max(0, o.cards.length - 1);
    const noPickBonus = noPick ? CHALLENGER_CFG.noPickBonus : 0;
    const zeroGroupBonus = points === 0 ? CHALLENGER_CFG.zeroGroupBonus * o.cards.length : 0;
    const setup = (!noPick && top)
      ? G.hands[me].filter(c => rankOf(c) === rankOf(top))
          .reduce((sum, c) => sum + valueOf(c, G.jokerRank), 0)
      : 0;
    // The opponent only saves one pick if they hold this rank, never more than an average card.
    const exposureCost = CHALLENGER_CFG.oppRisk * rankProb * Math.min(avg, exposedValue);
    // The card left on top is the opponent's free pickup: a cheap one (2, A, 0) is a gift,
    // a high one costs nothing. This stops the bot from dumping 2s and Aces for no reason.
    const oppTakeProb = 1 / (1 + Math.exp((exposedValue - (avg - CHALLENGER_CFG.pickMargin)) / CHALLENGER_CFG.leakSoft));
    const leakCost = CHALLENGER_CFG.leakW * oppTakeProb * Math.max(0, avg - exposedValue);
    o.challengerScore = points - ownPickupCost - exposureCost - leakCost
      + sizeBonus + noPickBonus + zeroGroupBonus + CHALLENGER_CFG.setupW * setup;
  }

  opts.sort((a, b) => b.challengerScore - a.challengerScore
    || b.cards.reduce((s,c)=>s+valueOf(c,G.jokerRank),0) - a.cards.reduce((s,c)=>s+valueOf(c,G.jokerRank),0)
    || b.cards.length - a.cards.length);
  return opts;
}
function challengerChooseDrop(me) { return challengerRankDrops(me)[0]; }

function challengerTakesOpen(me, openCard) {
  if (!openCard) return false;
  const r = rankOf(openCard);
  if (G.hands[me].some(c => rankOf(c) === r)) return true;
  const pool = hiddenPool(me);
  const avg = poolAverage(pool);
  const v = valueOf(openCard, G.jokerRank);
  const matchPotential = pool.filter(c => rankOf(c) === r).length;
  const threshold = avg - CHALLENGER_CFG.pickMargin
    - CHALLENGER_CFG.setupThresholdBonus * (matchPotential > 0 ? 1 : 0);
  return v < threshold;
}

function challengerPick(me, action) {
  const opp = 1 - me;
  if (challengerTakesOpen(me, action.prevOpen) && action.canTake) {
    const c = takePrevOpen(action);
    G.hands[me].push(c);
    G.known[opp].push(c);
    return { type: "take", card: c };
  }
  const c = drawInto(me);
  return { type: "draw", card: c };
}

function challengerShowCheck(me) {
  const t = handTotal(G.hands[me]);
  if (t > SHOW_MAX) return { shows: false, t };
  const est = estimateOpponent(me, t);
  const eg = expectedGain(est);
  const safeShow = t === 0 || est.penProb <= CHALLENGER_CFG.safeShowPenProb;
  return { shows: safeShow || eg >= CHALLENGER_CFG.showMargin, t, est, eg };
}

// ==== Score-aware Monte Carlo decision engine ================================
// Samples possible opponent hands (respecting what we know they cannot hold),
// plays each candidate move out to the end of the round, and picks the move that
// maximises the chance of WINNING THE MATCH (not just this round's points):
//   ahead   -> plays safe (avoids the 40-point wrong-show risk)
//   behind  -> plays daring (shows on thinner odds, accepts variance)
//   near 200 -> judged by who busts first
// The bot only leaves the heuristic's default move when another move wins by a clear
// statistical margin, so sampling noise cannot talk it into dropping a 2 or an A.
//
// UPGRADE v3 (all integrated below):
//  1. Human show model records BOTH choices (show / keep playing) per total, so a
//     cautious player is no longer modelled as "always shows at the 75th percentile".
//  2. Unfinished rollouts return real round POINTS, not raw hand totals.
//  3. valueOf / hiddenPool are memoised / count-based => many more samples per move.
//  4. The human pickup threshold is computed once per decision, not per rollout turn.
//  5. What the bot learned about you persists across games and browser sessions.

const MATCH = { sigma: 18, avgPtsPerRound: 12 };   // smaller sigma = reacts more to the score

// Rough match win chance for the player with score myS against oppS (lower score wins).
function matchWinProb(myS, oppS) {
  if (myS >= LIMIT || oppS >= LIMIT) return myS < oppS ? 1 : (myS > oppS ? 0 : 0.5);
  const roundsLeft = Math.max(1, (LIMIT - Math.max(myS, oppS)) / MATCH.avgPtsPerRound);
  const z = (oppS - myS) / (MATCH.sigma * Math.sqrt(roundsLeft));
  return 1 / (1 + Math.exp(-1.7 * z));
}

const MC = { ms: 700, min: 40, max: 800, topDrops: 5,
             switchZ: 1.5,     // normal final decision threshold
             minGain: 0.002,   // minimum win-probability improvement
             showZ: 0.5, debug: false,
             adaptive: true, earlyMin: 80, earlyZ: 2.5, earlyGain: 0.006 };

// Opponent (human) model.
//  shows        : totals the human actually showed with (legacy, used for A/B only)
//  showChoices  : every show / keep-playing decision made while total <= SHOW_MAX
//  pickup       : open-card pickup decisions (no matching rank)
const OPP_MODEL = { shows: [], pickup: [], showChoices: [] };
const UPGRADE = { on: true, persistKey: "lc_opp_v1", maxChoices: 150 };
let ROLLOUT_OPP = -1;              // which seat is the human inside a rollout
let ROLLOUT_THR = null;            // human pickup threshold, computed once per decision

// Legacy: 75th percentile of the human's show totals; null until 3 shows are seen.
function oppShowLimit() {
  const a = OPP_MODEL.shows;
  if (a.length < 3) return null;
  const s = a.slice().sort((x, y) => x - y);
  return s[Math.min(s.length - 1, Math.floor(0.75 * s.length))];
}

// P(human shows | their total is t): Beta-style prior + nearby observed choices
// (same total counts 100%, total +-1 counts 40%).
function humanShowProb(t) {
  if (t > SHOW_MAX) return 0;
  const prior = t <= 1 ? 0.95 : t <= 2 ? 0.85 : t <= 4 ? 0.55 : t <= 6 ? 0.25 : 0.08;
  let s = 0, n = 0;
  for (const c of OPP_MODEL.showChoices) {
    const d = Math.abs(c.t - t);
    const w = d === 0 ? 1 : d === 1 ? 0.4 : 0;
    if (w) { n += w; if (c.show) s += w; }
  }
  const k = 3;                       // prior strength
  return (s + k * prior) / (n + k);
}
function saveOppModel() {
  try {
    localStorage.setItem(UPGRADE.persistKey, JSON.stringify({
      showChoices: OPP_MODEL.showChoices, pickup: OPP_MODEL.pickup }));
  } catch (e) { /* storage unavailable */ }
}
function loadOppModel() {
  try {
    const o = JSON.parse(localStorage.getItem(UPGRADE.persistKey) || "null");
    if (o) {
      if (Array.isArray(o.showChoices)) OPP_MODEL.showChoices = o.showChoices.slice(-UPGRADE.maxChoices);
      if (Array.isArray(o.pickup)) OPP_MODEL.pickup = o.pickup.slice(-80);
    }
  } catch (e) { /* ignore */ }
}
function recordShowChoice(t, show) {
  if (t > SHOW_MAX) return;
  OPP_MODEL.showChoices.push({ t, show });
  if (OPP_MODEL.showChoices.length > UPGRADE.maxChoices) OPP_MODEL.showChoices.shift();
  saveOppModel();
}
// Clears everything the bot has learned about you.
function forgetHuman() {
  OPP_MODEL.showChoices = []; OPP_MODEL.pickup = []; OPP_MODEL.shows = [];
  try { localStorage.removeItem(UPGRADE.persistKey); } catch (e) { /* ignore */ }
}

// Learn the opponent's open-card pickup threshold from choices where they had no
// matching rank after their drop. Matching-rank choices are excluded because they
// reveal rank-building intent, not just a value threshold.
function recordHumanPickup(take, openCard) {
  if (!openCard) return;
  const rank = rankOf(openCard);
  if (G.hands[0].some(c => rankOf(c) === rank)) return;
  OPP_MODEL.pickup.push({ value: valueOf(openCard, G.jokerRank), take: !!take });
  if (OPP_MODEL.pickup.length > 80) OPP_MODEL.pickup.shift();
  saveOppModel();
}

function opponentPickupThreshold() {
  const samples = OPP_MODEL.pickup;
  const pool = hiddenPool(1);
  const prior = poolAverage(pool) - CHALLENGER_CFG.pickMargin;
  if (samples.length < 4) return prior;

  // Small-grid Bayesian/MAP estimate. The prior prevents a handful of actions
  // from causing extreme thresholds; the logistic likelihood models noisy choices.
  let bestThreshold = prior, bestLogPost = -Infinity;
  const softness = 1.5;
  for (let threshold = -1; threshold <= 10.0001; threshold += 0.25) {
    let logPost = -0.5 * Math.pow((threshold - prior) / 3, 2);
    for (const s of samples) {
      const p = 1 / (1 + Math.exp((s.value - threshold) / softness));
      logPost += Math.log(Math.max(1e-9, s.take ? p : 1 - p));
    }
    if (logPost > bestLogPost) { bestLogPost = logPost; bestThreshold = threshold; }
  }
  return bestThreshold;
}

function rolloutTakesOpen(me, openCard) {
  if (!openCard) return false;
  const rank = rankOf(openCard);
  if (G.hands[me].some(c => rankOf(c) === rank)) return true;
  if (me !== ROLLOUT_OPP) return challengerTakesOpen(me, openCard);
  const thr = ROLLOUT_THR !== null ? ROLLOUT_THR : opponentPickupThreshold();
  const pTake = 1 / (1 + Math.exp((valueOf(openCard, G.jokerRank) - thr) / 1.5));
  return Math.random() < pTake;
}

function rolloutPick(me, action) {
  const opp = 1 - me;
  if (rolloutTakesOpen(me, action.prevOpen) && action.canTake) {
    const c = takePrevOpen(action);
    G.hands[me].push(c);
    G.known[opp].push(c);
    return { type: "take", card: c };
  }
  const c = drawInto(me);
  return { type: "draw", card: c };
}

function mean(a) { let s = 0; for (const x of a) s += x; return a.length ? s / a.length : 0; }
// Paired comparison: same sampled world, two different moves.
function pairedStats(a, b) {
  const n = Math.min(a.length, b.length);
  if (n < 2) return { diff: 0, z: 0 };
  let m = 0;
  for (let i = 0; i < n; i++) m += a[i] - b[i];
  m /= n;
  let v = 0;
  for (let i = 0; i < n; i++) { const d = a[i] - b[i] - m; v += d * d; }
  const se = Math.sqrt(v / (n - 1) / n);
  return { diff: m, z: se > 1e-12 ? m / se : (m > 0 ? 99 : (m < 0 ? -99 : 0)) };
}

// Stop early only when paired samples give strong evidence: either a challenger
// clearly beats the heuristic default, or every alternative is clearly worse.
function mcConfidentEnough(U, base, n) {
  if (!MC.adaptive || n < MC.earlyMin || U.length < 2) return false;
  const means = U.map(mean);
  let best = 0;
  for (let i = 1; i < means.length; i++) if (means[i] > means[best]) best = i;
  if (best !== base) {
    const ps = pairedStats(U[best], U[base]);
    return ps.diff >= MC.earlyGain && ps.z >= MC.earlyZ;
  }
  for (let i = 0; i < U.length; i++) {
    if (i === base) continue;
    if (pairedStats(U[i], U[base]).z > -MC.earlyZ) return false;
  }
  return true;
}

// Draw a card into hand `me` and give the opponent's view a fresh, unconstrained slot.
function drawInto(me) {
  const c = drawFromDeck();
  if (c) { G.hands[me].push(c); G.slots[1 - me].push(new Set()); }
  return c;
}
// Viewer v saw the opponent drop `n` unseen cards of `rank`: those slots are gone.
// If excludeRank, no remaining unseen card can be that rank (valid only when the dropper
// always drops every card of a rank).
function trackDrop(v, rank, n, excludeRank = true) {
  const sl = G.slots[v];
  for (let k = 0; k < n && sl.length; k++) {
    let best = -1;
    sl.forEach((s, i) => { if (!s.has(rank) && (best < 0 || s.size < sl[best].size)) best = i; });
    sl.splice(best < 0 ? sl.length - 1 : best, 1);
  }
  if (excludeRank) for (const s of sl) s.add(rank);
}
function applyPick(me, a, take) {
  if (take && a.canTake) {
    const c = takePrevOpen(a);
    G.hands[me].push(c); G.known[1 - me].push(c);
    return { type: "take", card: c };
  }
  return { type: "draw", card: drawInto(me) };
}
function cloneState(s) {
  return { ...s, deck: s.deck.slice(), openPile: s.openPile.slice(),
    hands: s.hands.map(h => h.slice()), known: s.known.map(k => k.slice()),
    bound: s.bound.slice(), scores: s.scores.slice(),
    slots: s.slots.map(a => a.map(x => new Set(x))) };
}

// One possible world: the opponent's unseen cards (respecting exclusions) + the draw pile.
function sampleWorld(me) {
  const pool = shuffled(hiddenPool(me));
  const m = unknownCount(me);
  const order = G.slots[me].length === m
    ? G.slots[me].slice().sort((a, b) => b.size - a.size)
    : Array.from({ length: m }, () => new Set());
  const unknown = [];
  for (const ex of order) {
    if (!pool.length) break;
    let k = pool.findIndex(c => !ex.has(rankOf(c)));
    if (k < 0) k = 0;
    unknown.push(pool.splice(k, 1)[0]);
  }
  const oppTotal = handTotal(G.known[me]) + unknown.reduce((s, c) => s + valueOf(c, G.jokerRank), 0);
  return { unknown, deck: pool, oppTotal };
}

// Points (mine, theirs) if I show now against a hand totalling ot.
function showOutcome(t, ot) {
  if (t === 0 && ot === 0) return { mine: 0, theirs: 0 };
  return t < ot ? { mine: 0, theirs: ot } : { mine: PENALTY, theirs: 0 };
}

function rolloutTurn(me) {
  const opp = 1 - me;
  G.turnsInRound++;
  if (G.hands[me].length === 0) return endRound(me);
  if (G.forceShow || G.turnsInRound > STALL_TURNS) {
    if (G.forceShow || handTotal(G.hands[me]) <= handTotal(G.hands[opp])) return endRound(me);
    G.forceShow = true; G.turn = opp; return null;
  }
  if (me === ROLLOUT_OPP) {
    // The human seat inside a rollout shows with its learned per-total probability.
    const t = handTotal(G.hands[me]);
    if (UPGRADE.on) {
      if (t <= SHOW_MAX && Math.random() < humanShowProb(t)) return endRound(me);
    } else {
      const lim = oppShowLimit();                     // legacy model, kept for A/B tests
      if (lim !== null ? t <= Math.min(SHOW_MAX, lim) : challengerShowCheck(me).shows) return endRound(me);
    }
  } else if (challengerShowCheck(me).shows) return endRound(me);
  const d = challengerChooseDrop(me);
  const a = dropGroup(me, d.cards);
  if (!a.noPick) rolloutPick(me, a);
  G.turn = opp;
  return null;
}

// Play one candidate move in one sampled world to the end of the round.
// Returns both players' round points.
function rollout(me, plan, w) {
  const real = G, opp = 1 - me;
  G = cloneState(real);
  ROLLOUT_OPP = opp;
  try {
    G.hands[opp] = G.known[me].concat(w.unknown);
    G.deck = w.deck.slice();
    const a = dropGroup(me, plan.drop.cards);
    if (!a.noPick) applyPick(me, a, plan.take);
    G.turn = opp;
    let r = null, shower = -1, guard = 0;
    while (!G.roundOver && guard++ < 60) {
      const who = G.turn, x = rolloutTurn(who);
      if (x) { r = x; shower = who; }
    }
    if (r) return shower === me ? { mine: r.showerPts, theirs: r.otherPts }
                                : { mine: r.otherPts, theirs: r.showerPts };
    // Unfinished rollout: assume the lower hand shows correctly, so the result is in
    // real round POINTS (same scale as a finished round), not raw hand totals.
    const mt = handTotal(G.hands[me]), ot = handTotal(G.hands[opp]);
    if (mt < ot) return { mine: 0, theirs: ot };
    if (ot < mt) return { mine: mt, theirs: 0 };
    return { mine: 0, theirs: 0 };
  } finally { G = real; ROLLOUT_OPP = -1; }
}

async function mcDecide(me) {
  const opp = 1 - me;
  const t = handTotal(G.hands[me]);
  const top = G.topOpen;
  const sMe = G.scores[me], sOpp = G.scores[opp];
  ROLLOUT_THR = opponentPickupThreshold();     // once per decision, not once per rollout turn
  try {
    const drops = challengerRankDrops(me).slice(0, MC.topDrops);
    const plans = [];
    for (const d of drops) {
      plans.push({ drop: d, take: false });
      if (top && d.rank !== rankOf(top)) plans.push({ drop: d, take: true });
    }
    // Default move = what the heuristic would do.
    const wantTake = !!top && drops[0].rank !== rankOf(top) && challengerTakesOpen(me, top);
    let base = plans.findIndex(p => p.drop === drops[0] && p.take === wantTake);
    if (base < 0) base = 0;

    const U = plans.map(() => []);     // match win chance per sampled world, per plan
    const S = [];                      // same, for "show now"
    let n = 0;
    const t0 = performance.now();
    while (n < MC.max && (n < MC.min || performance.now() - t0 < MC.ms)) {
      const w = sampleWorld(me);
      if (t <= SHOW_MAX) {
        const o = showOutcome(t, w.oppTotal);
        S.push(matchWinProb(sMe + o.mine, sOpp + o.theirs));
      }
      plans.forEach((p, i) => {
        const o = rollout(me, p, w);
        U[i].push(matchWinProb(sMe + o.mine, sOpp + o.theirs));
      });
      n++;
      // When showing is available, keep sampling because show-vs-move is another
      // decision. Otherwise stop early only on a strong paired-confidence signal.
      if (t > SHOW_MAX && n % 24 === 0 && mcConfidentEnough(U, base, n)) break;
      if (n % 6 === 0) await new Promise(r => setTimeout(r, 0));  // keep the UI alive
    }

    const means = U.map(mean);
    let bi = 0;
    means.forEach((m, i) => { if (m > means[bi]) bi = i; });
    let switched = false;
    if (bi !== base) {
      const ps = pairedStats(U[bi], U[base]);
      if (ps.diff >= MC.minGain && ps.z >= MC.switchZ) switched = true; else bi = base;
    }

    let show = false, showEV = -Infinity;
    if (t <= SHOW_MAX && S.length) {
      showEV = mean(S);
      const ps = pairedStats(S, U[bi]);
      show = ps.diff > 0 && ps.z >= MC.showZ;
    }

    if (MC.debug) {
      console.log(`[bot] n=${n} total=${t} score ${sMe}:${sOpp} show=${(100 * showEV).toFixed(2)}%`);
      console.table(plans.map((p, i) => ({
        drop: p.drop.rank, take: p.take, heur: p.drop.challengerScore.toFixed(2),
        winPct: (100 * means[i]).toFixed(2),
        zVsDefault: i === base ? "-" : pairedStats(U[i], U[base]).z.toFixed(2),
        default: i === base, chosen: i === bi && !show,
      })));
    }
    return { show, t, drop: plans[bi].drop, take: plans[bi].take, n, showEV,
             bestEV: means[bi], switched, winChance: show ? showEV : means[bi] };
  } finally { ROLLOUT_THR = null; }
}

async function mcTurnCore(me) {          // headless version for simulation
  const opp = 1 - me;
  G.turnsInRound++;
  if (G.hands[me].length === 0) return endRound(me);
  if (G.forceShow || G.turnsInRound > STALL_TURNS) {
    if (G.forceShow || handTotal(G.hands[me]) <= handTotal(G.hands[opp])) return endRound(me);
    G.forceShow = true; G.turn = opp; return null;
  }
  const plan = await mcDecide(me);
  if (plan.show) return endRound(me);
  const a = dropGroup(me, plan.drop.cards);
  if (!a.noPick) applyPick(me, a, plan.take);
  G.turn = opp;
  return null;
}

// ---- Exact percentages for simulations ---------------------------------------
// A win rate over 100 games can only be whole numbers, so use 1000+ games.
function wilson(x, n, z = 1.96) {            // returns [low, high] in percent
  if (!n) return [0, 0];
  const p = x / n, d = 1 + z * z / n;
  const c = (p + z * z / (2 * n)) / d;
  const h = z * Math.sqrt(p * (1 - p) / n + z * z / (4 * n * n)) / d;
  return [100 * (c - h), 100 * (c + h)];
}
function pctLine(name, x, n) {
  const [lo, hi] = wilson(x, n);
  return `${name}: ${(100 * x / n).toFixed(2)}% (95% CI ${lo.toFixed(2)}-${hi.toFixed(2)}%)`;
}

// MC bot (player 1) vs challenger heuristic (player 0). Use from the console: await runSimMC(1000)
async function runSimMC(games) {
  const saved = { ...MC }; MC.ms = 60; MC.min = 24;
  const wins = [0, 0]; let ties = 0, lead = 0;
  for (let g = 0; g < games; g++) {
    G = newState();
    while (!G.gameOver) {
      dealCore();
      while (!G.roundOver) { if (G.turn === 0) rolloutTurn(0); else await mcTurnCore(1); }
    }
    lead += G.scores[0] - G.scores[1];          // > 0 means the MC bot finished with fewer points
    if (G.scores[0] < G.scores[1]) wins[0]++; else if (G.scores[1] < G.scores[0]) wins[1]++; else ties++;
  }
  Object.assign(MC, saved);
  return { games, challenger: wins[0], mc: wins[1], ties, avgPointLead: lead / games,
           report: [pctLine("Challenger", wins[0], games), pctLine("MC bot", wins[1], games),
                    pctLine("Ties", ties, games)].join(" | ") + ` | MC avg point lead ${(lead / games).toFixed(2)}` };
}

// ---- Stub-human test: MC bot vs a human with a FIXED show habit ---------------
// Console: await compareUpgrade(300, 3)   // human shows whenever total <= 3
// Runs the stub twice (legacy show model, then the new one) and prints both win rates.
function stubHumanTurn(showAt) {
  G.turnsInRound++;
  if (G.hands[0].length === 0) return endRound(0);
  if (G.forceShow || G.turnsInRound > STALL_TURNS) {
    if (G.forceShow || handTotal(G.hands[0]) <= handTotal(G.hands[1])) return endRound(0);
    G.forceShow = true; G.turn = 1; return null;
  }
  const t = handTotal(G.hands[0]);
  if (t <= SHOW_MAX) {
    const show = t <= showAt;
    OPP_MODEL.showChoices.push({ t, show });
    if (show) OPP_MODEL.shows.push(t);
    if (show) return endRound(0);
  }
  const d = challengerChooseDrop(0);
  const a = dropGroup(0, d.cards);
  if (!a.noPick) {
    const take = challengerTakesOpen(0, a.prevOpen) && a.canTake;
    recordHumanPickup(take, a.prevOpen);
    applyPick(0, a, take);
  }
  G.turn = 1;
  return null;
}
async function simVsStub(games, showAt) {
  const saved = { ...MC }, keepFull = ASSUME_FULL_DROPS;
  const keepModel = { sc: OPP_MODEL.showChoices, sh: OPP_MODEL.shows, pk: OPP_MODEL.pickup };
  MC.ms = 60; MC.min = 24; MC.max = 120;
  ASSUME_FULL_DROPS = true;
  OPP_MODEL.showChoices = []; OPP_MODEL.shows = []; OPP_MODEL.pickup = [];
  let botWins = 0, humanWins = 0, ties = 0;
  try {
    for (let g = 0; g < games; g++) {
      G = newState();
      while (!G.gameOver) {
        dealCore();
        let guard = 0;
        while (!G.roundOver && guard++ < 400) {
          if (G.turn === 0) stubHumanTurn(showAt); else await mcTurnCore(1);
        }
      }
      if (G.scores[1] < G.scores[0]) botWins++;
      else if (G.scores[0] < G.scores[1]) humanWins++;
      else ties++;
    }
  } finally {
    Object.assign(MC, saved);
    ASSUME_FULL_DROPS = keepFull;
    OPP_MODEL.showChoices = keepModel.sc; OPP_MODEL.shows = keepModel.sh; OPP_MODEL.pickup = keepModel.pk;
  }
  return { botWins, humanWins, ties, line: pctLine("MC bot", botWins, games) };
}
async function compareUpgrade(games = 300, showAt = 3) {
  UPGRADE.on = false; const oldR = await simVsStub(games, showAt);
  UPGRADE.on = true;  const newR = await simVsStub(games, showAt);
  console.log("LEGACY show model:", oldR.line);
  console.log("NEW show model:   ", newR.line);
  return { legacy: oldR, current: newR };
}
// ============================================================================

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
  const c = drawInto(me);
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
  return { games, wins, ties, avgRounds: rounds / games,
           report: [pctLine("P0", wins[0], games), pctLine("P1", wins[1], games),
                    pctLine("Ties", ties, games)].join(" | ") };
}

// ==== Self-improvement: self-play tuning ======================================
// The bot's heuristic (used directly AND inside every Monte Carlo rollout) has ~11 numeric
// knobs. trainBot() plays thousands of headless games: a mutated copy of the settings
// against the current champion, seats swapped every game. A mutant that beats the champion
// by a clear margin (sign-test z >= 1.3) becomes the new champion. At the end the result
// is re-checked against the ORIGINAL settings and only kept if it really is better,
// then saved in localStorage so the bot stays smarter next time you open the game.
const TUNE = {                       // [min, max] for every knob that may change
  pickMargin: [0, 8], groupBonus: [0, 4], noPickBonus: [0, 8], zeroGroupBonus: [0, 4],
  setupW: [0, 1.5], setupThresholdBonus: [0, 3], leakW: [0, 3], oppRisk: [0, 12],
  showMargin: [5, 60], safeShowPenProb: [0, 0.05], leakSoft: [0.5, 3],
};
const TRAIN = { running: false, stop: false, batch: 40, maxBatches: 6, acceptZ: 1.3 };
const CFG_KEY = "lc_cfg_v2";         // new key: older saved settings used the old, narrower ranges

// Tuned in 4000 headless games against the original settings: 73.35% win rate (95% CI 71.98-74.72%).
// NOTE: these values were tuned with SHOW_MAX = 6. For the new limit of 10, retrain with ?train=10
// and paste the output of exportCfg() here.
// Applied every time the game loads, on any browser or device.
// To go back to the original bot, set this to {} (and call resetBot() in the console).
const TRAINED_CFG = {
  "pickMargin": 3.8433,
  "groupBonus": 0.3808,
  "noPickBonus": 4.0176,
  "zeroGroupBonus": 1.1437,
  "setupW": 0.2225,
  "setupThresholdBonus": 0.2681,
  "leakW": 0.4644,
  "oppRisk": 3.1798,
  "showMargin": 41.4775,
  "safeShowPenProb": 0.0112,
  "leakSoft": 1.3922
};

function setCfg(c) {
  for (const k in TUNE) {
    if (typeof c[k] === "number" && isFinite(c[k])) CHALLENGER_CFG[k] = Math.min(TUNE[k][1], Math.max(TUNE[k][0], c[k]));
  }
}
function tunableCopy() { const o = {}; for (const k in TUNE) o[k] = CHALLENGER_CFG[k]; return o; }
function randn() {
  let u = 0, v = 0;
  while (!u) u = Math.random();
  while (!v) v = Math.random();
  return Math.sqrt(-2 * Math.log(u)) * Math.cos(2 * Math.PI * v);
}
function mutateCfg(c, scale) {
  const o = { ...c }, keys = Object.keys(TUNE);
  const bump = k => { const [lo, hi] = TUNE[k]; o[k] = Math.min(hi, Math.max(lo, o[k] + randn() * scale * (hi - lo))); };
  let changed = 0;
  for (const k of keys) if (Math.random() < 0.4) { bump(k); changed++; }
  if (!changed) bump(keys[Math.floor(Math.random() * keys.length)]);
  return o;
}
const zOf = (w, l) => (w - l) / Math.sqrt(Math.max(1, w + l));

// One headless game between two settings. cfgs[seat] is used by that seat. Returns final scores.
function playTrainGame(cfgs) {
  const savedG = G, keep = tunableCopy(), keepFull = ASSUME_FULL_DROPS;
  G = newState();
  ASSUME_FULL_DROPS = true;           // both sides always drop whole groups here
  try {
    while (!G.gameOver) {
      dealCore();
      let guard = 0;
      while (!G.roundOver && guard++ < 400) { const who = G.turn; setCfg(cfgs[who]); rolloutTurn(who); }
      if (!G.roundOver) break;        // safety net, should never happen
    }
    return G.scores.slice();
  } finally { setCfg(keep); ASSUME_FULL_DROPS = keepFull; G = savedG; }
}

// n games of a vs b, a sitting in alternating seats. Yields to the UI regularly.
async function playMatches(a, b, n, first = 0, respectStop = true) {
  let w = 0, l = 0, t = 0;
  for (let i = 0; i < n; i++) {
    if (respectStop && TRAIN.stop) break;
    const aSeat = (first + i) % 2;
    const sc = playTrainGame(aSeat === 0 ? [a, b] : [b, a]);
    const sa = sc[aSeat], sb = sc[1 - aSeat];
    if (sa < sb) w++; else if (sa > sb) l++; else t++;
    if (i % 5 === 4) await new Promise(r => setTimeout(r, 0));
  }
  return { w, l, t, n: w + l + t };
}

function trainSay(msg) {
  TRAIN.status = msg;
  const el = typeof document !== "undefined" ? document.getElementById("trainMsg") : null;
  if (el) el.textContent = msg;
}
function saveCfg(meta) {
  try { localStorage.setItem(CFG_KEY, JSON.stringify({ cfg: tunableCopy(), ...meta })); } catch (e) { /* storage unavailable */ }
}
function loadSavedCfg() {
  try {
    const raw = localStorage.getItem(CFG_KEY);
    if (!raw) return null;
    const o = JSON.parse(raw);
    if (o && o.cfg) { setCfg(o.cfg); return o; }
  } catch (e) { /* ignore */ }
  return null;
}
// Prints a ready-to-paste line with the current settings.
function exportCfg() {
  const o = {};
  for (const k in TUNE) o[k] = Math.round(CHALLENGER_CFG[k] * 10000) / 10000;
  const text = "const TRAINED_CFG = " + JSON.stringify(o, null, 2) + ";";
  console.log(text);
  return text;
}
function resetBot() {
  setCfg(DEFAULT_CFG);
  try { localStorage.removeItem(CFG_KEY); } catch (e) { /* ignore */ }
  trainSay("Bot reset to the original settings.");
}
// Current settings vs the original ones, with exact percentages: await benchmarkBot(1000)
async function benchmarkBot(games = 1000) {
  const r = await playMatches(tunableCopy(), DEFAULT_CFG, games, 0, false);
  return { ...r, report: [pctLine("Current", r.w, r.n), pctLine("Original", r.l, r.n), pctLine("Ties", r.t, r.n)].join(" | ") };
}

// Runs until you stop it (minutes = Infinity) or the time is up. Progress is checked against
// the original settings and saved every 5 minutes, and once more when you stop.
async function trainBot(minutes = Infinity) {
  if (TRAIN.running) return null;
  TRAIN.running = true; TRAIN.stop = false;
  const t0 = performance.now(), limit = minutes * 60000;
  const start = tunableCopy();
  let champ = { ...start }, scale = 0.15, tried = 0, accepted = 0, ckAccepted = 0, lastCk = t0;
  let saved = null;
  const validateAndSave = async () => {
    trainSay("Checking the result against the original…");
    const v = await playMatches(champ, start, 400, 0, false);
    if (v.w > v.l && zOf(v.w, v.l) >= 1.0) {
      setCfg(champ);
      saveCfg({ trainedAt: Date.now(), tried, accepted, winVsStart: v.w / Math.max(1, v.n) });
      saved = v;
    }
    return v;
  };
  trainSay("Training… warming up");
  try {
    while (!TRAIN.stop && performance.now() - t0 < limit) {
      const cand = mutateCfg(champ, scale);
      let w = 0, l = 0, t = 0, n = 0, z = 0, early = 0;
      for (let b = 0; b < TRAIN.maxBatches && !TRAIN.stop; b++) {
        const r = await playMatches(cand, champ, TRAIN.batch, n);
        w += r.w; l += r.l; t += r.t; n += r.n;
        z = zOf(w, l);
        if (z < -1.5) { early = -1; break; }      // clearly worse: stop wasting games
        if (z >= 2.2) { early = 1; break; }       // clearly better
      }
      if (TRAIN.stop) break;
      tried++;
      if (early >= 0 && z >= TRAIN.acceptZ && w > l) { champ = cand; accepted++; scale = Math.min(0.4, scale * 1.25); }
      else scale = Math.max(0.03, scale * 0.96);
      const secs = Math.round((performance.now() - t0) / 1000);
      trainSay(`Training… ${tried} tried, ${accepted} improvements, ${Math.floor(secs / 60)}m ${secs % 60}s` +
               (saved ? ` | last save: beat the original in ${(100 * saved.w / saved.n).toFixed(2)}% of games` : ""));
      // Checkpoint so closing the tab never loses the progress.
      if (accepted > ckAccepted && performance.now() - lastCk > 300000) {
        await validateAndSave();
        ckAccepted = accepted; lastCk = performance.now();
      }
    }

    // Final check when you stop (or the time is up).
    if (accepted > ckAccepted || (accepted > 0 && !saved)) await validateAndSave();
    const result = { saved: !!saved, tried, accepted, validation: saved };
    trainSay(saved
      ? `Trained AI saved. ${pctLine("Beats the original settings", saved.w, saved.n)}`
      : "Stopped. No clear improvement yet; kept the previous settings.");
    console.log("trainBot", result, tunableCopy());
    return result;
  } finally { TRAIN.running = false; }
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
let SHOWSTAT = { you: { n: 0, right: 0 }, bot: { n: 0, right: 0 } };  // right/total shows per side
let muted = false;
let humanFlying = false;   // a card is flying into your hand: hand order is locked
let suppressClick = false;
let drag = null;
let rulesInGame = false;   // true when the rules were opened from the header during a game
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

// ---- Score table and bars ----------------------------------------------------
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

  const bars = [["barYou", "barYouN", 0], ["barBot", "barBotN", 1]];
  for (const [barId, numId, p] of bars) {
    const pct = Math.min(100, 100 * G.scores[p] / LIMIT);
    $(barId).style.width = pct + "%";
    $(barId).classList.toggle("danger", pct >= 75);
    $(numId).textContent = G.scores[p];
  }
}

// ---- Rendering --------------------------------------------------------------
function renderInfo() {
  const shownRound = (phase === "over") ? G.round - 1 : G.round;
  const jr = G.jokerRank ? rankLabel(G.jokerRank) : "-";
  $("info").innerHTML =
    `<span class="chip">Round ${Math.max(1, shownRound)}</span>` +
    `<span class="chip joker" title="Cards of this rank are worth 0 this round">Joker rank <b>${jr}</b></span>` +
    `<span class="chip">You <b>${G.scores[0]}</b> : Bot <b>${G.scores[1]}</b></span>` +
    `<span class="chip dim" title="Rough estimate from the score only">Bot win chance ~${(100 * matchWinProb(G.scores[1], G.scores[0])).toFixed(2)}%</span>` +
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
  document.body.dataset.phase = phase;      // drives the "whose turn" highlight in the CSS
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
  await sleep(300);
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

  // 1. Monte Carlo decision: show now, or which drop and pick.
  const plan = await mcDecide(1);
  if (plan.show) {
    log(`Bot shows with ${plan.t}.`);
    finishRoundUI(1);
    return;
  }

  // 2. Drop: the cards fly from the bot's row to the open pile.
  const drop = plan.drop;
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
    const p = applyPick(1, a, plan.take);
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
  // Exact chance (from the shower's own information) that this show is right.
  const showT = handTotal(G.hands[showerIdx]);
  const conf = estimateOpponent(showerIdx, showT);
  const confPct = 100 * conf.P;
  if (showerIdx === 0) OPP_MODEL.shows.push(showT);    // legacy log of your show totals
  const r = endRound(showerIdx);
  const key = showerIdx === 0 ? "you" : "bot";
  SHOWSTAT[key].n++; if (r.right) SHOWSTAT[key].right++;
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
  log(`Show confidence before the reveal: ${confPct.toFixed(2)}% (exact).`);
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
    const sp = k => SHOWSTAT[k].n ? (100 * SHOWSTAT[k].right / SHOWSTAT[k].n).toFixed(2) + "%" : "n/a";
    showOver(tie ? "Tie game" : youWin ? "You win!" : "The bot wins",
             `Final scores: you ${G.scores[0]}, bot ${G.scores[1]}. ` +
             `Right shows: you ${sp("you")} (${SHOWSTAT.you.right}/${SHOWSTAT.you.n}), ` +
             `bot ${sp("bot")} (${SHOWSTAT.bot.right}/${SHOWSTAT.bot.n}).`);
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
  recordHumanPickup(true, lastAction.prevOpen);
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
  recordHumanPickup(false, lastAction && lastAction.prevOpen);
  if (G.deck.length === 0 && G.openPile.length > 1) { log("The draw pile is empty: reshuffling."); SFX.shuffle(); }
  pendingTake = null;
  const c = drawInto(0);
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
  recordShowChoice(t, true);          // the bot learns: you showed at this total
  log(`You show with ${t}.`);
  finishRoundUI(0);
}
function onContinue() {
  if (phase !== "showfirst" || busy) return;
  recordShowChoice(handTotal(G.hands[0]), false);   // ...and when you chose NOT to show
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

// ---- Rules walkthrough (shown before the game, reopenable from the header) ----
document.querySelectorAll("[data-showmax]").forEach(e => e.textContent = SHOW_MAX);
document.querySelectorAll("[data-penalty]").forEach(e => e.textContent = PENALTY);
document.querySelectorAll("[data-limit]").forEach(e => e.textContent = LIMIT);

const RULE_PAGES = [...document.querySelectorAll(".rule-page")];
let rulePage = 0;

function showRulePage(n) {
  rulePage = Math.max(0, Math.min(RULE_PAGES.length - 1, n));
  RULE_PAGES.forEach((p, i) => { p.hidden = i !== rulePage; });
  document.querySelectorAll("#rulePager i").forEach((d, i) => d.classList.toggle("on", i === rulePage));
  const last = rulePage === RULE_PAGES.length - 1;
  $("rulePrev").disabled = rulePage === 0;
  $("ruleNext").hidden = last;
  $("startBtn").hidden = !(last && !rulesInGame);
  $("ruleResume").hidden = !(last && rulesInGame);
  $("ruleX").hidden = !rulesInGame;
  $("ruleSkip").hidden = last || rulesInGame;
}
function openRules(inGame) {
  rulesInGame = inGame;
  showRulePage(inGame ? rulePage : 0);
  $("start").classList.remove("hidden");
}
function closeRules() { $("start").classList.add("hidden"); }

$("rulePrev").addEventListener("click", () => showRulePage(rulePage - 1));
$("ruleNext").addEventListener("click", () => showRulePage(rulePage + 1));
$("ruleSkip").addEventListener("click", () => showRulePage(RULE_PAGES.length - 1));
$("ruleResume").addEventListener("click", closeRules);
$("ruleX").addEventListener("click", closeRules);
$("rulesBtn").addEventListener("click", () => openRules(true));
document.addEventListener("keydown", e => {
  if ($("start").classList.contains("hidden")) return;
  if (e.key === "Escape" && rulesInGame) closeRules();
  if (e.key === "ArrowRight") showRulePage(rulePage + 1);
  if (e.key === "ArrowLeft") showRulePage(rulePage - 1);
});
showRulePage(0);

// ---- Start, buttons, URL modes ----------------------------------------------
function startGame() {
  rulesInGame = false;
  ctx();
  TRAIN.stop = true;               // never train while you play
  $("start").classList.add("hidden");
  $("over").classList.add("hidden");
  G = newState();
  SHOWSTAT = { you: { n: 0, right: 0 }, bot: { n: 0, right: 0 } };
  OPP_MODEL.shows = [];            // showChoices and pickup are kept: the bot keeps learning you
  ASSUME_FULL_DROPS = false;       // you may drop just one card of a pair
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

setCfg(TRAINED_CFG);                 // settings pasted into the file
loadSavedCfg();                      // previously trained settings, if any
loadOppModel();                      // what the bot already learned about you
const params = new URLSearchParams(location.search);
if (params.has("sim")) {
  const r = runSim(parseInt(params.get("sim"), 10) || 1000);
  console.log("Simulation", r);
  $("start").classList.add("hidden");
  log(`Simulation: ${r.games} games | ${r.report} | avg rounds ${r.avgRounds.toFixed(2)}`);
}
if (params.has("mcsim")) {
  $("start").classList.add("hidden");
  log("Running Monte Carlo simulation…");
  runSimMC(parseInt(params.get("mcsim"), 10) || 50).then(r => {
    console.log("MC simulation", r);
    log("MC simulation: " + r.report);
  });
}
if (params.has("upsim")) {           // ?upsim=300 compares legacy vs new show model (stub human shows at <=3)
  $("start").classList.add("hidden");
  log("Running upgrade comparison…");
  compareUpgrade(parseInt(params.get("upsim"), 10) || 300, parseInt(params.get("showAt"), 10) || 3).then(r => {
    console.log("Upgrade comparison", r);
    log("Legacy: " + r.legacy.line + " | New: " + r.current.line);
  });
}
if (params.has("train")) {           // ?train trains until stopped; ?train=5 trains for 5 minutes
  trainBot(parseFloat(params.get("train")) || Infinity);
}
if (params.has("bench")) {           // ?bench=1000 compares current vs original settings
  benchmarkBot(parseInt(params.get("bench"), 10) || 1000).then(r => { console.log("Benchmark", r); log("Benchmark: " + r.report); });
}
if (params.has("test")) {
  const r = selfTest();
  console.log("Probability self-test", r);
  $("start").classList.add("hidden");
  log(`Probability self-test: ${r.checked} states, worst error ${r.worst.toExponential(2)}`);
}

renderAll();
setButtons();

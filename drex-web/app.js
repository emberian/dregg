// app.js — DrEX web app. Drives the sealed order end-to-end:
//   confirm-intent approve → REAL sign + REAL prove (wallet wasm) →
//   sealed commit/reveal → REAL matcher (POST /clear → solver.rs +
//   verified_settle.rs) → fill + graded fairness panel.
//
// BOTH sides are real: the wallet proving is the extension wasm (unchanged), and
// the matcher/settlement is the actual Rust pipeline — serve.mjs shells to the
// `drex_clear` binary (exec-lean/src/bin/drex_clear.rs), the same solver.rs ring
// match + verified_settle.rs kernel fold as `cargo run --example drex_clear_book`.
import {
  initWallet, traderKey, signOrderTurn, proveSolvency, tamperCheck,
  proveEligibility, sealedCommit, sealedReveal, randHex, hex,
} from './drex-wallet.mjs';
import { demoBook, fairnessLedger } from './drex-clearside.js';
import { html, setHtml } from './html.mjs';

const $ = (id) => document.getElementById(id);
const book = demoBook();
let walletReady = false;

// ── render the sealed order book (left rail) ──
function renderBook(reveal = false) {
  setHtml($('book'), html`${book.map((o, i) => {
    const mine = o.trader === 'Ada';
    const body = reveal
      ? html`<span class="m">offers ${o.offerAmount} ${o.offerAsset} · wants ≥ ${o.wantMin} ${o.wantAsset}</span>`
      : html`<span class="m">committed · <span class="mono fade">H(order‖salt)</span></span>`;
    return html`<div class="card ord ${mine ? 'mine' : ''}">
      <span class="t">${o.trader}${mine ? ' · you' : ''}</span>
      <span class="sealed">${reveal ? 'revealed' : 'sealed'}</span>
      ${body}
      <span class="m">priority ${o.priority}</span>
    </div>`;
  })}`);
}

// ── flow log (center) ──
const steps = [];
function step(id, h, opts = {}) {
  let s = steps.find(x => x.id === id);
  if (!s) { s = { id }; steps.push(s); }
  Object.assign(s, { h, ...opts });
  drawFlow();
  return s;
}
function drawFlow() {
  setHtml($('flow'), html`${steps.map(s => {
    const badge = s.badge ? html`<span class="real">${s.badge}</span>`
      : s.real ? html`<span class="real">REAL wasm</span>` : '';
    return html`<div class="step ${s.state || ''}">
      <div class="h">${s.h}${badge}</div>
      ${s.d ? html`<div class="d">${s.d}</div>` : ''}
    </div>`;
  })}`);
}

// ── the stepper (Seal → Clear → Settle) — the strong single-phase shape ──
// Purely presentational: highlights where the sealed-bid mechanic currently is,
// so the flow is obvious. No "Reveal" headline node — the strong DrEX is
// single-phase (seal → clears at one price → proven); the demo's commit-reveal
// is folded into Clear as an honest floor-detail. 3 nodes: 0 Seal, 1 Clear,
// 2 Settle. Nodes before `activeIdx` read done; `activeIdx` reads active (or
// done when opts.complete). opts.failIdx marks a stalled step.
function setStepper(activeIdx, opts = {}) {
  document.querySelectorAll('.step-node').forEach((n, i) => {
    n.classList.remove('active', 'done', 'fail');
    n.removeAttribute('aria-current');
    if (opts.failIdx === i) n.classList.add('fail');
    else if (i < activeIdx) n.classList.add('done');
    else if (i === activeIdx) { n.classList.add(opts.complete ? 'done' : 'active'); if (!opts.complete) n.setAttribute('aria-current', 'step'); }
  });
}

// ── the proof celebration ("Settled · PROVEN") ──
// Shown only when the live node actually attached a proof to the settlement
// turn (a full-turn STARK proof, or a prove_pool witnessed receipt with
// has_proof). The turn hash is copyable; the microcopy points at re-checking it
// on the node — the guarantee comes from the math, not from us.
function renderProofBadge(r) {
  const el = $('proofBadge');
  if (!el) return;
  const proof = r.proof || {}, rc = r.receipt || {};
  const policy = rc.proofStatus || rc.proof_status || proof.proof_status;
  if (policy === 'not_required' && !proof.present && !rc.hasProof) {
    el.textContent = 'Coordination turn · signature attestation only · no validity proof';
    el.classList.add('show');
    return;
  }
  const proven = !!(proof.present || (rc && rc.hasProof));
  if (!proven) { el.classList.remove('show'); el.textContent = ''; return; }
  const h = r.turnHash || '';
  const proofDesc = proof.mode === 'stark_full_turn'
    ? `full-turn STARK proof · ${proof.len} bytes`
    : proof.mode === 'witnessed_receipt'
      ? `witnessed receipt · prove_pool (witness count ${proof.witnessCount || rc.witnessCount || 1})`
      : 'attached by the node prove_pool';
  setHtml(el, html`
    <div class="proof-card">
      <div class="crest">
        <div class="seal" aria-hidden="true">✓</div>
        <div class="titles">
          <h2>Settled&nbsp;·&nbsp;<span class="badge-proven">proven</span></h2>
          <p class="say">This batch cleared as one real turn on the live node — and math itself signed the receipt.</p>
        </div>
      </div>
      <div class="rows">
        <div class="pr"><span class="k">Turn hash</span><span class="v hash mono">${h}<button class="copybtn" id="copyHash" type="button" aria-label="Copy turn hash">copy</button></span></div>
        <div class="pr"><span class="k">Proof</span><span class="v">has_proof: <span class="ok">true</span> · ${proofDesc}</span></div>
        <div class="pr"><span class="k">Finality</span><span class="v">${rc.finality || '—'} · ${rc.computronsUsed ?? '—'} computrons · ${rc.actionCount ?? '—'} action(s) committed</span></div>
        <div class="pr"><span class="k">Ledger</span><span class="v mono">${(rc.preState || '').slice(0, 14)}… → ${(rc.postState || '').slice(0, 14)}…</span></div>
        <div class="pr"><span class="k">Node</span><span class="v">${r.node || ''} · operator ${(r.operator || '').slice(0, 14)}…</span></div>
      </div>
      <p class="recheck">Don't take our word for it — <b>anyone can re-run this check.</b> The proof is fetchable from the node at <span class="mono">/api/turn/${h.slice(0, 10)}…/proof</span> and re-verifies against the committed turn. The guarantee comes from the math, not from us.</p>
    </div>`);
  el.classList.add('show');
  const cb = $('copyHash');
  if (cb) cb.onclick = () => {
    try { navigator.clipboard && navigator.clipboard.writeText(h); } catch (_e) {}
    cb.textContent = 'copied ✓'; setTimeout(() => { cb.textContent = 'copy'; }, 1400);
  };
}

// ── the reused confirm-intent modal ──
function currentOrder() {
  return {
    v: 1,
    sell: { asset: $('sellAsset').value, amount: +$('sellAmt').value },
    want: { asset: $('wantAsset').value, min: +$('wantMin').value },
    limitRate: $('limit').value,
    sealedUntilBatch: 'T+1',
    priority: 3,
  };
}
function openIntent(order) {
  const nonce = randHex().slice(0, 16);
  $('mSell').querySelector('.v').textContent = `${order.sell.amount} ${order.sell.asset}`;
  $('mWant').querySelector('.v').textContent = `≥ ${order.want.min} ${order.want.asset}`;
  $('mLimit').querySelector('.v').textContent = order.limitRate;
  $('mExpl').textContent =
    `[order drex_place_order]\n  place a SEALED bid on DrEX:\n  sell ${order.sell.amount} ${order.sell.asset}\n  want ≥ ${order.want.min} ${order.want.asset}  (limit ${order.limitRate})\n  hidden until batch T+1, then matched in the multilateral clearing.\n  the cipherclerk signs this exact order (nonce-bound) — nothing else.`;
  $('mNonce').textContent = 'nonce ' + nonce + ' · this approval is bound to exactly what is shown above';
  $('modal').classList.add('show');
  return new Promise((resolve) => {
    const done = (ok) => { $('modal').classList.remove('show'); $('acceptBtn').onclick = null; $('rejectBtn').onclick = null; resolve({ ok, nonce }); };
    $('acceptBtn').onclick = () => done(true);
    $('rejectBtn').onclick = () => done(false);
  });
}

// ── the full flow ──
async function place() {
  steps.length = 0; drawFlow();
  setStepper(0);
  const pb = $('proofBadge'); if (pb) { pb.classList.remove('show'); pb.textContent = ''; }
  $('placeBtn').disabled = true;
  const order = currentOrder();
  const holdings = +$('holdings').value;

  // confirm-intent approve (anti-blind-sign)
  step('confirm', 'Confirm intent — nonce-bound order card', { state: 'active', d: 'awaiting your approval in the cipherclerk popup…' });
  const { ok, nonce } = await openIntent(order);
  if (!ok) { step('confirm', 'Confirm intent — rejected', { state: 'fail', d: 'you declined; nothing signed.' }); $('placeBtn').disabled = false; return; }
  step('confirm', 'Confirm intent — approved', { state: 'done', d: 'nonce ' + nonce + ' bound to the displayed order' });

  const key = traderKey(1);

  // STEP 1 — sealed commit
  const salt = randHex();
  const commit = await sealedCommit(order, salt);
  step('commit', 'Sealed-bid commit', { state: 'done', d: 'H(order‖salt) = ' + commit.slice(0, 40) + '…  (order hidden until batch T)' });

  // STEP 2 — REAL sign order-turn
  step('sign', 'Sign the order-turn', { real: true, state: 'active', d: 'cipherclerk_make_action_turn …' });
  await tick();
  const signed = signOrderTurn(order, key);
  step('sign', 'Sign the order-turn', { real: true, state: 'done',
    d: `Ed25519-signed dregg Turn\n  turn_id: ${signed.turnId}\n  agent cell: ${signed.agentCell.slice(0,24)}…\n  hybrid PQ envelope: ${signed.envelopeLen} bytes (ed25519 + ML-DSA-65 / FIPS-204)` });

  // STEP 3 — REAL solvency proof
  step('solv', 'Prove solvency (offer covered, non-inflating)', { real: true, state: 'active', d: 'prove_conservation → Bulletproofs + Schnorr …' });
  await tick();
  const sol = proveSolvency(holdings, order.sell.amount, signed.turnId);
  if (!sol.ok) {
    step('solv', 'Prove solvency — FAIL-CLOSED', { real: true, state: 'fail', d: sol.reason || 'proof did not verify' });
    $('placeBtn').disabled = false; return;
  }
  step('solv', 'Prove solvency', { real: true, state: 'done',
    d: `holdings ${sol.holdings} = offer ${sol.offer} + change ${sol.change}  ⇒  offer covered, change ≥ 0\n  verify_conservation_proof → valid=${sol.valid}, range_proofs_checked=${sol.rangeProofsChecked}\n  ${sol.rangeProofs} Bulletproof range proofs · bound to order via message_hex=turn_id` });

  // STEP 3b — tamper check
  const forgedTurn = signOrderTurn({ ...order, want: { asset: 'ART', min: 1 } }, key).turnId;
  const tamper = tamperCheck(sol, forgedTurn);
  step('tamper', 'Tamper check — substituted order rejected', { real: true, state: tamper.valid ? 'fail' : 'done',
    d: `re-verify the SAME proof against a forged order id → valid=${tamper.valid}\n  ${tamper.error || ''}` });

  // STEP 4 — REAL eligibility
  step('elig', 'Prove trading eligibility (anonymous)', { real: true, state: 'active', d: 'prove_anonymous_membership …' });
  await tick();
  const ring = book.map((_, i) => hex(traderKey(i + 1)));
  const elig = proveEligibility(hex(key), ring);
  step('elig', 'Prove trading eligibility', { real: true, state: 'done',
    d: `blinded ring membership over ${elig.ringSize} eligible traders (identity hidden)\n  presentation tag (nullifier): ${elig.presentationTag.slice(0,40)}…` });

  // hold onto the order for reveal/clear
  window.__drexPending = { order, salt, commit, signed, sol, elig };
  setHtml($('clock'), html`<span class="ok">Your order is sealed and proven.</span> Clear the batch — every sealed order settles together at one fair price.`);
  $('batchPill').className = 'pill warn'; $('batchPill').textContent = 'batch T+1 · ready to clear';
  setStepper(1); // Seal done → Clear is next
  // add an advance button
  if (!$('advanceBtn')) {
    const b = document.createElement('button'); b.className = 'primary'; b.id = 'advanceBtn';
    b.textContent = 'Clear the batch at one price →'; b.onclick = clearBatch;
    $('placeBtn').after(b);
  }
  $('placeBtn').disabled = false;
}

// ── reveal + clear the batch through the REAL matcher (POST /clear) ──
async function clearBatch() {
  $('advanceBtn').disabled = true;
  const p = window.__drexPending;

  // Confirm the sealed order binds to its commitment before the batch clears.
  // FLOOR DETAIL — the current demo does a commit-reveal confirm here; the STRONG
  // single-phase DrEX (shielded_ring_clears) has NO reveal round. We keep the call
  // (mechanism unchanged) but present it honestly as a floor step, not a headline.
  const rev = await sealedReveal(p.commit, p.order, p.salt);
  step('reveal', 'Confirm sealed order — demo floor (single-phase has no reveal)', { state: rev.ok ? 'done' : 'fail',
    d: 'the current demo confirms your sealed order binds to its commitment before the batch clears — a simpler commit-reveal floor while the shielded single-phase circuit (shielded_ring_clears) finishes wiring in. commitment binds: ' + rev.ok });
  setStepper(1); // Clear active — the reveal above is folded into Clear, not a headline step

  // Fold the trader's REVEALED order into the book (Ada's leg), so the real
  // matcher clears the order the user actually placed — not a fixed fixture.
  const mineIdx = book.findIndex(o => o.trader === 'Ada');
  if (mineIdx >= 0) {
    book[mineIdx] = {
      ...book[mineIdx],
      offerAsset: p.order.sell.asset,
      offerAmount: p.order.sell.amount,
      wantAsset: p.order.want.asset,
      wantMin: p.order.want.min,
      priority: p.order.priority,
    };
  }
  renderBook(true);
  $('batchPill').className = 'pill live'; $('batchPill').textContent = 'batch T+1 · cleared';

  // ── the REAL matcher + verified settlement (serve.mjs → the drex_clear binary) ──
  step('match', 'Match — REAL solver.rs (Johnson circuits + Shapley–Scarf TTC)',
    { badge: 'REAL solver.rs', state: 'active',
      d: 'POST /clear → running the real ring matcher over the revealed orders…' });
  const orders = book.map(o => ({
    trader: o.trader, offerAsset: o.offerAsset, offerAmount: o.offerAmount,
    wantAsset: o.wantAsset, wantMin: o.wantMin, priority: o.priority,
  }));
  let res;
  try {
    res = await fetch('/clear', {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(orders),
    }).then(r => r.json());
  } catch (e) {
    step('match', 'Match — REAL solver unreachable', { badge: 'REAL solver.rs', state: 'fail',
      d: 'POST /clear failed: ' + e.message + ' — run the app via serve.mjs (it shells to the Rust matcher)' });
    setStepper(1, { failIdx: 1 });
    return;
  }

  if (res.error || !res.ring) {
    step('match', 'Match — no clearing ring', { badge: 'REAL solver.rs', state: 'fail',
      d: res.error || res.provenance || 'the real matcher found no ring over this book' });
    setStepper(1, { failIdx: 1 });
    if (res.allocations) renderClearedReal(res);
    return;
  }

  step('match', 'Match — REAL multilateral ring found', { badge: 'REAL solver.rs', state: 'done',
    d: `bilateral (2-party) matches: ${res.twoCycles} → genuinely multilateral\n`
     + `  ring: ${res.ring.participants.join(' → ')} → ${res.ring.participants[0]}\n  `
     + res.ring.legs.map(l => `${l.fromTrader}→${l.toTrader} ${l.amount} ${l.asset}`).join('  ·  ')
     + `\n  ${res.provenance}` });

  const rj = res.reject;
  step('settle', 'Settle — verified kernel fold (recKExecAsset), conserving, all-or-nothing',
    { badge: 'REAL verified_settle.rs', state: 'done',
      d: rj
        ? `allocations read off the verified post-ledger.\n  reject-polarity: ${rj.victim} drained one short → leg ${rj.refusedAt} REFUSED by the verified kernel; whole ring aborts (${rj.settledLegs} legs settled)`
        : 'each leg folded through the proved recKExecAsset kernel; conserves per asset.' });

  renderClearedReal(res);
  renderFairness();

  // ── land the cleared batch as ONE REAL turn on the live dregg node ──
  await settleOnLiveNode(res);
}

// Settle the cleared batch on a LIVE dregg node: the ring the solver found lands
// as a single real turn (POST /settle → node /turn/submit), executed on the
// effect-VM and proven by the node's prove_pool. The turn hash, the proof, the
// committed receipt, and the ledger state come back FROM the node.
async function settleOnLiveNode(cleared) {
  if (!cleared || !cleared.ring) return;
  setStepper(2); // Clear done → Settle active
  step('node', 'Settle on the LIVE node — real turn → effect-VM → prove_pool',
    { badge: 'REAL node', state: 'active',
      d: 'POST /settle → node /turn/submit: the clearing settles as one real turn…' });
  let r;
  try {
    r = await fetch('/settle', {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(cleared),
    }).then((x) => x.json());
  } catch (e) {
    step('node', 'Settle on the LIVE node — proxy error', { badge: 'REAL node', state: 'fail',
      d: 'POST /settle failed: ' + e.message });
    setStepper(2, { failIdx: 2 });
    return;
  }

  if (r.nodeUp === false) {
    // GENUINELY offline: the node did not answer /status. Only this is "offline" —
    // a reachable node that merely could not settle is handled below, never here.
    step('node', 'Settle on the LIVE node — no node reachable (local matcher only)',
      { badge: 'LOCAL fallback', state: 'fail',
        d: `no dregg node at ${r.node || 'the configured address'} (${r.error || 'unreachable'}).\n`
         + '  the clearing shown is the REAL verified solver, but it did NOT land on a node this run.\n'
         + '  start one:  dregg-node run --port 8420 --enable-faucet --prove-turns' });
    $('nodePill') && ($('nodePill').className = 'pill warn', $('nodePill').textContent = 'node: offline · local matcher');
    setStepper(2, { failIdx: 2 });
    return;
  }
  if (!r.accepted) {
    // Reachable node, settle did not land — name the STAGE and real cause. This is
    // NOT "offline" and NOT a finalized settlement; the verified clearing stands.
    step('node', `Settle on the LIVE node — not landed (${r.stage || 'settle'})`, { badge: 'REAL node', state: 'fail',
      d: `node ${r.node} is up but the settle did not land: ${r.error || 'unknown'}`
       + (r.faucetDisabled ? '\n  (this node runs without a faucet; fund the settle operator out of band, or use a --enable-faucet dev node)' : '') });
    setStepper(2, { failIdx: 2 });
    return;
  }

  const proof = r.proof || {};
  const rc = r.receipt || {};
  const proofLine = proof.present
    ? (proof.mode === 'stark_full_turn'
        ? `full-turn STARK proof: ${proof.len} bytes (GET /api/turn/${r.turnHash.slice(0, 12)}…/proof)`
        : `witnessed receipt attached by prove_pool (witness_count=${proof.witnessCount})`)
    : `proof: ${r.proofNote || 'pending'} (status=${r.proofStatus})`;
  const settle = r.settle || {};
  const perTrader = r.perTrader || [];
  const alloClause = perTrader.length
    ? `  per-trader allocations settled as REAL transfers (balances read back from the node):\n`
      + perTrader.map((t) =>
          `    ${t.trader} · cell ${(t.cell || '').slice(0, 12)}… · got ${t.settled}${t.scaled ? ` (of ${t.received}, scaled)` : ''} → balance ${t.balance}`
        ).join('\n')
      + (settle.scaled ? `\n  (settled at scale ${settle.scale} — devnet computron-budget envelope; true cleared amounts kept)` : '')
    : `  batch cleared no fills — one carrier turn committed`;
  step('node', 'Settle on the LIVE node — committed + proven', { badge: 'REAL node', state: 'done',
    d: `node ${r.node}  ·  operator cell ${r.operator.slice(0, 16)}…\n`
     + `  turn ${r.turnHash.slice(0, 24)}…  → executed on the effect-VM, finality=${rc.finality}\n`
     + `  ${rc.computronsUsed} computrons · ${rc.actionCount} action(s) committed · executor-signed=${rc.executorSigned}\n`
     + `  pre-state ${(rc.preState || '').slice(0, 16)}…  →  post-state ${(rc.postState || '').slice(0, 16)}…\n`
     + `  ${proofLine}\n`
     + alloClause });
  if ($('nodePill')) { $('nodePill').className = 'pill live'; $('nodePill').textContent = 'node: live · turn committed + proven'; }
  // celebrate the proof moment — the sealed-bid trade cleared and math signed the receipt.
  renderProofBadge(r);
  const provenNow = !!(proof.present || (rc && rc.hasProof));
  setStepper(2, { complete: provenNow });
  if (!provenNow) setStepper(2, { failIdx: 2 }); // committed-but-unattested: honest, not a celebration
  if ($('batchPill') && provenNow) { $('batchPill').className = 'pill live'; $('batchPill').textContent = 'batch T+1 · settled · proven'; }
}

// Render the REAL clearing (JSON from POST /clear → the drex_clear binary).
function renderClearedReal(res) {
  const color = { GOLD: '#f0c14b', ART: '#bc8cff', WINE: '#f85149', SILVER: '#8b949e', PEARL: '#58a6ff' };
  const allocs = res.allocations || [];
  const settled = allocs.filter(a => !a.rested).map(a => {
    const mine = a.trader === 'Ada';
    return html`<div class="alloc ${mine ? 'mine' : ''}">
      <span class="who">${a.trader}${mine ? ' · you' : ''}</span>
      <span class="leg">sent ${a.sent} ${a.sentAsset} · got ${a.received} ${a.recvAsset} (≥${a.wantMin})</span>
      <span class="${a.ir && a.budget ? 'ok' : 'no'}">${a.ir && a.budget ? '✔' : '✗'}</span>
    </div>`;
  });
  const rested = allocs.filter(a => a.rested).map(a =>
    html`<div class="alloc"><span class="who fade">${a.trader}</span><span class="leg fade">rests — no match this batch</span><span class="fade">·</span></div>`);
  // conservation bars (from the verified settle)
  const conservation = res.conservation && res.conservation.length
    ? html`<div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">per-asset conservation (in = out) — from the verified settle (recTotalAsset)</div>${res.conservation.map(c =>
      html`<div class="leg">${c.asset}: ${c.in} in = ${c.out} out <span class="${c.ok?'ok':'no'}">${c.ok?'✔':'✗'}</span></div>
       <div class="bar"><span style="width:100%;background:${color[c.asset]||'#58a6ff'}"></span></div>`)}</div>`
    : '';
  $('cleared').classList.remove('empty');
  setHtml($('cleared'), html`<div class="card">${settled}${rested}</div>${conservation}`);
}

// ── the single-phase SHIELDED clear through the REAL fhEgg engine (POST /clear-shielded) ──
// The same batch, cleared through fhegg-solver (PDHG circulation + Cert-F certificate + the
// verified AIR gate). The clearing + certificate are REAL; the STARK-ZK wrap that hides the
// certificate (the reveal-nothing floor) is NAMED in the result, not run in this demo.
async function shieldedClear() {
  const btn = $('shieldedBtn');
  btn.disabled = true;
  const orders = book.map(o => ({
    trader: o.trader, offerAsset: o.offerAsset, offerAmount: o.offerAmount,
    wantAsset: o.wantAsset, wantMin: o.wantMin, priority: o.priority,
  }));
  const el = $('shieldedCleared');
  el.classList.remove('empty');
  setHtml(el, html`<div class="fade">running the real fhEgg engine (PDHG + Cert-F)…</div>`);
  let res;
  try {
    res = await fetch('/clear-shielded', {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(orders),
    }).then(r => r.json());
  } catch (e) {
    setHtml(el, html`<div class="no">fhEgg engine unreachable: ${e.message} — run via serve.mjs</div>`);
    btn.disabled = false;
    return;
  }
  if (res.error) {
    setHtml(el, html`<div class="no">${res.error}</div>${res.stderr ? html`<div class="fade mono">${res.stderr}</div>` : ''}`);
    btn.disabled = false;
    return;
  }
  renderShieldedCleared(res);
  btn.disabled = false;
}

// Render the REAL fhEgg shielded clearing (JSON from POST /clear-shielded → fhegg_clear).
function renderShieldedCleared(res) {
  const c = res.certificate || {};
  const air = res.air || {};
  const t = res.tamper || {};
  const st = res.starkStage || {};

  const orders = (res.orders || []).map(o => {
    const mine = o.trader === 'Ada';
    return html`<div class="alloc ${mine ? 'mine' : ''}">
      <span class="who">${o.trader}${mine ? ' · you' : ''}</span>
      <span class="leg">${o.offerAsset}→${o.wantAsset}: cleared <b>${o.clearedFlow}</b> of ${o.offerAmount} (want ≥${o.wantMin})</span>
      <span class="${o.filled ? 'ok' : 'fade'}">${o.filled ? '✔' : '·'}</span>
    </div>`;
  });

  setHtml($('shieldedCleared'), html`<div class="card">
    <div class="fade" style="font-size:11px;margin-bottom:6px">${res.mechanism || ''}  ·  ${res.nodes} assets, ${res.edges} orders, T=${res.iters} iters</div>
    ${orders}
  </div>
  <div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">Cert-F primal-dual certificate — the fair-batch gate the verified AIR checks</div>
    <div class="leg">cleared weighted volume wᵀf = <b>${c.clearedVolume}</b> · dual cᵀs = ${c.dualObjective} · duality gap = ${c.dualityGap}</div>
    <div class="leg">per-asset conservation ‖Af‖∞ = ${c.conservationResidual} <span class="${c.conserves ? 'ok' : 'no'}">${c.conserves ? '✔ conserves' : '✗'}</span></div>
    <div class="leg">certificate valid (conserves · boxed · s≥0 · dual-feasible · gap≤ε): <span class="${c.valid ? 'ok' : 'no'}">${c.valid ? '✔ PROVED-sound checks pass' : '✗'}</span></div>
  </div>
  <div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">the verified AIR gate (the exact n+4m+1 rows Market/CertF.lean proves sound)</div>
    <div class="leg">honest certificate → AIR <span class="${air.accept ? 'ok' : 'no'}">${air.accept ? '✔ ACCEPT' : '✗ reject'}</span> (${air.constraints} constraints, ${air.terms} terms, ${air.witnessCells} witness cells)</div>
    <div class="leg">tampered (${t.what || ''}) → AIR <span class="${!t.accept ? 'ok' : 'no'}">${!t.accept ? '✔ REJECT' : '✗ accepted (BUG)'}</span> [${(t.violated || []).join(', ')}]</div>
  </div>
  <div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">who sees what — the shielded tiers</div>
    ${(res.tiers || []).map(x => html`<div class="leg"><b>${x.tier}</b>: ${x.sees}</div>`)}
    <div class="leg" style="margin-top:8px"><span class="chip NOTBATCH">STARK-ZK: ${st.status || 'named'}</span></div>
    <div class="det">${st.revealNothingFloor || ''}. Hides: ${(st.hides || []).join(', ')}. Wire entry point: <span class="mono">${st.wireEntryPoint || ''}</span>.</div>
  </div>`);
}

// ── the reveal-nothing STARK: prove the shielded clearing, render the WORLD-view ──
// POST /prove-shielded runs the SAME batch through fhegg_clear (solver-side, sees f/π/s),
// then proves the certificate in a REAL dregg STARK (cert_f_prove → from_solution_json →
// prove_cert_f → verify_cert_f). The response carries ONLY what the world sees; the witness
// (f, π, s) stays server-side. This panel makes that boundary tangible: the flows the solver
// saw are shown REDACTED (locked), and the world-column shows only the proof + public inputs.
async function proveShielded() {
  const btn = $('worldBtn');
  btn.disabled = true;
  const el = $('worldView');
  el.classList.remove('empty');
  setHtml(el, html`<div class="fade">proving the clearing in a real STARK (BabyBear + FRI) — this is real work, a moment…</div>`);
  const orders = book.map(o => ({
    trader: o.trader, offerAsset: o.offerAsset, offerAmount: o.offerAmount,
    wantAsset: o.wantAsset, wantMin: o.wantMin, priority: o.priority,
  }));
  const t0 = performance.now();
  let r;
  try {
    r = await fetch('/prove-shielded', {
      method: 'POST', headers: { 'Content-Type': 'application/json' },
      body: JSON.stringify(orders),
    }).then(x => x.json());
  } catch (e) {
    setHtml(el, html`<div class="no">reveal-nothing prover unreachable: ${e.message} — run via serve.mjs</div>`);
    btn.disabled = false; return;
  }
  const wallMs = Math.round(performance.now() - t0);
  if (!r.ok) {
    setHtml(el, html`<div class="no">${r.error || 'prove failed'} (stage: ${r.stage || '?'})</div>${
      r.stderr ? html`<div class="fade mono">${r.stderr}</div>` : ''}${
      r.error && /not built/.test(r.error) ? html`<div class="det">build it: <span class="mono">cargo build --release -p dregg-circuit-prove --bin cert_f_prove</span></div>` : ''}`);
    btn.disabled = false; return;
  }
  renderWorldView(r, wallMs);
  btn.disabled = false;
}

function renderWorldView(r, wallMs) {
  const p = r.program || {}, tr = r.trace || {};
  // The flows the SOLVER saw (from the local book) — shown REDACTED in the world-view, to make
  // the hiding tangible: the solver knew these; the world does not (they are only in the trace).
  const flowsRedacted = book.map(o =>
    html`<div class="leg"><span class="who">${o.trader}</span> <span class="mono" style="filter:blur(4px);user-select:none" aria-hidden="true">${o.offerAsset}→${o.wantAsset} · ██ units</span> <span class="chip NOTBATCH">hidden</span></div>`);
  const rem = r.remaining || {};

  setHtml($('worldView'), html`
  <div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">the reveal-nothing boundary — the same clearing, two views</div>
    <div class="leg"><b>The solver saw</b> (server-side, plaintext, to clear fast): every order, every flow f, the dual prices π, the slacks s.</div>
    <div class="leg" style="margin-top:6px"><b>The world sees</b> (this response): only the proof + the public inputs below. The witness never left the server.</div>
  </div>
  <div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">per-order flows — what the world does NOT get</div>
    ${flowsRedacted}
    <div class="det" style="margin-top:6px">redacted: ${(r.hides || []).join(' · ')}. ${r.redaction || ''}</div>
  </div>
  <div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">the public output — a real dregg STARK (BabyBear + FRI) over the Cert-F AIR</div>
    <div class="leg">a fair batch cleared · per-asset conservation held <span class="${r.conserves ? 'ok' : 'no'}">${r.conserves ? '✔' : '✗'}</span></div>
    <div class="leg">cleared volume wᵀf = <b>${r.clearedVolume}</b> (the ONLY witness-derived scalar the STARK exposes; public inputs = [${(r.publicInputs || []).join(', ')}])</div>
    <div class="leg">proof verifies <span class="${r.verify ? 'ok' : 'no'}">${r.verify ? '✔ verify_cert_f → true' : '✗ did NOT verify'}</span></div>
    <div class="leg">proof size: <b>${r.proofBytes}</b> bytes · descriptor <span class="mono">${r.descriptor || 'cert-f'}</span> · trace width ${tr.width} (${tr.valueBits}-bit range gadget)</div>
    <div class="leg">public program shape: ${p.nodes} assets, ${p.edges} orders, ε=${p.epsilon} (A, w, c ride as descriptor constants — public)</div>
    <div class="leg">proving latency: <b>${r.proveMs} ms</b> prove · ${r.verifyMs} ms verify · ${wallMs} ms wall (real STARK work — a separate action, not a click)</div>
  </div>
  <div class="barwrap card"><div class="fade" style="font-size:11px;margin-bottom:6px">honest scope — what full reveal-nothing still needs</div>
    <div class="leg"><span class="chip NOTBATCH">named</span> ${rem.noteCommitmentMatching || ''}</div>
    <div class="leg" style="margin-top:6px"><span class="chip NOTBATCH">floor</span> ${rem.zkFloor || ''}</div>
    <div class="det" style="margin-top:6px">Here the flows are hidden from the PUBLIC OUTPUT (this proof). Full input-privacy — hidden bids end-to-end — is the shielded-pool wire, named above, not faked.</div>
  </div>`);
}

function renderFairness() {
  setHtml($('fair'), html`${fairnessLedger().map(f => {
    const chips = f.grades.map(g => html`<span class="chip ${g === 'NOT-IN-THIS-BATCH' ? 'NOTBATCH' : g}">${g}</span>`);
    return html`<div class="fair">
      <div>${chips}</div>
      <div class="lab" style="margin-top:6px">${f.label}</div>
      <div class="det">${f.detail}</div>
      <div class="cite">${f.lean}</div>
    </div>`;
  })}`);
}

const tick = () => new Promise(r => setTimeout(r, 30));

// ── boot ──
(async function boot() {
  renderBook(false);
  renderFairness();
  setStepper(0);
  $('placeBtn').onclick = place;
  $('shieldedBtn').onclick = shieldedClear;
  $('worldBtn').onclick = proveShielded;
  // probe the live node so the header shows whether settlement will land on-chain
  fetch('/node/status').then((r) => r.json()).then((s) => {
    if (s.up) { $('nodePill').className = 'pill live'; $('nodePill').textContent = 'node: live @ ' + (s.node || '').replace(/^https?:\/\//, ''); }
    else { $('nodePill').className = 'pill warn'; $('nodePill').textContent = 'node: offline · local matcher only'; }
  }).catch(() => { $('nodePill').className = 'pill warn'; $('nodePill').textContent = 'node: offline · local matcher only'; });
  try {
    await initWallet();
    walletReady = true;
    $('walletPill').className = 'pill live';
    $('walletPill').textContent = 'wallet: Dragon\'s Egg Cipherclerk · ready';
    $('placeBtn').disabled = false;
  } catch (e) {
    $('walletPill').className = 'pill warn';
    $('walletPill').textContent = 'wallet: wasm load failed — run via serve.mjs';
    console.error(e);
  }
})();

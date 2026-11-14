// serve.mjs — dev server for the DrEX web prototype.
//
//   node drex-web/serve.mjs   → http://localhost:8781
//
// Serves drex-web/ statically AND mounts the extension's wallet wasm at /wasm/
// so the page loads the SAME dregg_wasm.js + dregg_wasm_bg.wasm the browser
// extension ships — real in-browser proving, no copy, no mock.
//
// It ALSO exposes POST /clear — the REAL matcher. The web app posts the batch's
// revealed orders as JSON; the server shells to the `drex_clear` binary
// (exec-lean/src/bin/drex_clear.rs), which runs the SAME pipeline as
// `cargo run -p dregg-exec-lean --example drex_clear_book`: rung-2 aggregate →
// solver.rs multilateral ring match → verified_settle.rs (each leg folded through
// the proved recKExecAsset kernel) → allocations + conservation + reject-polarity.
// The clearing the UI renders is the REAL solver's, not a JS mirror.
//
// ── NODE-DRIVEN SETTLEMENT (the make-it-real unlock) ──
// POST /settle takes the cleared batch (the ring the solver found + allocations)
// and lands it as ONE real turn on a LIVE dregg node:
//   /cipherclerk/unlock  → bearer token (first unlock sets the dev passphrase)
//   POST /turn/submit     → the clearing settles as a real turn: one REAL per-trader
//                           Transfer (operator → the trader's deterministic ledger
//                           cell) per cleared fill lands each trader's `received`
//                           amount as a genuine, light-client-checkable balance
//                           change, plus one EmitEvent recording the batch. The node
//                           executes it on the effect-VM (execute_via_producer) and
//                           the async prove_pool proves it (a --prove-turns node
//                           attaches the full-turn STARK proof to the receipt).
//   GET  /api/turn/{h}/proof, /api/receipts, /api/cell/{op} → the proof, the
//                           committed receipt, and the ledger state — all read
//                           back FROM the node, not synthesized here.
// The node ingress is REAL; there is no faked node. If the node is unreachable,
// /settle returns { nodeUp:false } and the UI keeps the labeled local matcher.
// HONEST SCOPE: single-node dev instance (federation mode "solo"), not the
// multi-node BFT federation, and no on-chain settle (that is a separate wiring
// lane). The extension wallet + the solver + the node are all real.

import http from 'node:http';
import fs from 'node:fs';
import path from 'node:path';
import { fileURLToPath } from 'node:url';
import { spawn } from 'node:child_process';
import crypto from 'node:crypto';

const HERE = path.dirname(fileURLToPath(import.meta.url));
const EXT = path.resolve(HERE, '..', 'extension');
const REPO = path.resolve(HERE, '..');
const PORT = process.env.PORT || 8781;
// Bind address. Default localhost-only (nothing off-box reaches it). Set
// DREX_BIND to the hbox LAN IP (192.168.50.39) to let ember reach it from
// their Mac over the LAN — still PRIVATE: hbox's ufw is default-deny inbound
// with the LAN allowed, so a LAN bind is reachable-to-ember, not public.
//
// An all-interfaces bind (0.0.0.0 / ::) is PUBLIC unless a host firewall gates
// the port, so we REFUSE it by default. But to reach the app from BOTH the hbox
// LAN (192.168.50.39) AND the tailscale mesh (100.95.240.73 / hbox-dregg) with a
// single listener, an all-interfaces bind is required — a specific-interface
// bind can only cover ONE of the two. That is safe ONLY behind a default-deny
// firewall that allows just the LAN + tailscale0 in front of the port. hbox is
// exactly that (ufw: default-deny inbound, allow 192.168.50.0/24 + SSH +
// tailscale0 — so :8781 is reachable over the LAN and the tailnet, never the
// public internet). Require an explicit opt-in (DREX_ALLOW_WILDCARD=1) so the
// guard stays meaningful on any box that is NOT firewalled — the same
// assert-you-vetted-it shape as the node's DREGG_ALLOW_UNVERIFIED_CONSENSUS.
const HOST = process.env.DREX_BIND || '127.0.0.1';
const WILDCARD = HOST === '0.0.0.0' || HOST === '::' || HOST === '*';
if (WILDCARD && process.env.DREX_ALLOW_WILDCARD !== '1') {
  console.error(`refusing to bind ${HOST} (all-interfaces = public UNLESS a host firewall gates :${PORT}).`);
  console.error(`  LAN-only dogfood: set DREX_BIND to 127.0.0.1 or the LAN IP 192.168.50.39.`);
  console.error(`  LAN + tailscale reach from a firewalled box (hbox: ufw default-deny + allow`);
  console.error(`  LAN/SSH/tailscale0): set DREX_ALLOW_WILDCARD=1 — ONLY after confirming`);
  console.error(`  \`ufw status\` shows no public ALLOW on :${PORT} (LAN + tailscale0 only).`);
  process.exit(1);
}
if (WILDCARD) {
  console.log(`binding ${HOST} (all-interfaces) with DREX_ALLOW_WILDCARD=1 — the host firewall gates :${PORT} to the LAN + tailscale only.`);
}

// The live dregg node the settlement lands on. Default: a local single-node dev
// instance (`dregg-node run --port 8420 --enable-faucet --prove-turns`), or the
// forwarded port of one run on a build host (`ssh -L 8420:localhost:8420 …`).
const NODE = (process.env.DREGG_NODE || 'http://127.0.0.1:8420').replace(/\/$/, '');
const NODE_PASSPHRASE = process.env.DREGG_NODE_PASSPHRASE || 'drex-dev-node';
let nodeBearer = null; // cached across requests once the node is unlocked.

// The DrEX settlement-pool cell — the fallback destination for a batch that
// cleared nothing (no per-trader fills), so /settle still lands a committed +
// proven turn. A fixed dev address (`de55e771…`, "settle"); materialized once.
const SETTLE_CELL = 'de55e771' + '0'.repeat(56);

// The deterministic per-trader ledger cell: a stable 32-byte cell id namespaced
// under the DrEX trader space (v1), so re-settling the SAME trader credits the
// SAME cell — the trader's cleared allocations accrete as real, light-client-
// checkable balance. Any 64-hex value is a valid destination cell id (the node
// materializes it on first faucet-touch), so a namespaced sha-256 is a clean,
// collision-resistant address book keyed by the solver's trader label.
const traderCell = (trader) =>
  crypto.createHash('sha256').update('drex-trader-v1:' + String(trader)).digest('hex');

// Unlock the node (idempotent): the FIRST unlock on a fresh data dir sets the
// dev passphrase and returns the bearer token that authorizes /turn/submit;
// later unlocks verify it. Loopback-only on the node side, which the local
// serve.mjs (or an ssh -L forward) satisfies.
async function nodeUnlock() {
  if (nodeBearer) return nodeBearer;
  const r = await fetch(NODE + '/cipherclerk/unlock', {
    method: 'POST', headers: { 'Content-Type': 'application/json' },
    body: JSON.stringify({ passphrase: NODE_PASSPHRASE }),
  });
  const j = await r.json();
  if (!j.success || !j.bearer_token) throw new Error('node unlock failed: ' + (j.error || r.status));
  nodeBearer = j.bearer_token;
  return nodeBearer;
}

async function nodeGet(pathname) {
  const r = await fetch(NODE + pathname, { headers: nodeBearer ? { Authorization: 'Bearer ' + nodeBearer } : {} });
  if (!r.ok) return { __status: r.status };
  return r.json();
}

// A committed turn costs computrons, drawn against the operator cell's balance
// (the turn `fee` sets the budget). On a dev node the faucet tops the operator
// up so the settlement turn has budget. Materializes the cell if absent.
// A faucet grant that REPORTS its outcome. The old version swallowed everything
// with `.catch(()=>{})`, so a 404 (faucet DISABLED) and a 429 (rate-limited) both
// read as success and the caller blamed a downstream "underfunded" on nothing it
// could name. Three outcomes, three fixes, three returns.
async function nodeFaucet(cell, amount) {
  let r;
  try { r = await fetch(NODE + '/api/faucet', { method: 'POST', headers: { 'Content-Type': 'application/json' }, body: JSON.stringify({ recipient: cell, amount }) }); }
  catch (e) { return { ok: false, error: 'faucet fetch failed: ' + (e && e.message || e) }; }
  if (r.status === 404) return { ok: false, disabled: true };       // node started WITHOUT --enable-faucet
  if (r.status === 429) return { ok: false, rateLimited: true };
  let j = {}; try { j = await r.json(); } catch (_e) {}
  if (j.success) return { ok: true, turnHash: j.turn_hash };
  const err = String(j.error || ('http ' + r.status));
  return { ok: false, rateLimited: /rate limit/i.test(err), error: err };
}

// Is the node answering? This is the ONLY probe in the settle path allowed to
// conclude `{ nodeUp:false }`. A node that answers /status is up — reporting a
// reachable node that merely could not settle as "offline" is the same absence-
// dressed-as-verdict the drex_routing gate work killed.
async function nodeReachable() {
  try { const r = await fetch(NODE + '/status', { signal: AbortSignal.timeout(4000) }); return r.ok; }
  catch (_e) { return false; }
}

// Fund the settle operator (the node's own agent cell) up to `need`, robustly.
// Destinations are NOT pre-faucetted: a Transfer to a missing cell is auto-
// provisioned by finalization (`provision_transfer_destinations`, node/src/api.rs),
// so the old zero-amount dest touches were unnecessary AND, as a burst against the
// per-IP faucet limiter, they starved the operator grant — which then surfaced as a
// bogus "operator underfunded" on a node whose faucet was fine.
async function ensureOperatorFunded(operator, need) {
  let id = await nodeGet('/api/node/identity');
  const have = () => (id && Number(id.agent_balance) || 0);
  if (have() >= need) return { funded: true, have: have() };
  const grant = Math.min(10000, need + 500);
  const f = await nodeFaucet(operator, grant);
  if (f.disabled) return { funded: false, disabled: true, have: have() };
  if (!f.ok && !f.rateLimited) return { funded: false, error: f.error, have: have() };
  for (let i = 0; i < 24; i++) {
    await new Promise(x => setTimeout(x, 500));
    id = await nodeGet('/api/node/identity');
    if (have() >= need) return { funded: true, have: have() };
  }
  return { funded: false, rateLimited: !!f.rateLimited, have: have() };
}

// Encode a small unsigned int as a decimal string the node's parse_field_element
// packs little-endian into a field element (see node/src/api.rs).
const felt = (n) => String(Math.max(0, Math.min(Number.MAX_SAFE_INTEGER, Math.floor(Number(n) || 0))));

// Build the ONE settlement turn from the cleared batch and land it on the node.
async function settleOnNode(cleared) {
  // (0) REACHABILITY — the one and only place `nodeUp:false` is legitimate. Past
  //     here the node is up, and every failure says WHY, never "offline".
  if (!(await nodeReachable())) return { nodeUp: false, node: NODE };
  const fail = (stage, error, extra = {}) => ({ nodeUp: true, accepted: false, node: NODE, stage, error, ...extra });

  let bearer;
  try { bearer = await nodeUnlock(); } catch (e) { return fail('unlock', e.message); }
  const ident = await nodeGet('/api/node/identity');
  const operator = ident && ident.agent_cell;
  if (!operator) return fail('identity', 'node is up but its identity carries no agent cell');

  const legs = (cleared.ring && cleared.ring.legs) || [];
  const conserved = (cleared.conservation || []).reduce((s, c) => s + (Number(c.in) || 0), 0);

  // ── FAITHFUL PER-TRADER SETTLEMENT ──
  // Each trader's cleared `received` amount (read off the VERIFIED post-ledger by
  // drex_clear) lands as a REAL, INDIVIDUAL Transfer: operator → that trader's
  // deterministic ledger cell. Each fill is a genuine per-trader balance change,
  // light-client-checkable, not a single lump value-move into a pool.
  //
  // WHY TRANSFER, NOT SETFIELD (the cohort reality — INVESTIGATED against the
  // deployed --release binary, not assumed): a per-trader `SetField` allocation
  // turn COMMITS but is UNATTESTED at the deployed VK. Its rotated effect-vm proof
  // verifies under ALL EIGHT per-slot descriptors at once (setFieldVmDescriptor2-0R24
  // … -7R24 — the deployed `v3OfFrozen` freezes the field block and does NOT bind the
  // written slot uniquely into the PIs), so the SDK's uniqueness gate rejects it:
  // "rotated effect-vm proof verified under MULTIPLE cohort descriptors … selector
  // binding ambiguous, rejecting" (sdk/src/full_turn_proof.rs). Making SetField prove
  // needs a UNIQUE per-slot binding (the VALUE8 / freeze-EXCEPT weld) — a descriptor/VK
  // change, i.e. a VK-EPOCH FLIP, which is EMBER-GATED and NOT fired here. Transfer is a
  // clean, uniquely-binding DEPLOYED cohort (transferVmDescriptor2R24) that PROVES, so
  // per-trader value delivery is the faithful settle that needs no VK flip. (setFieldDyn
  // would bind uniquely but is field_idx>=8, which panics in the executor's trace-gen —
  // structurally unreachable — so it is not a live cohort either.)
  const fills = (cleared.allocations || [])
    .filter((a) => !a.rested && Number(a.received) > 0)
    .map((a) => ({
      trader: String(a.trader),
      cell: traderCell(a.trader),
      recvAsset: a.recvAsset,
      received: Math.floor(Number(a.received)),
      amount: Math.max(1, Math.floor(Number(a.received))),
    }));

  // Devnet computron-budget envelope (a LABELED inadequacy, not a silent clamp): the
  // operator is funded by the rate-limited faucet (<=10000/min). If the batch's total
  // cleared amount would exceed a fundable ceiling, we scale the settled COMPUTRON
  // amounts proportionally and SURFACE it (`scaled`/`scale` in the response) so the UI
  // can show the true `received` alongside the settled amount. Demo-scale batches settle
  // at the EXACT cleared amount (scale = 1).
  const FUND_CEILING = 9000; // headroom under the 10000 faucet cap for the turn fee
  const rawTotal = fills.reduce((s, f) => s + f.amount, 0);
  let scale = 1;
  if (rawTotal > FUND_CEILING) {
    scale = FUND_CEILING / rawTotal;
    for (const f of fills) f.amount = Math.max(1, Math.floor(f.amount * scale));
  }
  const settledTotal = fills.reduce((s, f) => s + f.amount, 0);

  // Destination cells are NOT pre-materialized. An earlier comment here claimed
  // "Transfer rejects an unmaterialized destination" — that is FALSE: finalization
  // auto-provisions any missing destination cell deterministically from the
  // Transfer's source (`provision_transfer_destinations`, node/src/api.rs). The
  // zero-amount touch was unnecessary and, as a burst, tripped the per-IP faucet
  // limiter and starved the operator grant below.

  // Build the settlement turn: one Transfer per cleared fill + a batch EmitEvent. A
  // batch with NO fills (nothing cleared) still lands one committed+proven turn: a
  // single 1-computron Transfer into the settlement-pool cell as the carrier.
  const effects = fills.length
    ? fills.map((f) => ({ kind: 'transfer', to: f.cell, amount: f.amount }))
    : [{ kind: 'transfer', to: SETTLE_CELL, amount: 1 }];
  effects.push({ kind: 'emit_event', topic: 'drex_clear_batch', data: [felt(fills.length), felt(conserved)] });

  // Budget: the turn fee sets the computron limit and the operator cell must back
  // fee + the total value transferred. Top the operator up first (faucet is 1/cell/min
  // on a dev node, so keep the fee modest).
  const fee = 800 + 350 * effects.length;
  const need = fee + settledTotal + (fills.length ? 0 : 1);

  const fund = await ensureOperatorFunded(operator, need);
  if (!fund.funded) {
    if (fund.disabled) return fail('fund',
      `this node has the faucet DISABLED (started without --enable-faucet); the settle operator ${operator.slice(0, 12)}… holds ${fund.have} and needs ${need}. On a hardened/live node the operator is funded out of band — which is why the OPEN tier settles on a --enable-faucet dev node, not the live PoA node.`,
      { operator, need, faucetDisabled: true });
    if (fund.rateLimited) return fail('fund',
      `operator underfunded (have ${fund.have}, need ${need}); the per-cell faucet is 1 grant/min and this batch needs more than one — retry in ~1 min or shrink the book`,
      { operator, need });
    return fail('fund', `could not fund the settle operator: ${fund.error || 'unknown'}`, { operator, need });
  }

  const submit = await fetch(NODE + '/turn/submit', {
    method: 'POST',
    headers: { 'Content-Type': 'application/json', Authorization: 'Bearer ' + bearer },
    body: JSON.stringify({ agent: operator, nonce: 0, fee, memo: 'drex_clear', actions: [{ effects }] }),
  }).then((r) => r.json()).catch((e) => ({ accepted: false, error: 'submit failed: ' + (e && e.message || e) }));

  if (!submit.accepted || !submit.turn_hash) {
    return fail('submit', submit.error || 'turn not accepted', { operator, submit });
  }
  const turnHash = submit.turn_hash;

  // Poll for the async/committed proof + the committed receipt. The receipt comes
  // from /api/starbridge/receipts (it supports a turn_hash filter; the row nests
  // the ReceiptInfo under `.receipt`). The STARK proof (a --prove-turns node)
  // comes from /api/turn/{h}/proof; otherwise the async prove_pool attaches a
  // WitnessedReceipt (has_proof / witness_count on the receipt).
  // The receipt endpoint returns a flat ReceiptInfo (serde-flattened): turn_hash,
  // pre_state/post_state, computrons_used, action_count, has_proof, witness_count.
  // The async prove_pool attaches the self-verified full-turn STARK proof within
  // ~4–15s (a Transfer cohort; queue-depth dependent), so poll for up to ~24s
  // rather than time out before it lands.
  let proof = null, r = null;
  for (let i = 0; i < 40; i++) {
    if (!proof) {
      const p = await nodeGet('/api/turn/' + turnHash + '/proof');
      if (p && !p.__status && p.proof_status === 'proved' && p.proof_len) proof = { present: true, len: p.proof_len, mode: 'stark_full_turn' };
    }
    const recs = await nodeGet('/api/starbridge/receipts?turn_hash=' + turnHash);
    if (Array.isArray(recs) && recs.length) r = recs[0].receipt || recs[0];
    if (proof || (r && (r.witness_count > 0 || r.has_proof || r.proof_status === 'not_required'))) break;
    await new Promise((x) => setTimeout(x, 600));
  }
  if (!proof && r && (r.witness_count > 0 || r.has_proof)) {
    proof = { present: true, len: null, mode: 'witnessed_receipt', witnessCount: r.witness_count };
  }
  const proofNote = proof ? null
    : r?.proof_status === 'not_required'
      ? 'Coordination turn: signature attestation only, no validity proof'
      : 'No validity proof attached; consult the receipt proof disposition';

  const cell = await nodeGet('/api/cell/' + operator);

  // Read each trader's cell balance back FROM the node — the per-trader allocation
  // is now a real ledger state change, not a synthesized number. The `balance` is
  // the node's committed value after this settle (it accretes across settles).
  const perTrader = await Promise.all(fills.map(async (f) => {
    const tc = await nodeGet('/api/cell/' + f.cell);
    return {
      trader: f.trader, cell: f.cell, recvAsset: f.recvAsset,
      received: f.received,          // the true cleared amount (drex_clear post-ledger)
      settled: f.amount,             // the computrons transferred this settle (== received unless scaled)
      balance: tc && !tc.__status && tc.found ? tc.balance : null,
    };
  }));

  return {
    nodeUp: true, accepted: true, node: NODE, operator, turnHash,
    proofStatus: r?.proof_status || submit.proof_status, witnessCount: submit.witness_count,
    proof: proof || { present: false }, proofNote,
    // The per-trader settlement summary: the faithful spine (each trader's cleared
    // amount as its OWN real, provable Transfer). `scaled` flags the devnet
    // computron-budget envelope (a LABELED inadequacy — the true `received` is kept).
    settle: {
      mode: 'per_trader_transfer', traders: fills.length,
      settledTotal, scaled: scale < 1, scale: Number(scale.toFixed(6)),
    },
    perTrader,
    receipt: r && {
      chainIndex: r.chain_index, finality: r.finality,
      preState: r.pre_state, postState: r.post_state,
      computronsUsed: r.computrons_used, actionCount: r.action_count,
      hasProof: r.has_proof, proofStatus: r.proof_status, witnessCount: r.witness_count,
      executorSigned: r.executor_signed,
    },
    cell: cell && !cell.__status && cell.found ? {
      balance: cell.balance, nonce: cell.nonce,
      stateCommitment: cell.state_commitment,
      fields: (cell.fields || []).slice(0, 10),
    } : null,
  };
}

// How to invoke the REAL `drex_clear` matcher (intent/src/bin/drex_clear.rs).
//
// The Mac dev box is too contended to build Rust locally, so by default the
// matcher runs on the persvati build host where the binary is already compiled:
// we ssh in and pipe the orders JSON to the prebuilt binary over stdin. If a
// LOCAL binary exists (someone built it), we prefer it — same binary, no network.
// Override the host/dir with DREX_REMOTE / DREX_REMOTE_DIR.
const REMOTE_HOST = process.env.DREX_REMOTE || 'persvati';
const REMOTE_DIR = process.env.DREX_REMOTE_DIR || 'dregg-build/drex-matcher';

function drexClearCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'target', prof, 'drex_clear');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local target/' + prof };
  }
  return {
    cmd: 'ssh',
    args: [REMOTE_HOST, `cd ${REMOTE_DIR} && ./target/debug/drex_clear`],
    where: REMOTE_HOST + ':' + REMOTE_DIR + ' (prebuilt)',
  };
}

// Run the REAL clear-book pipeline over the posted revealed orders.
function runClear(ordersJson) {
  return new Promise((resolve) => {
    const { cmd, args } = drexClearCmd();
    const child = spawn(cmd, args, { cwd: REPO });
    let out = '', err = '';
    child.stdout.on('data', (d) => (out += d));
    child.stderr.on('data', (d) => (err += d));
    child.on('error', (e) => resolve({ ok: false, error: 'spawn failed: ' + e.message }));
    child.on('close', (code) => {
      const line = out.trim().split('\n').filter(Boolean).pop() || '';
      try {
        resolve(JSON.parse(line));
      } catch (_e) {
        resolve({ ok: false, error: 'drex_clear produced no JSON (exit ' + code + ')', stderr: err.slice(-400), raw: out.slice(-400) });
      }
    });
    child.stdin.end(ordersJson);
  });
}

// How to invoke the REAL fhEgg single-phase SHIELDED clearing engine
// (fhegg-solver/src/bin/fhegg_clear.rs). fhegg-solver is a STANDALONE crate
// (opted out of the workspace), so its binary lands in its OWN target dir. The
// same revealed orders that /clear runs through the TTC ring matcher, /clear-shielded
// runs through the convex-clearing + Cert-F certificate route (the fair-batch gate).
// LOCAL only — if the binary is not built, we say so rather than touch anything remote.
function fheggClearCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'fhegg-solver', 'target', prof, 'fhegg_clear');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local fhegg-solver/target/' + prof };
  }
  return { cmd: null, args: [], where: '(not built)' };
}

// Run the REAL fhEgg single-phase shielded clearing over the posted revealed orders.
function runShieldedClear(ordersJson) {
  return new Promise((resolve) => {
    const { cmd, args } = fheggClearCmd();
    if (!cmd) {
      return resolve({
        ok: false,
        error: 'fhegg_clear not built — run: cargo build -p fhegg-solver --bin fhegg_clear  (in fhegg-solver/)',
      });
    }
    const child = spawn(cmd, args, { cwd: REPO });
    let out = '', err = '';
    child.stdout.on('data', (d) => (out += d));
    child.stderr.on('data', (d) => (err += d));
    child.on('error', (e) => resolve({ ok: false, error: 'spawn failed: ' + e.message }));
    child.on('close', (code) => {
      const line = out.trim().split('\n').filter(Boolean).pop() || '';
      try {
        resolve(JSON.parse(line));
      } catch (_e) {
        resolve({ ok: false, error: 'fhegg_clear produced no JSON (exit ' + code + ')', stderr: err.slice(-400), raw: out.slice(-400) });
      }
    });
    child.stdin.end(ordersJson);
  });
}

// How to invoke the REAL reveal-nothing STARK prover (circuit-prove/src/bin/cert_f_prove.rs).
// It lives in the WORKSPACE target (dregg-circuit-prove is a workspace member), not the
// standalone fhegg-solver target. Same locate-local-first discipline as the matcher.
// LOCAL only — if unbuilt, we say how to build it rather than reach off-box.
function certFProveCmd() {
  for (const prof of ['release', 'debug']) {
    const p = path.join(REPO, 'target', prof, 'cert_f_prove');
    if (fs.existsSync(p)) return { cmd: p, args: [], where: 'local target/' + prof };
  }
  return { cmd: null, args: [], where: '(not built)' };
}

// Run the REAL Cert-F STARK over a solver certificate JSON. The certificate carries the
// PRIVATE witness (f, π, s); this consumes it into the STARK trace and returns ONLY the
// world-visible result (verify, proof size, public inputs) — cert_f_prove never prints
// f/π/s. Proving costs SECONDS (BabyBear + FRI), so this is a SEPARATE action, not the
// click-latency /clear-shielded path.
function runCertFProve(certJson) {
  return new Promise((resolve) => {
    const { cmd, args } = certFProveCmd();
    if (!cmd) {
      return resolve({
        ok: false,
        error: 'cert_f_prove not built — run: cargo build --release -p dregg-circuit-prove --bin cert_f_prove',
      });
    }
    const child = spawn(cmd, args, { cwd: REPO });
    let out = '', err = '';
    child.stdout.on('data', (d) => (out += d));
    child.stderr.on('data', (d) => (err += d));
    child.on('error', (e) => resolve({ ok: false, error: 'spawn failed: ' + e.message }));
    child.on('close', (code) => {
      const line = out.trim().split('\n').filter(Boolean).pop() || '';
      try {
        resolve(JSON.parse(line));
      } catch (_e) {
        resolve({ ok: false, error: 'cert_f_prove produced no JSON (exit ' + code + ')', stderr: err.slice(-600), raw: out.slice(-400) });
      }
    });
    child.stdin.end(certJson);
  });
}

const MIME = {
  '.html': 'text/html; charset=utf-8',
  '.js': 'text/javascript; charset=utf-8',
  '.mjs': 'text/javascript; charset=utf-8',
  '.css': 'text/css; charset=utf-8',
  '.wasm': 'application/wasm',
  '.json': 'application/json',
  '.png': 'image/png',
  '.svg': 'image/svg+xml',
};

function send(res, code, body, type) {
  res.writeHead(code, { 'Content-Type': type || 'text/plain', 'Cache-Control': 'no-cache' });
  res.end(body);
}

http.createServer(async (req, res) => {
  let url = decodeURIComponent(req.url.split('?')[0]);
  if (url === '/') url = '/index.html';

  // ── POST /clear — the REAL matcher (solver.rs + verified_settle.rs) ──
  if (req.method === 'POST' && url === '/clear') {
    let body = '';
    req.on('data', (c) => { body += c; if (body.length > 1 << 20) req.destroy(); });
    req.on('end', async () => {
      const result = await runClear(body);
      send(res, result.error ? 502 : 200, JSON.stringify(result), MIME['.json']);
    });
    return;
  }

  // ── POST /clear-shielded — the REAL fhEgg single-phase shielded clearing ──
  // (fhegg-solver: PDHG circulation + Cert-F certificate + the verified AIR gate).
  if (req.method === 'POST' && url === '/clear-shielded') {
    let body = '';
    req.on('data', (c) => { body += c; if (body.length > 1 << 20) req.destroy(); });
    req.on('end', async () => {
      const result = await runShieldedClear(body);
      send(res, result.error ? 502 : 200, JSON.stringify(result), MIME['.json']);
    });
    return;
  }

  // ── POST /prove-shielded — the REAL reveal-nothing STARK (SEPARATE action) ──
  // Runs the SAME batch through fhegg_clear to get the SOLVER's plaintext certificate
  // (which carries the private witness f/π/s), then proves it in the REAL dregg STARK
  // (cert_f_prove → from_solution_json → prove_cert_f → verify_cert_f). The response the
  // BROWSER receives carries ONLY what the world may see: verify, proof size, the public
  // inputs (cleared volume wᵀf + program shape), and honest latency — NEVER f/π/s. The
  // solver certificate stays SERVER-SIDE; it is not forwarded. Proving costs seconds.
  if (req.method === 'POST' && url === '/prove-shielded') {
    let body = '';
    req.on('data', (c) => { body += c; if (body.length > 1 << 20) req.destroy(); });
    req.on('end', async () => {
      // [1] SOLVER view (server-side): clear the batch, obtain the Cert-F certificate.
      const cleared = await runShieldedClear(body);
      if (cleared.error || !cleared.solverCert) {
        return send(res, 502, JSON.stringify({
          ok: false, stage: 'clear',
          error: cleared.error || 'fhegg_clear did not emit solverCert (rebuild fhegg_clear)',
          stderr: cleared.stderr,
        }), MIME['.json']);
      }
      const cert = cleared.solverCert; // holds f, π, s — SERVER-SIDE ONLY, never sent on.

      // [2] PROVE (server-side): pipe the certificate to the real STARK. The witness is
      // consumed into the trace; cert_f_prove returns only the world-visible object.
      const prove = await runCertFProve(JSON.stringify(cert));
      if (!prove.ok) {
        return send(res, 502, JSON.stringify({ ok: false, stage: 'prove', error: prove.error, stderr: prove.stderr }), MIME['.json']);
      }

      // [3] WORLD view: build the response from the prover's output + PUBLIC clearing
      // scalars only. We EXPLICITLY do not spread `cleared` (which contains solverCert /
      // per-order flows) — the redaction is structural, not cosmetic.
      const conserves = !!(cleared.certificate && cleared.certificate.conserves);
      const worldView = {
        ok: true,
        // what the world sees:
        verify: prove.verify,
        proofBytes: prove.proofBytes,
        clearedVolume: prove.clearedVolume,   // the public input wᵀf
        publicInputs: prove.publicInputs,     // the STARK's exposed field elements = [wᵀf]
        program: { nodes: prove.nNodes, edges: prove.mEdges, epsilon: prove.epsilon, scale: prove.scale },
        conserves,
        trace: { width: prove.traceWidth, valueBits: prove.valueBits },
        descriptor: prove.descriptor,
        proveMs: prove.proveMs,
        verifyMs: prove.verifyMs,
        // what the world does NOT see (named, redacted):
        hides: prove.hides,
        redaction: prove.note,
        // honest scope of what full input-privacy still needs:
        remaining: {
          noteCommitmentMatching: 'the demo still takes REVEALED orders as input; matching over HIDDEN NOTE COMMITMENTS (the shielded pool, shielded_ring_clears) is the input-privacy lane',
          zkFloor: 'reveal-nothing rests on the STARK ZK: the HidingFriPcs statistical-ZK floor (Market/RevealNothing.lean — reveal_law is HidingFriPcs-conditional, like the linking tower is HashCR-conditional)',
        },
      };
      send(res, 200, JSON.stringify(worldView), MIME['.json']);
    });
    return;
  }

  // ── GET /node/status — is a live dregg node reachable? ──
  if (req.method === 'GET' && url === '/node/status') {
    try {
      const r = await fetch(NODE + '/status');
      const j = await r.json();
      return send(res, 200, JSON.stringify({ up: true, node: NODE, status: j }), MIME['.json']);
    } catch (e) {
      return send(res, 200, JSON.stringify({ up: false, node: NODE, error: e.message }), MIME['.json']);
    }
  }

  // ── POST /settle — land the cleared batch as ONE real turn on the live node ──
  if (req.method === 'POST' && url === '/settle') {
    let body = '';
    req.on('data', (c) => { body += c; if (body.length > 1 << 20) req.destroy(); });
    req.on('end', async () => {
      let cleared;
      try { cleared = JSON.parse(body); } catch (_e) { return send(res, 400, JSON.stringify({ error: 'bad json' }), MIME['.json']); }
      try {
        const result = await settleOnNode(cleared);
        send(res, 200, JSON.stringify(result), MIME['.json']);
      } catch (e) {
        // settleOnNode is throw-free by construction (structured outcome per
        // reachable-node failure). Reaching here is an UNEXPECTED internal error —
        // do NOT assert `nodeUp:false` and blame the node for a bug here. Re-probe.
        const up = await nodeReachable();
        send(res, 200, JSON.stringify(up
          ? { nodeUp: true, accepted: false, node: NODE, stage: 'internal', error: e.message }
          : { nodeUp: false, node: NODE, error: e.message }), MIME['.json']);
      }
    });
    return;
  }

  let file;
  if (url.startsWith('/wasm/')) {
    file = path.join(EXT, url.slice('/wasm/'.length));
  } else {
    file = path.join(HERE, url);
  }
  // prevent path escape
  const root = url.startsWith('/wasm/') ? EXT : HERE;
  if (!path.resolve(file).startsWith(root)) return send(res, 403, 'forbidden');

  fs.readFile(file, (err, buf) => {
    if (err) return send(res, 404, 'not found: ' + url);
    send(res, 200, buf, MIME[path.extname(file)] || 'application/octet-stream');
  });
}).listen(PORT, HOST, () => {
  console.log('DrEX dev server → http://' + HOST + ':' + PORT);
  console.log('  wallet wasm mounted from ' + EXT + '  (/wasm/dregg_wasm.js)');
  const { where } = drexClearCmd();
  console.log('  REAL matcher   POST /clear  → drex_clear @ ' + where + '  (solver.rs + verified_settle.rs)');
  console.log('  SHIELDED clear POST /clear-shielded → fhegg_clear @ ' + fheggClearCmd().where + '  (PDHG circulation + Cert-F + verified AIR gate)');
  console.log('  LIVE node      POST /settle → ' + NODE + '  (/turn/submit → effect-VM → prove_pool)');
  console.log('                 GET  /node/status probes it; start one with:');
  console.log('                 dregg-node run --port 8420 --enable-faucet --prove-turns');
});

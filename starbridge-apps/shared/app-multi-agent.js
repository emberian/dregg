// starbridge-apps/shared/app-multi-agent.js
//
// REAL multi-agent + Authorization::Custom flows for the subscription and
// governed-namespace starbridge-apps, driven through the in-browser
// DreggRuntime (window.__starbridgeAppRuntime) and the canonical
// TurnExecutor.
//
// This is the in-browser realization of the apps' Rust executor integration
// tests:
//   - subscription/tests/integration_publish_consume.rs
//   - governed-namespace/tests/integration_propose_vote_commit.rs
//
// Unlike the generic runtime-submit.js path (which mints each cell from its
// own writable agent and drops events), this module:
//   1. mints a dedicated APP cell from genesis and installs the canonical
//      cell-program on it (via wasm `install_app_program`), with open
//      permissions so non-owner agents' turns apply (slot caveats are the
//      load-bearing enforcement);
//   2. creates distinct agents (owner / publisher / consumer / committee
//      voters) — REAL separate cipherclerks signing REAL turns;
//   3. submits per-method turns (publish/consume/grant_* ;
//      propose/vote/commit) through `execute_app_turn` /
//      `execute_custom_auth_turn`, including EmitEvent effects so the
//      receipts carry inspectable event data.
//
// The governed-namespace commit step uses a REAL Ed25519 threshold signature:
// committee members sign the exact canonical custom signing message the
// executor recomputes, and a registered threshold verifier validates them
// before the atomic route-table swap commits.

function runtime() {
  return typeof window !== 'undefined' ? window.__starbridgeAppRuntime : null;
}

function rt() {
  const r = runtime();
  if (!r) throw new Error('no in-memory runtime attached (window.__starbridgeAppRuntime)');
  return r;
}

// Per-turn computron budget, debited from the *actor* cell's balance. The app
// turns are cheap (a few SetField + EmitEvent ≈ a few hundred computrons with
// default costs); 5_000 leaves ample headroom. Each acting agent is funded
// above this so its turns clear.
const TURN_FEE = 5_000;
const AGENT_FUNDING = 1_000_000;
const GENESIS_FUNDING = 50_000_000;

function bytesToHex(arr) {
  return Array.from(arr).map((b) => (b & 0xff).toString(16).padStart(2, '0')).join('');
}

function u64BEHex(n) {
  const out = new Uint8Array(32);
  let v = BigInt(n);
  for (let i = 31; i >= 24 && v > 0n; i -= 1) { out[i] = Number(v & 0xffn); v >>= 8n; }
  return bytesToHex(out);
}

// 32-byte commitment over `input`. The opaque roots the cell-program checks
// (message_root / publishers_root / pending_proposal_root) are only required
// to be *distinct + non-zero* by the slot caveats, so SHA-256 (always present
// via SubtleCrypto) suffices for these in-browser commitments. The canonical
// route_table_root commitment goes through wasm `routeTableCommitment`
// (real blake3) separately.
async function blake3Hex(input) {
  const enc = typeof input === 'string' ? new TextEncoder().encode(input) : input;
  const buf = await crypto.subtle.digest('SHA-256', enc);
  return bytesToHex(new Uint8Array(buf));
}

// A stable, distinct 32-byte hex value derived from a label (for opaque
// non-counter roots like message_root / publishers_root). Real deployments
// fold Poseidon2; here we just need a distinct non-zero commitment.
async function rootHex(label) {
  return blake3Hex(`dregg-app-root:${label}`);
}

// ─────────────────────────────────────────────────────────────────────────
// Subscription flow (multi-agent grant)
// ─────────────────────────────────────────────────────────────────────────

/**
 * Run the full subscription publish/grant/consume flow with three distinct
 * agents and a dedicated topic cell carrying the canonical subscription
 * cell-program. Returns a structured trace of every real turn + the final
 * topic-cell slot state.
 */
export async function runSubscriptionFlow() {
  const r = rt();
  const log = [];

  // Genesis (owner) + publisher + consumer — distinct cipherclerks, each
  // funded so its (fee-paying) turns clear.
  const owner = await r.createAgent('sub-owner', GENESIS_FUNDING);
  const ownerIdx = Number(owner.agent_index);
  const publisher = await r.createAgent('sub-publisher', AGENT_FUNDING);
  const consumer = await r.createAgent('sub-consumer', AGENT_FUNDING);
  const publisherIdx = Number(publisher.agent_index);
  const consumerIdx = Number(consumer.agent_index);

  // Mint the topic cell from genesis, then install the canonical program.
  const minted = await r.createCell(PREVIEW_TOPIC_OWNER, 0);
  const topicCell = minted.cell_id;
  const ownerPkHash = await blake3Hex(hexToBytes(owner.public_key));
  await r.installAppProgram(topicCell, 'subscription', {
    owner_pk_hash_hex: ownerPkHash,
    capacity: 1024,
  });
  log.push({ step: 'install', topicCell, program: 'subscription' });

  // Each acting agent (owner/publisher/consumer) needs a capability to reach
  // the topic cell — the executor's cross-cell reachability check (the
  // integration tests sidestep this by having the actor own the cell).
  for (const idx of [ownerIdx, publisherIdx, consumerIdx]) {
    r.grantReachCapability(idx, topicCell);
  }

  // 1. Owner grants the publisher (REAL grant_publisher turn: SetField +
  //    EmitEvent). The publisher pubkey is folded into a new publishers root.
  const pubRoot = await rootHex(`publishers:${publisher.public_key}`);
  const grantPubRes = await r.executeAppTurn(ownerIdx, topicCell, 'grant_publisher', [
    { type: 'set_field', cell: topicCell, index: 3, value_hex: pubRoot },
    { type: 'emit_event', cell: topicCell, topic: 'subscription-publisher-granted',
      data_hex: [pubRoot, await blake3Hex(hexToBytes(publisher.public_key))] },
  ], TURN_FEE);
  log.push({ step: 'grant_publisher', signer: 'owner', result: grantPubRes });

  // 2. Owner grants the consumer (REAL grant_consumer turn).
  const conRoot = await rootHex(`consumers:${consumer.public_key}`);
  const grantConRes = await r.executeAppTurn(ownerIdx, topicCell, 'grant_consumer', [
    { type: 'set_field', cell: topicCell, index: 4, value_hex: conRoot },
    { type: 'emit_event', cell: topicCell, topic: 'subscription-consumer-granted',
      data_hex: [conRoot, await blake3Hex(hexToBytes(consumer.public_key))] },
  ], TURN_FEE);
  log.push({ step: 'grant_consumer', signer: 'owner', result: grantConRes });

  // 3. The PUBLISHER (a different agent) publishes a message — head 0→1,
  //    message_root changes + non-zero, latest_payload written. REAL turn
  //    signed by the publisher cipherclerk, targeting the owner's topic cell.
  const payload1 = await blake3Hex('hello from publisher');
  const msgRoot1 = await rootHex('message:1');
  const publishRes = await r.executeAppTurn(publisherIdx, topicCell, 'publish', [
    { type: 'set_field', cell: topicCell, index: 0, value_hex: u64BEHex(1) },
    { type: 'set_field', cell: topicCell, index: 6, value_hex: msgRoot1 },
    { type: 'set_field', cell: topicCell, index: 7, value_hex: payload1 },
    { type: 'emit_event', cell: topicCell, topic: 'subscription-published',
      data_hex: [u64BEHex(1), msgRoot1, payload1] },
  ], TURN_FEE);
  log.push({ step: 'publish', signer: 'publisher', result: publishRes });

  // 4. The CONSUMER (third agent) consumes — tail 0→1. REAL turn signed by
  //    the consumer cipherclerk.
  const consumeRes = await r.executeAppTurn(consumerIdx, topicCell, 'consume', [
    { type: 'set_field', cell: topicCell, index: 1, value_hex: u64BEHex(1) },
    { type: 'emit_event', cell: topicCell, topic: 'subscription-consumed',
      data_hex: [u64BEHex(1), payload1] },
  ], TURN_FEE);
  log.push({ step: 'consume', signer: 'consumer', result: consumeRes });

  // Final on-ledger state.
  const state = {
    seq_head: r.readCellField(topicCell, 0),
    seq_tail: r.readCellField(topicCell, 1),
    capacity: r.readCellField(topicCell, 2),
    publishers_root: r.readCellField(topicCell, 3),
    consumers_root: r.readCellField(topicCell, 4),
    owner_pk_hash: r.readCellField(topicCell, 5),
    message_root: r.readCellField(topicCell, 6),
    latest_payload_hash: r.readCellField(topicCell, 7),
  };

  return {
    ok: true,
    topicCell,
    agents: { ownerIdx, publisherIdx, consumerIdx },
    log,
    state,
  };
}

// ─────────────────────────────────────────────────────────────────────────
// Governed-namespace flow (propose → vote → threshold-sig commit)
// ─────────────────────────────────────────────────────────────────────────

const GOVERNANCE_VK_HEX =
  // BLAKE3-free stable placeholder == ASCII of "starbridge-gov-threshold-verify!"
  // (mirrors starbridge_governed_namespace::GOVERNANCE_VK). 32 bytes.
  bytesToHex(new TextEncoder().encode('starbridge-gov-threshold-verify!'));

/**
 * Run the full governed-namespace propose → vote → commit flow with a real
 * 2-of-3 committee. The commit is a REAL Authorization::Custom turn discharged
 * by a registered Ed25519 threshold verifier over the canonical signing
 * message. Returns a structured trace + the final namespace-cell state.
 */
export async function runGovernedNamespaceFlow() {
  const r = rt();
  const log = [];

  // Genesis + a 3-member committee (distinct cipherclerks, each funded so its
  // fee-paying turns clear).
  await r.createAgent('gov-genesis', GENESIS_FUNDING);
  const c0 = await r.createAgent('gov-committee-0', AGENT_FUNDING);
  const c1 = await r.createAgent('gov-committee-1', AGENT_FUNDING);
  const c2 = await r.createAgent('gov-committee-2', AGENT_FUNDING);
  const committeePubkeys = [c0.public_key, c1.public_key, c2.public_key];

  // Committee root = blake3 over the concatenated committee pubkeys.
  const committeeRoot = await blake3Hex(
    hexToBytes(c0.public_key + c1.public_key + c2.public_key),
  );

  // Mint the namespace cell from genesis; install the governance program.
  const minted = await r.createCell(PREVIEW_TOPIC_OWNER, 0);
  const nsCell = minted.cell_id;
  const emptyTableRoot = await r.routeTableCommitment([]);
  await r.installAppProgram(nsCell, 'governed-namespace', {
    committee_root_hex: committeeRoot,
    threshold: 2,
    initial_route_table_root_hex: emptyTableRoot,
  });
  log.push({ step: 'install', nsCell, program: 'governed-namespace', committeeRoot });

  // Register the REAL Ed25519 2-of-3 threshold verifier under GOVERNANCE_VK.
  r.registerThresholdVerifier(GOVERNANCE_VK_HEX, committeePubkeys, 2);
  log.push({ step: 'register-verifier', threshold: 2, committeeSize: 3 });

  // Committee members that drive turns need a capability to reach the
  // namespace cell (cross-cell reachability check; see subscription flow).
  for (const c of [c0, c1, c2]) {
    r.grantReachCapability(Number(c.agent_index), nsCell);
  }

  // The proposed new route table + its canonical commitment.
  const proposedRoutes = [['/public/*', 'public'], ['/treasury/*', 'treasury']];
  const proposedRoot = await r.routeTableCommitment(proposedRoutes);

  // 1. Committee member 0 proposes (pending_proposal_root advances; window set).
  const proposalRoot = await blake3Hex(`proposal:${proposedRoot}`);
  const proposeRes = await r.executeAppTurn(Number(c0.agent_index), nsCell, 'propose_table_update', [
    { type: 'set_field', cell: nsCell, index: 5, value_hex: proposalRoot },
    { type: 'set_field', cell: nsCell, index: 4, value_hex: u64BEHex(1000) },
    { type: 'emit_event', cell: nsCell, topic: 'proposal-opened',
      data_hex: [proposalRoot, proposedRoot, u64BEHex(1000)] },
  ], TURN_FEE);
  log.push({ step: 'propose', signer: 'committee-0', result: proposeRes });

  // 2. Two votes advance the tally (pending_proposal_root rolls forward).
  let tally = proposalRoot;
  for (const [i, c] of [[0, c0], [1, c1]]) {
    const next = await blake3Hex(`vote:${tally}:${c.public_key}`);
    const voteRes = await r.executeAppTurn(Number(c.agent_index), nsCell, 'vote_on_proposal', [
      { type: 'set_field', cell: nsCell, index: 5, value_hex: next },
      { type: 'emit_event', cell: nsCell, topic: 'vote-cast',
        data_hex: [next, await blake3Hex(hexToBytes(c.public_key)), u64BEHex(1)] },
    ], TURN_FEE);
    log.push({ step: `vote-${i}`, signer: `committee-${i}`, result: voteRes });
    tally = next;
  }

  // 3. Commit via a REAL Authorization::Custom threshold-sig turn.
  //    The commit effects: route_table_root := proposedRoot, version 0→1,
  //    pending_proposal_root cleared, table-committed event.
  const commitEffects = [
    { type: 'set_field', cell: nsCell, index: 0, value_hex: proposedRoot },
    { type: 'set_field', cell: nsCell, index: 1, value_hex: u64BEHex(1) },
    { type: 'set_field', cell: nsCell, index: 5, value_hex: '0'.repeat(64) },
    { type: 'emit_event', cell: nsCell, topic: 'table-committed',
      data_hex: [proposedRoot, u64BEHex(1), committeeRoot] },
  ];

  // The carrier is committee member 0 (any member may carry; the threshold-sig
  // is what authorizes). Compute the canonical message the executor will
  // recompute, then have members 0 and 1 each sign it (2-of-3). Concatenate
  // the (pubkey ‖ sig) records into the proof bytes.
  const carrierIdx = Number(c0.agent_index);
  const msgHex = r.customCommitSigningMessage(
    carrierIdx, nsCell, 'commit_table_update', commitEffects,
    GOVERNANCE_VK_HEX, committeeRoot,
  );
  const sig0 = r.signCustomCommit(Number(c0.agent_index), msgHex);
  const sig1 = r.signCustomCommit(Number(c1.agent_index), msgHex);
  const proofHex = sig0 + sig1;

  const commitRes = await r.executeCustomAuthTurn(
    carrierIdx, nsCell, 'commit_table_update', commitEffects,
    GOVERNANCE_VK_HEX, committeeRoot, proofHex, TURN_FEE,
  );
  log.push({ step: 'commit', signer: 'threshold(2-of-3)', result: commitRes });

  const state = {
    route_table_root: r.readCellField(nsCell, 0),
    version: r.readCellField(nsCell, 1),
    governance_committee_root: r.readCellField(nsCell, 2),
    threshold: r.readCellField(nsCell, 3),
    dispute_window_height: r.readCellField(nsCell, 4),
    pending_proposal_root: r.readCellField(nsCell, 5),
  };

  return {
    ok: true,
    nsCell,
    committeePubkeys,
    proposedRoot,
    log,
    state,
    commitCommitted: commitRes && commitRes.status === 'committed',
  };
}

// ─── helpers ───────────────────────────────────────────────────────────────

const PREVIEW_TOPIC_OWNER =
  'b00b1eb00b1eb00b1eb00b1eb00b1eb00b1eb00b1eb00b1eb00b1eb00b1eb000';

function hexToBytes(hex) {
  const s = String(hex || '').replace(/^0x/, '');
  const out = new Uint8Array(s.length / 2);
  for (let i = 0; i < out.length; i += 1) out[i] = parseInt(s.slice(i * 2, i * 2 + 2), 16);
  return out;
}

// Expose on window for Playwright-driven smokes + inspector buttons.
if (typeof window !== 'undefined') {
  window.dregg ??= {};
  window.dregg.appFlows ??= {};
  window.dregg.appFlows.subscription = runSubscriptionFlow;
  window.dregg.appFlows.governedNamespace = runGovernedNamespaceFlow;
}

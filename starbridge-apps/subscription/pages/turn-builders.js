// starbridge-apps/subscription/pages/turn-builders.js
//
// JS shim wrapping `window.pyana.signTurn(turnSpec)` (the extension
// wallet API — see extension/src/page.ts) with subscription-domain
// conveniences that mirror the Rust turn-builders in src/lib.rs:
//
//   build_publish_action          → publish(...)
//   build_consume_action          → consume(...)
//   build_grant_publisher_action  → grant_publisher(...)
//   build_grant_consumer_action   → grant_consumer(...)
//
// All four produce a `turnSpec` for `window.pyana.signTurn` and resolve
// to the resulting `TurnReceipt`. No app-domain enforcement runs here:
// the subscription cell-program (`subscription_program` in src/lib.rs)
// is the enforcement loop, evaluated executor-side on every turn. The
// JS layer is the thinnest shim that produces the right shape.
//
// Pattern matches starbridge-apps/identity/pages/turn-builders.js and
// starbridge-apps/nameservice/pages/turn-builders.js: policy lives in
// Rust, the JS layer wraps `signTurn` with named presets.

// Slot indices — mirror constants in src/lib.rs. Keep in sync.
const SEQ_HEAD_SLOT        = 0;
const SEQ_TAIL_SLOT        = 1;
const CAPACITY_SLOT        = 2;
const PUBLISHERS_ROOT_SLOT = 3;
const CONSUMERS_ROOT_SLOT  = 4;
const OWNER_PK_HASH_SLOT   = 5;
const MESSAGE_ROOT_SLOT    = 6;
const LATEST_PAYLOAD_SLOT  = 7;

// Event topic names — mirror src/lib.rs symbol() calls.
const TOPIC_PUBLISHED         = 'subscription-published';
const TOPIC_CONSUMED          = 'subscription-consumed';
const TOPIC_PUBLISHER_GRANTED = 'subscription-publisher-granted';
const TOPIC_CONSUMER_GRANTED  = 'subscription-consumer-granted';

// ─── helpers ─────────────────────────────────────────────────────────────

function u64BE(n) {
  // Big-endian-padded 32-byte field element. Matches the Rust
  // `u64_field` helper in src/lib.rs and pyana_cell::program::field_from_u64_be.
  const view = new Uint8Array(32);
  const bn = BigInt(n);
  for (let i = 0; i < 8; i += 1) {
    view[31 - i] = Number((bn >> BigInt(i * 8)) & 0xffn);
  }
  return Array.from(view);
}

function fieldToU64BE(bytes) {
  let v = 0n;
  for (let i = 24; i < 32; i += 1) {
    v = (v << 8n) | BigInt(bytes?.[i] ?? 0);
  }
  return Number(v);
}

async function sha256(bytes) {
  // Browser SubtleCrypto fallback; matches the inspectors.js hash used
  // for `message_root` placeholder folding. A real deployment uses
  // pyana's Poseidon2 binding when wasm exposes it.
  const buf = bytes instanceof Uint8Array ? bytes : new Uint8Array(bytes);
  const out = await crypto.subtle.digest('SHA-256', buf);
  return new Uint8Array(out);
}

async function payloadHash(payload) {
  if (window.pyana?.blake3) return window.pyana.blake3(payload);
  return sha256(new TextEncoder().encode(payload));
}

async function foldRoot(oldRoot, leaf) {
  // Placeholder: `(old || leaf) -> SHA-256`. Real deployments fold via
  // Poseidon2 over the MerkleQueue ring.
  if (window.pyana?.poseidonFold) return window.pyana.poseidonFold(oldRoot, leaf);
  const buf = new Uint8Array(64);
  buf.set(oldRoot, 0);
  buf.set(leaf, 32);
  return sha256(buf);
}

// ─── builders ────────────────────────────────────────────────────────────

/**
 * Publish a payload into a subscription cell.
 *
 * Composes (`SetField(head, +1)`, `SetField(message_root, fold(old, payload))`,
 * `SetField(latest_payload, payload_hash)`, `EmitEvent("subscription-published")`)
 * into a single signed Action. Mirrors `build_publish_action` in src/lib.rs.
 *
 * @param {string} subscriptionUri  URI of the target subscription cell.
 * @param {string|Uint8Array} payload  Payload bytes (utf-8 string or raw bytes).
 * @returns {Promise<TurnReceipt>}
 */
async function publish(subscriptionUri, payload) {
  const cell = await window.pyana.readCell(subscriptionUri);
  const oldHead = fieldToU64BE(cell.state.fields[SEQ_HEAD_SLOT]);
  const newHead = u64BE(oldHead + 1);
  const payHash = await payloadHash(payload);
  const newRoot = await foldRoot(cell.state.fields[MESSAGE_ROOT_SLOT], payHash);
  return window.pyana.signTurn({
    target: subscriptionUri,
    method: 'publish',
    effects: [
      { kind: 'SetField', cell: subscriptionUri, index: SEQ_HEAD_SLOT,       value: newHead },
      { kind: 'SetField', cell: subscriptionUri, index: MESSAGE_ROOT_SLOT,   value: Array.from(newRoot) },
      { kind: 'SetField', cell: subscriptionUri, index: LATEST_PAYLOAD_SLOT, value: Array.from(payHash) },
      {
        kind: 'EmitEvent',
        cell: subscriptionUri,
        topic: TOPIC_PUBLISHED,
        data: [newHead, Array.from(newRoot), Array.from(payHash)],
      },
    ],
  });
}

/**
 * Consume the head-of-queue message from a subscription cell.
 *
 * Composes (`SetField(tail, +1)`, `EmitEvent("subscription-consumed")`) into a
 * single signed Action. Mirrors `build_consume_action` in src/lib.rs.
 *
 * @param {string} subscriptionUri  URI of the target subscription cell.
 * @returns {Promise<TurnReceipt>}
 */
async function consume(subscriptionUri) {
  const cell = await window.pyana.readCell(subscriptionUri);
  const oldTail = fieldToU64BE(cell.state.fields[SEQ_TAIL_SLOT]);
  const newTail = u64BE(oldTail + 1);
  const latestPayload = cell.state.fields[LATEST_PAYLOAD_SLOT];
  return window.pyana.signTurn({
    target: subscriptionUri,
    method: 'consume',
    effects: [
      { kind: 'SetField', cell: subscriptionUri, index: SEQ_TAIL_SLOT, value: newTail },
      {
        kind: 'EmitEvent',
        cell: subscriptionUri,
        topic: TOPIC_CONSUMED,
        data: [newTail, Array.from(latestPayload)],
      },
    ],
  });
}

/**
 * Add a publisher to the authorized publishers set on a subscription cell.
 *
 * Composes (`SetField(publishers_root, fold(old, new_publisher_pk))`,
 * `EmitEvent("subscription-publisher-granted")`) into a single signed Action.
 * Mirrors `build_grant_publisher_action` in src/lib.rs.
 *
 * @param {string} subscriptionUri        URI of the target cell.
 * @param {Uint8Array} newPublisherPk     32-byte publisher pubkey.
 * @returns {Promise<TurnReceipt>}
 */
async function grant_publisher(subscriptionUri, newPublisherPk) {
  const cell = await window.pyana.readCell(subscriptionUri);
  const newRoot = await foldRoot(
    cell.state.fields[PUBLISHERS_ROOT_SLOT],
    newPublisherPk,
  );
  return window.pyana.signTurn({
    target: subscriptionUri,
    method: 'grant_publisher',
    effects: [
      { kind: 'SetField', cell: subscriptionUri, index: PUBLISHERS_ROOT_SLOT, value: Array.from(newRoot) },
      {
        kind: 'EmitEvent',
        cell: subscriptionUri,
        topic: TOPIC_PUBLISHER_GRANTED,
        data: [Array.from(newRoot), Array.from(newPublisherPk)],
      },
    ],
  });
}

/**
 * Symmetric to `grant_publisher`: adds a consumer to the authorized
 * consumers set. Mirrors `build_grant_consumer_action` in src/lib.rs.
 */
async function grant_consumer(subscriptionUri, newConsumerPk) {
  const cell = await window.pyana.readCell(subscriptionUri);
  const newRoot = await foldRoot(
    cell.state.fields[CONSUMERS_ROOT_SLOT],
    newConsumerPk,
  );
  return window.pyana.signTurn({
    target: subscriptionUri,
    method: 'grant_consumer',
    effects: [
      { kind: 'SetField', cell: subscriptionUri, index: CONSUMERS_ROOT_SLOT, value: Array.from(newRoot) },
      {
        kind: 'EmitEvent',
        cell: subscriptionUri,
        topic: TOPIC_CONSUMER_GRANTED,
        data: [Array.from(newRoot), Array.from(newConsumerPk)],
      },
    ],
  });
}

// ─── registration ────────────────────────────────────────────────────────

if (typeof window !== 'undefined') {
  // Self-register the subscription builders under
  // `window.pyana.builders.subscription`. The shared turn-builders
  // registry imports this module for the side effect.
  if (!window.pyana) window.pyana = {};
  if (!window.pyana.builders) window.pyana.builders = {};
  window.pyana.builders.subscription = {
    publish,
    consume,
    grant_publisher,
    grant_consumer,
  };
}

export {
  publish,
  consume,
  grant_publisher,
  grant_consumer,
  // Re-export slot indices so the inspector + tests can pin them.
  SEQ_HEAD_SLOT,
  SEQ_TAIL_SLOT,
  CAPACITY_SLOT,
  PUBLISHERS_ROOT_SLOT,
  CONSUMERS_ROOT_SLOT,
  OWNER_PK_HASH_SLOT,
  MESSAGE_ROOT_SLOT,
  LATEST_PAYLOAD_SLOT,
};

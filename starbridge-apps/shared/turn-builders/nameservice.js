// starbridge-apps/shared/turn-builders/nameservice.js
//
// First typed turn-builder for starbridge-apps (per STARBRIDGE-PLAN §4.8 + §4.6).
// Pattern matches the example in starbridge-apps/nameservice/README.md and the
// Rust builders in src/lib.rs (via AppCipherclerk::make_action).
//
// Exports:
//   - Hash helpers (nameHash, ownerHash, ... ) for audit/reuse.
//   - Builder fns that return plain TurnSpec objects (the "typed" shape
//     consumed by signTurn / runtime submit).
//   - createNameserviceTurnBuilders(runtime) — runtime-bound preset for
//     InMemoryRuntime / RemoteRuntime use in Studio / <pyana-app> context.
//     The runtime param (PyanaRuntime shape) allows future typed calls
//     e.g. runtime.blake3(...) instead of window.
//
// All policy (slot caveats, VK, constraints) lives in the Rust crate.
// JS is the thinnest possible shim.
//
// This module is the single source of truth for the JS-side nameservice
// turn shape. The pages/ version and others should re-export from here.

const NAME_HASH_SLOT      = 2;
const OWNER_HASH_SLOT     = 3;
const EXPIRY_SLOT         = 4;
const REVOKED_SLOT        = 5;
const RESOLVE_TARGET_SLOT = 6;

const TOPIC_REGISTERED   = 'name-registered';
const TOPIC_RENEWED      = 'name-renewed';
const TOPIC_TRANSFERRED  = 'name-transferred';
const TOPIC_REVOKED      = 'name-revoked';
const TOPIC_TARGET_SET   = 'name-target-set';

const REVOKED_TOMBSTONE_PREFIX = new TextEncoder().encode('pyana-nameservice-revoked:');

// --- pure helpers (usable in any context, including tests / node) ---

function asUint8(input) {
  if (input == null) return new Uint8Array(0);
  if (input instanceof Uint8Array) return input;
  if (Array.isArray(input)) return new Uint8Array(input);
  if (typeof input === 'string') {
    const s = input.startsWith('0x') ? input.slice(2) : input;
    if (/^[0-9a-fA-F]*$/.test(s) && s.length % 2 === 0 && s.length > 0) {
      const out = new Uint8Array(s.length / 2);
      for (let i = 0; i < out.length; i += 1) {
        out[i] = parseInt(s.slice(i * 2, i * 2 + 2), 16);
      }
      return out;
    }
    return new TextEncoder().encode(input);
  }
  throw new TypeError('asUint8: unsupported input');
}

function concatBytes(...parts) {
  const total = parts.reduce((n, p) => n + p.length, 0);
  const out = new Uint8Array(total);
  let off = 0;
  for (const p of parts) { out.set(p, off); off += p.length; }
  return out;
}

async function blake3Field(bytes, runtime = null) {
  if (runtime && typeof runtime.blake3 === 'function') {
    const out = await runtime.blake3(bytes);
    return Array.from(asUint8(out));
  }
  if (typeof window !== 'undefined' && window.pyana?.blake3) {
    const out = await window.pyana.blake3(bytes);
    return Array.from(asUint8(out));
  }
  // Fallback (demo only — not executor-identical)
  const buf = await crypto.subtle.digest('SHA-256', asUint8(bytes));
  return Array.from(new Uint8Array(buf));
}

function u64BE(n) {
  const view = new Uint8Array(32);
  const bn = BigInt(n);
  for (let i = 0; i < 8; i += 1) {
    view[31 - i] = Number((bn >> BigInt(i * 8)) & 0xffn);
  }
  return Array.from(view);
}

async function nameHash(name, runtime) {
  return blake3Field(new TextEncoder().encode(String(name)), runtime);
}

async function ownerHash(owner, runtime) {
  return blake3Field(asUint8(owner), runtime);
}

async function revokedTombstone(name, runtime) {
  return blake3Field(concatBytes(REVOKED_TOMBSTONE_PREFIX, new TextEncoder().encode(String(name))), runtime);
}

async function resolveTarget(uriOrBytes, runtime) {
  const bytes = asUint8(uriOrBytes);
  if (bytes.length === 32 && typeof uriOrBytes !== 'string') {
    return Array.from(bytes);
  }
  return blake3Field(bytes, runtime);
}

// --- core builders (return TurnSpec; "typed" by the known shape + slots) ---

async function register_name(registryUri, { name, owner, expiry }, runtime = null) {
  const nh = await nameHash(name, runtime);
  const oh = await ownerHash(owner, runtime);
  const ef = u64BE(expiry);
  return {
    target: registryUri,
    method: 'register_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: NAME_HASH_SLOT,  value: nh },
      { kind: 'SetField',  cell: registryUri, index: OWNER_HASH_SLOT, value: oh },
      { kind: 'SetField',  cell: registryUri, index: EXPIRY_SLOT,     value: ef },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_REGISTERED, data: [nh, oh, ef] },
    ],
  };
}

async function renew_name(registryUri, { name, expiry }, runtime = null) {
  const nh = await nameHash(name, runtime);
  const ef = u64BE(expiry);
  return {
    target: registryUri,
    method: 'renew_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: EXPIRY_SLOT, value: ef },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_RENEWED, data: [nh, ef] },
    ],
  };
}

async function transfer_name(registryUri, { name, old_owner, new_owner }, runtime = null) {
  const nh = await nameHash(name, runtime);
  const oldH = await ownerHash(old_owner, runtime);
  const newH = await ownerHash(new_owner, runtime);
  return {
    target: registryUri,
    method: 'transfer_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: OWNER_HASH_SLOT, value: newH },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_TRANSFERRED, data: [nh, oldH, newH] },
    ],
  };
}

async function revoke_name(registryUri, { name }, runtime = null) {
  const nh = await nameHash(name, runtime);
  const tomb = await revokedTombstone(name, runtime);
  return {
    target: registryUri,
    method: 'revoke_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: REVOKED_SLOT, value: tomb },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_REVOKED, data: [nh, tomb] },
    ],
  };
}

async function set_target_name(registryUri, { name, target }, runtime = null) {
  const nh = await nameHash(name, runtime);
  const tg = await resolveTarget(target, runtime);
  return {
    target: registryUri,
    method: 'set_name_target',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: RESOLVE_TARGET_SLOT, value: tg },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_TARGET_SET, data: [nh, tg] },
    ],
  };
}

// --- runtime-bound API (the "typed" entrypoint for Studio / SDK consumers) ---

export function createNameserviceTurnBuilders(runtime) {
  // runtime: PyanaRuntime (or compatible with .blake3 etc.)
  const bound = (fn) => async (uri, args) => fn(uri, args, runtime);
  return {
    register_name: bound(register_name),
    renew_name: bound(renew_name),
    transfer_name: bound(transfer_name),
    revoke_name: bound(revoke_name),
    set_target_name: bound(set_target_name),
    // aliases used by forms
    register: bound(register_name),
    renew: bound(renew_name),
    transfer: bound(transfer_name),
    revoke: bound(revoke_name),
    set_target: bound(set_target_name),
  };
}

// --- default / window registration (cclerk path, for pages that have signTurn) ---

async function submitViaWindow(turnSpec) {
  if (typeof window === 'undefined' || !window.pyana?.signTurn) {
    console.warn('[nameservice-shared] window.pyana.signTurn not available; turnSpec was', turnSpec);
    throw new Error('nameservice: window.pyana.signTurn is not available');
  }
  return window.pyana.signTurn(turnSpec);
}

const windowBuilders = {
  register_name: async (u, a) => submitViaWindow(await register_name(u, a)),
  renew_name: async (u, a) => submitViaWindow(await renew_name(u, a)),
  transfer_name: async (u, a) => submitViaWindow(await transfer_name(u, a)),
  revoke_name: async (u, a) => submitViaWindow(await revoke_name(u, a)),
  set_target_name: async (u, a) => submitViaWindow(await set_target_name(u, a)),
  register: async (u, a) => submitViaWindow(await register_name(u, a)),
  renew: async (u, a) => submitViaWindow(await renew_name(u, a)),
  transfer: async (u, a) => submitViaWindow(await transfer_name(u, a)),
  revoke: async (u, a) => submitViaWindow(await revoke_name(u, a)),
  set_target: async (u, a) => submitViaWindow(await set_target_name(u, a)),
};

if (typeof window !== 'undefined') {
  window.pyana ??= {};
  window.pyana.builders ??= {};
  window.pyana.builders.nameservice = {
    ...(window.pyana.builders.nameservice ?? {}),
    ...windowBuilders,
  };
}

// Public surface
export {
  // builders (pure + TurnSpec return)
  register_name,
  renew_name,
  transfer_name,
  revoke_name,
  set_target_name,
  // helpers
  nameHash,
  ownerHash,
  revokedTombstone,
  resolveTarget,
  u64BE,
  blake3Field,
  // consts
  NAME_HASH_SLOT,
  OWNER_HASH_SLOT,
  EXPIRY_SLOT,
  REVOKED_SLOT,
  RESOLVE_TARGET_SLOT,
  TOPIC_REGISTERED,
  TOPIC_RENEWED,
  TOPIC_TRANSFERRED,
  TOPIC_REVOKED,
  TOPIC_TARGET_SET,
};

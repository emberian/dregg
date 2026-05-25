// starbridge-apps/nameservice/pages/turn-builders.js
//
// JS shim wrapping `window.pyana.signTurn(turnSpec)` (the extension
// cclerk API — see extension/src/page.ts) with name-domain
// conveniences that mirror the Rust turn-builders in src/lib.rs:
//
//   register_name(registryUri, { name, owner, expiry })
//   renew_name(registryUri, { name, expiry })
//   transfer_name(registryUri, { name, old_owner, new_owner })
//   revoke_name(registryUri, { name })
//   set_target_name(registryUri, { name, target })
//
// Each builder is async and resolves to whatever `signTurn` returns
// (typically a turn receipt). When `window.pyana.signTurn` is absent
// (no extension installed, no in-page bridge wired) the builder
// surfaces the prepared turnSpec via `console.warn` and rethrows.
//
// All hashing matches the Rust convention:
//   - name_hash    = blake3(name_bytes)
//   - owner_hash   = blake3(owner_pubkey_bytes)
//   - tombstone    = blake3(b"pyana-nameservice-revoked:" || name_bytes)
//   - expiry_field = u64 big-endian-padded to 32 bytes
//   - target_field = blake3(target_uri_bytes) (when given as a URI)

// Slot indices — mirror constants in src/lib.rs.
const NAME_HASH_SLOT      = 2;
const OWNER_HASH_SLOT     = 3;
const EXPIRY_SLOT         = 4;
const REVOKED_SLOT        = 5;
const RESOLVE_TARGET_SLOT = 6;

// Event topic names — mirror src/lib.rs symbol() calls.
const TOPIC_REGISTERED   = 'name-registered';
const TOPIC_RENEWED      = 'name-renewed';
const TOPIC_TRANSFERRED  = 'name-transferred';
const TOPIC_REVOKED      = 'name-revoked';
const TOPIC_TARGET_SET   = 'name-target-set';

const REVOKED_TOMBSTONE_PREFIX = new TextEncoder().encode('pyana-nameservice-revoked:');

// ─── helpers ─────────────────────────────────────────────────────────────

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

async function blake3Field(bytes) {
  // Prefer pyana's wasm-backed blake3 (matches the Rust executor exactly).
  if (typeof window !== 'undefined' && window.pyana?.blake3) {
    const out = await window.pyana.blake3(bytes);
    return Array.from(asUint8(out));
  }
  // Fallback: SubtleCrypto SHA-256. NOTE: this is *not* the same hash
  // the executor computes; it is a deterministic-enough placeholder for
  // demo / preview environments where pyana.blake3 isn't wired. Hosts
  // running against a real ledger MUST provide window.pyana.blake3.
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

async function nameHash(name) {
  return blake3Field(new TextEncoder().encode(String(name)));
}

async function ownerHash(owner) {
  return blake3Field(asUint8(owner));
}

async function revokedTombstone(name) {
  return blake3Field(concatBytes(REVOKED_TOMBSTONE_PREFIX, new TextEncoder().encode(String(name))));
}

async function resolveTarget(uriOrBytes) {
  // If the caller hands us a URI string, hash it. If they hand us 32
  // bytes (the target is already a content-addressed field element),
  // pass through.
  const bytes = asUint8(uriOrBytes);
  if (bytes.length === 32 && typeof uriOrBytes !== 'string') {
    return Array.from(bytes);
  }
  return blake3Field(bytes);
}

async function submit(turnSpec) {
  if (typeof window === 'undefined' || !window.pyana?.signTurn) {
    console.warn('[nameservice] window.pyana.signTurn not available; turnSpec was', turnSpec);
    throw new Error('nameservice: window.pyana.signTurn is not available');
  }
  return window.pyana.signTurn(turnSpec);
}

// ─── builders ────────────────────────────────────────────────────────────

async function register_name(registryUri, { name, owner, expiry }) {
  const nh = await nameHash(name);
  const oh = await ownerHash(owner);
  const ef = u64BE(expiry);
  return submit({
    target: registryUri,
    method: 'register_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: NAME_HASH_SLOT,  value: nh },
      { kind: 'SetField',  cell: registryUri, index: OWNER_HASH_SLOT, value: oh },
      { kind: 'SetField',  cell: registryUri, index: EXPIRY_SLOT,     value: ef },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_REGISTERED, data: [nh, oh, ef] },
    ],
  });
}

async function renew_name(registryUri, { name, expiry }) {
  const nh = await nameHash(name);
  const ef = u64BE(expiry);
  return submit({
    target: registryUri,
    method: 'renew_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: EXPIRY_SLOT, value: ef },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_RENEWED, data: [nh, ef] },
    ],
  });
}

async function transfer_name(registryUri, { name, old_owner, new_owner }) {
  const nh = await nameHash(name);
  const oldH = await ownerHash(old_owner);
  const newH = await ownerHash(new_owner);
  return submit({
    target: registryUri,
    method: 'transfer_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: OWNER_HASH_SLOT, value: newH },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_TRANSFERRED, data: [nh, oldH, newH] },
    ],
  });
}

async function revoke_name(registryUri, { name }) {
  const nh = await nameHash(name);
  const tomb = await revokedTombstone(name);
  return submit({
    target: registryUri,
    method: 'revoke_name',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: REVOKED_SLOT, value: tomb },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_REVOKED, data: [nh, tomb] },
    ],
  });
}

async function set_target_name(registryUri, { name, target }) {
  const nh = await nameHash(name);
  const tg = await resolveTarget(target);
  return submit({
    target: registryUri,
    method: 'set_name_target',
    effects: [
      { kind: 'SetField',  cell: registryUri, index: RESOLVE_TARGET_SLOT, value: tg },
      { kind: 'EmitEvent', cell: registryUri, topic: TOPIC_TARGET_SET, data: [nh, tg] },
    ],
  });
}

// ─── registration ────────────────────────────────────────────────────────

const BUILDERS = {
  register_name,
  renew_name,
  transfer_name,
  revoke_name,
  set_target_name,
  // Convenience aliases for the inspector's mode buttons.
  register: register_name,
  renew: renew_name,
  transfer: transfer_name,
  revoke: revoke_name,
  set_target: set_target_name,
};

if (typeof window !== 'undefined') {
  window.pyana ??= {};
  window.pyana.builders ??= {};
  window.pyana.builders.nameservice = {
    ...(window.pyana.builders.nameservice ?? {}),
    ...BUILDERS,
  };
}

export {
  register_name,
  renew_name,
  transfer_name,
  revoke_name,
  set_target_name,
  // Public helpers so a host can audit / reuse the hashing convention.
  nameHash,
  ownerHash,
  revokedTombstone,
  resolveTarget,
  u64BE,
  // Slot indices.
  NAME_HASH_SLOT,
  OWNER_HASH_SLOT,
  EXPIRY_SLOT,
  REVOKED_SLOT,
  RESOLVE_TARGET_SLOT,
};

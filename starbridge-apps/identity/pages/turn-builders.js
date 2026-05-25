// starbridge-apps/identity/pages/turn-builders.js
//
// JS shim wrapping `window.pyana.signTurn(turnSpec)` (the extension
// wallet API — see extension/src/page.ts) with credential-domain
// conveniences that mirror the Rust turn-builders in src/lib.rs.
//
// Pattern matches starbridge-apps/nameservice/pages/turn-builders.js:
// the JS produces the right `turnSpec` shape; all *policy* lives in the
// Rust crate (the audit-trail and proof code path see only Rust types).
//
// Builders:
//
//   issue_credential(issuerCellHex, schemaName, subjectHex, claims)
//   revoke_credential(issuerCellHex, credentialIdHex, newRootHex)
//   present_credential({ credentialUri, disclose, predicates, anonymous })
//   verify_presentation({ verifierUri, presentationJson, schema, disclose, predicate })
//
// Each builder is async and resolves to either the turn receipt (for
// on-ledger actions: issue/revoke/verify) or the presentation bytes (for
// present, which is off-ledger by default — present_credential's
// build_present_credential_action is an *optional* anchor and the holder
// chooses whether to commit it).

// Slot indices — mirror constants in src/lib.rs.
const SCHEMA_COMMITMENT_SLOT  = 2;
const ISSUANCE_COUNTER_SLOT   = 3;
const REVOCATION_ROOT_SLOT    = 4;
const ISSUER_AUTH_ROOT_SLOT   = 5;

// Event topic names — mirror src/lib.rs symbol() calls.
const TOPIC_ISSUED    = 'credential-issued';
const TOPIC_REVOKED   = 'credential-revoked';
const TOPIC_PRESENTED = 'credential-presented';
const TOPIC_ACCEPTED  = 'presentation-accepted';
const TOPIC_REJECTED  = 'presentation-rejected';

// ─── helpers ─────────────────────────────────────────────────────────────

function u64BE(n) {
  // Encode as a 32-byte BE-padded value (matches u64_field in src/lib.rs).
  const view = new Uint8Array(32);
  const bn = BigInt(n);
  for (let i = 0; i < 8; i += 1) {
    view[31 - i] = Number((bn >> BigInt(i * 8)) & 0xffn);
  }
  return Array.from(view);
}

function bool32(b) {
  const view = new Uint8Array(32);
  view[31] = b ? 1 : 0;
  return Array.from(view);
}

async function blake3Bytes(s) {
  if (window.pyana?.blake3) return window.pyana.blake3(s);
  // Fallback hash via SubtleCrypto if pyana's blake3 isn't wired.
  const buf = new TextEncoder().encode(s);
  const hash = await crypto.subtle.digest('SHA-256', buf);
  return Array.from(new Uint8Array(hash));
}

// ─── builders ────────────────────────────────────────────────────────────

async function issue_credential(issuerCellHex, schemaName, subjectHex, claims) {
  // Step 1: invoke pyana-credentials' issue() through wasm to mint the
  // signed credential. The wasm binding is responsible for hashing the
  // schema, calling MacaroonToken::mint, applying the attenuation, and
  // returning a `Credential` JSON.
  const credential = await window.pyana.credentials.issue({
    schemaName,
    subject: subjectHex,
    claims,
  });
  // Step 2: read the issuer cell's current ISSUANCE_COUNTER_SLOT to
  // compute new_counter = old + 1 (MonotonicSequence will reject any
  // other delta at execution time).
  const oldCounter = await window.pyana.cell.readField(issuerCellHex, ISSUANCE_COUNTER_SLOT);
  const newCounter = (BigInt(oldCounter ?? 0) + 1n).toString();
  // Step 3: read the current revocation root (we re-write it unchanged
  // — Monotonic accepts new == old).
  const revRoot = await window.pyana.cell.readField(issuerCellHex, REVOCATION_ROOT_SLOT)
    ?? new Array(32).fill(0);

  // Step 4: emit the issue turn — three effects, matching
  // `build_issue_credential_action`.
  return window.pyana.signTurn({
    target: issuerCellHex,
    method: 'issue_credential',
    effects: [
      { kind: 'SetField',  cell: issuerCellHex, index: ISSUANCE_COUNTER_SLOT, value: u64BE(newCounter) },
      { kind: 'SetField',  cell: issuerCellHex, index: REVOCATION_ROOT_SLOT,  value: revRoot },
      { kind: 'EmitEvent', cell: issuerCellHex, topic: TOPIC_ISSUED,
        data: [credential.id, credential.holder_id, u64BE(newCounter)] },
    ],
    metadata: { credential },
  });
}

async function revoke_credential(issuerCellHex, credentialIdHex, newRootHex) {
  return window.pyana.signTurn({
    target: issuerCellHex,
    method: 'revoke_credential',
    effects: [
      { kind: 'SetField',  cell: issuerCellHex, index: REVOCATION_ROOT_SLOT, value: newRootHex },
      { kind: 'EmitEvent', cell: issuerCellHex, topic: TOPIC_REVOKED,
        data: [credentialIdHex, newRootHex] },
    ],
  });
}

async function present_credential({ credentialUri, disclose, predicates, anonymous }) {
  // The bulk of present is off-ledger: produce a Presentation via wasm
  // (which routes through pyana-credentials::present /
  // pyana-credentials::present_anonymous).
  const presentation = await window.pyana.credentials[anonymous ? 'presentAnonymous' : 'present']({
    credentialUri,
    disclose,
    predicates,
  });

  // The userspace anchor is OPTIONAL — the holder may emit a
  // `credential-presented` event on their own cell for an audit trail.
  // We default to NO emission to preserve unlinkability; hosts that
  // want the audit can call build_present_credential_action separately.
  return { presentation };
}

async function verify_presentation({ verifierUri, presentationJson, schema, disclose, predicate }) {
  // Step 1: run verification through wasm (calls pyana_credentials::verify).
  const presentation = JSON.parse(presentationJson);
  const opts = {
    expected_schema: schema || null,
    expected_disclosure: disclose ?? [],
    expected_predicates: parsePredicateSpec(predicate),
  };
  const verifyResult = await window.pyana.credentials.verify({
    presentation,
    options: opts,
  });

  // Step 2: emit the accept/reject event on the verifier cell.
  const topic = verifyResult.accept ? TOPIC_ACCEPTED : TOPIC_REJECTED;
  const commitment = presentation.proof?.revealed_facts_commitment_hash
                    ?? new Array(32).fill(0);
  await window.pyana.signTurn({
    target: verifierUri,
    method: 'verify_presentation',
    effects: [
      { kind: 'EmitEvent', cell: verifierUri, topic,
        data: [commitment, bool32(verifyResult.accept),
               u64BE((presentation.predicate_proofs ?? []).length)] },
    ],
  });
  return verifyResult;
}

function parsePredicateSpec(spec) {
  if (!spec) return [];
  // "verification_level Gte 1" → [{attribute, predicate: {Gte: 1}}]
  const m = String(spec).trim().match(/^(\S+)\s+(Gte|Lte|Eq)\s+(\d+)$/);
  if (!m) return [];
  return [{
    attribute: m[1],
    predicate: { [m[2]]: Number(m[3]) },
  }];
}

// ─── registration ────────────────────────────────────────────────────────

const BUILDERS = {
  issue_credential,
  revoke_credential,
  present_credential,
  verify_presentation,
};

if (typeof window !== 'undefined') {
  window.pyana ??= {};
  window.pyana.builders ??= {};
  window.pyana.builders.identity = {
    ...(window.pyana.builders.identity ?? {}),
    ...BUILDERS,
  };
}

export {
  issue_credential,
  revoke_credential,
  present_credential,
  verify_presentation,
  // exported constants so a host can audit the slot indices it's writing.
  SCHEMA_COMMITMENT_SLOT,
  ISSUANCE_COUNTER_SLOT,
  REVOCATION_ROOT_SLOT,
  ISSUER_AUTH_ROOT_SLOT,
};

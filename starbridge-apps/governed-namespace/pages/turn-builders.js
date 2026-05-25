// starbridge-apps/governed-namespace/pages/turn-builders.js
//
// Cipherclerk-named turn-builder presets for the governed-namespace app.
// Each builder produces the canonical turnSpec shape that
// `window.pyana.signTurn(turnSpec)` (the extension cclerk API — see
// extension/src/page.ts) consumes. The builders never touch raw private
// keys; signing always crosses the cclerk boundary.
//
// Mirrors the four `build_*_action` helpers in
// starbridge-apps/governed-namespace/src/lib.rs:
//
//   propose_table_update({ target, routes, description, dispute_window_height })
//   vote_on_proposal({ target, prior_proposal_root_hex, vote_kind, vote_weight })
//   commit_table_update({ target, routes, new_version,
//                         governance_committee_root_hex, threshold_sig_hex })
//   register_service({ target, path, target_uri })
//
// Registers under both:
//   window.pyana.builders['governed-namespace'].<method>
//   window.pyanaTurnBuilders['governed-namespace'].<method>
//
// The dual registration is for back-compat with the inspector module
// which imported from `window.pyanaTurnBuilders`. New code should prefer
// `window.pyana.builders['governed-namespace']` for consistency with
// nameservice / identity / subscription.

// Slot indices — mirror constants in src/lib.rs.
const ROUTE_TABLE_ROOT_SLOT          = 0;
const VERSION_SLOT                   = 1;
const GOVERNANCE_COMMITTEE_ROOT_SLOT = 2;
const THRESHOLD_SLOT                 = 3;
const DISPUTE_WINDOW_HEIGHT_SLOT     = 4;
const PENDING_PROPOSAL_ROOT_SLOT     = 5;

const METHOD_PROPOSE  = 'propose_table_update';
const METHOD_VOTE     = 'vote_on_proposal';
const METHOD_COMMIT   = 'commit_table_update';
const METHOD_REGISTER = 'register_service';

const TOPIC_PROPOSED      = 'namespace-proposal-submitted';
const TOPIC_VOTED         = 'namespace-vote-cast';
const TOPIC_COMMITTED     = 'namespace-table-committed';
const TOPIC_SERVICE_BOUND = 'namespace-service-registered';

const VOTE_TAG_APPROVE = 1;
const VOTE_TAG_REJECT  = 2;

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

function u64BE(n) {
  const out = new Uint8Array(32);
  let v = BigInt(n);
  for (let i = 31; i >= 24 && v > 0n; i -= 1) {
    out[i] = Number(v & 0xffn);
    v >>= 8n;
  }
  return Array.from(out);
}

async function blake3(bytes) {
  if (typeof window !== 'undefined' && window.pyana?.blake3) {
    const out = await window.pyana.blake3(bytes);
    return Array.from(asUint8(out));
  }
  // Fallback to SubtleCrypto SHA-256 — NOT the same hash the executor
  // uses, but deterministic enough for demo/dev environments where
  // pyana.blake3 isn't wired.
  const buf = await crypto.subtle.digest('SHA-256', asUint8(bytes));
  return Array.from(new Uint8Array(buf));
}

async function routesCommitment(routes) {
  // Content-address the proposed route table as a hash of its
  // canonical JSON serialization. The Rust side computes the same
  // commitment via blake3 over the canonical encoding; a fully-faithful
  // implementation would route through wasm. Hosts wanting exact byte
  // agreement should expose `window.pyana.governedNamespace.commitRoutes(...)`.
  if (typeof window !== 'undefined' && window.pyana?.governedNamespace?.commitRoutes) {
    return Array.from(asUint8(await window.pyana.governedNamespace.commitRoutes(routes)));
  }
  const canonical = JSON.stringify(routes);
  return blake3(canonical);
}

async function descriptionCommitment(description) {
  return blake3(description ?? '');
}

async function pathCommitment(path) {
  return blake3(path ?? '');
}

async function targetCommitment(targetUri) {
  return blake3(targetUri ?? '');
}

// ─── builders ────────────────────────────────────────────────────────────

async function propose_table_update({ target, routes, description, dispute_window_height }) {
  const proposalRoot = await routesCommitment(routes);
  const descCommit   = await descriptionCommitment(description);
  return {
    target,
    method: METHOD_PROPOSE,
    effects: [
      { kind: 'SetField', cell: target, index: PENDING_PROPOSAL_ROOT_SLOT, value: proposalRoot },
      { kind: 'EmitEvent', cell: target, topic: TOPIC_PROPOSED,
        data: [proposalRoot, descCommit, u64BE(dispute_window_height ?? 0)] },
    ],
    metadata: { routes, description, dispute_window_height },
  };
}

async function vote_on_proposal({ target, prior_proposal_root_hex, vote_kind, vote_weight }) {
  const priorRoot = prior_proposal_root_hex
    ? Array.from(asUint8(prior_proposal_root_hex))
    : new Array(32).fill(0);
  const tag = (String(vote_kind).toLowerCase() === 'reject') ? VOTE_TAG_REJECT : VOTE_TAG_APPROVE;
  return {
    target,
    method: METHOD_VOTE,
    effects: [
      { kind: 'EmitEvent', cell: target, topic: TOPIC_VOTED,
        data: [priorRoot, u64BE(tag), u64BE(vote_weight ?? 1)] },
    ],
    metadata: { vote_kind, vote_weight },
  };
}

async function commit_table_update({
  target,
  routes,
  new_version,
  governance_committee_root_hex,
  threshold_sig_hex,
}) {
  const newRoot = await routesCommitment(routes);
  const committee = governance_committee_root_hex
    ? Array.from(asUint8(governance_committee_root_hex))
    : new Array(32).fill(0);
  return {
    target,
    method: METHOD_COMMIT,
    authorization: { kind: 'Custom', payload_hex: threshold_sig_hex ?? '' },
    effects: [
      { kind: 'SetField',  cell: target, index: ROUTE_TABLE_ROOT_SLOT,          value: newRoot },
      { kind: 'SetField',  cell: target, index: VERSION_SLOT,                   value: u64BE(new_version ?? 1) },
      { kind: 'SetField',  cell: target, index: GOVERNANCE_COMMITTEE_ROOT_SLOT, value: committee },
      { kind: 'SetField',  cell: target, index: PENDING_PROPOSAL_ROOT_SLOT,     value: new Array(32).fill(0) },
      { kind: 'EmitEvent', cell: target, topic: TOPIC_COMMITTED,
        data: [newRoot, u64BE(new_version ?? 1), committee] },
    ],
    metadata: { routes, new_version },
  };
}

async function register_service({ target, path, target_uri }) {
  const pathCommit = await pathCommitment(path);
  const targetCommit = await targetCommitment(target_uri);
  return {
    target,
    method: METHOD_REGISTER,
    effects: [
      { kind: 'EmitEvent', cell: target, topic: TOPIC_SERVICE_BOUND,
        data: [pathCommit, targetCommit] },
    ],
    metadata: { path, target_uri },
  };
}

// ─── registration ────────────────────────────────────────────────────────

const BUILDERS = {
  [METHOD_PROPOSE]:  propose_table_update,
  [METHOD_VOTE]:     vote_on_proposal,
  [METHOD_COMMIT]:   commit_table_update,
  [METHOD_REGISTER]: register_service,
  propose_table_update,
  vote_on_proposal,
  commit_table_update,
  register_service,
};

if (typeof window !== 'undefined') {
  window.pyana ??= {};
  window.pyana.builders ??= {};
  window.pyana.builders['governed-namespace'] = {
    ...(window.pyana.builders['governed-namespace'] ?? {}),
    ...BUILDERS,
  };
  // Legacy alias — the inspector module imports this name. Keep both
  // surfaces so older host pages don't break.
  window.pyanaTurnBuilders ??= {};
  window.pyanaTurnBuilders['governed-namespace'] = {
    ...(window.pyanaTurnBuilders['governed-namespace'] ?? {}),
    ...BUILDERS,
  };
}

export {
  propose_table_update,
  vote_on_proposal,
  commit_table_update,
  register_service,
  ROUTE_TABLE_ROOT_SLOT,
  VERSION_SLOT,
  GOVERNANCE_COMMITTEE_ROOT_SLOT,
  THRESHOLD_SLOT,
  DISPUTE_WINDOW_HEIGHT_SLOT,
  PENDING_PROPOSAL_ROOT_SLOT,
  METHOD_PROPOSE,
  METHOD_VOTE,
  METHOD_COMMIT,
  METHOD_REGISTER,
  VOTE_TAG_APPROVE,
  VOTE_TAG_REJECT,
  u64BE,
};

// starbridge-apps/shared/runtime-submit.js
//
// The real local-preview submission path for starbridge-apps.
//
// Background. The app pages' turn-builders historically terminated in
// `window.dregg.signTurn(turnSpec)`. In the in-browser preview (the only
// runtime available in the static site build / Playwright smokes) the
// Cipherclerk extension is absent, so `app-boot.js` installs a *read-only*
// `signTurn` stub that returns `{ submitted:false, error:'… read-only' }`.
// The result: every "register name", "issue credential", "publish" button
// failed silently and no real state ever changed.
//
// This module closes that gap WITHOUT touching the frame-embedding lane's
// `app-boot.js`. It drives the real in-memory `DreggRuntime`
// (`window.__starbridgeAppRuntime`, attached by app-boot) directly:
//
//   1. `ensureAppCell(uriHint)` — lazily creates a REAL cell in the runtime
//      (genesis agent + its cell) and returns its real hex cell-id. The
//      app's placeholder URI (e.g. `dregg://cell/registry-default`) is
//      mapped to this real id so every read/write keys off the same cell.
//
//   2. `submitTurnSpec(turnSpec)` — converts a turn-builder TurnSpec (the
//      `{ effects:[{kind:'SetField',cell,index,value}] }` shape) into the
//      wasm `execute_turn` action JSON (`{type:'set_field',cell,index,
//      value_hex}`), executes it as a REAL signed turn through the canonical
//      `TurnExecutor`, and returns a real receipt `{ id: turn_hash, ... }`.
//      `EmitEvent` effects are recorded for the UI but are not wasm actions
//      (the wasm `parse_effects` surface covers set_field/transfer/
//      increment_nonce); the on-ledger state change is the SetField writes.
//
//   3. `installRealSignTurn()` — overrides the read-only `window.dregg.
//      signTurn` stub with a real one routed through (2), and wires
//      `window.dregg.nameservice.listEntries` to enumerate real cells.
//
// All of this is local-preview only. When the real extension cclerk is
// present (`window.dregg` frozen) we DO NOT override it — the extension's
// signing path wins.

const PREVIEW_OWNER_PK =
  // A stable, arbitrary 32-byte owner pubkey for the preview registry cell.
  // Real deployments mint from a real key via the extension cclerk.
  'a17e57a17e57a17e57a17e57a17e57a17e57a17e57a17e57a17e57a17e57a100';

// uriHint (placeholder URI string) -> { cellId (hex), agentIndex }
const cellMap = new Map();
let genesisAgentIndex = null;

function runtime() {
  return typeof window !== 'undefined' ? window.__starbridgeAppRuntime : null;
}

function isExtensionPresent() {
  return typeof window !== 'undefined' && window.dregg && Object.isFrozen(window.dregg);
}

// Normalize a turn-builder field value into a 64-char hex string for the
// wasm `value_hex` action field.
function valueToHex(value) {
  if (value == null) return '0'.repeat(64);
  if (typeof value === 'string') {
    const s = value.startsWith('0x') ? value.slice(2) : value;
    if (/^[0-9a-fA-F]+$/.test(s)) return s.padStart(64, '0').slice(-64);
    // A non-hex string: encode its UTF-8 bytes and zero-pad to 32 bytes.
    const enc = new TextEncoder().encode(value);
    return bytesToHex(enc).padEnd(64, '0').slice(0, 64);
  }
  if (Array.isArray(value) || value instanceof Uint8Array) {
    return bytesToHex(Array.from(value)).padStart(64, '0').slice(-64);
  }
  if (typeof value === 'number' || typeof value === 'bigint') {
    let bn = BigInt(value);
    let h = bn.toString(16);
    return h.padStart(64, '0').slice(-64);
  }
  return '0'.repeat(64);
}

function bytesToHex(arr) {
  return Array.from(arr).map((b) => (b & 0xff).toString(16).padStart(2, '0')).join('');
}

function stripUri(u) {
  return String(u || '').replace(/^dregg:\/\/(cell|credential)\//, '');
}

/**
 * Ensure a real cell exists in the runtime for the given placeholder URI,
 * returning its real hex cell-id. Creates the genesis agent on first call.
 */
export async function ensureAppCell(uriHint) {
  const rt = runtime();
  if (!rt) throw new Error('no in-memory runtime attached (window.__starbridgeAppRuntime)');
  const key = stripUri(uriHint) || 'default';
  if (cellMap.has(key)) return cellMap.get(key).cellId;
  // The hint may already be a real cell-id we created (post URI-rewrite). Map
  // it to the existing entry instead of minting a duplicate agent.
  const existing = lookupCell(uriHint);
  if (existing) {
    cellMap.set(key, existing);
    return existing.cellId;
  }

  if (genesisAgentIndex == null) {
    // The first agent is genesis (born by fiat); its cell is a real ledger
    // entry we can write SetField turns against. We seed a balance so any
    // subsequent app cells can be minted from genesis (each mint debits a fee).
    const agent = await rt.createAgent(`starbridge-${key}`, 1_000_000);
    genesisAgentIndex = Number(agent.agent_index ?? 0);
    const entry = { cellId: agent.cell_id, agentIndex: genesisAgentIndex };
    cellMap.set(key, entry);
    return entry.cellId;
  }

  // Subsequent app cells: mint a fresh agent+cell (idx >= 1). Each becomes a
  // real cell in the ledger. We use createAgent (not factory mint) so the
  // cell is born writable; the canonical slot-caveat enforcement is proven
  // in the Rust executor tests (tests/integration_*.rs).
  const agent = await rt.createAgent(`starbridge-${key}`, 0);
  const entry = { cellId: agent.cell_id, agentIndex: Number(agent.agent_index) };
  cellMap.set(key, entry);
  return entry.cellId;
}

function lookupCell(uriOrId) {
  const key = stripUri(uriOrId) || 'default';
  if (cellMap.has(key)) return cellMap.get(key);
  // Maybe the caller already passed a real hex cell-id we created.
  for (const v of cellMap.values()) {
    if (v.cellId === stripUri(uriOrId)) return v;
  }
  return null;
}

/**
 * Submit a turn-builder TurnSpec as a real turn through the in-memory
 * runtime. Returns a real receipt-shaped object.
 */
export async function submitTurnSpec(turnSpec) {
  const rt = runtime();
  if (!rt) throw new Error('no in-memory runtime attached');
  const targetUri = turnSpec.target || (turnSpec.effects?.[0]?.cell);
  // Make sure the target cell exists; resolve to real id + owning agent.
  await ensureAppCell(targetUri);
  const cellEntry = lookupCell(targetUri);
  if (!cellEntry) throw new Error(`no runtime cell for ${targetUri}`);

  // Capture the human-readable name label for the registry view (preview
  // only — the ledger stores the name *hash*, not the cleartext name).
  if (turnSpec.name && typeof window !== 'undefined') {
    window.__starbridgeNameLabels = window.__starbridgeNameLabels || {};
    window.__starbridgeNameLabels[cellEntry.cellId] = String(turnSpec.name);
  }

  const actions = [];
  for (const eff of turnSpec.effects || []) {
    if (eff.kind === 'SetField') {
      actions.push({
        type: 'set_field',
        cell: cellEntry.cellId,
        index: Number(eff.index),
        value_hex: valueToHex(eff.value),
      });
    }
    // EmitEvent is UI/audit-only here (not in the wasm action surface).
  }

  if (actions.length === 0) {
    // A no-state turn (e.g. a pure present/verify with only events). Treat as
    // accepted but flag that nothing hit the ledger.
    return {
      id: '',
      submitted: true,
      method: turnSpec.method || '',
      note: 'no on-ledger SetField effects in this turn (event-only)',
    };
  }

  // `fee` here is the turn's computron budget (debited from the agent's
  // balance). Genesis was seeded with a large balance; give each turn ample
  // budget so multi-effect actions (register writes 3 slots) commit.
  const result = await rt.executeTurn(cellEntry.agentIndex, actions, 1_000_000);
  if (result && result.status === 'rejected') {
    throw new Error(`turn rejected: ${result.error || 'unknown'} at ${JSON.stringify(result.at_action)}`);
  }
  return {
    id: result?.turn_hash || '',
    turnId: result?.turn_hash || '',
    submitted: true,
    method: turnSpec.method || '',
    status: result?.status || 'committed',
    post_state_hash: result?.post_state_hash || '',
    computrons_used: result?.computrons_used ?? 0,
  };
}

/**
 * Read a slot from the real runtime cell behind a placeholder URI.
 * Returns the raw hex string (matching get_cell_state's `fields` shape).
 */
export function readAppField(uriOrId, slot) {
  const rt = runtime();
  if (!rt) return null;
  const entry = lookupCell(uriOrId);
  const id = entry ? entry.cellId : stripUri(uriOrId);
  try {
    const cell = rt.getCell(id).value;
    const fields = cell?.fields || cell?.state_fields || cell?.slots || [];
    return fields[Number(slot)] ?? null;
  } catch {
    return null;
  }
}

/**
 * Install a REAL window.dregg.signTurn that routes through the in-memory
 * runtime, plus real cell field reads and a real nameservice enumerator.
 * No-op when the extension cclerk owns a frozen window.dregg.
 */
export function installRealSignTurn() {
  if (typeof window === 'undefined') return;
  if (isExtensionPresent()) return; // extension wins; never override it.
  window.dregg = window.dregg || {};
  const api = window.dregg;

  // Real signing path (replaces app-boot's read-only stub).
  api.signTurn = async (turnSpec) => submitTurnSpec(turnSpec);

  // Real field reads keyed on our cell map (so the inspectors that call
  // readField against the placeholder URI see the real cell).
  api.cell = api.cell || {};
  api.cell.readField = async (uriOrId, slot) => readAppField(uriOrId, slot);

  // Real readCell (full state) for inspectors that prefer it.
  api.readCell = async (uri) => {
    const rt = runtime();
    if (!rt) return null;
    const entry = lookupCell(uri);
    const id = entry ? entry.cellId : stripUri(uri);
    try {
      const cell = rt.getCell(id).value;
      return { state: { fields: cell?.fields || [] }, ...cell };
    } catch {
      return null;
    }
  };

  // Real nameservice enumerator: surface the cells we've created with their
  // current slot values (one registered name per registry cell in preview).
  api.nameservice = api.nameservice || {};
  api.nameservice.listEntries = async () => {
    const rt = runtime();
    if (!rt) return [];
    const out = [];
    for (const [, entry] of cellMap) {
      try {
        const cell = rt.getCell(entry.cellId).value;
        const f = cell?.fields || [];
        const nameHash = f[2];
        if (!nameHash || isZeroHex(nameHash)) continue;
        out.push({
          uri: `dregg://cell/${entry.cellId}`,
          name: window.__starbridgeNameLabels?.[entry.cellId] || shortHex(nameHash),
          owner_hash: f[3],
          expiry: hexToU64(f[4]),
          revoked: !isZeroHex(f[5]),
        });
      } catch { /* skip */ }
    }
    return out;
  };
}

function isZeroHex(h) {
  if (!h) return true;
  const s = String(h).replace(/^0x/, '');
  return /^0*$/.test(s);
}

function shortHex(h) {
  const s = String(h || '').replace(/^0x/, '');
  return s.length > 12 ? `${s.slice(0, 6)}…${s.slice(-4)}` : s;
}

function hexToU64(h) {
  if (!h) return 0;
  const s = String(h).replace(/^0x/, '');
  try { return Number(BigInt('0x' + (s || '0'))); } catch { return 0; }
}

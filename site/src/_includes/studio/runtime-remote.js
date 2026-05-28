/**
 * RemoteRuntime — read-only Runtime over a live dregg federation node's HTTP API.
 *
 * Mirrors the API shape of createInMemoryRuntime, but every mutation throws
 * NotPermitted: this runtime is a viewport, not a controller. The live node
 * decides what writes happen.
 *
 * Polling: every POLL_INTERVAL_MS we refresh /status and /api/cells. If the
 * status height or the cell list shape changes, we bump `version` (and `cursor`,
 * if height moved) so dependent signals re-render. Network failures are logged
 * once per failure and the previously-cached value is retained — we don't
 * thrash on flaky links and we don't error-storm the console.
 *
 * The endpoint conventions match explorer/api.js (status at /status, cells at
 * /api/cells, single cell at /api/cell/<id>). We intentionally don't import
 * api.js — that module is bound to localStorage-configured base URL + the
 * explorer's auth flow; this runtime takes its base URL explicitly.
 *
 * CORS realism: when used against devnet.dregg.fg-goose.online from a
 * browser-localhost origin the fetches will reject with a CORS error. The
 * runtime still constructs cleanly; signals stay null until the network
 * cooperates. (FOLLOWUP-07: now surfaces actionable guidance in logs for
 * Starbridge users; see improved logOnce + getJSON catch.)
 */

import { attachRuntimeObjectAdapter } from './runtime-object-adapter.js';

const POLL_INTERVAL_MS = 5000;

const CAPS = Object.freeze({
  read: true,
  mutate: false,
  debug: false,
  timeTravel: false,
});

function notPermitted(op) {
  return () => {
    throw new Error(`NotPermitted: RemoteRuntime is read-only (${op})`);
  };
}

export async function createRemoteRuntime({ signals, baseUrl }) {
  if (!signals || typeof signals.signal !== 'function') {
    throw new Error('createRemoteRuntime: signals.signal is required');
  }
  const { signal } = signals;
  const base = String(baseUrl || '').replace(/\/+$/, '');

  const version = signal(0);
  const cursor = signal(0);
  const events = new EventTarget();

  // Observability live events (Task #30). Same signal shape as InMemoryRuntime.
  // Populated by SSE consumer below (or empty until /observability/stream connected).
  const traceEventsSignal = signal({ schema_version: 1, event_count: 0, events: [] });
  function getTraceEvents() { return traceEventsSignal; }

  // SSE consumer for remote observability stream (broadcast from node).
  // Uses browser EventSource; pushes parsed JSON log into the signal.
  let obsEs = null;
  if (base && typeof EventSource !== 'undefined') {
    try {
      obsEs = new EventSource(`${base}/observability/stream`);
      obsEs.onmessage = (msg) => {
        try {
          const data = JSON.parse(msg.data || '{}');
          traceEventsSignal.value = data;
        } catch {}
      };
      obsEs.onerror = () => { /* keep last good value */ };
    } catch {}
  }

  // --- Extension bridge for passive debugger (Phase 1/2, STARBRIDGE-FOLLOWUP-06) ---
  // When running inside the Dragon's Egg Cipherclerk extension (iframe panel, or any
  // extension page), chrome.runtime is present. We poll the background's
  // synthesized activity feed (populated from the live WS bus + cclerk ops,
  // exactly the TraceEvent shape for <dregg-activity>) via "dregg:getActivityFeed".
  // This lets RemoteRuntime (and all inspectors including activity) work against
  // *real node events* using the extension's authenticated connection, without
  // needing direct node /observability/stream (avoids CORS/auth issues).
  // High-leverage integration: makes the embedded debugger vision real even before
  // full studio assets are packaged into the extension.
  let extPollTimer = null;
  const isExtensionContext = (typeof chrome !== 'undefined' && chrome.runtime && chrome.runtime.sendMessage);
  if (isExtensionContext) {
    const pollExtFeed = async () => {
      if (destroyed) return;
      try {
        const resp = await new Promise((resolve) => {
          chrome.runtime.sendMessage({ type: 'dregg:getActivityFeed' }, (r) => resolve(r));
        });
        if (resp && resp.result) {
          traceEventsSignal.value = resp.result;
        }
      } catch (e) { /* keep last; background may not be ready */ }
    };
    pollExtFeed();
    extPollTimer = setInterval(pollExtFeed, 2000);  // live enough for debugger feed
  }

  // Cached payloads. Signals are read on demand by callers; we hold the latest
  // successful value here and surface it via per-id signal wrappers.
  let cachedStatus = null;            // last /status response
  let cachedCellList = null;          // last /api/cells response
  let cachedReceipts = null;          // last receipt API response
  let cachedBlocks = null;            // last block/root API response
  let cachedFederations = null;       // explicit or synthesized federation list
  let cachedIntents = null;           // last /api/intents response
  let cachedTokens = null;            // last /api/tokens response (capabilities)
  const cellSignals = new Map();      // id -> signal<CellState | null>
  const cellPending = new Map();      // id -> in-flight Promise (dedupe)
  let listSignal = null;              // signal<CellSummary[] | null>
  let receiptListSignal = null;
  let blockListSignal = null;
  let federationListSignal = null;
  let intentListSignal = null;
  let capabilityListSignal = null;
  const receiptSignals = new Map();
  const blockSignals = new Map();
  const intentSignals = new Map();

  // One AbortController per runtime instance; aborted on destroy(). Every
  // fetch wires this in so destroy() actually cancels in-flight requests.
  const abort = new AbortController();
  let pollTimer = null;
  let destroyed = false;

  // Log each distinct error once per kind to avoid console spam.
  const loggedErrors = new Set();
  function logOnce(key, err) {
    if (loggedErrors.has(key)) return;
    loggedErrors.add(key);
    // eslint-disable-next-line no-console
    console.warn(`[RemoteRuntime] ${key}:`, err && err.message ? err.message : err);
  }

  function isCorsError(err) {
    if (!err) return false;
    const m = (err.message || err.toString() || '').toLowerCase();
    return m.includes('cors') || m.includes('failed to fetch') || (err.name === 'TypeError' && m.includes('fetch'));
  }

  async function getJSON(path) {
    if (destroyed) return null;
    if (!base) return null;
    try {
      const res = await fetch(`${base}${path}`, {
        headers: { Accept: 'application/json' },
        signal: abort.signal,
      });
      if (!res.ok) {
        logOnce(`GET ${path} ${res.status}`, new Error(`status ${res.status}`));
        return null;
      }
      return await res.json();
    } catch (err) {
      // AbortError on destroy is expected; swallow silently.
      if (err && err.name === 'AbortError') return null;
      if (isCorsError(err)) {
        // High-signal for Starbridge users (the primary RemoteRuntime consumers).
        logOnce(`GET ${path} CORS_BLOCKED`, new Error(
          `CORS blocked contacting ${base}. Starbridge Remote against non-local nodes requires the node to allow browser origins (node/src/api.rs cors_middleware currently localhost+extension only; discord-bot is permissive). Workarounds: (1) use the Chrome extension's embedded Starbridge panel, (2) run a local node with relaxed CORS for dev, (3) target the discord-bot HTTP surface. Original err: ${err.message || err}`
        ));
      } else {
        logOnce(`GET ${path} failed`, err);
      }
      return null;
    }
  }

  async function getFirstJSON(paths) {
    for (const path of paths) {
      const data = await getJSON(path);
      if (data != null) return data;
    }
    return null;
  }

  function fire(type, detail) {
    events.dispatchEvent(new CustomEvent(type, { detail }));
  }
  function bump() { version.value = version.value + 1; }

  // --- Polling ----------------------------------------------------------
  async function pollOnce() {
    if (destroyed) return;
    const [status, cells, receipts, blocks, federations, intents, tokens] = await Promise.all([
      getJSON('/status'),
      getJSON('/api/cells'),
      getFirstJSON(['/api/starbridge/receipts?limit=100', '/api/receipts', '/api/receipts/recent']),
      // Prefer the real blocklace DAG (lane: node consensus) — height-sorted
      // BlockView with real prev_hash/predecessors. Fall back to the legacy
      // attested-roots alias for older nodes that lack the DAG route.
      getFirstJSON(['/api/blocklace/blocks', '/api/blocks', '/federation/roots']),
      getFirstJSON(['/api/federations']),
      getJSON('/api/intents'),
      getJSON('/api/tokens'),
    ]);
    if (destroyed) return;

    let changed = false;

    if (status) {
      // Height field is best-effort — different node versions name it
      // differently; try a few. cursor stays at 0 if none are present.
      const h = pickHeight(status);
      if (typeof h === 'number' && h !== cursor.value) {
        cursor.value = h;
        changed = true;
      }
      if (!shallowEqual(status, cachedStatus)) {
        cachedStatus = status;
        changed = true;
      }
    }

    if (cells) {
      // Cheap change detection: compare length + last-id. Good enough to
      // know whether to re-fetch derived signals.
      const normalized = normalizeCells(cells);
      const sigChanged = !sameCellListShape(normalized, cachedCellList);
      cachedCellList = normalized;
      if (listSignal) listSignal.value = normalized;
      if (sigChanged) changed = true;
    }

    if (receipts) {
      const normalized = normalizeReceipts(receipts);
      if (!sameIdListShape(normalized, cachedReceipts, receiptIdOf)) changed = true;
      cachedReceipts = normalized;
      if (receiptListSignal) receiptListSignal.value = normalized;
      for (const [id, sig] of receiptSignals) sig.value = findReceipt(normalized, id);
    }

    if (blocks) {
      const normalized = normalizeBlocks(blocks);
      if (!sameIdListShape(normalized, cachedBlocks, blockIdOf)) changed = true;
      cachedBlocks = normalized;
      if (blockListSignal) blockListSignal.value = normalized;
      for (const [key, sig] of blockSignals) sig.value = findBlock(normalized, key);
    }

    if (intents) {
      const normalized = normalizeIntents(intents);
      if (!sameIdListShape(normalized, cachedIntents, intentIdOf)) changed = true;
      cachedIntents = normalized;
      if (intentListSignal) intentListSignal.value = normalized;
      for (const [id, sig] of intentSignals) sig.value = findIntent(normalized, id);
    }

    if (tokens) {
      const normalized = normalizeTokens(tokens);
      if (!sameIdListShape(normalized, cachedTokens, tokenIdOf)) changed = true;
      cachedTokens = normalized;
      if (capabilityListSignal) capabilityListSignal.value = normalized;
    }

    const normalizedFederations = normalizeFederations(federations, status, cachedBlocks);
    if (!sameIdListShape(normalizedFederations, cachedFederations, federationIdOf)) changed = true;
    cachedFederations = normalizedFederations;
    if (federationListSignal) federationListSignal.value = normalizedFederations;

    if (changed) {
      bump();
      fire('poll', { status: cachedStatus, cells: cachedCellList });
    }
  }

  function startPolling() {
    // Fire immediately so first-read isn't blocked for 5s; then on interval.
    pollOnce();
    pollTimer = setInterval(pollOnce, POLL_INTERVAL_MS);
  }

  // --- Public getters ---------------------------------------------------
  function listCells() {
    if (!listSignal) listSignal = signal(cachedCellList);
    return listSignal;
  }

  function getCell(id) {
    if (!cellSignals.has(id)) {
      const sig = signal(null);
      cellSignals.set(id, sig);
      // Kick off a fetch; result populates the signal asynchronously.
      // Subsequent calls return the same signal and re-fetch is triggered
      // by version bumps (see refreshCells below).
      fetchCellInto(id, sig);
    }
    return cellSignals.get(id);
  }

  async function fetchCellInto(id, sig) {
    if (cellPending.has(id)) return cellPending.get(id);
    const p = (async () => {
      const data = await getJSON(`/api/cell/${encodeURIComponent(id)}`);
      if (destroyed) return;
      sig.value = normalizeCell(data, id);
    })();
    cellPending.set(id, p);
    try { await p; } finally { cellPending.delete(id); }
  }

  // Refresh any observed individual cell signals whenever version changes.
  // We don't have a real subscribe loop for those — piggy-back on the poll.
  events.addEventListener('poll', () => {
    for (const [id, sig] of cellSignals) fetchCellInto(id, sig);
  });

  function listReceipts() {
    if (!receiptListSignal) receiptListSignal = signal(cachedReceipts || []);
    return receiptListSignal;
  }

  function getReceipt(id) {
    if (!receiptSignals.has(id)) receiptSignals.set(id, signal(findReceipt(cachedReceipts, id)));
    return receiptSignals.get(id);
  }

  function listBlocks() {
    if (!blockListSignal) blockListSignal = signal(cachedBlocks || []);
    return blockListSignal;
  }

  function getBlock(ref) {
    const key = typeof ref === 'object'
      ? `${ref.fedIndex ?? ref.fed_index ?? 0}/${ref.height ?? ref.block_height ?? 0}`
      : `0/${ref}`;
    if (!blockSignals.has(key)) blockSignals.set(key, signal(findBlock(cachedBlocks, key)));
    return blockSignals.get(key);
  }

  // A turn and its receipt share the same hash in the node's read surface; the
  // <dregg-turn> inspector consumes the same receipt shape, so getTurn aliases
  // getReceipt (matches InMemoryRuntime, which does the same).
  function getTurn(id) { return getReceipt(id); }

  function listIntents() {
    if (!intentListSignal) intentListSignal = signal(cachedIntents || []);
    return intentListSignal;
  }

  function getIntent(idOrIndex) {
    const key = String(idOrIndex);
    if (!intentSignals.has(key)) {
      intentSignals.set(key, signal(findIntent(cachedIntents, idOrIndex)));
    }
    return intentSignals.get(key);
  }

  // Capabilities/tokens. The node exposes the node cipherclerk's own held tokens
  // at /api/tokens (a flat list), not per-agent capability trees. We surface the
  // flat list for <dregg-capability-list> and resolve single tokens by id/slot.
  function listCapabilities(_agentIdx) {
    if (!capabilityListSignal) capabilityListSignal = signal(cachedTokens || []);
    return capabilityListSignal;
  }

  function getCapability(idOrAgent, slotOrIndex) {
    const sig = signal(null);
    const update = () => {
      const list = cachedTokens || [];
      const wantId = String(idOrAgent ?? '');
      const wantSlot = slotOrIndex != null ? String(slotOrIndex) : null;
      sig.value = list.find((t) =>
        String(t.id ?? '') === wantId ||
        (wantSlot != null && String(t.slot ?? '') === wantSlot) ||
        (wantSlot != null && String(t.id ?? '') === wantSlot)
      ) || (wantSlot != null ? list[Number(wantSlot)] : null) || null;
    };
    update();
    events.addEventListener('poll', update);
    return sig;
  }

  // Outbox is an extension/sim-only concept (pending local submissions). A
  // read-only remote viewport has none; return an always-empty signal so the
  // shared <dregg-outbox> inspector renders its honest empty state.
  let outboxSignal = null;
  function getOutbox() {
    if (!outboxSignal) outboxSignal = signal([]);
    return outboxSignal;
  }

  function listKnownFederations() {
    if (!federationListSignal) federationListSignal = signal(cachedFederations || []);
    return federationListSignal;
  }

  function getFederation(idOrIndex) {
    const sig = signal(null);
    const update = () => {
      const want = String(idOrIndex ?? '0');
      sig.value = (cachedFederations || []).find((f) =>
        String(f.fed_index ?? '') === want ||
        String(f.id ?? '') === want ||
        String(f.federation_id ?? '') === want ||
        String(f.name ?? '') === want
      ) || null;
    };
    update();
    events.addEventListener('poll', update);
    return sig;
  }

  function destroy() {
    if (destroyed) return;
    destroyed = true;
    if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
    if (extPollTimer) { clearInterval(extPollTimer); extPollTimer = null; }
    if (obsEs) { try { obsEs.close(); } catch {} obsEs = null; }
    try { abort.abort(); } catch { /* noop */ }
  }

  startPolling();

  return attachRuntimeObjectAdapter({
    caps: CAPS,
    source: { kind: 'remote', label: `remote ${base || '(unset)'}` },
    version,
    cursor,
    events,

    getCell,
    listCells,
    listReceipts,
    getReceipt,
    getTurn,
    listIntents,
    getIntent,
    listCapabilities,
    getCapability,
    getOutbox,
    listKnownFederations,
    getFederation,
    listBlocks,
    getBlock,
    getTraceEvents,

    // Read-only: all mutations refuse.
    createAgent: notPermitted('createAgent'),
    createCell: notPermitted('createCell'),
    executeTurn: notPermitted('executeTurn'),
    mintToken: notPermitted('mintToken'),
    advanceHeight: notPermitted('advanceHeight'),

    destroy,
  });
}

// --- helpers ------------------------------------------------------------

function pickHeight(status) {
  if (!status || typeof status !== 'object') return null;
  // Common field names seen across node versions.
  const candidates = ['height', 'block_height', 'tip_height', 'head_height', 'cursor'];
  for (const k of candidates) {
    const v = status[k];
    if (typeof v === 'number') return v;
    if (typeof v === 'string' && /^\d+$/.test(v)) return Number(v);
  }
  return null;
}

function sameCellListShape(a, b) {
  if (a === b) return true;
  if (!Array.isArray(a) || !Array.isArray(b)) return false;
  if (a.length !== b.length) return false;
  // Compare ids at head + tail; cheap and adequate for change detection.
  const idOf = (x) => x && (x.id || x.cell_id || x.hash);
  return idOf(a[0]) === idOf(b[0]) && idOf(a[a.length - 1]) === idOf(b[b.length - 1]);
}

function sameIdListShape(a, b, idOf) {
  if (a === b) return true;
  if (!Array.isArray(a) || !Array.isArray(b)) return false;
  if (a.length !== b.length) return false;
  return idOf(a[0]) === idOf(b[0]) && idOf(a[a.length - 1]) === idOf(b[b.length - 1]);
}

function normalizeCells(cells) {
  return Array.isArray(cells) ? cells.map((cell) => normalizeCell(cell)).filter(Boolean) : [];
}

function normalizeCell(cell, fallbackId = '') {
  if (!cell || typeof cell !== 'object') return null;
  const id = cell.cell_id || cell.id || fallbackId;
  return {
    ...cell,
    id,
    cell_id: id,
    balance: cell.balance ?? cell.state?.balance ?? 0,
    nonce: cell.nonce ?? cell.state?.nonce ?? 0,
    num_capabilities: cell.num_capabilities ?? cell.capability_count ?? cell.capabilities?.length ?? 0,
    proved_state: cell.proved_state ?? cell.provedState ?? false,
    delegation_epoch: cell.delegation_epoch ?? cell.delegationEpoch ?? 0,
    program: cell.program || (cell.program_kind ? { kind: cell.program_kind } : null),
  };
}

function normalizeReceipts(receipts) {
  const list = Array.isArray(receipts) ? receipts : (Array.isArray(receipts?.receipts) ? receipts.receipts : []);
  return list.map((entry) => {
    const r = entry.receipt || entry;
    const turnHash = r.turn_hash || r.turnHash || r.hash || r.receipt_hash || '';
    const witnessArtifacts = Array.isArray(r.witness_artifacts) ? r.witness_artifacts : [];
    const witnessCount = Number(r.witness_count ?? witnessArtifacts.length ?? 0);
    return {
      ...entry,
      ...r,
      turn_hash: turnHash,
      receipt_hash: r.receipt_hash || r.receiptHash || turnHash,
      pre_state_hash: r.pre_state_hash || r.pre_state || r.preState || '',
      post_state_hash: r.post_state_hash || r.post_state || r.postState || '',
      action_count: r.action_count ?? r.actions?.length ?? 0,
      computrons_used: r.computrons_used ?? r.computrons ?? 0,
      timestamp: r.timestamp ?? r.committed_at ?? '',
      has_witness: Boolean(r.has_witness || witnessCount > 0),
      witness_count: witnessCount,
      artifact_format: r.artifact_format || (witnessArtifacts.length ? 'DWR1' : undefined),
      witness_artifacts: witnessArtifacts,
      proof_view: r.proof_view || (r.has_proof || r.has_witness || witnessCount > 0 ? {
        kind: (r.has_witness || witnessCount > 0) ? 'WitnessedReceipt' : 'ExecutorSignature',
        public_inputs: [],
        bilateral_pi: null,
        is_agent_cell: false,
        is_sovereign_cell: false,
      } : null),
    };
  }).filter((r) => r.turn_hash || r.receipt_hash);
}

function receiptIdOf(r) {
  return r && (r.turn_hash || r.receipt_hash || r.hash);
}

function findReceipt(receipts, id) {
  const want = String(id || '').toLowerCase();
  return (receipts || []).find((r) =>
    String(r.turn_hash || '').toLowerCase() === want ||
    String(r.receipt_hash || '').toLowerCase() === want ||
    String(r.hash || '').toLowerCase() === want
  ) || null;
}

function normalizeBlocks(blocks) {
  const list = Array.isArray(blocks) ? blocks : (Array.isArray(blocks?.blocks) ? blocks.blocks : []);
  return list.map((block) => {
    const height = block.height ?? block.block_height ?? block.index ?? 0;
    const fedIndex = block.fed_index ?? block.federation_index ?? 0;
    const hash = block.block_hash || block.hash || block.merkle_root || block.root || '';
    return {
      ...block,
      height,
      block_height: height,
      fed_index: fedIndex,
      block_hash: hash,
      events: Array.isArray(block.events) ? block.events : (block.merkle_root ? [`root:${block.merkle_root}`] : []),
    };
  });
}

function blockIdOf(b) {
  return b ? `${b.fed_index ?? 0}/${b.height ?? b.block_height ?? 0}/${b.block_hash || ''}` : '';
}

function findBlock(blocks, key) {
  const [fed, height] = String(key || '').split('/');
  return (blocks || []).find((b) =>
    String(b.fed_index ?? 0) === String(fed ?? 0) &&
    String(b.height ?? b.block_height ?? 0) === String(height ?? '')
  ) || null;
}

function normalizeFederations(federations, status, blocks) {
  const explicit = Array.isArray(federations) ? federations : (Array.isArray(federations?.federations) ? federations.federations : []);
  if (explicit.length) return explicit.map((f, idx) => normalizeFederation(f, idx, blocks));
  if (!status) return [];
  return [normalizeFederation(status, 0, blocks)];
}

function normalizeFederation(f, idx, blocks) {
  const height = pickHeight(f) ?? (blocks || []).reduce((max, b) => Math.max(max, Number(b.height || 0)), 0);
  return {
    ...f,
    fed_index: f.fed_index ?? f.registered_index ?? idx,
    name: f.name || f.federation_name || f.federation_id || f.silo_id || 'remote federation',
    height,
    num_nodes: f.num_nodes ?? f.nodes ?? f.federation_members ?? f.peer_count ?? 0,
    num_events: f.num_events ?? f.events ?? 0,
    num_finalized_roots: f.num_finalized_roots ?? (blocks || []).length,
    latest_root: f.latest_root || f.merkle_root || f.root || (blocks || [])[blocks.length - 1]?.block_hash || null,
  };
}

function federationIdOf(f) {
  return f && (f.fed_index ?? f.id ?? f.federation_id ?? f.name);
}

function normalizeIntents(intents) {
  // Node /api/intents returns Vec<{ id, intent }>; tolerate a bare-array form.
  const list = Array.isArray(intents)
    ? intents
    : (Array.isArray(intents?.intents) ? intents.intents : []);
  return list.map((entry, idx) => {
    const inner = entry && typeof entry === 'object' && entry.intent ? entry.intent : entry;
    const id = entry?.id || entry?.intent_id || inner?.id || inner?.intent_id || String(idx);
    return {
      ...(inner || {}),
      ...entry,
      intent_id: id,
      id,
      intent_index: idx,
      kind: inner?.kind || inner?.type || entry?.kind || 'intent',
    };
  });
}

function intentIdOf(i) {
  return i && (i.intent_id || i.id);
}

function findIntent(intents, idOrIndex) {
  const list = intents || [];
  const asNum = Number(idOrIndex);
  if (!Number.isNaN(asNum) && list[asNum]) return list[asNum];
  const want = String(idOrIndex || '');
  return list.find((i) => String(i.intent_id || i.id || '') === want) || null;
}

function normalizeTokens(tokens) {
  const list = Array.isArray(tokens)
    ? tokens
    : (Array.isArray(tokens?.tokens) ? tokens.tokens : []);
  return list.map((t, idx) => ({
    ...t,
    id: t.id || t.token_id || String(idx),
    label: t.label || t.id || `token ${idx}`,
    service: t.service || '',
    slot: t.slot ?? idx,
  }));
}

function tokenIdOf(t) {
  return t && (t.id || t.token_id || t.label);
}

function shallowEqual(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  const ka = Object.keys(a), kb = Object.keys(b);
  if (ka.length !== kb.length) return false;
  for (const k of ka) if (a[k] !== b[k]) return false;
  return true;
}

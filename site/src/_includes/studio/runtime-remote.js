/**
 * RemoteRuntime — read-only Runtime over a live pyana federation node's HTTP API.
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
 * CORS realism: when used against devnet.pyana.fg-goose.online from a
 * browser-localhost origin the fetches will reject with a CORS error. The
 * runtime still constructs cleanly; signals stay null until the network
 * cooperates. (FOLLOWUP-07: now surfaces actionable guidance in logs for
 * Starbridge users; see improved logOnce + getJSON catch.)
 */

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
  // When running inside the Pyana Cipherclerk extension (iframe panel, or any
  // extension page), chrome.runtime is present. We poll the background's
  // synthesized activity feed (populated from the live WS bus + cclerk ops,
  // exactly the TraceEvent shape for <pyana-activity>) via "pyana:getActivityFeed".
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
          chrome.runtime.sendMessage({ type: 'pyana:getActivityFeed' }, (r) => resolve(r));
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
  const cellSignals = new Map();      // id -> signal<CellState | null>
  const cellPending = new Map();      // id -> in-flight Promise (dedupe)
  let listSignal = null;              // signal<CellSummary[] | null>

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

  function fire(type, detail) {
    events.dispatchEvent(new CustomEvent(type, { detail }));
  }
  function bump() { version.value = version.value + 1; }

  // --- Polling ----------------------------------------------------------
  async function pollOnce() {
    if (destroyed) return;
    const [status, cells] = await Promise.all([
      getJSON('/status'),
      getJSON('/api/cells'),
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
      const sigChanged = !sameCellListShape(cells, cachedCellList);
      cachedCellList = cells;
      if (listSignal) listSignal.value = cells;
      if (sigChanged) changed = true;
    }

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
      sig.value = data;
    })();
    cellPending.set(id, p);
    try { await p; } finally { cellPending.delete(id); }
  }

  // Refresh any observed individual cell signals whenever version changes.
  // We don't have a real subscribe loop for those — piggy-back on the poll.
  events.addEventListener('poll', () => {
    for (const [id, sig] of cellSignals) fetchCellInto(id, sig);
  });

  function destroy() {
    if (destroyed) return;
    destroyed = true;
    if (pollTimer) { clearInterval(pollTimer); pollTimer = null; }
    if (extPollTimer) { clearInterval(extPollTimer); extPollTimer = null; }
    if (obsEs) { try { obsEs.close(); } catch {} obsEs = null; }
    try { abort.abort(); } catch { /* noop */ }
  }

  startPolling();

  return {
    caps: CAPS,
    source: { kind: 'remote', label: `remote ${base || '(unset)'}` },
    version,
    cursor,
    events,

    getCell,
    listCells,
    getTraceEvents,

    // Read-only: all mutations refuse.
    createAgent: notPermitted('createAgent'),
    createCell: notPermitted('createCell'),
    executeTurn: notPermitted('executeTurn'),
    mintToken: notPermitted('mintToken'),
    advanceHeight: notPermitted('advanceHeight'),

    destroy,
  };
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

function shallowEqual(a, b) {
  if (a === b) return true;
  if (!a || !b) return false;
  const ka = Object.keys(a), kb = Object.keys(b);
  if (ka.length !== kb.length) return false;
  for (const k of ka) if (a[k] !== b[k]) return false;
  return true;
}

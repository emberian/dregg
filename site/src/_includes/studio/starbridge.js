/**
 * Starbridge — page-specific orchestration.
 *
 * Wires up the runtime picker, URI input, time-cursor scrubber, object tree,
 * and raw-JSON pane on the /starbridge page. Driven entirely off the same
 * Runtime substrate exposed to the rest of the Studio (see STUDIO.md § 3).
 *
 * URL state: ?at=dregg://...&runtime=<id> — restored on load, updated via
 * history.replaceState on user navigation (no back-button spam).
 */

import { parseRef, isRef } from './uri.js';

// ----------------------------------------------------------------------------
// Bootstrap: wait for window.dreggUi (Preact + signals + htm) to load.
// ----------------------------------------------------------------------------
function whenDregg() {
  return new Promise(resolve => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', e => resolve(e.detail), { once: true });
  });
}

// ----------------------------------------------------------------------------
// Runtime registry — try shared registry, fall back to in-memory only.
// ----------------------------------------------------------------------------
async function loadRuntimeKinds() {
  try {
    const mod = await import('/_includes/studio/runtimes.js');
    if (mod && mod.RUNTIME_KINDS && Object.keys(mod.RUNTIME_KINDS).length) {
      return mod.RUNTIME_KINDS;
    }
  } catch (e) {
    console.warn('[starbridge] runtimes.js unavailable, falling back to in-memory only:', e);
  }
  // Fallback — defer to the known module.
  const { createInMemoryRuntime } = await import('/_includes/studio/runtime-in-memory.js');
  return {
    'in-memory': { label: 'In-browser (wasm)', factory: createInMemoryRuntime },
  };
}

// ----------------------------------------------------------------------------
// URL state helpers.
// ----------------------------------------------------------------------------
function readUrlState() {
  const p = new URLSearchParams(window.location.search);
  return {
    at: p.get('at'),
    runtime: p.get('runtime'),
  };
}
function writeUrlState({ at, runtime }) {
  const p = new URLSearchParams(window.location.search);
  if (at) p.set('at', at); else p.delete('at');
  if (runtime) p.set('runtime', runtime); else p.delete('runtime');
  const q = p.toString();
  const u = window.location.pathname + (q ? '?' + q : '');
  window.history.replaceState(null, '', u);
}

// ----------------------------------------------------------------------------
// Main.
// ----------------------------------------------------------------------------
(async function main() {
  const statusEl   = document.getElementById('sb-status');
  const pickerEl   = document.getElementById('sb-runtime');
  const uriInput   = document.getElementById('sb-uri');
  const goBtn      = document.getElementById('sb-go');
  const snapBtn    = document.getElementById('sb-snapshot');
  const cursorEl   = document.getElementById('sb-cursor');
  const cursorVal  = document.getElementById('sb-cursor-val');
  const cursorMax  = document.getElementById('sb-cursor-max');
  const treeListEl = document.getElementById('sb-cell-list');
  const cellCount  = document.getElementById('sb-cell-count');
  const receiptListEl = document.getElementById('sb-receipt-list');
  const receiptCount = document.getElementById('sb-receipt-count');
  const intentListEl = document.getElementById('sb-intent-list');
  const intentCount = document.getElementById('sb-intent-count');
  const capListEl = document.getElementById('sb-capability-list');
  const capCount = document.getElementById('sb-capability-count');
  const fedListEl = document.getElementById('sb-federation-list');
  const fedCount = document.getElementById('sb-federation-count');
  const blockListEl = document.getElementById('sb-block-list');
  const blockCount = document.getElementById('sb-block-count');
  const activityListEl = document.getElementById('sb-activity-list');
  const activityCount = document.getElementById('sb-activity-count');
  const simActions = document.getElementById('sb-sim-actions');
  const inspector  = document.getElementById('sb-inspector');
  const rawEl      = document.getElementById('sb-raw');
  const app        = document.getElementById('sb-app');

  function setStatus(text, state) {
    statusEl.textContent = text;
    if (state) statusEl.dataset.state = state;
    else delete statusEl.dataset.state;
  }

  let api = null;
  let wasm = null;
  let runtime = null;
  let currentRuntimeId = null;
  let currentUri = null;
  let kinds = null;

  // Per-runtime teardown of effects we owned. Cleared and rebuilt on swap.
  const teardowns = [];
  function disposeRuntimeEffects() {
    while (teardowns.length) {
      const t = teardowns.pop();
      try { t(); } catch (e) { console.warn('[starbridge] teardown:', e); }
    }
  }

  // --------------------------------------------------------------------------
  // Inspector pane: mount a `<dregg-${kind}>` for the current URI, or show a
  // helpful empty/missing-kind message.
  // --------------------------------------------------------------------------
  function renderAppWorkspace(appMeta) {
    inspector.replaceChildren();
    rawEl.textContent = JSON.stringify(appMeta, null, 2);
    currentUri = `dregg://app/${appMeta.id}`;
    uriInput.value = currentUri;
    writeUrlState({ at: currentUri, runtime: currentRuntimeId });

    const shell = document.createElement('div');
    shell.className = 'sb__app-host';
    const page = appMeta.page || `/starbridge-apps/${appMeta.id}/pages/index.html`;
    const registryUri = appMeta.registry_uri || appMeta.registryUri || '';
    shell.innerHTML = `
      <div class="sb__app-hostbar">
        <div>
          <div class="sb__app-title">${escapeHtml(appMeta.name || appMeta.id)}</div>
          <div class="sb__app-meta">${escapeHtml(appMeta.description || 'starbridge-app')}</div>
        </div>
        <div class="sb__app-actions">
          ${registryUri ? `<button type="button" class="sb__btn sb__btn--small" data-uri="${escapeHtml(registryUri)}">Inspect registry</button>` : ''}
          <a class="sb__btn sb__btn--small sb__btn--ghost" href="${escapeHtml(page)}" target="_blank">Standalone</a>
        </div>
      </div>
      <iframe
        class="sb__app-frame"
        title="${escapeHtml(appMeta.name || appMeta.id)} app workspace"
        src="${escapeHtml(page)}"
      ></iframe>
    `;
    shell.querySelector('[data-uri]')?.addEventListener('click', (e) => {
      setCurrentUri(e.currentTarget.dataset.uri);
    });
    inspector.appendChild(shell);
    setStatus(`app workspace · ${appMeta.name || appMeta.id}`, 'ready');
  }

  function renderInspectorPane(uri) {
    inspector.replaceChildren();
    if (!uri) {
      const empty = document.createElement('div');
      empty.className = 'sb__inspector-empty';
      empty.textContent = 'paste a dregg:// URI above and hit Go';
      inspector.appendChild(empty);
      return;
    }
    let parsed;
    try { parsed = parseRef(uri); }
    catch (e) {
      const err = document.createElement('div');
      err.className = 'sb__inspector-empty';
      err.textContent = `bad URI: ${e.message}`;
      inspector.appendChild(err);
      return;
    }
    if (parsed.kind === 'app') {
      renderAppWorkspace({ id: parsed.id, name: parsed.id, page: `/starbridge-apps/${parsed.id}/pages/index.html` });
      return;
    }
    const tagName = `dregg-${parsed.kind}`;
    if (!customElements.get(tagName)) {
      const err = document.createElement('div');
      err.className = 'sb__inspector-empty';
      err.textContent = `no inspector registered for kind "${parsed.kind}" (yet)`;
      inspector.appendChild(err);
      return;
    }
    const el = document.createElement(tagName);
    el.setAttribute('uri', uri);
    inspector.appendChild(el);
  }

  function escapeHtml(s) {
    return String(s ?? '').replace(/[&<>"']/g, (c) => ({
      '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
    })[c]);
  }

  // --------------------------------------------------------------------------
  // Object tree. Re-renders on runtime signals so Starbridge is a real object
  // navigator, not just a single inspector mount point.
  // --------------------------------------------------------------------------
  function renderTreeList({ listEl, countEl, items, empty, map }) {
    countEl.textContent = String(items.length);
    listEl.replaceChildren();
    if (!items.length) {
      const li = document.createElement('li');
      li.className = 'sb__list-empty';
      li.textContent = empty;
      listEl.appendChild(li);
      return;
    }
    for (const [idx, item] of items.entries()) {
      const mapped = map(item, idx);
      if (!mapped || !mapped.uri) continue;
      const li = document.createElement('li');
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'sb__list-item';
      btn.dataset.uri = mapped.uri;
      btn.textContent = mapped.label;
      btn.title = mapped.title || mapped.uri;
      if (currentUri === mapped.uri) btn.setAttribute('aria-current', 'true');
      btn.addEventListener('click', () => setCurrentUri(mapped.uri));
      li.appendChild(btn);
      listEl.appendChild(li);
    }
  }

  function bindSignalList({ listEl, countEl, empty, getSignal, normalize, map }) {
    if (!listEl || !countEl || typeof getSignal !== 'function') return;
    let sig = null;
    try { sig = getSignal(); } catch {}
    if (!sig) {
      renderTreeList({ listEl, countEl, items: [], empty, map });
      return;
    }
    const stop = api.effect(() => {
      const raw = sig.value;
      const items = normalize ? normalize(raw) : (Array.isArray(raw) ? raw : []);
      renderTreeList({ listEl, countEl, items, empty, map });
    });
    teardowns.push(stop);
  }

  function bindObjectTree() {
    const sig = runtime.listCells();
    const stop = api.effect(() => {
      const cells = sig.value || [];
      renderTreeList({
        listEl: treeListEl,
        countEl: cellCount,
        items: cells,
        empty: 'no cells yet',
        map: (c) => {
          const id = c.cell_id || c.id || (typeof c === 'string' ? c : null);
          if (!id) return null;
          return { uri: `dregg://cell/${id}`, label: `cell ${id.slice(0, 12)}…`, title: id };
        },
      });
    });
    teardowns.push(stop);

    bindSignalList({
      listEl: receiptListEl,
      countEl: receiptCount,
      empty: 'no receipts yet',
      getSignal: () => runtime.listReceipts && runtime.listReceipts(),
      map: (r) => {
        const id = r.turn_hash || r.receipt_hash || r.hash;
        if (!id) return null;
        return {
          uri: `dregg://receipt/${id}`,
          label: `receipt ${id.slice(0, 10)}… · ${String(r.action_count ?? 0)} act`,
          title: id,
        };
      },
    });

    bindSignalList({
      listEl: intentListEl,
      countEl: intentCount,
      empty: 'no intents yet',
      getSignal: () => runtime.listIntents && runtime.listIntents(),
      map: (intent, idx) => {
        const id = intent.intent_id || intent.id || String(intent.intent_index ?? idx);
        return {
          uri: `dregg://intent/${id}`,
          label: `${intent.kind || 'intent'} ${String(id).slice(0, 10)}…`,
          title: String(id),
        };
      },
    });

    bindSignalList({
      listEl: capListEl,
      countEl: capCount,
      empty: 'no agent-0 capabilities yet',
      getSignal: () => runtime.listCapabilities && runtime.listCapabilities(0),
      normalize: (tree) => (tree && Array.isArray(tree.capabilities)) ? tree.capabilities : [],
      map: (cap, idx) => {
        const slot = cap.slot ?? idx;
        return {
          uri: `dregg://capability/0/${slot}`,
          label: `slot ${String(slot)} · ${String(cap.permissions || 'cap')}`,
          title: cap.target || `agent 0 slot ${slot}`,
        };
      },
    });

    bindSignalList({
      listEl: fedListEl,
      countEl: fedCount,
      empty: 'no known federations yet',
      getSignal: () => runtime.listKnownFederations && runtime.listKnownFederations(),
      map: (fed, idx) => {
        const id = fed.fed_index ?? fed.registered_index ?? idx;
        return {
          uri: `dregg://federation/${id}`,
          label: fed.name || fed.federationId || `federation #${id}`,
          title: fed.federationId || `federation #${id}`,
        };
      },
    });

    bindSignalList({
      listEl: blockListEl,
      countEl: blockCount,
      empty: 'no finalized blocks yet',
      getSignal: () => runtime.listBlocks && runtime.listBlocks(),
      map: (block) => {
        const h = block.height ?? block.block_height ?? 0;
        return {
          uri: `dregg://block/${h}`,
          label: `h=${String(h)} · fed #${String(block.fed_index ?? 0)}`,
          title: block.block_hash || `height ${h}`,
        };
      },
    });

    bindSignalList({
      listEl: activityListEl,
      countEl: activityCount,
      empty: 'no activity yet',
      getSignal: () => runtime.getTraceEvents && runtime.getTraceEvents(),
      normalize: (feed) => Array.isArray(feed?.events) ? feed.events : [],
      map: (event, idx) => ({
        uri: 'dregg://activity/feed',
        label: `${event.kind || event.event_type || 'event'} #${idx}`,
        title: JSON.stringify(event).slice(0, 180),
      }),
    });
  }

  // --------------------------------------------------------------------------
  // Cursor scrubber. Read-only on runtimes without timeTravel; otherwise the
  // user can rewind/fast-forward through history. We treat the live cursor as
  // the "max known height" — bump whenever it advances.
  // --------------------------------------------------------------------------
  function bindCursor() {
    const writable = !!(runtime.caps && runtime.caps.timeTravel);
    cursorEl.disabled = !writable;
    if (!runtime.cursor) {
      cursorEl.max = 0;
      cursorVal.textContent = '0';
      cursorMax.textContent = '0';
      return;
    }
    let maxKnown = 0;
    const stop = api.effect(() => {
      const v = Number(runtime.cursor.value || 0);
      if (v > maxKnown) maxKnown = v;
      cursorEl.max = String(maxKnown);
      // For non-writable runtimes, mirror the head; for writable, leave the
      // user's slider position alone unless we just bumped past it.
      if (!writable || Number(cursorEl.value) > maxKnown) {
        cursorEl.value = String(v);
      }
      cursorVal.textContent = String(v);
      cursorMax.textContent = String(maxKnown);
    });
    teardowns.push(stop);

    if (writable) {
      cursorEl.addEventListener('input', () => {
        const n = Number(cursorEl.value);
        try { runtime.cursor.value = n; }
        catch (e) { console.warn('[starbridge] cursor write failed:', e); }
        cursorVal.textContent = String(n);
      });
    }
  }

  // --------------------------------------------------------------------------
  // Current URI mutator. Single funnel: pane render + raw pane + URL sync.
  // --------------------------------------------------------------------------
  function setCurrentUri(uri) {
    currentUri = uri || null;
    if (uri) uriInput.value = uri;
    // Refresh tree highlight without rebuilding (cheap path).
    for (const btn of document.querySelectorAll('.sb__list-item')) {
      btn.removeAttribute('aria-current');
    }
    if (uri) {
      for (const btn of document.querySelectorAll('.sb__list-item')) {
        if (btn.dataset.uri === uri) {
          btn.setAttribute('aria-current', 'true');
        }
      }
    }
    renderInspectorPane(uri);
    // Rebind raw pane: rebuild teardowns for the raw effect only? We use a
    // sub-teardown list so we don't kill the tree+cursor effects.
    rebindRawOnly(uri);
    writeUrlState({ at: uri, runtime: currentRuntimeId });
  }

  // Independent teardown list for the raw pane, so URI changes don't dispose
  // the tree/cursor effects.
  const rawTeardowns = [];
  function rebindRawOnly(uri) {
    while (rawTeardowns.length) {
      const t = rawTeardowns.pop();
      try { t(); } catch {}
    }
    rawEl.textContent = 'no object selected';
    if (!uri || !runtime) return;
    let parsed;
    try { parsed = parseRef(uri); } catch { return; }
    let sig = null;
    if (parsed.kind === 'cell' && typeof runtime.getCell === 'function') {
      sig = runtime.getCell(parsed.id);
    } else if (parsed.kind === 'receipt' && typeof runtime.getReceipt === 'function') {
      sig = runtime.getReceipt(parsed.id);
    } else if (parsed.kind === 'turn' && typeof runtime.getTurn === 'function') {
      sig = runtime.getTurn(parsed.id);
    } else if (parsed.kind === 'intent' && typeof runtime.getIntent === 'function') {
      sig = runtime.getIntent(parsed.id);
    } else if (parsed.kind === 'capability' && typeof runtime.getCapability === 'function') {
      sig = runtime.getCapability(parsed.id, parsed.sub[0]);
    } else if (parsed.kind === 'federation' && typeof runtime.getFederation === 'function') {
      sig = runtime.getFederation(parsed.id);
    } else if (parsed.kind === 'block' && typeof runtime.getBlock === 'function') {
      sig = runtime.getBlock(parsed.id);
    } else if (parsed.kind === 'activity' && typeof runtime.getTraceEvents === 'function') {
      sig = runtime.getTraceEvents();
    }
    if (!sig) {
      rawEl.textContent = `no resolver for kind "${parsed.kind}"`;
      return;
    }
    const stop = api.effect(() => {
      const v = sig.value;
      if (v == null) {
        rawEl.textContent = 'no object loaded (not in this runtime)';
        return;
      }
      try {
        rawEl.textContent = JSON.stringify(v, (_, val) =>
          typeof val === 'bigint' ? val.toString() : val, 2);
      } catch (e) {
        rawEl.textContent = '/* unserializable: ' + e.message + ' */';
      }
    });
    rawTeardowns.push(stop);
  }

  // --------------------------------------------------------------------------
  // Runtime creation/swap.
  // --------------------------------------------------------------------------
  async function swapRuntime(id) {
    setStatus(`creating ${id}…`, 'boot');
    if (runtime) {
      disposeRuntimeEffects();
      while (rawTeardowns.length) { try { rawTeardowns.pop()(); } catch {} }
      try { runtime.destroy && runtime.destroy(); }
      catch (e) { console.warn('[starbridge] destroy:', e); }
      runtime = null;
      app.runtime = null;
    }
    const entry = kinds[id];
    if (!entry) {
      setStatus(`unknown runtime: ${id}`, 'err');
      return;
    }
    try {
      // In-memory needs the wasm module; remote takes a baseUrl. Pass the
      // union of likely opts and let the factory pick what it cares about.
      const opts = { wasm, signals: api };
      if (id === 'remote') {
        // Best-effort: try to read a configured base URL; otherwise empty.
        opts.baseUrl = (window.localStorage && localStorage.getItem('dregg.remote.baseUrl')) || '';
      }
      runtime = await entry.factory(opts);
      currentRuntimeId = id;
      app.runtime = runtime;
      if (simActions) simActions.hidden = !(runtime.caps && runtime.caps.mutate);
      bindObjectTree();
      bindCursor();
      rebindRawOnly(currentUri);
      setStatus(`ready · ${runtime.source ? runtime.source.label : id}`, 'ready');
      writeUrlState({ at: currentUri, runtime: id });
    } catch (e) {
      console.error('[starbridge] runtime create failed:', e);
      setStatus('runtime failed: ' + (e?.message || e), 'err');
    }
  }

  // --------------------------------------------------------------------------
  // Boot.
  // --------------------------------------------------------------------------
  try {
    setStatus('loading runtime…', 'boot');
    api = await whenDregg();

    setStatus('loading wasm…', 'boot');
    wasm = await import('/pkg/dregg_wasm.js');
    await wasm.default();

    setStatus('loading inspectors…', 'boot');
    await import('/_includes/studio/inspectors.js');

    kinds = await loadRuntimeKinds();

    // Populate picker.
    pickerEl.replaceChildren();
    for (const [id, meta] of Object.entries(kinds)) {
      const opt = document.createElement('option');
      opt.value = id;
      opt.textContent = meta.label || id;
      pickerEl.appendChild(opt);
    }
    if (!pickerEl.options.length) {
      throw new Error('no runtimes registered');
    }

    // Initial state from URL (with safe fallback).
    const url = readUrlState();
    const initialId =
      (url.runtime && kinds[url.runtime]) ? url.runtime :
      (kinds['in-memory'] ? 'in-memory' : Object.keys(kinds)[0]);
    pickerEl.value = initialId;

    await swapRuntime(initialId);

    if (url.at && isRef(url.at)) {
      setCurrentUri(url.at);
    } else {
      renderInspectorPane(null);
    }

    // --- Event wiring ---
    pickerEl.addEventListener('change', () => swapRuntime(pickerEl.value));

    function commitUri() {
      const v = uriInput.value.trim();
      if (!v) {
        setCurrentUri(null);
        return;
      }
      if (!isRef(v)) {
        setStatus('not a valid dregg:// URI', 'err');
        return;
      }
      setStatus(`ready · ${runtime.source ? runtime.source.label : currentRuntimeId}`, 'ready');
      setCurrentUri(v);
    }
    goBtn.addEventListener('click', commitUri);
    uriInput.addEventListener('keydown', e => {
      if (e.key === 'Enter') { e.preventDefault(); commitUri(); }
    });

    snapBtn.addEventListener('click', () => {
      window.alert('Snapshot export will be wired up once the wasm side is shipped.');
    });

    // Sim convenience buttons (best-effort; absent on read-only runtimes).
    const btn = (id, fn) => {
      const e = document.getElementById(id);
      if (!e) return;
      e.addEventListener('click', () => {
        try { fn(); } catch (err) {
          console.warn(`[starbridge] ${id} failed:`, err);
          window.dreggUi?.toast?.(`${id}: ${err.message || err}`, 'err');
        }
      });
    };
    btn('sb-mk-alice', () => runtime.createAgent && runtime.createAgent('alice', 5000));
    btn('sb-mk-bob',   () => runtime.createAgent && runtime.createAgent('bob',   0));
    btn('sb-advance',  () => runtime.advanceHeight && runtime.advanceHeight(1));

    // Expose for tests / console debugging.
    window.__starbridge = {
      get runtime() { return runtime; },
      get api() { return api; },
      get wasm() { return wasm; },
      setCurrentUri,
      swapRuntime,
    };

    // Wire Apps as hosted workspaces. Starbridge is the IDE host; apps are
    // embedded userspace surfaces with the object tree/raw debugger around them.
    const appListEl = document.getElementById('sb-app-list');
    if (appListEl) {
      appListEl.addEventListener('app-open', (e) => {
        const { app } = e.detail || {};
        if (app) renderAppWorkspace(app);
      });
    }
  } catch (e) {
    console.error('[starbridge] boot failed:', e);
    setStatus('boot failed: ' + (e?.message || e), 'err');
  }
})();

/**
 * Starbridge — page-specific orchestration.
 *
 * Wires up the runtime picker, URI input, time-cursor scrubber, object tree,
 * and raw-JSON pane on the /starbridge page. Driven entirely off the same
 * Runtime substrate exposed to the rest of the Studio (see STUDIO.md § 3).
 *
 * URL state: ?at=pyana://...&runtime=<id> — restored on load, updated via
 * history.replaceState on user navigation (no back-button spam).
 */

import { parseRef, isRef } from './uri.js';

// ----------------------------------------------------------------------------
// Bootstrap: wait for window.pyanaUi (Preact + signals + htm) to load.
// ----------------------------------------------------------------------------
function whenPyana() {
  return new Promise(resolve => {
    if (window.pyanaUi) return resolve(window.pyanaUi);
    window.addEventListener('pyanaUi:ready', e => resolve(e.detail), { once: true });
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
  // Inspector pane: mount a `<pyana-${kind}>` for the current URI, or show a
  // helpful empty/missing-kind message.
  // --------------------------------------------------------------------------
  function renderInspectorPane(uri) {
    inspector.replaceChildren();
    if (!uri) {
      const empty = document.createElement('div');
      empty.className = 'sb__inspector-empty';
      empty.textContent = 'paste a pyana:// URI above and hit Go';
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
    const tagName = `pyana-${parsed.kind}`;
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

  // --------------------------------------------------------------------------
  // Object tree (cells, for now). Re-renders on listCells signal change.
  // --------------------------------------------------------------------------
  function bindObjectTree() {
    if (typeof runtime.listCells !== 'function') {
      treeListEl.innerHTML = '<li class="sb__list-empty">runtime has no listCells()</li>';
      return;
    }
    const sig = runtime.listCells();
    const stop = api.effect(() => {
      const cells = sig.value || [];
      cellCount.textContent = String(cells.length);
      treeListEl.replaceChildren();
      if (!cells.length) {
        const li = document.createElement('li');
        li.className = 'sb__list-empty';
        li.textContent = 'no cells yet';
        treeListEl.appendChild(li);
        return;
      }
      for (const c of cells) {
        const id = c.cell_id || c.id || (typeof c === 'string' ? c : null);
        if (!id) continue;
        const uri = `pyana://cell/${id}`;
        const li = document.createElement('li');
        const btn = document.createElement('button');
        btn.type = 'button';
        btn.className = 'sb__list-item';
        btn.textContent = `cell ${id.slice(0, 12)}…`;
        btn.title = id;
        if (currentUri === uri) btn.setAttribute('aria-current', 'true');
        btn.addEventListener('click', () => setCurrentUri(uri));
        li.appendChild(btn);
        treeListEl.appendChild(li);
      }
    });
    teardowns.push(stop);
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
    for (const btn of treeListEl.querySelectorAll('.sb__list-item')) {
      btn.removeAttribute('aria-current');
    }
    if (uri) {
      for (const btn of treeListEl.querySelectorAll('.sb__list-item')) {
        if (btn.title === uri.replace(/^pyana:\/\/[a-z-]+\//, '')) {
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
        opts.baseUrl = (window.localStorage && localStorage.getItem('pyana.remote.baseUrl')) || '';
      }
      runtime = await entry.factory(opts);
      currentRuntimeId = id;
      app.runtime = runtime;
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
    api = await whenPyana();

    setStatus('loading wasm…', 'boot');
    wasm = await import('/pkg/pyana_wasm.js');
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
        setStatus('not a valid pyana:// URI', 'err');
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
          window.pyanaUi?.toast?.(`${id}: ${err.message || err}`, 'err');
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

    // Wire the new Apps tab / <pyana-app-list> (STARBRIDGE-PLAN §4.8).
    // The list reads manifests; "Demo in inspector" for nameservice mounts
    // the first end-to-end starbridge-app inspectors (which reuse platform
    // <pyana-cell> + <pyana-capability> and the typed turn-builders).
    const appListEl = document.getElementById('sb-app-list');
    if (appListEl) {
      appListEl.addEventListener('app-demo', (e) => {
        const { app } = e.detail || {};
        if (app && app.id === 'nameservice') {
          inspector.replaceChildren();
          const demoWrap = document.createElement('div');
          demoWrap.style.cssText = 'padding:0.5rem;';
          demoWrap.innerHTML = `
            <h4 style="margin:0 0 0.5rem;font-size:0.95rem">Nameservice — first e2e starbridge-app demo (§4.8)</h4>
            <p style="margin:0 0 0.5rem;font-size:0.8rem;color:#555">Registry + detail using new shared inspectors (reusing &lt;pyana-cell&gt; etc.) + typed turn-builders from shared/.</p>
            <pyana-name-registry uri="pyana://cell/registry-default" page-size="6"></pyana-name-registry>
            <details style="margin-top:0.6rem;font-size:0.8rem">
              <summary>Per-name detail (reuses platform inspectors)</summary>
              <pyana-name uri="pyana://cell/registry-default" name="demo.pyana"></pyana-name>
            </details>
            <div style="margin-top:0.5rem;font-size:0.75rem;color:#666">
              Open full interactive page: <a href="/starbridge-apps/nameservice/pages/index.html" target="_blank">/starbridge-apps/nameservice/pages/index.html</a>
            </div>
          `;
          inspector.appendChild(demoWrap);
          setStatus('nameservice e2e demo (Apps tab)', 'ready');
        } else if (app && app.id === 'identity') {
          inspector.replaceChildren();
          const demoWrap = document.createElement('div');
          demoWrap.style.cssText = 'padding:0.5rem;';
          demoWrap.innerHTML = `
            <h4 style="margin:0 0 0.5rem;font-size:0.95rem">Identity — high-quality additional starbridge-app demo (§4.8 FOLLOWUP-05)</h4>
            <p style="margin:0 0 0.5rem;font-size:0.8rem;color:#555">Credential lifecycle using platform vocabulary + app-specific <code>&lt;pyana-credential&gt;</code> inspectors (loaded via shared/ path fix) + typed turn-builders. Reuses &lt;pyana-cell&gt; etc. No new Effects.</p>
            <pyana-credential uri="pyana://cell/identity-issuer" style="max-width:480px"></pyana-credential>
            <div style="margin-top:0.5rem;font-size:0.75rem;color:#666">
              Full interactive: <a href="/starbridge-apps/identity/pages/index.html" target="_blank">/starbridge-apps/identity/pages/index.html</a> (issue/present/verify flows with real proofs).
            </div>
          `;
          inspector.appendChild(demoWrap);
          setStatus('identity high-quality e2e demo (Apps tab, beyond nameservice)', 'ready');
        } else if (app) {
          setStatus(`App: ${app.name} — open standalone for full demo`, 'ready');
        }
      });
    }
  } catch (e) {
    console.error('[starbridge] boot failed:', e);
    setStatus('boot failed: ' + (e?.message || e), 'err');
  }
})();

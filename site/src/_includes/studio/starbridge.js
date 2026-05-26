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
  const paletteOpenBtn = document.getElementById('sb-palette-open');
  const paletteEl = document.getElementById('sb-palette');
  const paletteInput = document.getElementById('sb-palette-input');
  const paletteList = document.getElementById('sb-palette-list');
  const paletteCloseBtn = document.getElementById('sb-palette-close');
  const runtimeConfig = document.getElementById('sb-runtime-config');
  const remoteUrlInput = document.getElementById('sb-remote-url');
  const connectBtn = document.getElementById('sb-connect');
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
  const workspaceTitle = document.getElementById('sb-workspace-title');
  const rawEl      = document.getElementById('sb-raw');
  const rawFilter = document.getElementById('sb-raw-filter');
  const rawCopyBtn = document.getElementById('sb-raw-copy');
  const consoleEl = document.getElementById('sb-console');
  const consoleOut = document.getElementById('sb-console-output');
  const consoleForm = document.getElementById('sb-console-form');
  const consoleInput = document.getElementById('sb-console-input');
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
  const appCatalog = new Map();
  let rawText = 'no object selected';
  let labBusy = 0;
  const labState = {
    alice: null,
    bob: null,
    federation: null,
    lastTransfer: null,
    lastIntent: null,
  };

  // Per-runtime teardown of effects we owned. Cleared and rebuilt on swap.
  const teardowns = [];
  function disposeRuntimeEffects() {
    while (teardowns.length) {
      const t = teardowns.pop();
      try { t(); } catch (e) { console.warn('[starbridge] teardown:', e); }
    }
  }

  function updateRuntimeConfigVisibility() {
    if (!runtimeConfig) return;
    runtimeConfig.hidden = pickerEl.value !== 'remote';
    if (remoteUrlInput && !remoteUrlInput.value) {
      remoteUrlInput.value = (window.localStorage && localStorage.getItem('dregg.remote.baseUrl'))
        || 'https://devnet.dregg.fg-goose.online';
    }
  }

  function runtimeLabel() {
    return runtime?.source?.label || currentRuntimeId || 'runtime';
  }

  function currentCounts() {
    const safeLen = (read) => {
      try {
        const v = read();
        return Array.isArray(v) ? v.length : 0;
      } catch { return 0; }
    };
    return {
      cells: safeLen(() => runtime?.listCells?.().value || []),
      receipts: safeLen(() => runtime?.listReceipts?.().value || []),
      intents: safeLen(() => runtime?.listIntents?.().value || []),
      activities: safeLen(() => runtime?.getTraceEvents?.().value?.events || []),
    };
  }

  function selectWorkbenchTool(tool) {
    const showConsole = tool === 'console';
    if (rawEl) rawEl.hidden = showConsole;
    if (consoleEl) consoleEl.hidden = !showConsole;
    for (const btn of document.querySelectorAll('[data-tool]')) {
      btn.setAttribute('aria-selected', btn.dataset.tool === tool ? 'true' : 'false');
    }
    if (showConsole) queueMicrotask(() => consoleInput?.focus());
  }

  function consoleLog(message, kind = 'info') {
    if (!consoleOut) return;
    const line = document.createElement('div');
    line.className = `sb__console-line sb__console-line--${kind}`;
    line.textContent = message;
    consoleOut.appendChild(line);
    consoleOut.scrollTop = consoleOut.scrollHeight;
  }

  function appMetaFor(id) {
    return appCatalog.get(id) || {
      id,
      name: id.replace(/-/g, ' '),
      page: `/starbridge-apps/${id}/pages/index.html`,
    };
  }

  function setRawText(text) {
    rawText = String(text ?? '');
    renderRawText();
  }

  function renderRawText() {
    if (!rawEl) return;
    const filter = rawFilter?.value.trim().toLowerCase() || '';
    if (!filter) {
      rawEl.textContent = rawText;
      return;
    }
    const lines = rawText.split('\n').filter((line) => line.toLowerCase().includes(filter));
    rawEl.textContent = lines.length ? lines.join('\n') : 'no matching lines';
  }

  function readArraySignal(read) {
    try {
      const value = read();
      return Array.isArray(value) ? value : [];
    } catch {
      return [];
    }
  }

  function paletteItems() {
    const items = [
      { group: 'Scripts', label: 'Seed alice + bob', detail: 'Create starter agents', run: seedWorld },
      { group: 'Scripts', label: 'Run transfer turn', detail: 'Transfer from alice to bob', run: runTransferFlow },
      { group: 'Scripts', label: 'Create federation block', detail: 'Finalize a local federation block', run: createFederationFlow },
      { group: 'Scripts', label: 'Post storage intent', detail: 'Publish a storage need intent', run: postIntentFlow },
      { group: 'Workbench', label: 'Open console', detail: 'Switch right pane to console', run: () => selectWorkbenchTool('console') },
      { group: 'Workbench', label: 'Open raw view', detail: 'Switch right pane to raw JSON', run: () => selectWorkbenchTool('raw') },
      { group: 'Workbench', label: 'Export snapshot', detail: 'Download runtime JSON snapshot', run: exportSnapshot },
      { group: 'Workbench', label: 'Activity feed', detail: 'Inspect runtime activity', run: () => setCurrentUri('dregg://activity/feed') },
    ];

    for (const id of ['nameservice', 'identity', 'governed-namespace', 'subscription']) {
      const appMeta = appMetaFor(id);
      items.push({
        group: 'Programs',
        label: appMeta.name || id,
        detail: `Open ${id}`,
        run: () => renderAppWorkspace(appMetaFor(id)),
      });
    }
    for (const id of Object.keys(kinds || {})) {
      items.push({
        group: 'Runtimes',
        label: kinds[id]?.label || id,
        detail: id,
        run: async () => {
          pickerEl.value = id;
          updateRuntimeConfigVisibility();
          await swapRuntime(id);
        },
      });
    }

    const cells = readArraySignal(() => runtime?.listCells?.().value);
    for (const cell of cells.slice(0, 16)) {
      const id = cell.cell_id || cell.id || (typeof cell === 'string' ? cell : '');
      if (!id) continue;
      items.push({ group: 'Objects', label: `Cell ${id.slice(0, 12)}`, detail: id, run: () => setCurrentUri(`dregg://cell/${id}`) });
    }
    const receipts = readArraySignal(() => runtime?.listReceipts?.().value);
    for (const receipt of receipts.slice(0, 16)) {
      const id = receipt.turn_hash || receipt.receipt_hash || receipt.hash || '';
      if (!id) continue;
      items.push({ group: 'Objects', label: `Receipt ${id.slice(0, 12)}`, detail: id, run: () => setCurrentUri(`dregg://receipt/${id}`) });
    }
    const intents = readArraySignal(() => runtime?.listIntents?.().value);
    for (const [idx, intent] of intents.slice(0, 16).entries()) {
      const id = intent.intent_id || intent.id || String(intent.intent_index ?? idx);
      items.push({ group: 'Objects', label: `${intent.kind || 'Intent'} ${String(id).slice(0, 12)}`, detail: String(id), run: () => setCurrentUri(`dregg://intent/${id}`) });
    }
    const blocks = readArraySignal(() => runtime?.listBlocks?.().value);
    for (const block of blocks.slice(0, 16)) {
      const h = block.height ?? block.block_height ?? 0;
      const fedIndex = block.fed_index ?? 0;
      items.push({ group: 'Objects', label: `Block h=${h} fed #${fedIndex}`, detail: block.block_hash || '', run: () => setCurrentUri(`dregg://block/${fedIndex}/${h}`) });
    }
    return items;
  }

  function paletteScore(item, query) {
    if (!query) return 1;
    const hay = `${item.group} ${item.label} ${item.detail}`.toLowerCase();
    const needle = query.toLowerCase().trim();
    if (hay.includes(needle)) return 10 + needle.length;
    let pos = 0;
    for (const ch of needle) {
      pos = hay.indexOf(ch, pos);
      if (pos < 0) return 0;
      pos += 1;
    }
    return 2;
  }

  function renderPalette() {
    if (!paletteList) return;
    const query = paletteInput?.value || '';
    const matches = paletteItems()
      .map((item) => ({ item, score: paletteScore(item, query) }))
      .filter((entry) => entry.score > 0)
      .sort((a, b) => b.score - a.score || a.item.group.localeCompare(b.item.group) || a.item.label.localeCompare(b.item.label))
      .slice(0, 18);
    paletteList.replaceChildren();
    if (!matches.length) {
      const empty = document.createElement('div');
      empty.className = 'sb__palette-empty';
      empty.textContent = 'No matching command';
      paletteList.appendChild(empty);
      return;
    }
    for (const [idx, { item }] of matches.entries()) {
      const btn = document.createElement('button');
      btn.type = 'button';
      btn.className = 'sb__palette-item';
      btn.setAttribute('role', 'option');
      btn.setAttribute('aria-selected', idx === 0 ? 'true' : 'false');
      btn.innerHTML = `
        <span class="sb__palette-item-main">${escapeHtml(item.label)}</span>
        <span class="sb__palette-item-detail">${escapeHtml(item.group)} · ${escapeHtml(item.detail || '')}</span>
      `;
      btn.addEventListener('click', async () => {
        closePalette();
        await item.run();
      });
      paletteList.appendChild(btn);
    }
  }

  function openPalette(seed = '') {
    if (!paletteEl) return;
    paletteEl.hidden = false;
    if (paletteInput) paletteInput.value = seed;
    renderPalette();
    queueMicrotask(() => paletteInput?.focus());
  }

  function closePalette() {
    if (paletteEl) paletteEl.hidden = true;
  }

  async function runSelectedPaletteItem() {
    const selected = paletteList?.querySelector('.sb__palette-item[aria-selected="true"]');
    if (!selected) return;
    selected.click();
  }

  function movePaletteSelection(delta) {
    const items = Array.from(paletteList?.querySelectorAll('.sb__palette-item') || []);
    if (!items.length) return;
    const current = items.findIndex((item) => item.getAttribute('aria-selected') === 'true');
    const next = (current + delta + items.length) % items.length;
    items.forEach((item, idx) => item.setAttribute('aria-selected', idx === next ? 'true' : 'false'));
    items[next].scrollIntoView({ block: 'nearest' });
  }

  // --------------------------------------------------------------------------
  // Inspector pane: mount a `<dregg-${kind}>` for the current URI, or show a
  // helpful empty/missing-kind message.
  // --------------------------------------------------------------------------
  function renderAppWorkspace(appMeta) {
    if (appMeta?.id) appCatalog.set(appMeta.id, appMeta);
    inspector.replaceChildren();
    if (workspaceTitle) workspaceTitle.textContent = 'Program';
    setRawText(JSON.stringify(appMeta, null, 2));
    currentUri = `dregg://app/${appMeta.id}`;
    uriInput.value = currentUri;
    writeUrlState({ at: currentUri, runtime: currentRuntimeId });

    const shell = document.createElement('div');
    shell.className = 'sb__app-host';
    const pageUrl = new URL(appMeta.page || `/starbridge-apps/${appMeta.id}/pages/index.html`, window.location.origin);
    if (pageUrl.pathname.endsWith('/index.html')) {
      pageUrl.pathname = pageUrl.pathname.slice(0, -'index.html'.length);
    }
    pageUrl.searchParams.set('embedded', '1');
    pageUrl.searchParams.set('runtime', currentRuntimeId || 'in-memory');
    const page = pageUrl.pathname + pageUrl.search + pageUrl.hash;
    const registryUri = appMeta.registry_uri || appMeta.registryUri || '';
    shell.innerHTML = `
      <div class="sb__app-hostbar">
        <div>
          <div class="sb__app-title">${escapeHtml(appMeta.name || appMeta.id)}</div>
          <div class="sb__app-meta">
            <span>${escapeHtml(appMeta.description || 'starbridge-app')}</span>
            <code>${escapeHtml(currentRuntimeId || 'runtime')}</code>
            <code>dregg://app/${escapeHtml(appMeta.id)}</code>
          </div>
        </div>
        <div class="sb__app-actions">
          ${registryUri ? `<button type="button" class="sb__btn sb__btn--small" data-uri="${escapeHtml(registryUri)}">Inspect registry</button>` : ''}
          <button type="button" class="sb__btn sb__btn--small sb__btn--ghost" data-reload-app>Reload</button>
          <a class="sb__btn sb__btn--small sb__btn--ghost" href="${escapeHtml(page)}" target="_blank">Pop out</a>
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
    shell.querySelector('[data-reload-app]')?.addEventListener('click', () => {
      const frame = shell.querySelector('.sb__app-frame');
      if (frame) frame.src = frame.src;
    });
    inspector.appendChild(shell);
    setStatus(`app workspace · ${appMeta.name || appMeta.id}`, 'ready');
  }

  function renderInspectorPane(uri) {
    inspector.replaceChildren();
    if (workspaceTitle) workspaceTitle.textContent = uri ? 'Inspector' : 'Workspace';
    if (!uri) {
      inspector.appendChild(renderDashboard());
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

  function renderDashboard() {
    const counts = currentCounts();
    const recent = [];
    for (const cell of readArraySignal(() => runtime?.listCells?.().value).slice(-4).reverse()) {
      const id = cell.cell_id || cell.id || (typeof cell === 'string' ? cell : '');
      if (id) recent.push({ uri: `dregg://cell/${id}`, label: `cell ${id.slice(0, 12)}`, kind: 'Cell' });
    }
    for (const receipt of readArraySignal(() => runtime?.listReceipts?.().value).slice(-3).reverse()) {
      const id = receipt.turn_hash || receipt.receipt_hash || receipt.hash || '';
      if (id) recent.push({ uri: `dregg://receipt/${id}`, label: `receipt ${id.slice(0, 12)}`, kind: 'Receipt' });
    }
    for (const block of readArraySignal(() => runtime?.listBlocks?.().value).slice(-2).reverse()) {
      const h = block.height ?? block.block_height ?? 0;
      const fedIndex = block.fed_index ?? 0;
      recent.push({ uri: `dregg://block/${fedIndex}/${h}`, label: `h=${h} fed #${fedIndex}`, kind: 'Block' });
    }
    const recentHtml = recent.length
      ? recent.slice(0, 8).map((item) => `
          <button type="button" class="sb__workbench-row" data-uri="${escapeHtml(item.uri)}">
            <span>${escapeHtml(item.kind)}</span>
            <strong>${escapeHtml(item.label)}</strong>
          </button>
        `).join('')
      : '<div class="sb__workbench-empty">No runtime objects yet</div>';
    const panel = document.createElement('div');
    panel.className = 'sb__dashboard';
    panel.innerHTML = `
      <section class="sb__workbench-status" aria-label="Runtime summary">
        <div class="sb__runtime-card">
          <span>Runtime</span>
          <strong>${escapeHtml(runtimeLabel())}</strong>
          <code>${escapeHtml(currentRuntimeId || 'boot')}</code>
        </div>
        <div class="sb__metric"><span>Cells</span><strong>${counts.cells}</strong></div>
        <div class="sb__metric"><span>Receipts</span><strong>${counts.receipts}</strong></div>
        <div class="sb__metric"><span>Intents</span><strong>${counts.intents}</strong></div>
        <div class="sb__metric"><span>Activity</span><strong>${counts.activities}</strong></div>
      </section>
      <section class="sb__workbench-grid">
        <div class="sb__workbench-panel sb__workbench-panel--programs">
          <h3>System Programs</h3>
          <div class="sb__program-grid">
            <button type="button" class="sb__program" data-open-app="nameservice"><span>NS</span><strong>Nameservice</strong></button>
            <button type="button" class="sb__program" data-open-app="identity"><span>ID</span><strong>Identity</strong></button>
            <button type="button" class="sb__program" data-open-app="governed-namespace"><span>GN</span><strong>Namespace</strong></button>
            <button type="button" class="sb__program" data-open-app="subscription"><span>SUB</span><strong>Subscription</strong></button>
            <button type="button" class="sb__program" data-open-activity><span>ACT</span><strong>Activity</strong></button>
            <button type="button" class="sb__program" data-open-console><span>&gt;</span><strong>Console</strong></button>
          </div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Scripts</h3>
          <div class="sb__script-grid">
            <button type="button" class="sb__flow" data-flow="seed"><span>Seed</span><strong>alice + bob</strong></button>
            <button type="button" class="sb__flow" data-flow="transfer"><span>Turn</span><strong>transfer + receipt</strong></button>
            <button type="button" class="sb__flow" data-flow="federation"><span>Consensus</span><strong>federation block</strong></button>
            <button type="button" class="sb__flow" data-flow="intent"><span>Intent</span><strong>storage need</strong></button>
          </div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Recent Objects</h3>
          <div class="sb__recent-list">${recentHtml}</div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Direct Inspect</h3>
          <form class="sb__inline-form" data-uri-form>
            <input class="sb__input" name="uri" placeholder="dregg://cell/..." autocomplete="off" spellcheck="false">
            <button class="sb__btn" type="submit">Inspect</button>
          </form>
          <button type="button" class="sb__btn sb__btn--ghost sb__palette-inline" data-open-palette>Palette</button>
        </div>
      </section>
    `;
    panel.querySelector('[data-flow="seed"]')?.addEventListener('click', seedWorld);
    panel.querySelector('[data-flow="transfer"]')?.addEventListener('click', runTransferFlow);
    panel.querySelector('[data-flow="federation"]')?.addEventListener('click', createFederationFlow);
    panel.querySelector('[data-flow="intent"]')?.addEventListener('click', postIntentFlow);
    panel.querySelector('[data-open-activity]')?.addEventListener('click', () => setCurrentUri('dregg://activity/feed'));
    panel.querySelector('[data-open-console]')?.addEventListener('click', () => {
      selectWorkbenchTool('console');
      consoleLog('console ready. try: help, seed, transfer, fed, intent, app nameservice', 'ok');
    });
    for (const btn of panel.querySelectorAll('[data-open-app]')) {
      btn.addEventListener('click', () => renderAppWorkspace(appMetaFor(btn.dataset.openApp)));
    }
    panel.querySelector('[data-open-palette]')?.addEventListener('click', () => openPalette());
    for (const btn of panel.querySelectorAll('[data-uri]')) {
      btn.addEventListener('click', () => setCurrentUri(btn.dataset.uri));
    }
    panel.querySelector('[data-uri-form]')?.addEventListener('submit', (e) => {
      e.preventDefault();
      const v = new FormData(e.currentTarget).get('uri')?.toString().trim();
      if (v) setCurrentUri(v);
    });
    return panel;
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
        const fedIndex = block.fed_index ?? 0;
        return {
          uri: `dregg://block/${fedIndex}/${h}`,
          label: `h=${String(h)} · fed #${String(fedIndex)}`,
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

  async function setupSplitPanes() {
    if (!window.matchMedia('(min-width: 821px)').matches) return;
    try {
      const { default: Split } = await import('/_includes/vendor/split.es.js');
      const saved = window.localStorage && localStorage.getItem('starbridge.split.sizes');
      const sizes = saved ? JSON.parse(saved) : [18, 52, 30];
      Split(['.sb__pane--tree', '.sb__pane--inspector', '.sb__pane--raw'], {
        sizes,
        minSize: [180, 360, 260],
        gutterSize: 8,
        cursor: 'col-resize',
        onDragEnd(next) {
          try { localStorage.setItem('starbridge.split.sizes', JSON.stringify(next)); } catch {}
        },
      });
    } catch (e) {
      console.warn('[starbridge] split panes unavailable:', e);
    }
  }

  // --------------------------------------------------------------------------
  // Current URI mutator. Single funnel: pane render + raw pane + URL sync.
  // --------------------------------------------------------------------------
  function setCurrentUri(uri) {
    currentUri = uri || null;
    if (uri) uriInput.value = uri;
    if (uri) consoleLog(`inspect ${uri}`, 'cmd');
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

  async function runLab(label, fn) {
    if (!runtime) return;
    labBusy += 1;
    setLabButtonsDisabled(true);
    setStatus(`${label}…`, 'boot');
    consoleLog(`run ${label}`, 'cmd');
    try {
      const result = await fn();
      setStatus(`ready · ${runtimeLabel()}`, 'ready');
      consoleLog(`${label} complete`, 'ok');
      return result;
    } catch (err) {
      console.warn(`[starbridge] ${label} failed:`, err);
      setStatus(`${label} failed: ${err?.message || err}`, 'err');
      consoleLog(`${label} failed: ${err?.message || err}`, 'err');
      window.dreggUi?.toast?.(`${label}: ${err?.message || err}`, 'err');
      return null;
    } finally {
      labBusy = Math.max(0, labBusy - 1);
      if (labBusy === 0) setLabButtonsDisabled(false);
    }
  }

  function setLabButtonsDisabled(disabled) {
    for (const el of document.querySelectorAll('#sb-sim-actions button, .sb__flow')) {
      el.disabled = disabled;
    }
  }

  function requireMutable() {
    if (!(runtime?.caps && runtime.caps.mutate)) {
      throw new Error('current runtime is read-only');
    }
  }

  async function seedWorld() {
    return runLab('seed world', async () => {
      requireMutable();
      if (!labState.alice) labState.alice = await runtime.createAgent('alice', 5000);
      if (!labState.bob) labState.bob = await runtime.createAgent('bob', 0);
      const id = labState.alice?.cell_id || labState.alice?.cellId;
      if (id) setCurrentUri(`dregg://cell/${id}`);
      return { alice: labState.alice, bob: labState.bob };
    });
  }

  async function ensureSeeded() {
    if (!labState.alice || !labState.bob) await seedWorld();
    if (!labState.alice || !labState.bob) throw new Error('seed world did not produce agents');
  }

  async function runTransferFlow() {
    return runLab('transfer turn', async () => {
      requireMutable();
      await ensureSeeded();
      const result = await runtime.executeTurn(
        Number(labState.alice.agent_index ?? 0),
        [{ type: 'transfer', to: labState.bob.cell_id, amount: 100, excess: 500 }],
        500,
      );
      labState.lastTransfer = result;
      const hash = result?.turn_hash || result?.receipt_hash || result?.hash;
      if (hash) setCurrentUri(`dregg://receipt/${hash}`);
      return result;
    });
  }

  async function createFederationFlow() {
    return runLab('federation block', async () => {
      requireMutable();
      const fed = labState.federation || await runtime.createFederation('local-devnet', 4);
      labState.federation = fed;
      const fedIndex = Number(fed.fed_index ?? fed.registered_index ?? 0);
      let block = null;
      if (typeof runtime.proposeBlock === 'function') {
        block = await runtime.proposeBlock(fedIndex, [
          `event-${Date.now().toString(36)}`,
          `height-${runtime.cursor?.value ?? 0}`,
        ]);
      }
      if (block?.height != null) setCurrentUri(`dregg://block/${fedIndex}/${block.height}`);
      else setCurrentUri(`dregg://federation/${fedIndex}`);
      return { fed, block };
    });
  }

  async function postIntentFlow() {
    return runLab('storage intent', async () => {
      requireMutable();
      await ensureSeeded();
      if (typeof runtime.createIntent !== 'function') throw new Error('runtime has no createIntent');
      const expiry = Math.floor(Date.now() / 1000) + 3600;
      const intent = await runtime.createIntent(
        Number(labState.alice.agent_index ?? 0),
        'Need',
        [{ action: 'read', resource: 'docs/starbridge/*' }],
        [{ Service: 'storage' }],
        'dregg://resource/storage/docs/*',
        expiry,
      );
      labState.lastIntent = intent;
      const id = intent?.intent_id || intent?.intent_index || 0;
      setCurrentUri(`dregg://intent/${id}`);
      return intent;
    });
  }

  async function runConsoleCommand(raw) {
    const line = String(raw || '').trim();
    if (!line) return;
    consoleLog(`> ${line}`, 'input');
    const [cmd, ...args] = line.split(/\s+/);
    const rest = args.join(' ');
    switch (cmd.toLowerCase()) {
      case 'help':
      case '?':
        consoleLog('commands: help, status, seed, transfer, fed, intent, app <id>, inspect <uri>, runtime <id>, raw, clear, snapshot', 'ok');
        break;
      case 'status': {
        const counts = currentCounts();
        consoleLog(`${runtimeLabel()} · cells=${counts.cells} receipts=${counts.receipts} intents=${counts.intents} activity=${counts.activities} selected=${currentUri || '(none)'}`, 'ok');
        break;
      }
      case 'seed':
        await seedWorld();
        break;
      case 'transfer':
      case 'turn':
        await runTransferFlow();
        break;
      case 'fed':
      case 'federation':
      case 'block':
        await createFederationFlow();
        break;
      case 'intent':
        await postIntentFlow();
        break;
      case 'app':
      case 'open': {
        const id = rest || 'nameservice';
        renderAppWorkspace(appMetaFor(id));
        consoleLog(`opened app ${id}`, 'ok');
        break;
      }
      case 'inspect':
      case 'go':
        if (!rest || !isRef(rest)) consoleLog('usage: inspect dregg://kind/id', 'err');
        else setCurrentUri(rest);
        break;
      case 'raw':
        selectWorkbenchTool('raw');
        break;
      case 'console':
        selectWorkbenchTool('console');
        break;
      case 'snapshot':
        exportSnapshot();
        break;
      case 'runtime': {
        if (!rest) {
          consoleLog(`runtime ${currentRuntimeId}; available: ${Object.keys(kinds || {}).join(', ')}`, 'ok');
        } else if (!kinds?.[rest]) {
          consoleLog(`unknown runtime: ${rest}`, 'err');
        } else {
          pickerEl.value = rest;
          updateRuntimeConfigVisibility();
          await swapRuntime(rest);
          consoleLog(`runtime switched to ${rest}`, 'ok');
        }
        break;
      }
      case 'clear':
        if (consoleOut) consoleOut.replaceChildren();
        break;
      default:
        consoleLog(`unknown command: ${cmd}. type "help"`, 'err');
    }
  }

  // Independent teardown list for the raw pane, so URI changes don't dispose
  // the tree/cursor effects.
  const rawTeardowns = [];
  function rebindRawOnly(uri) {
    while (rawTeardowns.length) {
      const t = rawTeardowns.pop();
      try { t(); } catch {}
    }
    setRawText('no object selected');
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
      sig = parsed.sub?.length
        ? runtime.getBlock({ fedIndex: parsed.id, height: parsed.sub[0] })
        : runtime.getBlock(parsed.id);
    } else if (parsed.kind === 'activity' && typeof runtime.getTraceEvents === 'function') {
      sig = runtime.getTraceEvents();
    } else if (parsed.kind === 'app') {
      const appMeta = appCatalog.get(parsed.id) || { id: parsed.id, page: `/starbridge-apps/${parsed.id}/pages/index.html` };
      setRawText(JSON.stringify(appMeta, null, 2));
      return;
    }
    if (!sig) {
      setRawText(`no resolver for kind "${parsed.kind}"`);
      return;
    }
    const stop = api.effect(() => {
      const v = sig.value;
      if (v == null) {
        setRawText('no object loaded (not in this runtime)');
        return;
      }
      try {
        setRawText(JSON.stringify(v, (_, val) =>
          typeof val === 'bigint' ? val.toString() : val, 2));
      } catch (e) {
        setRawText('/* unserializable: ' + e.message + ' */');
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
        opts.baseUrl = (remoteUrlInput?.value || (window.localStorage && localStorage.getItem('dregg.remote.baseUrl')) || '').trim();
      }
      runtime = await entry.factory(opts);
      currentRuntimeId = id;
      app.runtime = runtime;
      if (simActions) simActions.hidden = !(runtime.caps && runtime.caps.mutate);
      bindObjectTree();
      bindCursor();
      rebindRawOnly(currentUri);
      updateRuntimeConfigVisibility();
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
    if (remoteUrlInput) {
      remoteUrlInput.value = (window.localStorage && localStorage.getItem('dregg.remote.baseUrl'))
        || 'https://devnet.dregg.fg-goose.online';
    }

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
    updateRuntimeConfigVisibility();

    await swapRuntime(initialId);
    await setupSplitPanes();

    if (url.at && isRef(url.at)) {
      setCurrentUri(url.at);
    } else {
      renderInspectorPane(null);
    }

    // --- Event wiring ---
    pickerEl.addEventListener('change', () => {
      updateRuntimeConfigVisibility();
      swapRuntime(pickerEl.value);
    });
    connectBtn?.addEventListener('click', () => {
      if (remoteUrlInput && window.localStorage) {
        localStorage.setItem('dregg.remote.baseUrl', remoteUrlInput.value.trim());
      }
      swapRuntime(pickerEl.value);
    });
    remoteUrlInput?.addEventListener('keydown', (e) => {
      if (e.key === 'Enter') {
        e.preventDefault();
        connectBtn?.click();
      }
    });

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
      exportSnapshot();
    });

    for (const tab of document.querySelectorAll('[data-tool]')) {
      tab.addEventListener('click', () => selectWorkbenchTool(tab.dataset.tool || 'raw'));
    }
    consoleForm?.addEventListener('submit', async (e) => {
      e.preventDefault();
      const raw = consoleInput?.value || '';
      if (consoleInput) consoleInput.value = '';
      await runConsoleCommand(raw);
    });
    consoleLog('console ready. type help for commands.', 'ok');

    paletteOpenBtn?.addEventListener('click', () => openPalette());
    paletteCloseBtn?.addEventListener('click', closePalette);
    paletteEl?.addEventListener('click', (e) => {
      if (e.target === paletteEl) closePalette();
    });
    paletteInput?.addEventListener('input', renderPalette);
    paletteInput?.addEventListener('keydown', async (e) => {
      if (e.key === 'Escape') {
        e.preventDefault();
        closePalette();
      } else if (e.key === 'ArrowDown') {
        e.preventDefault();
        movePaletteSelection(1);
      } else if (e.key === 'ArrowUp') {
        e.preventDefault();
        movePaletteSelection(-1);
      } else if (e.key === 'Enter') {
        e.preventDefault();
        await runSelectedPaletteItem();
      }
    });
    document.addEventListener('keydown', (e) => {
      if ((e.metaKey || e.ctrlKey) && e.key.toLowerCase() === 'k') {
        e.preventDefault();
        openPalette();
      } else if (e.key === 'Escape' && paletteEl && !paletteEl.hidden) {
        e.preventDefault();
        closePalette();
      }
    });

    // Sim convenience buttons (best-effort; absent on read-only runtimes).
    const btn = (id, fn) => {
      const e = document.getElementById(id);
      if (!e) return;
      e.addEventListener('click', () => runLab(id, fn));
    };
    btn('sb-seed-world', seedWorld);
    btn('sb-run-transfer', runTransferFlow);
    btn('sb-create-fed', createFederationFlow);
    btn('sb-post-intent', postIntentFlow);
    btn('sb-mk-alice', async () => {
      requireMutable();
      labState.alice = await runtime.createAgent('alice', 5000);
      if (labState.alice?.cell_id) setCurrentUri(`dregg://cell/${labState.alice.cell_id}`);
      return labState.alice;
    });
    btn('sb-mk-bob', async () => {
      requireMutable();
      labState.bob = await runtime.createAgent('bob', 0);
      if (labState.bob?.cell_id) setCurrentUri(`dregg://cell/${labState.bob.cell_id}`);
      return labState.bob;
    });
    btn('sb-advance', async () => {
      requireMutable();
      return runtime.advanceHeight && runtime.advanceHeight(1);
    });

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

  function readSignal(fn, fallback) {
    try {
      const sig = fn();
      return sig && 'value' in sig ? sig.value : fallback;
    } catch { return fallback; }
  }

  function buildSnapshot() {
    const state = {
      schema_version: 1,
      generated_at: new Date().toISOString(),
      runtime: currentRuntimeId,
      source: runtime?.source || null,
      selected_uri: currentUri,
      cursor: runtime?.cursor?.value ?? null,
      caps: runtime?.caps || null,
      cells: readSignal(() => runtime.listCells(), []),
      receipts: readSignal(() => runtime.listReceipts(), []),
      intents: readSignal(() => runtime.listIntents(), []),
      federations: readSignal(() => runtime.listKnownFederations(), []),
      blocks: readSignal(() => runtime.listBlocks(), []),
      activity: readSignal(() => runtime.getTraceEvents(), null),
    };
    return state;
  }

  function exportSnapshot() {
    const snapshot = buildSnapshot();
    const blob = new Blob([JSON.stringify(snapshot, null, 2)], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = `starbridge-${new Date().toISOString().replace(/[:.]/g, '-')}.json`;
    document.body.appendChild(a);
    a.click();
    a.remove();
    URL.revokeObjectURL(url);
    setStatus('snapshot exported', 'ready');
    consoleLog('snapshot exported', 'ok');
  }
})();

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

const STARBRIDGE_APP_IDS = [
  'nameservice',
  'identity',
  'governed-namespace',
  'subscription',
  'bounty-board',
  'gallery',
  'privacy-voting',
  'compute-exchange',
];
const FALLBACK_APPS = {
  nameservice: {
    id: 'nameservice',
    name: 'Nameservice',
    description: 'Federation name directory built from dregg-native primitives.',
    version: '0.1.0',
    page: '/starbridge-apps/nameservice/pages/index.html',
    inspectors: ['dregg-name', 'dregg-name-registry', 'dregg-name-register-form'],
    turn_builders: ['register_name', 'renew_name', 'transfer_name', 'revoke_name', 'set_target_name'],
    required_apis: ['signTurn', 'blake3', 'cell.readField', 'builders.nameservice'],
  },
  identity: {
    id: 'identity',
    name: 'Identity',
    description: 'Credential issuance and selective disclosure.',
    version: '0.1.0',
    page: '/starbridge-apps/identity/pages/index.html',
    inspectors: ['dregg-credential', 'dregg-credential-issue-form', 'dregg-credential-present-form', 'dregg-credential-verifier'],
    turn_builders: ['issue_credential', 'present_credential', 'verify_presentation'],
    required_apis: ['signTurn'],
  },
  'governed-namespace': {
    id: 'governed-namespace',
    name: 'Governed Namespace',
    description: 'Governance tables and proposals.',
    version: '0.1.0',
    page: '/starbridge-apps/governed-namespace/pages/index.html',
    inspectors: ['dregg-namespace', 'dregg-namespace-route-table', 'dregg-namespace-proposal', 'dregg-namespace-dispatch'],
    turn_builders: ['propose_route_table', 'vote_route_table', 'commit_route_table'],
    required_apis: ['signTurn'],
  },
  subscription: {
    id: 'subscription',
    name: 'Subscription',
    description: 'Pub/sub topic and capability subscription app.',
    version: '0.1.0',
    page: '/starbridge-apps/subscription/pages/index.html',
    inspectors: ['dregg-subscription', 'dregg-subscription-publish-form', 'dregg-subscription-feed'],
    turn_builders: ['publish', 'consume', 'grant_publisher', 'grant_consumer'],
    required_apis: ['signTurn'],
  },
  'bounty-board': {
    id: 'bounty-board',
    name: 'Bounty Board',
    description: 'Legacy bounty workflow app retained for porting.',
    version: '0.0.0',
    status: 'unported',
    legacy_path: 'apps/bounty-board',
    page: null,
  },
  gallery: {
    id: 'gallery',
    name: 'Gallery',
    description: 'Legacy private auction/gallery app retained for porting.',
    version: '0.0.0',
    status: 'unported',
    legacy_path: 'apps/gallery',
    page: null,
  },
  'privacy-voting': {
    id: 'privacy-voting',
    name: 'Privacy Voting',
    description: 'Legacy privacy voting app retained for porting.',
    version: '0.0.0',
    status: 'unported',
    legacy_path: 'apps/privacy-voting',
    page: null,
  },
  'compute-exchange': {
    id: 'compute-exchange',
    name: 'Compute Exchange',
    description: 'Legacy compute marketplace app retained for porting.',
    version: '0.0.0',
    status: 'unported',
    legacy_path: 'apps/compute-exchange',
    page: null,
  },
};

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
  const rootEl     = document.querySelector('.sb');
  const statusEl   = document.getElementById('sb-status');
  const pickerEl   = document.getElementById('sb-runtime');
  const uriInput   = document.getElementById('sb-uri');
  const goBtn      = document.getElementById('sb-go');
  const navBackBtn = document.getElementById('sb-nav-back');
  const navForwardBtn = document.getElementById('sb-nav-forward');
  const toggleMapBtn = document.getElementById('sb-toggle-map');
  const toggleWorkbenchBtn = document.getElementById('sb-toggle-workbench');
  const surfaceWorkbenchBtn = document.getElementById('sb-surface-workbench');
  const surfaceAppsBtn = document.getElementById('sb-surface-apps');
  const surfaceActivityBtn = document.getElementById('sb-surface-activity');
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
  const appCount = document.getElementById('sb-app-count');
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
  const outboxListEl = document.getElementById('sb-outbox-list');
  const outboxCount = document.getElementById('sb-outbox-count');
  const simActions = document.getElementById('sb-sim-actions');
  const inspector  = document.getElementById('sb-inspector');
  const workspaceTitle = document.getElementById('sb-workspace-title');
  const currentUriEl = document.getElementById('sb-current-uri');
  const currentKindEl = document.getElementById('sb-current-kind');
  const copyUriBtn = document.getElementById('sb-copy-uri');
  const pinUriBtn = document.getElementById('sb-pin-uri');
  const openExplorerLink = document.getElementById('sb-open-explorer');
  const rawEl      = document.getElementById('sb-raw');
  const rawFilter = document.getElementById('sb-raw-filter');
  const rawCopyBtn = document.getElementById('sb-raw-copy');
  const consoleEl = document.getElementById('sb-console');
  const consoleOut = document.getElementById('sb-console-output');
  const consoleForm = document.getElementById('sb-console-form');
  const consoleInput = document.getElementById('sb-console-input');
  const activityEl = document.getElementById('sb-activity');
  const activityPane = document.getElementById('sb-activity-list-pane');
  const activityRefreshBtn = document.getElementById('sb-activity-refresh');
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
  let navApplying = false;
  const localActivity = [];
  const navHistory = [];
  let navIndex = -1;
  const labState = {
    alice: null,
    bob: null,
    federation: null,
    lastTransfer: null,
    lastIntent: null,
  };

  function readShellLayout() {
    try {
      return JSON.parse(localStorage.getItem('starbridge.shell.layout') || '{}');
    } catch {
      return {};
    }
  }

  function writeShellLayout(next) {
    try { localStorage.setItem('starbridge.shell.layout', JSON.stringify(next)); } catch {}
  }

  function applyShellLayout(next = readShellLayout()) {
    if (!rootEl) return;
    rootEl.dataset.map = next.map === 'hidden' ? 'hidden' : 'visible';
    rootEl.dataset.workbench = next.workbench === 'hidden' ? 'hidden' : 'visible';
    if (toggleMapBtn) toggleMapBtn.setAttribute('aria-pressed', rootEl.dataset.map !== 'hidden' ? 'true' : 'false');
    if (toggleWorkbenchBtn) toggleWorkbenchBtn.setAttribute('aria-pressed', rootEl.dataset.workbench !== 'hidden' ? 'true' : 'false');
  }

  function toggleShellPane(key) {
    const next = readShellLayout();
    next[key] = next[key] === 'hidden' ? 'visible' : 'hidden';
    writeShellLayout(next);
    applyShellLayout(next);
  }

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
      outbox: safeLen(() => runtime?.getOutbox?.().value || []),
    };
  }

  function selectWorkbenchTool(tool) {
    const selected = ['raw', 'console', 'activity'].includes(tool) ? tool : 'raw';
    const showRaw = selected === 'raw';
    if (rawEl) rawEl.hidden = !showRaw;
    if (rawFilter) rawFilter.hidden = !showRaw;
    if (rawCopyBtn) rawCopyBtn.hidden = !showRaw;
    if (consoleEl) consoleEl.hidden = selected !== 'console';
    if (activityEl) activityEl.hidden = selected !== 'activity';
    for (const btn of document.querySelectorAll('[data-tool]')) {
      btn.setAttribute('aria-selected', btn.dataset.tool === selected ? 'true' : 'false');
    }
    if (selected === 'console') queueMicrotask(() => consoleInput?.focus());
    if (selected === 'activity') renderActivityPane();
  }

  function consoleLog(message, kind = 'info') {
    if (!consoleOut) return;
    const line = document.createElement('div');
    line.className = `sb__console-line sb__console-line--${kind}`;
    line.textContent = message;
    consoleOut.appendChild(line);
    consoleOut.scrollTop = consoleOut.scrollHeight;
  }

  function logActivity(kind, label, detail = {}) {
    localActivity.unshift({
      source: 'starbridge',
      kind,
      label,
      detail,
      at: new Date().toISOString(),
      uri: currentUri,
    });
    localActivity.splice(80);
    if (activityEl && !activityEl.hidden) renderActivityPane();
  }

  function appMetaFor(id) {
    return appCatalog.get(id) || fallbackAppMeta(id);
  }

  function openAppWorkspace(appMeta) {
    if (!appMeta?.id) return;
    if (appMeta.status === 'unported') {
      consoleLog(`${appMeta.name || appMeta.id} is a legacy app awaiting Starbridge porting`, 'err');
    }
    appCatalog.set(appMeta.id, appMeta);
    setCurrentUri(`dregg://app/${appMeta.id}`);
  }

  function setSurfaceCurrent(surface) {
    const entries = [
      [surfaceWorkbenchBtn, 'workbench'],
      [surfaceAppsBtn, 'apps'],
      [surfaceActivityBtn, 'activity'],
    ];
    for (const [btn, id] of entries) {
      if (!btn) continue;
      if (id === surface) btn.setAttribute('aria-current', 'page');
      else btn.removeAttribute('aria-current');
    }
  }

  function fallbackAppMeta(id) {
    const base = FALLBACK_APPS[id] || {};
    const hasPage = Object.prototype.hasOwnProperty.call(base, 'page');
    return {
      ...base,
      id,
      name: base.name || id.replace(/-/g, ' '),
      description: base.description || 'starbridge-app userspace surface',
      page: hasPage ? base.page : `/starbridge-apps/${id}/pages/index.html`,
    };
  }

  function normalizeAppMeta(meta, id) {
    const fallback = fallbackAppMeta(id || meta?.id);
    const metaHasPage = Object.prototype.hasOwnProperty.call(meta || {}, 'page');
    return {
      ...fallback,
      ...(meta || {}),
      id: meta?.id || fallback.id,
      name: meta?.name || fallback.name,
      description: meta?.description || fallback.description,
      page: metaHasPage ? meta.page : fallback.page,
      inspectors: Array.isArray(meta?.inspectors) ? meta.inspectors : (fallback.inspectors || []),
      turn_builders: Array.isArray(meta?.turn_builders) ? meta.turn_builders : (fallback.turn_builders || []),
      required_apis: Array.isArray(meta?.required_apis) ? meta.required_apis : (fallback.required_apis || []),
      factory_vks: Array.isArray(meta?.factory_vks) ? meta.factory_vks : (fallback.factory_vks || []),
      status: meta?.status || fallback.status || 'ported',
      legacy_path: meta?.legacy_path || fallback.legacy_path || null,
      manifest_path: `/starbridge-apps/${meta?.id || fallback.id}/manifest.json`,
    };
  }

  async function loadAppCatalog() {
    const loaded = await Promise.all(STARBRIDGE_APP_IDS.map(async (id) => {
      try {
        const resp = await fetch(`/starbridge-apps/${id}/manifest.json`, { headers: { Accept: 'application/json' } });
        if (!resp.ok) throw new Error(`${resp.status} ${resp.statusText}`);
        return normalizeAppMeta(await resp.json(), id);
      } catch (e) {
        console.warn(`[starbridge] app manifest unavailable for ${id}; using fallback`, e);
        return normalizeAppMeta(null, id);
      }
    }));
    appCatalog.clear();
    loaded.filter(Boolean).forEach((meta) => appCatalog.set(meta.id, meta));
    if (appCount) appCount.textContent = String(appCatalog.size);
    return loaded;
  }

  function appCatalogList() {
    return STARBRIDGE_APP_IDS.map((id) => appMetaFor(id));
  }

  function appInitials(appMeta) {
    const name = appMeta?.name || appMeta?.id || 'app';
    const words = name.replace(/[^a-z0-9 -]/gi, '').split(/\s+|-/).filter(Boolean);
    const letters = words.length > 1 ? words.slice(0, 2).map((w) => w[0]).join('') : name.slice(0, 3);
    return letters.toUpperCase();
  }

  function appPageHref(appMeta, { embedded = false } = {}) {
    if (appMeta.page === null) return '';
    const pageUrl = new URL(appMeta.page || `/starbridge-apps/${appMeta.id}/pages/index.html`, window.location.origin);
    if (embedded && pageUrl.pathname.endsWith('/index.html')) {
      pageUrl.pathname = pageUrl.pathname.slice(0, -'index.html'.length);
    }
    if (embedded) {
      pageUrl.searchParams.set('embedded', '1');
      pageUrl.searchParams.set('runtime', currentRuntimeId || 'in-memory');
    }
    return pageUrl.pathname + pageUrl.search + pageUrl.hash;
  }

  function appApiRows(appMeta) {
    const api = (typeof window !== 'undefined' && window.dregg) ? window.dregg : null;
    const runtimeCaps = runtime?.caps || {};
    return (appMeta.required_apis || []).map((name) => {
      let available = false;
      let source = 'missing';
      if (name === 'signTurn' || name === 'signTurnV3') {
        available = !!(api && (api[name] || api.signTurn));
        source = available ? 'extension' : 'extension required';
      } else if (name.startsWith('builders.') || name.startsWith('cell.')) {
        available = currentRuntimeId === 'in-memory' || currentRuntimeId === 'extension';
        source = available ? currentRuntimeId : 'host helper required';
      } else if (runtimeCaps.read && ['listCells', 'getCell'].includes(name)) {
        available = true;
        source = 'runtime';
      } else if (api && typeof api[name] === 'function') {
        available = true;
        source = 'extension';
      }
      return { name, available, source };
    });
  }

  function appHostMode(appMeta) {
    const rows = appApiRows(appMeta);
    if (appMeta.status === 'unported') return { label: 'Legacy', detail: 'not yet ported to Starbridge host' };
    if (!rows.length) return { label: 'View', detail: 'no explicit API requirements' };
    const missing = rows.filter((row) => !row.available);
    if (!missing.length) return { label: 'Ready', detail: 'all declared host APIs available' };
    return { label: 'Inspect-only', detail: `${missing.length} API requirement(s) unavailable in this host` };
  }

  function compactList(values, empty = 'none') {
    const list = Array.isArray(values) ? values.filter(Boolean) : [];
    return list.length ? list.join(', ') : empty;
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

  function rememberNavigation(uri) {
    if (navApplying) return;
    const key = uri || '';
    if (navHistory[navIndex] === key) {
      updateNavButtons();
      return;
    }
    navHistory.splice(navIndex + 1);
    navHistory.push(key);
    navIndex = navHistory.length - 1;
    updateNavButtons();
    if (uri) recordHistory(uri);
  }

  function updateNavButtons() {
    if (navBackBtn) navBackBtn.disabled = navIndex <= 0;
    if (navForwardBtn) navForwardBtn.disabled = navIndex < 0 || navIndex >= navHistory.length - 1;
  }

  function updateCurrentContext(uri) {
    if (!uri) {
      if (currentUriEl) currentUriEl.textContent = 'no object selected';
      if (currentKindEl) currentKindEl.textContent = 'Dashboard';
      if (copyUriBtn) copyUriBtn.disabled = true;
      if (openExplorerLink) openExplorerLink.href = '/explorer/';
      if (pinUriBtn) {
        pinUriBtn.disabled = true;
        pinUriBtn.textContent = 'Pin';
        pinUriBtn.setAttribute('aria-pressed', 'false');
      }
      return;
    }
    let label = 'Object';
    try {
      const parsed = parseRef(uri);
      label = parsed.kind ? parsed.kind[0].toUpperCase() + parsed.kind.slice(1) : 'Object';
    } catch {}
    if (currentUriEl) currentUriEl.textContent = uri;
    if (currentKindEl) currentKindEl.textContent = label;
    if (copyUriBtn) copyUriBtn.disabled = false;
    if (openExplorerLink) openExplorerLink.href = `/explorer/?at=${encodeURIComponent(uri)}`;
    if (pinUriBtn) {
      const pinned = isPinned(uri);
      pinUriBtn.disabled = false;
      pinUriBtn.textContent = pinned ? 'Pinned' : 'Pin';
      pinUriBtn.setAttribute('aria-pressed', pinned ? 'true' : 'false');
    }
  }

  function parseKind(uri) {
    try { return parseRef(uri).kind || 'object'; }
    catch { return 'object'; }
  }

  function readPins() {
    try {
      const pins = JSON.parse(localStorage.getItem('starbridge.pins') || '[]');
      return Array.isArray(pins) ? pins.filter((pin) => pin && pin.uri) : [];
    } catch {
      return [];
    }
  }

  function writePins(pins) {
    try { localStorage.setItem('starbridge.pins', JSON.stringify(pins.slice(0, 80))); } catch {}
  }

  function isPinned(uri) {
    return readPins().some((pin) => pin.uri === uri);
  }

  function pinLabel(uri) {
    const kind = parseKind(uri);
    const id = uri.split('/').pop() || uri;
    return `${kind} ${id.length > 18 ? id.slice(0, 18) + '…' : id}`;
  }

  function readHistory() {
    try {
      const history = JSON.parse(localStorage.getItem('starbridge.history') || '[]');
      return Array.isArray(history) ? history.filter((item) => item && item.uri) : [];
    } catch {
      return [];
    }
  }

  function writeHistory(history) {
    try { localStorage.setItem('starbridge.history', JSON.stringify(history.slice(0, 60))); } catch {}
  }

  function recordHistory(uri) {
    const history = readHistory().filter((item) => item.uri !== uri);
    history.unshift({
      uri,
      label: pinLabel(uri),
      kind: parseKind(uri),
      runtime: currentRuntimeId,
      visited_at: new Date().toISOString(),
    });
    writeHistory(history);
  }

  function togglePin(uri = currentUri) {
    if (!uri) return;
    const pins = readPins();
    const existing = pins.findIndex((pin) => pin.uri === uri);
    if (existing >= 0) {
      const [removed] = pins.splice(existing, 1);
      writePins(pins);
      setStatus('unpinned ' + removed.label, 'ready');
      logActivity('pin', `unpinned ${removed.label}`, { uri });
    } else {
      const pin = {
        uri,
        label: pinLabel(uri),
        kind: parseKind(uri),
        runtime: currentRuntimeId,
        created_at: new Date().toISOString(),
      };
      pins.unshift(pin);
      writePins(pins);
      setStatus('pinned ' + pin.label, 'ready');
      logActivity('pin', `pinned ${pin.label}`, { uri });
    }
    updateCurrentContext(currentUri);
    if (!currentUri) renderInspectorPane(null);
  }

  function readSnapshots() {
    try {
      const snapshots = JSON.parse(localStorage.getItem('starbridge.snapshots') || '[]');
      return Array.isArray(snapshots) ? snapshots.filter((s) => s && s.id && s.snapshot) : [];
    } catch {
      return [];
    }
  }

  function writeSnapshots(snapshots) {
    try { localStorage.setItem('starbridge.snapshots', JSON.stringify(snapshots.slice(0, 12))); } catch {}
  }

  function snapshotLabel(snapshot) {
    const counts = [
      `${Array.isArray(snapshot.cells) ? snapshot.cells.length : 0} cells`,
      `${Array.isArray(snapshot.receipts) ? snapshot.receipts.length : 0} receipts`,
      `${Array.isArray(snapshot.blocks) ? snapshot.blocks.length : 0} blocks`,
    ];
    return `${snapshot.runtime || 'runtime'} · ${counts.join(' · ')}`;
  }

  function saveSnapshotRecord(snapshot) {
    const record = {
      id: `snap-${Date.now().toString(36)}`,
      label: snapshotLabel(snapshot),
      created_at: snapshot.generated_at,
      selected_uri: snapshot.selected_uri,
      snapshot,
    };
    const snapshots = readSnapshots();
    snapshots.unshift(record);
    writeSnapshots(snapshots);
    return record;
  }

  function openSnapshotRecord(id) {
    const record = readSnapshots().find((snap) => snap.id === id);
    if (!record) return;
    setRawText(JSON.stringify(record.snapshot, null, 2));
    selectWorkbenchTool('raw');
    setStatus('snapshot opened', 'ready');
    logActivity('snapshot', `opened ${record.label}`, { id });
  }

  function snapshotStats(record) {
    const snap = record?.snapshot || {};
    return {
      cells: Array.isArray(snap.cells) ? snap.cells.length : 0,
      receipts: Array.isArray(snap.receipts) ? snap.receipts.length : 0,
      intents: Array.isArray(snap.intents) ? snap.intents.length : 0,
      blocks: Array.isArray(snap.blocks) ? snap.blocks.length : 0,
      cursor: snap.cursor ?? 0,
    };
  }

  function compareSnapshotRecords(leftId, rightId) {
    const snapshots = readSnapshots();
    const left = snapshots.find((snap) => snap.id === leftId);
    const right = snapshots.find((snap) => snap.id === rightId);
    if (!left || !right) return;
    const a = snapshotStats(left);
    const b = snapshotStats(right);
    const rows = ['cursor', 'cells', 'receipts', 'intents', 'blocks'].map((key) => ({
      field: key,
      left: a[key],
      right: b[key],
      delta: Number(b[key] || 0) - Number(a[key] || 0),
    }));
    setRawText(JSON.stringify({
      compare: {
        left: { id: left.id, created_at: left.created_at, label: left.label },
        right: { id: right.id, created_at: right.created_at, label: right.label },
        rows,
      },
    }, null, 2));
    selectWorkbenchTool('raw');
    setStatus('snapshot comparison opened', 'ready');
    logActivity('snapshot', `compared ${left.label} -> ${right.label}`, { left: left.id, right: right.id });
  }

  function mountInspectorSlot(parent, uri) {
    const slot = document.createElement('section');
    slot.className = 'sb__side-slot';
    slot.innerHTML = `
      <header>
        <strong>${escapeHtml(pinLabel(uri))}</strong>
        <code>${escapeHtml(uri)}</code>
      </header>
    `;
    let parsed = null;
    try { parsed = parseRef(uri); } catch {}
    if (!parsed) {
      const empty = document.createElement('div');
      empty.className = 'sb__inspector-empty';
      empty.textContent = 'bad URI';
      slot.appendChild(empty);
    } else {
      const tagName = `dregg-${parsed.kind}`;
      if (customElements.get(tagName)) {
        const el = document.createElement(tagName);
        el.setAttribute('uri', uri);
        slot.appendChild(el);
      } else {
        const empty = document.createElement('div');
        empty.className = 'sb__inspector-empty';
        empty.textContent = `no inspector registered for kind "${parsed.kind}"`;
        slot.appendChild(empty);
      }
    }
    parent.appendChild(slot);
  }

  function renderSideBySide(leftUri, rightUri = currentUri) {
    if (!leftUri || !rightUri) return;
    inspector.replaceChildren();
    if (workspaceTitle) workspaceTitle.textContent = 'Side by Side';
    updateCurrentContext(rightUri);
    currentUri = rightUri;
    uriInput.value = rightUri;
    writeUrlState({ at: rightUri, runtime: currentRuntimeId });
    const panel = document.createElement('div');
    panel.className = 'sb__side-by-side';
    const head = document.createElement('div');
    head.className = 'sb__side-head';
    head.innerHTML = `
      <span>Inspector compare</span>
      <button type="button" class="sb__icon-btn" data-close-split>Single inspector</button>
    `;
    panel.appendChild(head);
    const grid = document.createElement('div');
    grid.className = 'sb__side-grid';
    mountInspectorSlot(grid, leftUri);
    mountInspectorSlot(grid, rightUri);
    panel.appendChild(grid);
    panel.querySelector('[data-close-split]')?.addEventListener('click', () => setCurrentUri(rightUri));
    inspector.appendChild(panel);
    rebindRawOnly(rightUri);
    rememberNavigation(rightUri);
    setStatus('side-by-side inspectors opened', 'ready');
  }

  function jumpNavigation(delta) {
    const next = navIndex + delta;
    if (next < 0 || next >= navHistory.length) return;
    navApplying = true;
    navIndex = next;
    setCurrentUri(navHistory[navIndex] || null);
    navApplying = false;
    updateNavButtons();
  }

  function activityEvents() {
    let runtimeEvents = [];
    try {
      const feed = runtime?.getTraceEvents?.().value;
      runtimeEvents = Array.isArray(feed?.events) ? feed.events : [];
    } catch {
      runtimeEvents = [];
    }
    return [...localActivity, ...runtimeEvents.map((event) => ({ source: 'runtime', ...event }))];
  }

  function renderActivityPane() {
    if (!activityPane) return;
    const events = activityEvents();
    activityPane.replaceChildren();
    if (!events.length) {
      const empty = document.createElement('div');
      empty.className = 'sb__activity-empty';
      empty.textContent = 'No activity yet';
      activityPane.appendChild(empty);
      return;
    }
    for (const [idx, event] of events.slice(0, 80).entries()) {
      const row = document.createElement('button');
      row.type = 'button';
      row.className = 'sb__activity-row';
      const kind = event.kind || event.event_type || event.type || 'event';
      const label = event.label || event.message || event.cell_id || event.turn_hash || event.receipt_hash || `event ${events.length - idx}`;
      row.innerHTML = `
        <span>${escapeHtml(kind)}</span>
        <strong>${escapeHtml(label)}</strong>
        <code>${escapeHtml(safeJson(event).slice(0, 160))}</code>
      `;
      row.addEventListener('click', () => {
        setRawText(safeJson(event, 2));
        selectWorkbenchTool('raw');
      });
      activityPane.appendChild(row);
    }
  }

  function paletteItems() {
    const items = [
      { group: 'Scripts', label: 'Seed alice + bob', detail: 'Create starter agents', run: seedWorld },
      { group: 'Scripts', label: 'Run transfer turn', detail: 'Transfer from alice to bob', run: runTransferFlow },
      { group: 'Scripts', label: 'Create federation block', detail: 'Finalize a local federation block', run: createFederationFlow },
      { group: 'Scripts', label: 'Post storage intent', detail: 'Publish a storage need intent', run: postIntentFlow },
      { group: 'Workbench', label: 'Open console', detail: 'Switch right pane to console', priority: 8, run: () => selectWorkbenchTool('console') },
      { group: 'Workbench', label: 'Open raw view', detail: 'Switch right pane to raw JSON', priority: 8, run: () => selectWorkbenchTool('raw') },
      { group: 'Workbench', label: 'Open activity', detail: 'Show runtime event feed', priority: 10, run: () => selectWorkbenchTool('activity') },
      { group: 'Workbench', label: 'Export snapshot', detail: 'Download runtime JSON snapshot', run: exportSnapshot },
      { group: 'Workbench', label: 'Inspect activity feed', detail: 'Open activity inspector URI', run: () => setCurrentUri('dregg://activity/feed') },
      { group: 'Workbench', label: 'Inspect outbox', detail: 'Queued extension submissions', priority: 10, run: () => setCurrentUri('dregg://outbox/queue') },
      { group: 'Collections', label: 'All receipts', detail: 'Open runtime receipt list', priority: 7, run: () => setCurrentUri('dregg://receipt-list/all') },
      { group: 'Collections', label: 'All federations', detail: 'Open known federation list', priority: 7, run: () => setCurrentUri('dregg://federation-list/all') },
      { group: 'Collections', label: 'Agent 0 capabilities', detail: 'Open capability list for first agent', priority: 6, run: () => setCurrentUri('dregg://capability-list/0') },
    ];

    for (const snap of readSnapshots()) {
      items.push({
        group: 'Snapshots',
        label: snap.label || 'Snapshot',
        detail: snap.created_at || snap.id,
        priority: 4,
        run: () => openSnapshotRecord(snap.id),
      });
    }

    for (const pin of readPins()) {
      items.push({
        group: 'Pinned',
        label: pin.label || pinLabel(pin.uri),
        detail: pin.uri,
        priority: 6,
        run: () => setCurrentUri(pin.uri),
      });
    }

    for (const appMeta of appCatalogList()) {
      const hostMode = appHostMode(appMeta);
      items.push({
        group: 'Programs',
        label: appMeta.name || appMeta.id,
        detail: `${hostMode.label} · ${appMeta.id} · ${compactList(appMeta.required_apis, 'no API requirements')}`,
        priority: appMeta.status === 'unported' ? 1 : 5,
        run: () => openAppWorkspace(appMetaFor(appMeta.id)),
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
      .sort((a, b) => b.score - a.score || (b.item.priority || 0) - (a.item.priority || 0) || a.item.group.localeCompare(b.item.group) || a.item.label.localeCompare(b.item.label))
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
        <span class="sb__palette-item-main">
          <span>${escapeHtml(item.label)}</span>
          <code>${escapeHtml(item.group)}</code>
        </span>
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
    updateCurrentContext(`dregg://app/${appMeta.id}`);
    setRawText(JSON.stringify(appMeta, null, 2));
    currentUri = `dregg://app/${appMeta.id}`;
    uriInput.value = currentUri;
    writeUrlState({ at: currentUri, runtime: currentRuntimeId });

    const shell = document.createElement('div');
    shell.className = 'sb__app-host';
    const page = appPageHref(appMeta, { embedded: true });
    const standalonePage = appPageHref(appMeta);
    const hasPage = !!page;
    const registryUri = appMeta.registry_uri || appMeta.registryUri || '';
    const apiRows = appApiRows(appMeta);
    const hostMode = appHostMode(appMeta);
    const inspectorButtons = (appMeta.inspectors || []).slice(0, 8).map((name) => `
      <button type="button" class="sb__app-chip" data-inspector-kind="${escapeHtml(String(name).replace(/^dregg-/, ''))}">
        ${escapeHtml(name)}
      </button>
    `).join('');
    const factoryButtons = (appMeta.factory_vks || []).slice(0, 6).map((vk) => `
      <button type="button" class="sb__app-chip" data-uri="dregg://factory/${escapeHtml(vk)}">
        factory ${escapeHtml(String(vk).slice(0, 10))}
      </button>
    `).join('');
    const apiRowsHtml = apiRows.length
      ? apiRows.map((row) => `
        <div class="sb__app-api-row" data-ok="${row.available ? 'true' : 'false'}">
          <span>${escapeHtml(row.available ? 'ready' : 'missing')}</span>
          <strong>${escapeHtml(row.name)}</strong>
          <code>${escapeHtml(row.source)}</code>
        </div>
      `).join('')
      : '<div class="sb__app-empty">No required APIs declared</div>';
    const details = [
      ['Version', appMeta.version || 'unknown'],
      ['Required APIs', compactList(appMeta.required_apis)],
      ['Inspectors', compactList(appMeta.inspectors)],
      ['Turn builders', compactList(appMeta.turn_builders)],
      ['Factory VKs', compactList(appMeta.factory_vks)],
    ];
    shell.innerHTML = `
      <div class="sb__app-hostbar">
        <div>
          <div class="sb__app-title">${escapeHtml(appMeta.name || appMeta.id)}</div>
          <div class="sb__app-meta">
            <span>${escapeHtml(appMeta.description || 'starbridge-app')}</span>
            <code>${escapeHtml(currentRuntimeId || 'runtime')}</code>
            <code>dregg://app/${escapeHtml(appMeta.id)}</code>
          </div>
          <dl class="sb__app-manifest">
            ${details.map(([term, value]) => `
              <div>
                <dt>${escapeHtml(term)}</dt>
                <dd>${escapeHtml(value)}</dd>
              </div>
            `).join('')}
          </dl>
        </div>
        <div class="sb__app-actions">
          ${registryUri ? `<button type="button" class="sb__btn sb__btn--small" data-uri="${escapeHtml(registryUri)}">Inspect registry</button>` : ''}
          <button type="button" class="sb__btn sb__btn--small sb__btn--ghost" data-manifest>Manifest</button>
          ${hasPage ? '<button type="button" class="sb__btn sb__btn--small sb__btn--ghost" data-reload-app>Reload</button>' : ''}
          ${standalonePage ? `<a class="sb__btn sb__btn--small sb__btn--ghost" href="${escapeHtml(standalonePage)}" target="_blank">Pop out</a>` : ''}
        </div>
      </div>
      <div class="sb__app-console">
        <section>
          <h3>Host Readiness <span data-mode="${escapeHtml(hostMode.label.toLowerCase())}">${escapeHtml(hostMode.label)}</span></h3>
          <p>${escapeHtml(hostMode.detail)}</p>
          <div class="sb__app-api-grid">${apiRowsHtml}</div>
        </section>
        <section>
          <h3>Contributed Inspectors</h3>
          <div class="sb__app-chip-row">${inspectorButtons || '<span class="sb__app-empty">No inspectors declared</span>'}</div>
        </section>
        <section>
          <h3>Factories</h3>
          <div class="sb__app-chip-row">${factoryButtons || '<span class="sb__app-empty">No factory VKs declared</span>'}</div>
        </section>
      </div>
      ${hasPage ? `
        <iframe
          class="sb__app-frame"
          title="${escapeHtml(appMeta.name || appMeta.id)} app workspace"
          src="${escapeHtml(page)}"
        ></iframe>
      ` : `
        <div class="sb__app-migration">
          <strong>Legacy app awaiting Starbridge port</strong>
          <p>This app is visible in the host catalog so the IDE can track its migration, inspect its manifest, and keep the end-user app roadmap in one place.</p>
          <dl>
            <div><dt>Legacy path</dt><dd><code>${escapeHtml(appMeta.legacy_path || 'apps/' + appMeta.id)}</code></dd></div>
            <div><dt>Target URI</dt><dd><code>dregg://app/${escapeHtml(appMeta.id)}</code></dd></div>
            <div><dt>Status</dt><dd>${escapeHtml(appMeta.status || 'unported')}</dd></div>
          </dl>
        </div>
      `}
    `;
    shell.querySelector('[data-uri]')?.addEventListener('click', (e) => {
      setCurrentUri(e.currentTarget.dataset.uri);
    });
    shell.querySelector('[data-manifest]')?.addEventListener('click', () => {
      setRawText(JSON.stringify(appMeta, null, 2));
      selectWorkbenchTool('raw');
    });
    shell.querySelector('[data-reload-app]')?.addEventListener('click', () => {
      const frame = shell.querySelector('.sb__app-frame');
      if (frame) frame.src = frame.src;
    });
    for (const btn of shell.querySelectorAll('[data-inspector-kind]')) {
      btn.addEventListener('click', () => {
        const kind = btn.dataset.inspectorKind;
        if (!kind) return;
        setCurrentUri(`dregg://${kind}/sample`);
      });
    }
    inspector.appendChild(shell);
    setStatus(`app workspace · ${appMeta.name || appMeta.id}`, 'ready');
    logActivity('program', `opened ${appMeta.name || appMeta.id}`, { app: appMeta.id, page });
  }

  function renderInspectorPane(uri) {
    inspector.replaceChildren();
    if (workspaceTitle) workspaceTitle.textContent = uri ? 'Inspector' : 'Workspace';
    if (!uri) {
      setSurfaceCurrent('workbench');
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
      setSurfaceCurrent('apps');
      renderAppWorkspace(appMetaFor(parsed.id));
      return;
    }
    setSurfaceCurrent(parsed.kind === 'activity' ? 'activity' : 'workbench');
    const inspectorAliases = {
      token: 'attenuated-token',
      queue: 'programmable-queue',
    };
    const inspectorKind = inspectorAliases[parsed.kind] || parsed.kind;
    const tagName = `dregg-${inspectorKind}`;
    if (!customElements.get(tagName)) {
      const err = document.createElement('div');
      err.className = 'sb__inspector-empty';
      err.textContent = `no inspector registered for kind "${parsed.kind}" (yet)`;
      inspector.appendChild(err);
      return;
    }
    const el = document.createElement(tagName);
    el.setAttribute('uri', inspectorKind === parsed.kind ? uri : `dregg://${inspectorKind}/${parsed.id}${parsed.sub?.length ? `/${parsed.sub.join('/')}` : ''}`);
    inspector.appendChild(el);
  }

  function escapeHtml(s) {
    return String(s ?? '').replace(/[&<>"']/g, (c) => ({
      '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
    })[c]);
  }

  function safeJson(value, spaces = 0) {
    const seen = new WeakSet();
    try {
      return JSON.stringify(value, (_, val) => {
        if (typeof val === 'bigint') return val.toString();
        if (val && typeof val === 'object') {
          if (seen.has(val)) return '[circular]';
          seen.add(val);
        }
        return val;
      }, spaces);
    } catch (e) {
      return `/* unserializable: ${e.message} */`;
    }
  }

  function runtimeBoundaryRows() {
    const caps = runtime?.caps || {};
    const status = readSignal(() => runtime.getExtensionStatus(), null);
    const balance = readSignal(() => runtime.getBalance(), null);
    const rows = [
      ['Runtime', runtimeLabel()],
      ['Mutation', caps.mutate ? 'enabled in this browser runtime' : 'not exposed by this runtime'],
      ['Cell hosting', currentRuntimeId === 'in-memory'
        ? 'local wasm simulation only'
        : currentRuntimeId === 'extension'
          ? 'node ledger required; extension stores keys/tokens/receipts'
          : 'remote node owns ledger state'],
      ['Offline queue', currentRuntimeId === 'extension'
        ? `${currentCounts().outbox} queued extension submission(s)`
        : currentRuntimeId === 'in-memory'
          ? 'local-only, not chain-synced'
          : 'read-only'],
      ['Node path', currentRuntimeId === 'extension'
        ? 'window.dregg -> extension background -> configured node HTTP/WS'
        : currentRuntimeId === 'remote'
          ? 'browser fetch/EventSource to configured node'
          : 'none'],
      ['Trust boundary', currentRuntimeId === 'extension'
        ? 'extension signs; node WS messages require /status public_key'
        : currentRuntimeId === 'remote'
          ? 'node data over HTTP/SSE; no signing controls'
          : 'simulator receipts are placeholders unless proof data exists'],
    ];
    if (status) {
      rows.push(['Node status', status.error ? `error: ${status.error}` : `${status.mode || 'unknown'} · height ${status.height ?? 0}`]);
    }
    if (balance) {
      rows.push(['Balance', balance.error ? `error: ${balance.error}` : `${balance.balance ?? 'unknown'}`]);
    }
    return rows;
  }

  function renderDashboard() {
    const counts = currentCounts();
    const pins = readPins();
    const snapshots = readSnapshots();
    const history = readHistory();
    const boundaryHtml = runtimeBoundaryRows().map(([label, value]) => `
      <div class="sb__boundary-row">
        <span>${escapeHtml(label)}</span>
        <strong>${escapeHtml(value)}</strong>
      </div>
    `).join('');
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
    const pinsHtml = pins.length
      ? pins.slice(0, 10).map((pin) => `
          <div class="sb__pin-row">
            <button type="button" class="sb__workbench-row" data-uri="${escapeHtml(pin.uri)}">
              <span>${escapeHtml(pin.kind || parseKind(pin.uri))}</span>
              <strong>${escapeHtml(pin.label || pinLabel(pin.uri))}</strong>
            </button>
            <div class="sb__pin-actions">
              <button type="button" class="sb__pin-tool" data-uri="${escapeHtml(pin.uri)}" title="Inspect">I</button>
              <button type="button" class="sb__pin-tool" data-raw-uri="${escapeHtml(pin.uri)}" title="Open raw JSON">R</button>
              <button type="button" class="sb__pin-tool" data-split-uri="${escapeHtml(pin.uri)}" title="Compare beside current inspector">S</button>
              <button type="button" class="sb__pin-remove" data-unpin="${escapeHtml(pin.uri)}" title="Remove pin">×</button>
            </div>
          </div>
        `).join('')
      : '<div class="sb__workbench-empty">No pinned objects</div>';
    const historyHtml = history.length
      ? history.slice(0, 8).map((item) => `
          <button type="button" class="sb__workbench-row" data-uri="${escapeHtml(item.uri)}">
            <span>${escapeHtml(item.kind || parseKind(item.uri))}</span>
            <strong>${escapeHtml(item.label || pinLabel(item.uri))}</strong>
          </button>
        `).join('')
      : '<div class="sb__workbench-empty">No inspected objects yet</div>';
    const snapshotsHtml = snapshots.length
      ? snapshots.slice(0, 6).map((snap) => `
          <div class="sb__snapshot-row">
            <button type="button" class="sb__workbench-row" data-snapshot="${escapeHtml(snap.id)}">
              <span>Snapshot</span>
              <strong>${escapeHtml(snap.label || 'runtime snapshot')}</strong>
            </button>
            <div class="sb__snapshot-actions">
              <button type="button" class="sb__pin-tool" data-snapshot="${escapeHtml(snap.id)}" title="Open snapshot raw JSON">O</button>
              ${snapshots[1] && snap.id !== snapshots[1].id ? `<button type="button" class="sb__pin-tool" data-compare-snapshot="${escapeHtml(snapshots[1].id)}:${escapeHtml(snap.id)}" title="Compare with previous snapshot">C</button>` : ''}
              <time>${escapeHtml(new Date(snap.created_at || Date.now()).toLocaleTimeString())}</time>
            </div>
          </div>
        `).join('')
      : '<div class="sb__workbench-empty">No saved snapshots</div>';
    const appsHtml = appCatalogList().map((appMeta) => {
      const requiredApis = appMeta.required_apis || [];
      const inspectors = appMeta.inspectors || [];
      const turnBuilders = appMeta.turn_builders || [];
      const factoryVks = appMeta.factory_vks || [];
      return `
        <article class="sb__program-card">
          <button type="button" class="sb__program-launch" data-open-app="${escapeHtml(appMeta.id)}">
            <span>${escapeHtml(appInitials(appMeta))}</span>
            <strong>${escapeHtml(appMeta.name || appMeta.id)}</strong>
          </button>
          <p>${escapeHtml(appMeta.description || 'starbridge-app userspace surface')}</p>
          <div class="sb__program-stats" aria-label="${escapeHtml(appMeta.name || appMeta.id)} manifest summary">
            <span>${requiredApis.length} APIs</span>
            <span>${inspectors.length} inspectors</span>
            <span>${turnBuilders.length} builders</span>
            <span>${factoryVks.length} factories</span>
          </div>
          <div class="sb__program-tags">
            ${(requiredApis.length ? requiredApis : ['no API requirements']).slice(0, 4).map((apiName) => `<code>${escapeHtml(apiName)}</code>`).join('')}
          </div>
          <div class="sb__program-actions">
            <button type="button" class="sb__icon-btn" data-open-app="${escapeHtml(appMeta.id)}">Embed</button>
            <button type="button" class="sb__icon-btn" data-preview-app="${escapeHtml(appMeta.id)}">Manifest</button>
            <a class="sb__icon-btn" href="${escapeHtml(appPageHref(appMeta))}" target="_blank">Standalone</a>
          </div>
        </article>
      `;
    }).join('');
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
        <button type="button" class="sb__metric sb__metric--button" data-uri="dregg://outbox/queue"><span>Outbox</span><strong>${counts.outbox}</strong></button>
      </section>
      <section class="sb__workbench-grid">
        <div class="sb__workbench-panel sb__workbench-panel--programs">
          <h3>Apps Dashboard</h3>
          <div class="sb__program-grid">
            ${appsHtml}
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
          <h3>Runtime Boundary</h3>
          <div class="sb__boundary-grid">${boundaryHtml}</div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Recent Objects</h3>
          <div class="sb__recent-list">${recentHtml}</div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Inspector History</h3>
          <div class="sb__recent-list">${historyHtml}</div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Pinned Objects</h3>
          <div class="sb__pin-list">${pinsHtml}</div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Snapshots</h3>
          <div class="sb__snapshot-list">${snapshotsHtml}</div>
        </div>
        <div class="sb__workbench-panel">
          <h3>Extension Outbox</h3>
          <dregg-outbox uri="dregg://outbox/queue" mode="compact"></dregg-outbox>
          <button type="button" class="sb__btn sb__btn--ghost sb__palette-inline" data-uri="dregg://outbox/queue">Open outbox inspector</button>
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
    panel.querySelector('[data-open-activity]')?.addEventListener('click', () => selectWorkbenchTool('activity'));
    panel.querySelector('[data-open-console]')?.addEventListener('click', () => {
      selectWorkbenchTool('console');
      consoleLog('console ready. try: help, seed, transfer, fed, intent, app nameservice', 'ok');
    });
    for (const btn of panel.querySelectorAll('[data-open-app]')) {
      btn.addEventListener('click', () => openAppWorkspace(appMetaFor(btn.dataset.openApp)));
    }
    for (const btn of panel.querySelectorAll('[data-preview-app]')) {
      btn.addEventListener('click', () => {
        setRawText(JSON.stringify(appMetaFor(btn.dataset.previewApp), null, 2));
        selectWorkbenchTool('raw');
      });
    }
    panel.querySelector('[data-open-palette]')?.addEventListener('click', () => openPalette());
    for (const btn of panel.querySelectorAll('[data-uri]')) {
      btn.addEventListener('click', () => setCurrentUri(btn.dataset.uri));
    }
    for (const btn of panel.querySelectorAll('[data-raw-uri]')) {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        rebindRawOnly(btn.dataset.rawUri);
        selectWorkbenchTool('raw');
        setStatus('raw inspector opened', 'ready');
      });
    }
    for (const btn of panel.querySelectorAll('[data-split-uri]')) {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        renderSideBySide(btn.dataset.splitUri, currentUri || btn.dataset.splitUri);
      });
    }
    for (const btn of panel.querySelectorAll('[data-unpin]')) {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        togglePin(btn.dataset.unpin);
        renderInspectorPane(null);
      });
    }
    for (const btn of panel.querySelectorAll('[data-snapshot]')) {
      btn.addEventListener('click', () => openSnapshotRecord(btn.dataset.snapshot));
    }
    for (const btn of panel.querySelectorAll('[data-compare-snapshot]')) {
      btn.addEventListener('click', (e) => {
        e.stopPropagation();
        const [leftId, rightId] = btn.dataset.compareSnapshot.split(':');
        compareSnapshotRecords(leftId, rightId);
      });
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

    bindSignalList({
      listEl: outboxListEl,
      countEl: outboxCount,
      empty: currentRuntimeId === 'extension' ? 'outbox empty' : 'extension runtime only',
      getSignal: () => runtime.getOutbox && runtime.getOutbox(),
      map: (entry) => ({
        uri: 'dregg://outbox/queue',
        label: `${entry.status || 'pending'} · ${entry.label || entry.kind || entry.id}`,
        title: `${entry.endpoint || ''} ${entry.lastError || ''}`,
      }),
    });

    if (typeof runtime.getTraceEvents === 'function') {
      const sig = runtime.getTraceEvents();
      const stop = api.effect(() => {
        sig.value;
        if (activityEl && !activityEl.hidden) renderActivityPane();
      });
      teardowns.push(stop);
    }
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
    updateCurrentContext(currentUri);
    if (uri) uriInput.value = uri;
    else uriInput.value = '';
    if (uri) {
      consoleLog(`inspect ${uri}`, 'cmd');
      logActivity('inspect', uri, { runtime: currentRuntimeId });
    }
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
    rememberNavigation(uri);
  }

  async function runLab(label, fn) {
    if (!runtime) return;
    labBusy += 1;
    setLabButtonsDisabled(true);
    setStatus(`${label}…`, 'boot');
    consoleLog(`run ${label}`, 'cmd');
    logActivity('script', `started ${label}`, { runtime: currentRuntimeId });
    try {
      const result = await fn();
      setStatus(`ready · ${runtimeLabel()}`, 'ready');
      consoleLog(`${label} complete`, 'ok');
      logActivity('script', `completed ${label}`, { result });
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
        consoleLog('commands: help, status, seed, transfer, fed, intent, app <id>, inspect <uri>, runtime <id>, raw, console, activity, outbox, clear, snapshot', 'ok');
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
        openAppWorkspace(appMetaFor(id));
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
      case 'activity':
      case 'events':
        selectWorkbenchTool('activity');
        break;
      case 'outbox':
      case 'queue':
        setCurrentUri('dregg://outbox/queue');
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
    } else if (parsed.kind === 'outbox') {
      if (typeof runtime.getOutbox !== 'function') {
        setRawText('outbox unavailable in this runtime');
        return;
      }
      sig = runtime.getOutbox();
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
    applyShellLayout();
    await loadAppCatalog();

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
    toggleMapBtn?.addEventListener('click', () => toggleShellPane('map'));
    toggleWorkbenchBtn?.addEventListener('click', () => toggleShellPane('workbench'));
    copyUriBtn?.addEventListener('click', async () => {
      if (!currentUri) return;
      try {
        await navigator.clipboard.writeText(currentUri);
        setStatus('URI copied', 'ready');
        consoleLog(`copied ${currentUri}`, 'ok');
        logActivity('copy', `copied ${currentUri}`, { uri: currentUri });
      } catch (err) {
        setStatus('copy failed: ' + (err?.message || err), 'err');
      }
    });
    pinUriBtn?.addEventListener('click', () => togglePin());
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
    navBackBtn?.addEventListener('click', () => jumpNavigation(-1));
    navForwardBtn?.addEventListener('click', () => jumpNavigation(1));

    snapBtn.addEventListener('click', () => {
      exportSnapshot();
    });

    for (const tab of document.querySelectorAll('[data-tool]')) {
      tab.addEventListener('click', () => selectWorkbenchTool(tab.dataset.tool || 'raw'));
    }
    activityRefreshBtn?.addEventListener('click', renderActivityPane);
    rawFilter?.addEventListener('input', renderRawText);
    rawCopyBtn?.addEventListener('click', async () => {
      try {
        await navigator.clipboard.writeText(rawText);
        setStatus('raw copied', 'ready');
        consoleLog('raw copied', 'ok');
      } catch (err) {
        setStatus('copy failed: ' + (err?.message || err), 'err');
        consoleLog('copy failed: ' + (err?.message || err), 'err');
      }
    });
    consoleForm?.addEventListener('submit', async (e) => {
      e.preventDefault();
      const raw = consoleInput?.value || '';
      if (consoleInput) consoleInput.value = '';
      await runConsoleCommand(raw);
    });
    consoleLog('console ready. type help for commands.', 'ok');

    paletteOpenBtn?.addEventListener('click', () => openPalette());
    surfaceWorkbenchBtn?.addEventListener('click', () => {
      setCurrentUri(null);
      selectWorkbenchTool('raw');
    });
    surfaceAppsBtn?.addEventListener('click', () => {
      setCurrentUri(null);
      setSurfaceCurrent('apps');
      if (workspaceTitle) workspaceTitle.textContent = 'Apps';
      inspector.querySelector('.sb__workbench-panel--programs')?.scrollIntoView({ block: 'start' });
    });
    surfaceActivityBtn?.addEventListener('click', () => {
      setCurrentUri('dregg://activity/feed');
      selectWorkbenchTool('activity');
    });
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
        if (app) openAppWorkspace(app);
      });
    }
    app.addEventListener('dregg:navigate', (e) => {
      const uri = e.detail?.uri;
      if (!uri || !isRef(uri)) return;
      e.preventDefault();
      setCurrentUri(uri);
    });
    window.addEventListener('message', (e) => {
      const data = e.data || {};
      if (data.type !== 'dregg:navigate' && data.type !== 'starbridge:navigate') return;
      const uri = data.uri || data.at;
      if (!uri || !isRef(uri)) return;
      setCurrentUri(uri);
    });
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
    const record = saveSnapshotRecord(snapshot);
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
    consoleLog(`snapshot exported · ${record.label}`, 'ok');
    logActivity('snapshot', `exported ${record.label}`, { id: record.id });
  }
})();

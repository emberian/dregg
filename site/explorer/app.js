/**
 * dregg explorer — inspector-substrate shell.
 *
 * The explorer is the SAME inspectors as the Studio/Playground, over a live
 * federation node instead of an in-browser wasm runtime. We mount a single
 * <dregg-app> whose `.runtime` is a read-only RemoteRuntime, then render every
 * object view through the platform <dregg-*> inspectors (STUDIO.md § 3, § 5).
 *
 * There is NO bespoke node viewer here and NO fabricated data: when the node is
 * unreachable the inspectors render their own honest empty states and the
 * connection chrome says "offline". When connected, every pixel is real node
 * data resolved through a real inspector via dregg:// URIs.
 *
 *   search/nav  ──▶  dregg:// URI  ──▶  <dregg-KIND uri="...">  (inside <dregg-app>)
 */

import { createRemoteRuntime } from '../_includes/studio/runtime-remote.js';
import { parseRef, isRef } from '../_includes/studio/uri.js';
// Side-effect import: registers every <dregg-*> inspector custom element and
// the <dregg-app> context provider. This is the platform vocabulary.
import '../_includes/studio/context.js';
import '../_includes/studio/inspectors.js';

const NODE_URL_KEY = 'dregg_node_url';
const DEFAULT_NODE_URL = 'http://localhost:8420';
const AUTO_REFRESH_KEY = 'dregg_auto_refresh';

// ---------------------------------------------------------------------------
// Node URL config (localStorage).
// ---------------------------------------------------------------------------
export function getNodeUrl() {
  return localStorage.getItem(NODE_URL_KEY) || DEFAULT_NODE_URL;
}
export function setNodeUrl(url) {
  localStorage.setItem(NODE_URL_KEY, String(url || '').trim());
}

// ---------------------------------------------------------------------------
// Nav pages → the inspector (and URI) each one mounts.
//
// "list" pages mount a collection inspector against the live runtime; "object"
// pages are reached by search/deep-link and mount a single-object inspector.
// Every tag here is a platform-level <dregg-*> element (STUDIO.md § 5).
// ---------------------------------------------------------------------------
const PAGES = {
  overview:     { kind: 'overview' },
  blocks:       { tag: 'dregg-block-dag',    uri: () => 'dregg://block-dag/0' },
  cells:        { tag: 'dregg-cell-list',    uri: () => 'dregg://cell-list/all' },
  receipts:     { tag: 'dregg-receipt-list', uri: () => 'dregg://receipt-list/all' },
  turns:        { tag: 'dregg-receipt-list', uri: () => 'dregg://receipt-list/all' },
  capabilities: { tag: 'dregg-capability-list', uri: () => 'dregg://capability-list/0' },
  intents:      { custom: 'intents' },
  federation:   { tag: 'dregg-federation-list', uri: () => 'dregg://federation-list/all' },
  activity:     { tag: 'dregg-activity',     uri: () => 'dregg://activity/feed' },
};

// Map a parsed dregg:// kind to the nav page that hosts its inspector.
const KIND_TO_PAGE = {
  cell: 'cells',
  receipt: 'receipts',
  turn: 'turns',
  block: 'blocks',
  'block-dag': 'blocks',
  federation: 'federation',
  'federation-list': 'federation',
  capability: 'capabilities',
  'capability-list': 'capabilities',
  token: 'capabilities',
  intent: 'intents',
  'intent-list': 'intents',
  activity: 'activity',
};

// Some dregg:// kinds alias to a different inspector element.
const INSPECTOR_ALIASES = {
  token: 'attenuated-token',
};

// ---------------------------------------------------------------------------
// Module state.
// ---------------------------------------------------------------------------
let runtime = null;
let api = null;            // window.dreggUi (Preact + signals)
let appEl = null;          // the single <dregg-app>
let currentPage = 'overview';
let connected = false;
let livenessTimer = null;

function latestHeight() {
  try {
    const blocks = runtime?.listBlocks?.().value || [];
    return blocks.reduce((max, b) => Math.max(max, Number(b.height ?? b.block_height ?? 0)), 0);
  } catch { return 0; }
}

function whenDreggUi() {
  return new Promise(resolve => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', e => resolve(e.detail), { once: true });
  });
}

// ---------------------------------------------------------------------------
// Connection indicator + liveness.
// ---------------------------------------------------------------------------
function setConnection(state) {
  const el = document.getElementById('connection-status');
  if (!el) return;
  el.classList.remove('connected', 'error');
  const label = el.querySelector('.ex-connection__label');
  if (state === 'connected') {
    el.classList.add('connected');
    if (label) label.textContent = 'connected';
  } else if (state === 'connecting') {
    if (label) label.textContent = 'connecting…';
  } else {
    el.classList.add('error');
    if (label) label.textContent = 'offline';
  }
  connected = state === 'connected';
}

/**
 * Probe /status directly for an honest connected/offline signal that is
 * independent of whether any particular object exists. RemoteRuntime polls in
 * the background; this is just for the chrome indicator. No fabricated data —
 * a failed probe shows "offline".
 */
async function probeLiveness() {
  const base = getNodeUrl().replace(/\/+$/, '');
  try {
    const res = await fetch(`${base}/status`, { headers: { Accept: 'application/json' } });
    setConnection(res.ok ? 'connected' : 'offline');
    if (res.ok) {
      const status = await res.json().catch(() => null);
      updateStatusChrome(status);
    }
  } catch {
    setConnection('offline');
    updateStatusChrome(null);
  }
}

function updateStatusChrome(status) {
  const heightEl = document.getElementById('nav-height-value');
  const urlEl = document.getElementById('devnet-node-url');
  const metaEl = document.getElementById('devnet-node-meta');
  if (urlEl) urlEl.textContent = getNodeUrl();
  if (!status) {
    if (heightEl) heightEl.textContent = '--';
    if (metaEl) metaEl.textContent = connected ? 'connected' : 'not connected';
    return;
  }
  const h = status.latest_height ?? status.height ?? status.block_height ?? 0;
  if (heightEl) heightEl.textContent = String(h);
  if (metaEl) {
    const mode = status.federation_mode || (status.healthy ? 'healthy' : 'responding');
    metaEl.textContent = `${mode} · height ${h} · ${status.peer_count ?? 0} peer(s)`;
  }
}

function autoRefreshEnabled() {
  return localStorage.getItem(AUTO_REFRESH_KEY) !== 'false';
}

function startLiveness() {
  stopLiveness();
  probeLiveness();
  if (autoRefreshEnabled()) {
    livenessTimer = setInterval(probeLiveness, 5000);
  }
}
function stopLiveness() {
  if (livenessTimer) { clearInterval(livenessTimer); livenessTimer = null; }
}

// ---------------------------------------------------------------------------
// Runtime lifecycle.
// ---------------------------------------------------------------------------
async function buildRuntime() {
  if (runtime && runtime.destroy) {
    try { runtime.destroy(); } catch {}
  }
  runtime = await createRemoteRuntime({ signals: api, baseUrl: getNodeUrl() });
  if (appEl) appEl.runtime = runtime;
  return runtime;
}

// ---------------------------------------------------------------------------
// Inspector mounting. Every object view is a platform <dregg-*> element placed
// inside the shared <dregg-app>, so it resolves through the RemoteRuntime.
// ---------------------------------------------------------------------------
function mountInspector(container, uri) {
  container.replaceChildren();
  let parsed = null;
  try { parsed = parseRef(uri); } catch {}
  if (!parsed) {
    container.appendChild(emptyNotice('Bad object reference', uri));
    return;
  }
  const kind = INSPECTOR_ALIASES[parsed.kind] || parsed.kind;
  const tag = `dregg-${kind}`;
  if (!customElements.get(tag)) {
    container.appendChild(emptyNotice(`No inspector registered for "${parsed.kind}"`, uri));
    return;
  }
  const el = document.createElement(tag);
  el.setAttribute('uri', kind === parsed.kind ? uri : `dregg://${kind}/${parsed.id}`);
  container.appendChild(el);
}

function emptyNotice(title, detail) {
  const div = document.createElement('div');
  div.className = 'ex-inspector-empty';
  div.innerHTML = `<strong>${escapeHtml(title)}</strong>${detail ? `<code>${escapeHtml(detail)}</code>` : ''}`;
  return div;
}

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, c => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

// ---------------------------------------------------------------------------
// Routing / navigation.
// ---------------------------------------------------------------------------
export function navigateTo(page) {
  if (!PAGES[page]) page = 'overview';
  currentPage = page;

  document.querySelectorAll('.ex-nav__item').forEach(el => el.classList.remove('active'));
  const navItem = document.querySelector(`[data-page="${page}"]`);
  if (navItem) navItem.classList.add('active');

  document.querySelectorAll('.ex-page').forEach(el => el.classList.remove('active'));
  const pageEl = document.getElementById(`page-${page}`);
  if (pageEl) pageEl.classList.add('active');

  if (page === 'overview') { renderOverview(); return; }

  const def = PAGES[page];
  const mount = document.getElementById(`mount-${page}`);
  if (!mount) return;
  if (def.custom === 'intents') { renderIntentList(mount); return; }
  if (def.uri) mountInspector(mount, def.uri());
}

/**
 * Open a dregg:// URI: switch to the hosting page and mount the single-object
 * inspector in that page's detail slot. Sharable via ?at=.
 */
function openUri(uri) {
  let parsed;
  try { parsed = parseRef(uri); } catch { return false; }
  const page = KIND_TO_PAGE[parsed.kind] || 'overview';
  navigateTo(page);
  const detail = document.getElementById(`detail-${page}`) || document.getElementById(`mount-${page}`);
  if (detail) {
    mountInspector(detail, uri);
    detail.scrollIntoView?.({ behavior: 'smooth', block: 'start' });
  }
  writeAt(uri);
  return true;
}

function writeAt(uri) {
  const p = new URLSearchParams(window.location.search);
  if (uri) p.set('at', uri); else p.delete('at');
  const q = p.toString();
  window.history.replaceState(null, '', window.location.pathname + (q ? '?' + q : ''));
}

// ---------------------------------------------------------------------------
// Search: resolve free-text to a dregg:// URI.
//   - a full dregg:// URI passes through
//   - 64-hex → try cell, then receipt (whichever the runtime resolves)
//   - bare integer → block height
//   - "block/<h>", "cell/<id>", "receipt/<h>", "intent/<id>" shorthand
// ---------------------------------------------------------------------------
function resolveSearch(raw) {
  const q = String(raw || '').trim();
  if (!q) return null;
  if (isRef(q)) return q;

  const shorthand = /^(cell|receipt|turn|block|intent|federation|capability|token)\/(.+)$/i.exec(q);
  if (shorthand) {
    const kind = shorthand[1].toLowerCase();
    const id = shorthand[2];
    if (kind === 'block') return `dregg://block/0/${id}`;
    return `dregg://${kind}/${id}`;
  }

  if (/^\d+$/.test(q)) return `dregg://block/0/${q}`;          // block height
  if (/^[0-9a-f]{64}$/i.test(q)) return resolveHash(q);         // cell or receipt hash
  if (/^[0-9a-f]{6,}$/i.test(q)) return resolveHash(q);
  return null;
}

// A 32-byte hash can be a cell id, a receipt/turn hash, or an intent id. Prefer
// whichever the live runtime actually has; default to cell.
function resolveHash(hash) {
  try {
    const cells = runtime?.listCells?.().value || [];
    if (cells.some(c => String(c.cell_id || c.id || '').toLowerCase() === hash.toLowerCase())) {
      return `dregg://cell/${hash}`;
    }
    const receipts = runtime?.listReceipts?.().value || [];
    if (receipts.some(r => [r.turn_hash, r.receipt_hash, r.hash].some(h => String(h || '').toLowerCase() === hash.toLowerCase()))) {
      return `dregg://receipt/${hash}`;
    }
    const intents = runtime?.listIntents?.().value || [];
    if (intents.some(i => String(i.intent_id || i.id || '').toLowerCase() === hash.toLowerCase())) {
      return `dregg://intent/${hash}`;
    }
  } catch {}
  return `dregg://cell/${hash}`;
}

function runSearch(raw) {
  const uri = resolveSearch(raw);
  const errEl = document.getElementById('search-error');
  if (!uri) {
    if (errEl) {
      errEl.textContent = `Could not resolve "${raw}". Try a cell id, receipt hash, block height, or dregg:// URI.`;
      errEl.hidden = false;
    }
    return;
  }
  if (errEl) errEl.hidden = true;
  openUri(uri);
}

// ---------------------------------------------------------------------------
// Overview: a live dashboard built entirely from runtime list inspectors.
// No bespoke rendering of node internals — just inspector tiles.
// ---------------------------------------------------------------------------
function renderOverview() {
  const grid = document.getElementById('overview-inspectors');
  if (!grid || grid.dataset.mounted === 'true') return;
  grid.dataset.mounted = 'true';
  const tiles = [
    { title: 'Cells', tag: 'dregg-cell-list', uri: 'dregg://cell-list/all' },
    { title: 'Receipts', tag: 'dregg-receipt-list', uri: 'dregg://receipt-list/all' },
    { title: 'Federations', tag: 'dregg-federation-list', uri: 'dregg://federation-list/all' },
    { title: 'Activity', tag: 'dregg-activity', uri: 'dregg://activity/feed' },
  ];
  for (const t of tiles) {
    const card = document.createElement('div');
    card.className = 'overview-panel';
    const head = document.createElement('div');
    head.className = 'overview-panel__header';
    head.innerHTML = `<h3>${escapeHtml(t.title)}</h3>`;
    const body = document.createElement('div');
    body.className = 'overview-panel__body';
    card.append(head, body);
    grid.appendChild(card);
    mountInspector(body, t.uri);
  }
}

// ---------------------------------------------------------------------------
// Intents: no platform list-inspector exists for intents, so this page is
// search/nav chrome — a live (signals-backed) index of the runtime's intent
// pool, each entry opening the platform <dregg-intent> inspector. The actual
// object view is still a real inspector over real node data.
// ---------------------------------------------------------------------------
function renderIntentList(mount) {
  mount.replaceChildren();
  const list = document.createElement('div');
  list.className = 'ex-intent-index';
  mount.appendChild(list);
  const detail = document.getElementById('detail-intents');

  const sig = runtime?.listIntents?.();
  const paint = () => {
    const intents = (sig?.value) || [];
    list.replaceChildren();
    if (!intents.length) {
      list.appendChild(emptyNotice('No intents in the node pool', connected ? '' : 'not connected'));
      return;
    }
    for (const intent of intents) {
      const id = intent.intent_id || intent.id || '';
      const row = document.createElement('button');
      row.type = 'button';
      row.className = 'ex-intent-index__row';
      row.innerHTML = `<span>${escapeHtml(intent.kind || 'intent')}</span><code>${escapeHtml(String(id).slice(0, 24))}</code>`;
      row.addEventListener('click', () => {
        if (detail) mountInspector(detail, `dregg://intent/${id}`);
        writeAt(`dregg://intent/${id}`);
      });
      list.appendChild(row);
    }
  };
  // Live: re-paint on every runtime signal change.
  if (api?.effect && sig) {
    api.effect(() => { sig.value; paint(); });
  } else {
    paint();
  }
}

// ---------------------------------------------------------------------------
// Wire chrome: nav, search, settings, deep-link handling.
// ---------------------------------------------------------------------------
function wireChrome() {
  document.querySelectorAll('.ex-nav__item').forEach(btn => {
    btn.addEventListener('click', () => navigateTo(btn.dataset.page));
  });
  document.querySelectorAll('[data-map-page]').forEach(btn => {
    btn.addEventListener('click', () => navigateTo(btn.dataset.mapPage));
  });

  const search = document.getElementById('search-input');
  if (search) {
    search.addEventListener('keydown', e => {
      if (e.key === 'Enter') runSearch(search.value);
    });
    document.addEventListener('keydown', e => {
      if (e.key === '/' && document.activeElement !== search) {
        e.preventDefault();
        search.focus();
      }
    });
  }

  // Delegate clicks on inspector-emitted dregg:// links to in-app navigation.
  document.addEventListener('click', e => {
    const link = e.target.closest('[data-dregg-uri], a[href*="?at=dregg"]');
    if (!link) return;
    const uri = link.getAttribute('data-dregg-uri')
      || new URLSearchParams(new URL(link.href, window.location.origin).search).get('at');
    if (uri && isRef(uri)) {
      e.preventDefault();
      openUri(uri);
    }
  });

  wireSettings();
}

function wireSettings() {
  const btn = document.getElementById('settings-btn');
  const modal = document.getElementById('settings-modal');
  const urlInput = document.getElementById('node-url-input');
  const autoToggle = document.getElementById('auto-refresh-toggle');
  const save = document.getElementById('settings-save');
  const cancel = document.getElementById('settings-cancel');
  const test = document.getElementById('settings-test');
  if (!modal) return;

  const open = () => {
    if (urlInput) urlInput.value = getNodeUrl();
    if (autoToggle) autoToggle.checked = autoRefreshEnabled();
    modal.hidden = false;
  };
  const close = () => { modal.hidden = true; };

  btn?.addEventListener('click', open);
  cancel?.addEventListener('click', close);
  modal.querySelector('.ex-modal__backdrop')?.addEventListener('click', close);

  test?.addEventListener('click', async () => {
    const url = (urlInput?.value || '').trim().replace(/\/+$/, '');
    const msg = document.getElementById('diag-message');
    if (msg) msg.textContent = 'Probing…';
    try {
      const res = await fetch(`${url}/status`, { headers: { Accept: 'application/json' } });
      if (msg) msg.textContent = res.ok ? `OK (HTTP ${res.status})` : `HTTP ${res.status}`;
    } catch (err) {
      if (msg) msg.textContent = `Unreachable: ${err?.message || err} (CORS or offline — node allows only localhost/extension origins by default)`;
    }
  });

  save?.addEventListener('click', async () => {
    if (urlInput) setNodeUrl(urlInput.value);
    if (autoToggle) localStorage.setItem(AUTO_REFRESH_KEY, autoToggle.checked ? 'true' : 'false');
    close();
    setConnection('connecting');
    await buildRuntime();
    startLiveness();
    navigateTo(currentPage);
  });
}

// ---------------------------------------------------------------------------
// Boot.
// ---------------------------------------------------------------------------
export async function boot() {
  api = await whenDreggUi();

  appEl = document.getElementById('explorer-app');
  if (!appEl) {
    console.error('[explorer] missing <dregg-app id="explorer-app">');
    return;
  }

  setConnection('connecting');
  await buildRuntime();
  wireChrome();
  startLiveness();

  // Deep link: ?at=dregg://... or /explorer/<kind>/<id> path.
  const params = new URLSearchParams(window.location.search);
  const at = params.get('at');
  const routeUri = parsePathRoute(window.location.pathname);
  if (at && isRef(at)) {
    openUri(at);
  } else if (routeUri) {
    openUri(routeUri);
  } else {
    navigateTo('overview');
  }
}

// /explorer/cell/<id>, /explorer/block/<h>, /explorer/receipt/<h>, /explorer/tx/<h>
function parsePathRoute(pathname) {
  const parts = String(pathname || '').split('/').filter(Boolean);
  const idx = parts.lastIndexOf('explorer');
  if (idx === -1) return null;
  const rest = parts.slice(idx + 1).map(p => { try { return decodeURIComponent(p); } catch { return p; } });
  if (rest.length < 2) return null;
  const [rawKind, id] = rest;
  const kind = rawKind.toLowerCase();
  if (kind === 'tx' || kind === 'turn') return `dregg://turn/${id}`;
  if (kind === 'block') return `dregg://block/0/${id}`;
  if (['cell', 'receipt', 'intent', 'federation', 'capability'].includes(kind)) {
    return `dregg://${kind}/${id}`;
  }
  return null;
}

export { runtime };

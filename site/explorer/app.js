/**
 * dregg explorer — modular app shell.
 *
 * Provides: event bus (pub/sub), router, module loader, shared state.
 * Each view/visualizer exports: init(container), update(data), destroy()
 */

import * as api from './api.js';

// =============================================================================
// Event Bus — lightweight pub/sub for decoupled communication
// =============================================================================

class EventBus {
  constructor() {
    this._listeners = {};
  }

  on(event, fn) {
    if (!this._listeners[event]) this._listeners[event] = [];
    this._listeners[event].push(fn);
    return () => this.off(event, fn);
  }

  off(event, fn) {
    const fns = this._listeners[event];
    if (fns) this._listeners[event] = fns.filter(f => f !== fn);
  }

  emit(event, data) {
    const fns = this._listeners[event] || [];
    fns.forEach(fn => {
      try { fn(data); } catch (e) { console.error(`[bus] error in ${event}:`, e); }
    });
  }

  once(event, fn) {
    const unsub = this.on(event, (data) => { unsub(); fn(data); });
    return unsub;
  }
}

export const bus = new EventBus();

// =============================================================================
// Shared State
// =============================================================================

export const state = {
  connected: false,
  autoRefresh: localStorage.getItem('dregg_auto_refresh') !== 'false',
  currentPage: 'overview',
  status: null,
  blocks: null,
  checkpoint: null,
  receipts: null,
  tokens: null,
  intents: null,
  conditionals: null,
};

export function updateState(patch) {
  Object.assign(state, patch);
  bus.emit('state:changed', state);
}

// =============================================================================
// Module Registry
// =============================================================================

const modules = {};
let activeView = null;
const initializedViews = new Set();

/**
 * Register a view module. Module must export:
 *   init(container) — render initial DOM into container
 *   update(data)    — refresh with new data (optional)
 *   destroy()       — cleanup (optional)
 */
export function registerView(name, mod) {
  modules[name] = mod;
}

/**
 * Register a visualizer module. Same interface as views but meant
 * to be embedded within views (composable).
 */
export function registerVisualizer(name, mod) {
  modules[`viz:${name}`] = mod;
}

export function getVisualizer(name) {
  return modules[`viz:${name}`] || null;
}

export function getView(name) {
  return modules[name] || null;
}

// =============================================================================
// Router
// =============================================================================

export function navigateTo(page) {
  const prev = state.currentPage;
  if (prev === page && activeView) return;

  // Deactivate old
  if (activeView && activeView.destroy) {
    try { activeView.destroy(); } catch (e) { console.error('[router] destroy error:', e); }
  }

  // Update nav UI
  document.querySelectorAll('.ex-nav__item').forEach(el => el.classList.remove('active'));
  const navItem = document.querySelector(`[data-page="${page}"]`);
  if (navItem) navItem.classList.add('active');

  // Switch page container
  document.querySelectorAll('.ex-page').forEach(el => el.classList.remove('active'));
  const pageEl = document.getElementById(`page-${page}`);
  if (pageEl) pageEl.classList.add('active');

  updateState({ currentPage: page });

  // Activate new view
  const mod = modules[page];
  if (mod) {
    activeView = mod;
    const container = pageEl;
    if (mod.init && !initializedViews.has(page)) {
      mod.init(container);
      initializedViews.add(page);
    }
    if (mod.update) {
      mod.update(state);
    }
  }

  bus.emit('navigate', { from: prev, to: page });
}

// =============================================================================
// Data Refresh
// =============================================================================

let refreshTimer = null;

export async function refresh() {
  try {
    const status = await api.getStatus();
    updateState({ status, connected: true });
    bus.emit('status:updated', status);
    bus.emit('connection:changed', true);

    // Load page-specific data
    loadPageData(state.currentPage);
  } catch (err) {
    updateState({ connected: false });
    bus.emit('connection:changed', false);
    bus.emit('error', { source: 'refresh', error: err });
  }
}

export async function loadPageData(page) {
  bus.emit('page:loading', page);
  try {
    switch (page) {
      case 'overview':
        await loadOverviewData();
        break;
      case 'blocks':
      case 'blocklace':
        const blocks = await api.getBlocks();
        updateState({ blocks });
        bus.emit('blocks:updated', blocks);
        break;
      case 'cells':
        const cells = await api.getCells().catch(() => []);
        bus.emit('cells:updated', cells);
        break;
      case 'turns':
      case 'receipts':
        const receipts = await api.getReceipts();
        updateState({ receipts });
        bus.emit('receipts:updated', receipts);
        break;
      case 'capabilities':
        const tokens = await api.getTokens();
        updateState({ tokens });
        bus.emit('tokens:updated', tokens);
        break;
      case 'proofs':
        const pirInfo = await api.getPirInfo().catch(() => null);
        bus.emit('proofs:updated', pirInfo);
        break;
      case 'intents':
        const [intents, conditionals] = await Promise.all([
          api.getIntents().catch(() => []),
          api.getPendingConditionals().catch(() => []),
        ]);
        updateState({ intents, conditionals });
        bus.emit('intents:updated', { intents, conditionals });
        break;
      case 'federation':
        const fedStatus = await api.getFederationStatus();
        bus.emit('federation:updated', fedStatus);
        break;
      case 'notes':
        const noteData = await loadNoteData();
        bus.emit('notes:updated', noteData);
        break;
      case 'effects':
        bus.emit('effects:ready', state);
        break;
      case 'apps':
        const appCells = await api.getCells().catch(() => []);
        bus.emit('apps:updated', appCells);
        break;
    }
    bus.emit('page:loaded', page);
  } catch (err) {
    bus.emit('page:error', { page, error: err });
  }

  // Notify active view
  if (activeView && activeView.update) {
    activeView.update(state);
  }
}

async function loadOverviewData() {
  const [intents, conditionals, checkpoint, blocks] = await Promise.all([
    api.getIntents().catch(() => []),
    api.getPendingConditionals().catch(() => []),
    api.getCheckpoint().catch(() => null),
    api.getBlocks().catch(() => []),
  ]);
  updateState({ intents, conditionals, checkpoint, blocks });
  bus.emit('overview:updated', { intents, conditionals, checkpoint, blocks });
}

async function loadNoteData() {
  const [checkpoint, blocks] = await Promise.all([
    api.getCheckpoint().catch(() => null),
    state.blocks || api.getBlocks().catch(() => []),
  ]);
  updateState({ checkpoint, blocks });
  return { checkpoint, blocks, status: state.status };
}

// =============================================================================
// Auto-Refresh
// =============================================================================

export function startAutoRefresh() {
  stopAutoRefresh();
  if (state.autoRefresh) {
    refreshTimer = setInterval(refresh, 5000);
  }
}

export function stopAutoRefresh() {
  if (refreshTimer) {
    clearInterval(refreshTimer);
    refreshTimer = null;
  }
}

// =============================================================================
// Bootstrap
// =============================================================================

export async function boot() {
  // Load all view modules dynamically
  const viewModules = await Promise.all([
    import('./views/overview.js'),
    import('./views/blocks.js'),
    import('./views/cells.js'),
    import('./views/turns.js'),
    import('./views/receipts.js'),
    import('./views/capabilities.js'),
    import('./views/proofs.js'),
    import('./views/intents.js'),
    import('./views/federation.js'),
    import('./views/notes.js'),
    import('./views/apps.js'),
    import('./views/blocklace.js'),
    import('./views/effects.js'),
    import('./views/queues.js'),
    import('./views/names.js'),
    import('./views/delegations.js'),
  ]);

  // Register each view module
  viewModules.forEach(mod => {
    if (mod.name && mod.init) {
      registerView(mod.name, mod);
    }
  });

  // Load visualizer modules
  const vizModules = await Promise.all([
    import('./visualizers/dag-graph.js'),
    import('./visualizers/merkle-tree.js'),
    import('./visualizers/state-diff.js'),
    import('./visualizers/proof-anatomy.js'),
    import('./visualizers/timeline.js'),
  ]);

  vizModules.forEach(mod => {
    if (mod.name) {
      registerVisualizer(mod.name, mod);
    }
  });

  // Load component modules
  const [navMod, statusBarMod, searchMod, authDialogMod] = await Promise.all([
    import('./components/nav.js'),
    import('./components/status-bar.js'),
    import('./components/search.js'),
    import('./components/auth-dialog.js'),
  ]);

  navMod.init();
  statusBarMod.init();
  searchMod.init();
  authDialogMod.init();

  // Load tweaker modules (they register themselves)
  await Promise.all([
    import('./tweakers/effect-builder.js'),
    import('./tweakers/proof-simulator.js'),
    import('./tweakers/fee-estimator.js'),
  ]);

  // Initialize the default view
  navigateTo('overview');

  // Start data flow
  refresh();
  startAutoRefresh();
}

// Export api for use by views
export { api };

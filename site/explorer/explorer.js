/**
 * pyana explorer — main application logic.
 *
 * Single-page chain explorer that connects to a pyana node and displays
 * federation state: blocks, turns, receipts, cells, capabilities, proofs, intents.
 */

import * as api from './api.js';

// =============================================================================
// State
// =============================================================================

let currentPage = 'overview';
let autoRefresh = localStorage.getItem('pyana_auto_refresh') !== 'false';
let refreshTimer = null;
let connected = false;

// Cached data
let cachedStatus = null;
let cachedBlocks = null;
let cachedCheckpoint = null;
let cachedReceipts = null;
let cachedTokens = null;
let cachedIntents = null;
let cachedConditionals = null;

// =============================================================================
// Initialization
// =============================================================================

document.addEventListener('DOMContentLoaded', () => {
  initNavigation();
  initSearch();
  initSettings();
  initKeyBindings();
  refresh();
  startAutoRefresh();
});

// =============================================================================
// Navigation
// =============================================================================

function initNavigation() {
  const nav = document.getElementById('ex-nav');
  nav.addEventListener('click', (e) => {
    const item = e.target.closest('[data-page]');
    if (!item) return;
    navigateTo(item.dataset.page);
  });
}

function navigateTo(page) {
  // Update nav
  document.querySelectorAll('.ex-nav__item').forEach(el => el.classList.remove('active'));
  const navItem = document.querySelector(`[data-page="${page}"]`);
  if (navItem) navItem.classList.add('active');

  // Update pages
  document.querySelectorAll('.ex-page').forEach(el => el.classList.remove('active'));
  const pageEl = document.getElementById(`page-${page}`);
  if (pageEl) pageEl.classList.add('active');

  currentPage = page;

  // Load page-specific data
  loadPageData(page);
}

// =============================================================================
// Search
// =============================================================================

function initSearch() {
  const input = document.getElementById('search-input');
  input.addEventListener('keydown', (e) => {
    if (e.key === 'Enter') {
      handleSearch(input.value.trim());
    }
  });
}

function handleSearch(query) {
  if (!query) return;

  // Detect query type
  if (/^\d+$/.test(query)) {
    // Block height
    navigateTo('blocks');
    highlightBlock(parseInt(query));
  } else if (query.length === 64 && /^[0-9a-fA-F]+$/.test(query)) {
    // Full hex hash — could be cell, turn, or receipt
    navigateTo('cells');
    lookupByHash(query);
  } else if (query.length > 8 && /^[0-9a-fA-F]+$/.test(query)) {
    // Partial hash
    navigateTo('cells');
    lookupByHash(query);
  }
}

async function highlightBlock(height) {
  // Will be highlighted when blocks render
}

async function lookupByHash(hash) {
  // Try cell first
  try {
    const cell = await api.getCell(hash.padEnd(64, '0'));
    if (cell && cell.found) {
      renderCellDetail(cell);
      return;
    }
  } catch {}
}

// =============================================================================
// Settings
// =============================================================================

function initSettings() {
  const modal = document.getElementById('settings-modal');
  const btn = document.getElementById('settings-btn');
  const cancel = document.getElementById('settings-cancel');
  const save = document.getElementById('settings-save');
  const backdrop = modal.querySelector('.ex-modal__backdrop');
  const urlInput = document.getElementById('node-url-input');
  const autoRefreshToggle = document.getElementById('auto-refresh-toggle');

  // Load current settings
  urlInput.value = api.getNodeUrl();
  autoRefreshToggle.checked = autoRefresh;

  btn.addEventListener('click', () => modal.hidden = false);
  cancel.addEventListener('click', () => modal.hidden = true);
  backdrop.addEventListener('click', () => modal.hidden = true);

  save.addEventListener('click', () => {
    api.setNodeUrl(urlInput.value.trim() || 'http://localhost:8420');
    autoRefresh = autoRefreshToggle.checked;
    localStorage.setItem('pyana_auto_refresh', autoRefresh);
    modal.hidden = true;
    refresh();
    if (autoRefresh) startAutoRefresh();
    else stopAutoRefresh();
  });
}

// =============================================================================
// Key bindings
// =============================================================================

function initKeyBindings() {
  document.addEventListener('keydown', (e) => {
    // Focus search on /
    if (e.key === '/' && !isInputFocused()) {
      e.preventDefault();
      document.getElementById('search-input').focus();
    }
    // Escape closes modals and detail panels
    if (e.key === 'Escape') {
      document.getElementById('settings-modal').hidden = true;
      document.querySelectorAll('.ex-detail-panel').forEach(el => el.hidden = true);
      document.getElementById('search-input').blur();
    }
  });
}

function isInputFocused() {
  const tag = document.activeElement?.tagName?.toLowerCase();
  return tag === 'input' || tag === 'textarea' || tag === 'select';
}

// =============================================================================
// Auto-refresh
// =============================================================================

function startAutoRefresh() {
  stopAutoRefresh();
  if (autoRefresh) {
    refreshTimer = setInterval(refresh, 5000);
  }
}

function stopAutoRefresh() {
  if (refreshTimer) {
    clearInterval(refreshTimer);
    refreshTimer = null;
  }
}

// =============================================================================
// Data fetching
// =============================================================================

async function refresh() {
  try {
    cachedStatus = await api.getStatus();
    connected = true;
    updateConnectionStatus(true);
    updateOverviewStats();
    updateNavHeight();
    loadPageData(currentPage);
  } catch (err) {
    connected = false;
    updateConnectionStatus(false, err.message);
  }
}

async function loadPageData(page) {
  switch (page) {
    case 'overview': await loadOverview(); break;
    case 'blocks': await loadBlocks(); break;
    case 'cells': await loadCells(); break;
    case 'turns': await loadTurns(); break;
    case 'receipts': await loadReceipts(); break;
    case 'capabilities': await loadCapabilities(); break;
    case 'proofs': await loadProofs(); break;
    case 'intents': await loadIntents(); break;
  }
}

// =============================================================================
// Connection Status
// =============================================================================

function updateConnectionStatus(ok, errMsg) {
  const el = document.getElementById('connection-status');
  const label = el.querySelector('.ex-connection__label');
  el.classList.toggle('connected', ok);
  el.classList.toggle('error', !ok);
  label.textContent = ok ? 'connected' : (errMsg ? 'error' : 'disconnected');
}

function updateNavHeight() {
  const el = document.getElementById('nav-height-value');
  if (cachedStatus) {
    el.textContent = api.formatNumber(cachedStatus.latest_height);
  }
}

// =============================================================================
// Overview
// =============================================================================

function updateOverviewStats() {
  if (!cachedStatus) return;
  document.getElementById('stat-height').textContent = api.formatNumber(cachedStatus.latest_height);
  document.getElementById('stat-peers').textContent = api.formatNumber(cachedStatus.peer_count);
  document.getElementById('stat-revocations').textContent = api.formatNumber(cachedStatus.revocation_count);
  document.getElementById('stat-notes').textContent = api.formatNumber(cachedStatus.note_count);
}

async function loadOverview() {
  // Update intent/conditional counts
  try {
    cachedIntents = await api.getIntents();
    document.getElementById('stat-intents').textContent = api.formatNumber(cachedIntents.length);
  } catch {
    document.getElementById('stat-intents').textContent = '--';
  }

  try {
    cachedConditionals = await api.getPendingConditionals();
    document.getElementById('stat-conditionals').textContent = api.formatNumber(cachedConditionals.length);
  } catch {
    document.getElementById('stat-conditionals').textContent = '--';
  }

  // Checkpoint
  try {
    cachedCheckpoint = await api.getCheckpoint();
    renderCheckpoint(cachedCheckpoint);
  } catch {
    document.getElementById('checkpoint-info').innerHTML =
      '<div class="empty-state">No checkpoint available</div>';
    document.getElementById('checkpoint-badge').textContent = '--';
  }

  // Recent roots
  try {
    cachedBlocks = await api.getBlocks();
    renderRecentRoots(cachedBlocks.slice(-10).reverse());
  } catch {
    document.getElementById('recent-roots').innerHTML =
      '<div class="empty-state">No attested roots found</div>';
  }
}

function renderCheckpoint(cp) {
  document.getElementById('checkpoint-badge').textContent = `height ${cp.height}`;
  document.getElementById('checkpoint-info').innerHTML = `
    <div class="checkpoint-grid">
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Height</div>
        <div class="checkpoint-field__value">${api.formatNumber(cp.height)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Epoch</div>
        <div class="checkpoint-field__value">${api.formatNumber(cp.epoch)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Federation Members</div>
        <div class="checkpoint-field__value">${cp.federation_members}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">QC Votes</div>
        <div class="checkpoint-field__value">${cp.qc_votes}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Ledger Root</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(cp.ledger_state_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Note Tree</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(cp.note_tree_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Nullifier Set</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(cp.nullifier_set_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Revocation Tree</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(cp.revocation_tree_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Timestamp</div>
        <div class="checkpoint-field__value">${api.formatTime(cp.timestamp)}</div>
      </div>
    </div>
  `;
}

function renderRecentRoots(roots) {
  const container = document.getElementById('recent-roots');
  if (!roots.length) {
    container.innerHTML = '<div class="empty-state">No attested roots yet</div>';
    return;
  }
  container.innerHTML = roots.map(r => `
    <div class="root-item">
      <span class="root-item__height">#${r.height}</span>
      <span class="root-item__hash">${api.shortHash(r.merkle_root, 12, 6)}</span>
      <span class="root-item__sigs">${r.signatures} sigs</span>
      <span class="root-item__time">${api.relativeTime(r.timestamp)}</span>
    </div>
  `).join('');
}

// =============================================================================
// Blocks
// =============================================================================

async function loadBlocks() {
  try {
    cachedBlocks = await api.getBlocks();
    renderBlocksTable(cachedBlocks);
  } catch (err) {
    document.getElementById('blocks-table').innerHTML =
      `<div class="empty-state"><div class="empty-state__icon">&#9632;</div>Unable to load blocks: ${err.message}</div>`;
  }
}

function renderBlocksTable(blocks) {
  const container = document.getElementById('blocks-table');
  if (!blocks.length) {
    container.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#9632;</div>No blocks found</div>';
    return;
  }

  // Sort descending by height
  const sorted = [...blocks].sort((a, b) => b.height - a.height);

  container.innerHTML = `
    <table class="ex-table">
      <thead>
        <tr>
          <th>Height</th>
          <th>Merkle Root</th>
          <th>Signatures</th>
          <th>Time</th>
        </tr>
      </thead>
      <tbody>
        ${sorted.map(b => `
          <tr data-height="${b.height}">
            <td class="cell-number">${api.formatNumber(b.height)}</td>
            <td class="cell-hash">${api.shortHash(b.merkle_root, 12, 6)}</td>
            <td>${b.signatures}</td>
            <td>${api.relativeTime(b.timestamp)}</td>
          </tr>
        `).join('')}
      </tbody>
    </table>
  `;

  // Click handler for rows
  container.querySelectorAll('tr[data-height]').forEach(row => {
    row.addEventListener('click', () => {
      const height = parseInt(row.dataset.height);
      const block = sorted.find(b => b.height === height);
      if (block) renderBlockDetail(block);
    });
  });
}

function renderBlockDetail(block) {
  const panel = document.getElementById('block-detail');
  const content = document.getElementById('block-detail-content');
  panel.hidden = false;

  content.innerHTML = `
    <h4>Block #${block.height}</h4>
    <div class="detail-grid">
      <span class="detail-grid__label">Height</span>
      <span class="detail-grid__value detail-grid__value--highlight">${api.formatNumber(block.height)}</span>
      <span class="detail-grid__label">Merkle Root</span>
      <span class="detail-grid__value detail-grid__value--hash">${block.merkle_root}</span>
      <span class="detail-grid__label">Signatures</span>
      <span class="detail-grid__value">${block.signatures}</span>
      <span class="detail-grid__label">Timestamp</span>
      <span class="detail-grid__value">${api.formatTime(block.timestamp)}</span>
    </div>
  `;

  document.getElementById('block-detail-close').onclick = () => panel.hidden = true;
}

// =============================================================================
// Cells
// =============================================================================

async function loadCells() {
  try {
    const cells = await api.getCells();
    renderCellsTable(cells);
  } catch (err) {
    // getCells might 404 if endpoint doesn't exist yet
    document.getElementById('cells-table').innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#9673;</div>
        Cell listing requires the /api/cells endpoint.<br>
        Use the search bar to look up a specific cell by ID.
      </div>`;
  }
}

function renderCellsTable(cells) {
  const container = document.getElementById('cells-table');
  if (!cells || !cells.length) {
    container.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#9673;</div>No cells in ledger</div>';
    return;
  }

  container.innerHTML = `
    <table class="ex-table">
      <thead>
        <tr>
          <th>Cell ID</th>
          <th>Balance</th>
          <th>Nonce</th>
          <th>Capabilities</th>
          <th>Delegation</th>
          <th>Program</th>
        </tr>
      </thead>
      <tbody>
        ${cells.map(c => `
          <tr data-cell-id="${c.id}">
            <td class="cell-hash">${api.shortHash(c.id, 10, 6)}</td>
            <td class="cell-number">${api.formatNumber(c.balance)}</td>
            <td>${api.formatNumber(c.nonce)}</td>
            <td>${c.capability_count}</td>
            <td>${c.has_delegate ? '<span class="cell-badge cell-badge--info">delegated</span>' : '--'}</td>
            <td>${c.has_program ? '<span class="cell-badge cell-badge--success">active</span>' : '<span class="cell-badge cell-badge--warning">none</span>'}</td>
          </tr>
        `).join('')}
      </tbody>
    </table>
  `;

  container.querySelectorAll('tr[data-cell-id]').forEach(row => {
    row.addEventListener('click', async () => {
      try {
        const detail = await api.getCell(row.dataset.cellId);
        renderCellDetail(detail);
      } catch {
        const cell = cells.find(c => c.id === row.dataset.cellId);
        if (cell) renderCellDetail(cell);
      }
    });
  });
}

function renderCellDetail(cell) {
  const panel = document.getElementById('cell-detail');
  const content = document.getElementById('cell-detail-content');
  panel.hidden = false;

  content.innerHTML = `
    <h4>Cell Detail</h4>
    <div class="detail-grid">
      <span class="detail-grid__label">Cell ID</span>
      <span class="detail-grid__value detail-grid__value--hash">${cell.id}</span>
      <span class="detail-grid__label">Status</span>
      <span class="detail-grid__value">${cell.found ? '<span class="cell-badge cell-badge--success">active</span>' : '<span class="cell-badge cell-badge--danger">not found</span>'}</span>
      <span class="detail-grid__label">Balance</span>
      <span class="detail-grid__value detail-grid__value--highlight">${api.formatNumber(cell.balance)} computrons</span>
      <span class="detail-grid__label">Nonce</span>
      <span class="detail-grid__value">${api.formatNumber(cell.nonce)}</span>
      <span class="detail-grid__label">Capabilities</span>
      <span class="detail-grid__value">${cell.capability_count} held</span>
      <span class="detail-grid__label">Public Key</span>
      <span class="detail-grid__value detail-grid__value--hash">${cell.public_key || '--'}</span>
      <span class="detail-grid__label">Token ID</span>
      <span class="detail-grid__value detail-grid__value--hash">${cell.token_id || '--'}</span>
      <span class="detail-grid__label">Delegation</span>
      <span class="detail-grid__value">${cell.has_delegate ? `delegated to ${api.shortHash(cell.delegate, 8, 4)}` : 'none'}</span>
      <span class="detail-grid__label">Program</span>
      <span class="detail-grid__value">${cell.has_program ? '<span class="cell-badge cell-badge--success">active</span>' : '<span class="cell-badge cell-badge--warning">none</span>'}</span>
      <span class="detail-grid__label">Proved State</span>
      <span class="detail-grid__value">${cell.proved_state ? '<span class="cell-badge cell-badge--success">verified</span>' : 'no'}</span>
    </div>
  `;

  document.getElementById('cell-detail-close').onclick = () => panel.hidden = true;
}

// =============================================================================
// Turns
// =============================================================================

async function loadTurns() {
  // Turns are visible via receipts on the local node
  try {
    cachedReceipts = await api.getReceipts();
    renderTurnsFromReceipts(cachedReceipts);
  } catch (err) {
    document.getElementById('turns-table').innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#8634;</div>
        Turns are tracked via the receipt chain.<br>
        ${err.message}
      </div>`;
  }
}

function renderTurnsFromReceipts(receipts) {
  const container = document.getElementById('turns-table');
  if (!receipts || !receipts.length) {
    container.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#8634;</div>No turns executed yet</div>';
    return;
  }

  container.innerHTML = `
    <table class="ex-table">
      <thead>
        <tr>
          <th>Turn Hash</th>
          <th>Computrons</th>
          <th>Time</th>
          <th>Status</th>
        </tr>
      </thead>
      <tbody>
        ${receipts.map(r => `
          <tr data-turn-hash="${r.turn_hash}">
            <td class="cell-hash">${api.shortHash(r.turn_hash, 10, 6)}</td>
            <td class="cell-number">${api.formatNumber(r.computrons_used)}</td>
            <td>${api.relativeTime(r.timestamp)}</td>
            <td><span class="cell-badge cell-badge--success">committed</span></td>
          </tr>
        `).join('')}
      </tbody>
    </table>
  `;

  container.querySelectorAll('tr[data-turn-hash]').forEach(row => {
    row.addEventListener('click', () => {
      const receipt = receipts.find(r => r.turn_hash === row.dataset.turnHash);
      if (receipt) renderTurnDetail(receipt);
    });
  });
}

function renderTurnDetail(receipt) {
  const panel = document.getElementById('turn-detail');
  const content = document.getElementById('turn-detail-content');
  panel.hidden = false;

  content.innerHTML = `
    <h4>Turn Detail</h4>
    <div class="detail-grid">
      <span class="detail-grid__label">Turn Hash</span>
      <span class="detail-grid__value detail-grid__value--hash">${receipt.turn_hash}</span>
      <span class="detail-grid__label">Computrons</span>
      <span class="detail-grid__value detail-grid__value--highlight">${api.formatNumber(receipt.computrons_used)}</span>
      <span class="detail-grid__label">Pre-State</span>
      <span class="detail-grid__value detail-grid__value--hash">${receipt.pre_state}</span>
      <span class="detail-grid__label">Post-State</span>
      <span class="detail-grid__value detail-grid__value--hash">${receipt.post_state}</span>
      <span class="detail-grid__label">Timestamp</span>
      <span class="detail-grid__value">${api.formatTime(receipt.timestamp)}</span>
      <span class="detail-grid__label">Status</span>
      <span class="detail-grid__value"><span class="cell-badge cell-badge--success">committed</span></span>
    </div>
  `;

  document.getElementById('turn-detail-close').onclick = () => panel.hidden = true;
}

// =============================================================================
// Receipts
// =============================================================================

async function loadReceipts() {
  try {
    cachedReceipts = await api.getReceipts();
    renderReceiptChain(cachedReceipts);
  } catch (err) {
    document.getElementById('receipts-chain').innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#9830;</div>
        Unable to load receipts: ${err.message}
      </div>`;
  }
}

function renderReceiptChain(receipts) {
  const container = document.getElementById('receipts-chain');
  if (!receipts || !receipts.length) {
    container.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#9830;</div>No receipts in the chain yet</div>';
    return;
  }

  container.innerHTML = receipts.map(r => `
    <div class="receipt-item">
      <div class="receipt-item__header">
        <span class="receipt-item__hash">${api.shortHash(r.turn_hash, 12, 6)}</span>
        <span class="receipt-item__time">${api.formatTime(r.timestamp)}</span>
        <span class="receipt-item__computrons">${api.formatNumber(r.computrons_used)} computrons</span>
      </div>
      <div class="receipt-item__states">
        <div class="receipt-item__state">
          <span class="receipt-item__state-label">Pre-state</span>
          <span class="receipt-item__state-value">${api.shortHash(r.pre_state, 10, 6)}</span>
        </div>
        <div class="receipt-item__state">
          <span class="receipt-item__state-label">Post-state</span>
          <span class="receipt-item__state-value">${api.shortHash(r.post_state, 10, 6)}</span>
        </div>
      </div>
    </div>
  `).join('');
}

// =============================================================================
// Capabilities
// =============================================================================

async function loadCapabilities() {
  try {
    cachedTokens = await api.getTokens();
    renderCapabilities(cachedTokens);
  } catch (err) {
    document.getElementById('capabilities-list').innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#8669;</div>
        Unable to load capabilities: ${err.message}
      </div>`;
  }
}

function renderCapabilities(tokens) {
  const container = document.getElementById('capabilities-list');
  if (!tokens || !tokens.length) {
    container.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#8669;</div>No capability tokens held</div>';
    return;
  }

  container.innerHTML = tokens.map(t => `
    <div class="cap-item">
      <span class="cap-item__id">${api.shortHash(t.id, 8, 4)}</span>
      <span class="cap-item__service">${t.service || 'universal'}</span>
      <span class="cap-item__badge cell-badge cell-badge--success">${t.label || 'active'}</span>
    </div>
  `).join('');
}

// =============================================================================
// Proofs
// =============================================================================

async function loadProofs() {
  // Proofs are generated locally; the node doesn't expose a proof list endpoint yet.
  // Show PIR info as a proxy for proof system status.
  try {
    const pirInfo = await api.getPirInfo();
    renderProofsFromPir(pirInfo);
  } catch (err) {
    document.getElementById('proofs-list').innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#9651;</div>
        Proof system info unavailable: ${err.message}
      </div>`;
  }
}

function renderProofsFromPir(pirInfo) {
  const container = document.getElementById('proofs-list');

  container.innerHTML = `
    <div class="proof-item">
      <div class="proof-item__header">
        <span class="proof-item__type">PIR Index</span>
        <span class="proof-item__size">${pirInfo.num_rows} rows x ${pirInfo.row_width} cols</span>
      </div>
      <div class="proof-item__details">
        <div>
          <div class="proof-item__detail-label">Database Size</div>
          <div class="proof-item__detail-value">${pirInfo.num_rows} capability tags</div>
        </div>
        <div>
          <div class="proof-item__detail-label">Row Width</div>
          <div class="proof-item__detail-value">${pirInfo.row_width} field elements</div>
        </div>
        <div>
          <div class="proof-item__detail-label">Tags</div>
          <div class="proof-item__detail-value">${pirInfo.tags.length > 0 ? pirInfo.tags.slice(0, 5).join(', ') + (pirInfo.tags.length > 5 ? '...' : '') : 'none'}</div>
        </div>
      </div>
    </div>
    <div class="empty-state" style="padding: 20px;">
      STARK proof verification requires the WASM verifier module.<br>
      Proofs are generated during block transitions and membership queries.
    </div>
  `;
}

// =============================================================================
// Intents
// =============================================================================

async function loadIntents() {
  // Active intents
  try {
    cachedIntents = await api.getIntents();
    renderActiveIntents(cachedIntents);
    document.getElementById('intents-count-badge').textContent = cachedIntents.length;
  } catch (err) {
    document.getElementById('intents-active').innerHTML =
      `<div class="empty-state">Unable to load intents: ${err.message}</div>`;
  }

  // Pending conditionals
  try {
    cachedConditionals = await api.getPendingConditionals();
    renderConditionals(cachedConditionals);
    document.getElementById('conditionals-count-badge').textContent = cachedConditionals.length;
  } catch (err) {
    document.getElementById('intents-conditionals').innerHTML =
      `<div class="empty-state">Unable to load conditionals: ${err.message}</div>`;
  }
}

function renderActiveIntents(intents) {
  const container = document.getElementById('intents-active');
  if (!intents || !intents.length) {
    container.innerHTML = '<div class="empty-state">No active intents in pool</div>';
    return;
  }

  container.innerHTML = intents.map(entry => {
    const intent = entry.intent;
    const kindLabel = intent.kind !== undefined ? `kind:${intent.kind}` : 'unknown';
    return `
      <div class="intent-item">
        <div class="intent-item__header">
          <span class="intent-item__id">${api.shortHash(entry.id, 8, 4)}</span>
          <span class="intent-item__kind">${kindLabel}</span>
        </div>
        <div class="intent-item__details">
          expiry: ${intent.expiry || '--'}
          ${intent.matcher ? ` | actions: ${intent.matcher.actions?.length || 0}` : ''}
        </div>
      </div>
    `;
  }).join('');
}

function renderConditionals(conditionals) {
  const container = document.getElementById('intents-conditionals');
  if (!conditionals || !conditionals.length) {
    container.innerHTML = '<div class="empty-state">No pending conditionals</div>';
    return;
  }

  container.innerHTML = conditionals.map(c => `
    <div class="conditional-item">
      <div class="conditional-item__header">
        <span class="conditional-item__hash">${api.shortHash(c.hash, 8, 4)}</span>
        <span class="conditional-item__type">${c.condition_type}</span>
      </div>
      <div class="conditional-item__meta">
        timeout: height ${api.formatNumber(c.timeout_height)} | submitted: height ${api.formatNumber(c.submitted_at)}
      </div>
    </div>
  `).join('');
}

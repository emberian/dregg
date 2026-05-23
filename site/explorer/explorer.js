/**
 * pyana explorer — main application logic.
 *
 * Single-page chain explorer that connects to a pyana node and displays
 * federation state: blocks, turns, receipts, cells, capabilities, proofs,
 * intents, federation status, notes, and deployed apps.
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
  document.querySelectorAll('.ex-nav__item').forEach(el => el.classList.remove('active'));
  const navItem = document.querySelector(`[data-page="${page}"]`);
  if (navItem) navItem.classList.add('active');

  document.querySelectorAll('.ex-page').forEach(el => el.classList.remove('active'));
  const pageEl = document.getElementById(`page-${page}`);
  if (pageEl) pageEl.classList.add('active');

  currentPage = page;
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
  if (/^\d+$/.test(query)) {
    navigateTo('blocks');
    highlightBlock(parseInt(query));
  } else if (query.length === 64 && /^[0-9a-fA-F]+$/.test(query)) {
    navigateTo('cells');
    lookupByHash(query);
  } else if (query.length > 8 && /^[0-9a-fA-F]+$/.test(query)) {
    navigateTo('cells');
    lookupByHash(query);
  }
}

async function highlightBlock(height) { /* highlighted on render */ }

async function lookupByHash(hash) {
  try {
    const cell = await api.getCell(hash.padEnd(64, '0'));
    if (cell && cell.found) {
      renderCellDetail(cell);
    }
  } catch { /* ignore */ }
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
    if (e.key === '/' && !isInputFocused()) {
      e.preventDefault();
      document.getElementById('search-input').focus();
    }
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
    case 'federation': await loadFederation(); break;
    case 'notes': await loadNotes(); break;
    case 'apps': await loadApps(); break;
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

  try {
    cachedCheckpoint = await api.getCheckpoint();
    renderCheckpoint(cachedCheckpoint);
  } catch {
    document.getElementById('checkpoint-info').innerHTML = '<div class="empty-state">No checkpoint available</div>';
    document.getElementById('checkpoint-badge').textContent = '--';
  }

  try {
    cachedBlocks = await api.getBlocks();
    renderRecentRoots(cachedBlocks.slice(-10).reverse());
  } catch {
    document.getElementById('recent-roots').innerHTML = '<div class="empty-state">No attested roots found</div>';
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
  const sorted = [...blocks].sort((a, b) => b.height - a.height);
  container.innerHTML = `
    <table class="ex-table">
      <thead><tr><th>Height</th><th>Merkle Root</th><th>Signatures</th><th>Time</th></tr></thead>
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
  container.querySelectorAll('tr[data-height]').forEach(row => {
    row.addEventListener('click', () => {
      const block = sorted.find(b => b.height === parseInt(row.dataset.height));
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
    document.getElementById('cells-table').innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#9673;</div>
        Cell listing requires the /api/cells endpoint.<br>
        Use the search bar to look up a specific cell by ID.
      </div>`;
  }
}

function classifyCell(cell) {
  if (cell.mode === 'sovereign') return 'sovereign';
  if (cell.mode === 'hosted') return 'hosted';
  if (!cell.balance && !cell.has_delegate && cell.capability_count === 0 && !cell.has_program) return 'sovereign';
  if (cell.has_program) return 'factory';
  return 'hosted';
}

function renderCellMode(mode) {
  switch (mode) {
    case 'sovereign': return '<span class="cell-badge cell-badge--sovereign">sovereign</span>';
    case 'factory': return '<span class="cell-badge cell-badge--factory">factory</span>';
    default: return '<span class="cell-badge cell-badge--hosted">hosted</span>';
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
      <thead><tr><th>Cell ID</th><th>Mode</th><th>Balance</th><th>Nonce</th><th>Caps</th><th>Delegation</th><th>Program</th></tr></thead>
      <tbody>
        ${cells.map(c => {
          const mode = classifyCell(c);
          return `
          <tr data-cell-id="${c.id}">
            <td class="cell-hash">${api.shortHash(c.id, 10, 6)}</td>
            <td>${renderCellMode(mode)}</td>
            <td class="cell-number">${api.formatNumber(c.balance)}</td>
            <td>${api.formatNumber(c.nonce)}</td>
            <td>${c.capability_count}</td>
            <td>${c.has_delegate ? '<span class="cell-badge cell-badge--info">delegated</span>' : '--'}</td>
            <td>${c.has_program ? '<span class="cell-badge cell-badge--success">active</span>' : '<span class="cell-badge cell-badge--warning">none</span>'}</td>
          </tr>`;
        }).join('')}
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

  const mode = classifyCell(cell);
  let modeSection = `<span class="detail-grid__label">Mode</span><span class="detail-grid__value">${renderCellMode(mode)}</span>`;
  if (mode === 'sovereign') {
    modeSection += `<span class="detail-grid__label">Storage</span><span class="detail-grid__value">Commitment only (state held locally)</span>`;
  } else if (mode === 'factory') {
    modeSection += `<span class="detail-grid__label">Provenance</span><span class="detail-grid__value">Factory-created (VK derived from parent)</span>`;
  }

  content.innerHTML = `
    <h4>Cell Detail</h4>
    <div class="detail-grid">
      <span class="detail-grid__label">Cell ID</span>
      <span class="detail-grid__value detail-grid__value--hash">${cell.id}</span>
      <span class="detail-grid__label">Status</span>
      <span class="detail-grid__value">${cell.found ? '<span class="cell-badge cell-badge--success">active</span>' : '<span class="cell-badge cell-badge--danger">not found</span>'}</span>
      ${modeSection}
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
  try {
    cachedReceipts = await api.getReceipts();
    renderTurnsFromReceipts(cachedReceipts);
  } catch (err) {
    document.getElementById('turns-table').innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#8634;</div>
        Turns are tracked via the receipt chain.<br>${err.message}
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
      <thead><tr><th>Turn Hash</th><th>Computrons</th><th>Time</th><th>Status</th></tr></thead>
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
      <span class="detail-grid__label">Auth Mode</span>
      <span class="detail-grid__value">${receipt.bearer_auth ? '<span class="cell-badge cell-badge--info">bearer</span>' : '<span class="cell-badge cell-badge--hosted">signature</span>'}</span>
      <span class="detail-grid__label">Proof</span>
      <span class="detail-grid__value">${receipt.has_proof ? '<span class="cell-badge cell-badge--success">proof-carrying</span>' : 'none'}</span>
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
      <div class="empty-state"><div class="empty-state__icon">&#9830;</div>Unable to load receipts: ${err.message}</div>`;
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
      <div class="empty-state"><div class="empty-state__icon">&#8669;</div>Unable to load capabilities: ${err.message}</div>`;
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
  const container = document.getElementById('proofs-list');
  try {
    const pirInfo = await api.getPirInfo();
    renderProofsView(pirInfo);
  } catch (err) {
    container.innerHTML = `
      <div class="empty-state"><div class="empty-state__icon">&#9651;</div>Proof system info unavailable: ${err.message}</div>`;
  }
}

function renderProofsView(pirInfo) {
  const container = document.getElementById('proofs-list');
  container.innerHTML = `
    <div class="proof-item">
      <div class="proof-item__header">
        <span class="proof-item__type">STARK</span>
        <span class="proof-item__size">BabyBear field, Poseidon2 hash</span>
      </div>
      <div class="proof-item__details">
        <div><div class="proof-item__detail-label">Backend</div><div class="proof-item__detail-value">MerklePoseidon2StarkAir (production)</div></div>
        <div><div class="proof-item__detail-label">Uses</div><div class="proof-item__detail-value">Membership, block transition, presentation</div></div>
        <div><div class="proof-item__detail-label">Verification</div><div class="proof-item__detail-value">FRI + Fiat-Shamir + action binding</div></div>
      </div>
    </div>
    <div class="proof-item">
      <div class="proof-item__header">
        <span class="proof-item__type">Kimchi</span>
        <span class="proof-item__size">Pasta curves</span>
      </div>
      <div class="proof-item__details">
        <div><div class="proof-item__detail-label">Backend</div><div class="proof-item__detail-value">Plonkish constraint system</div></div>
        <div><div class="proof-item__detail-label">Uses</div><div class="proof-item__detail-value">Recursive verification, IVC folding</div></div>
        <div><div class="proof-item__detail-label">Status</div><div class="proof-item__detail-value">Spike phase (constraint system verified)</div></div>
      </div>
    </div>
    <div class="proof-item">
      <div class="proof-item__header">
        <span class="proof-item__type">Composed</span>
        <span class="proof-item__size">Multi-proof binding</span>
      </div>
      <div class="proof-item__details">
        <div><div class="proof-item__detail-label">Binding</div><div class="proof-item__detail-value">BLAKE3 composition commitment over sub-proofs</div></div>
        <div><div class="proof-item__detail-label">Modes</div><div class="proof-item__detail-value">sequential, parallel, recursive</div></div>
        <div><div class="proof-item__detail-label">Public Inputs</div><div class="proof-item__detail-value">pi[2..6] action binding, pi[6..10] composition commitment</div></div>
      </div>
    </div>
    <div class="proof-item">
      <div class="proof-item__header">
        <span class="proof-item__type">PIR Index</span>
        <span class="proof-item__size">${pirInfo.num_rows} rows x ${pirInfo.row_width} cols</span>
      </div>
      <div class="proof-item__details">
        <div><div class="proof-item__detail-label">Database Size</div><div class="proof-item__detail-value">${pirInfo.num_rows} capability tags</div></div>
        <div><div class="proof-item__detail-label">Row Width</div><div class="proof-item__detail-value">${pirInfo.row_width} field elements</div></div>
        <div><div class="proof-item__detail-label">Tags</div><div class="proof-item__detail-value">${pirInfo.tags.length > 0 ? pirInfo.tags.slice(0, 5).join(', ') + (pirInfo.tags.length > 5 ? '...' : '') : 'none'}</div></div>
      </div>
    </div>
  `;
}

// =============================================================================
// Intents
// =============================================================================

async function loadIntents() {
  try {
    cachedIntents = await api.getIntents();
    renderActiveIntents(cachedIntents);
    document.getElementById('intents-count-badge').textContent = cachedIntents.length;
  } catch (err) {
    document.getElementById('intents-active').innerHTML =
      `<div class="empty-state">Unable to load intents: ${err.message}</div>`;
  }
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
          expiry: ${intent.expiry || '--'}${intent.matcher ? ` | actions: ${intent.matcher.actions?.length || 0}` : ''}
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

// =============================================================================
// Federation
// =============================================================================

async function loadFederation() {
  try {
    const status = cachedStatus || await api.getStatus();
    const blocks = cachedBlocks || await api.getBlocks();
    const checkpoint = cachedCheckpoint || await api.getCheckpoint().catch(() => null);

    document.getElementById('fed-stat-nodes').textContent = api.formatNumber((status.peer_count || 0) + 1);
    document.getElementById('fed-stat-height').textContent = api.formatNumber(status.latest_height);
    document.getElementById('fed-stat-health').textContent = status.healthy ? 'healthy' : 'degraded';
    document.getElementById('fed-stat-health').style.color = status.healthy ? 'var(--success)' : 'var(--danger)';

    if (blocks && blocks.length > 0) {
      const latest = blocks[blocks.length - 1];
      document.getElementById('fed-stat-root').textContent = api.shortHash(latest.merkle_root, 8, 4);
    }

    renderFederationNodes(status, checkpoint);
    renderFederationRootHistory(blocks);
  } catch (err) {
    document.getElementById('federation-nodes').innerHTML =
      `<div class="empty-state">Unable to load federation status: ${err.message}</div>`;
  }
}

function renderFederationNodes(status, checkpoint) {
  const container = document.getElementById('federation-nodes');
  let html = `
    <div class="fed-node-item">
      <span class="fed-node-item__icon">&#9679;</span>
      <span class="fed-node-item__name">Local Node (self)</span>
      <span class="cell-badge cell-badge--success">active</span>
    </div>
  `;
  for (let i = 0; i < (status.peer_count || 0); i++) {
    html += `
      <div class="fed-node-item">
        <span class="fed-node-item__icon">&#9679;</span>
        <span class="fed-node-item__name">Peer ${i + 1}</span>
        <span class="cell-badge cell-badge--info">connected</span>
      </div>
    `;
  }
  if (checkpoint) {
    html += `
      <div class="fed-node-item" style="margin-top: 12px; padding-top: 12px; border-top: 1px solid var(--border);">
        <span class="fed-node-item__icon">&#9670;</span>
        <span class="fed-node-item__name">Federation Members</span>
        <span class="cell-badge cell-badge--info">${checkpoint.federation_members}</span>
      </div>
      <div class="fed-node-item">
        <span class="fed-node-item__icon">&#9651;</span>
        <span class="fed-node-item__name">QC Votes</span>
        <span class="cell-badge cell-badge--success">${checkpoint.qc_votes}</span>
      </div>
      <div class="fed-node-item">
        <span class="fed-node-item__icon">&#9776;</span>
        <span class="fed-node-item__name">Epoch</span>
        <span class="cell-badge cell-badge--hosted">${checkpoint.epoch}</span>
      </div>
    `;
  }
  container.innerHTML = html;
}

function renderFederationRootHistory(blocks) {
  const container = document.getElementById('federation-root-history');
  if (!blocks || !blocks.length) {
    container.innerHTML = '<div class="empty-state">No roots attested yet</div>';
    return;
  }
  const recent = blocks.slice(-15).reverse();
  container.innerHTML = recent.map(r => `
    <div class="root-item">
      <span class="root-item__height">#${r.height}</span>
      <span class="root-item__hash">${api.shortHash(r.merkle_root, 12, 6)}</span>
      <span class="root-item__sigs">${r.signatures} sigs</span>
      <span class="root-item__time">${api.relativeTime(r.timestamp)}</span>
    </div>
  `).join('');
}

// =============================================================================
// Notes
// =============================================================================

async function loadNotes() {
  try {
    const status = cachedStatus || await api.getStatus();
    const checkpoint = await api.getCheckpoint().catch(() => null);
    const blocks = cachedBlocks || await api.getBlocks();

    document.getElementById('notes-stat-count').textContent = api.formatNumber(status.note_count);
    document.getElementById('notes-stat-revocations').textContent = api.formatNumber(status.revocation_count);

    if (checkpoint) {
      document.getElementById('notes-stat-nullifier-root').textContent = api.shortHash(checkpoint.nullifier_set_root, 8, 4);
      document.getElementById('notes-stat-tree-root').textContent = api.shortHash(checkpoint.note_tree_root, 8, 4);
    }

    renderNoteRootHistory(blocks);
    renderNoteCheckpointState(checkpoint);
  } catch (err) {
    document.getElementById('notes-root-history').innerHTML =
      `<div class="empty-state">Unable to load note data: ${err.message}</div>`;
  }
}

function renderNoteRootHistory(blocks) {
  const container = document.getElementById('notes-root-history');
  if (!blocks || !blocks.length) {
    container.innerHTML = '<div class="empty-state">No roots attested yet</div>';
    return;
  }
  const recent = blocks.slice(-12).reverse();
  container.innerHTML = `
    <div class="note-root-list">
      ${recent.map(r => `
        <div class="root-item">
          <span class="root-item__height">#${r.height}</span>
          <span class="root-item__hash">${api.shortHash(r.merkle_root, 12, 6)}</span>
          <span class="root-item__time">${api.relativeTime(r.timestamp)}</span>
        </div>
      `).join('')}
    </div>
    <div style="margin-top: 12px; font-family: var(--mono); font-size: 10px; color: var(--text-muted);">
      Each root represents a committed note tree state. Nullifiers prevent double-spend.
    </div>
  `;
}

function renderNoteCheckpointState(checkpoint) {
  const container = document.getElementById('notes-checkpoint-state');
  if (!checkpoint) {
    container.innerHTML = '<div class="empty-state">No checkpoint available</div>';
    return;
  }
  container.innerHTML = `
    <div class="checkpoint-grid">
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Note Tree Root</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(checkpoint.note_tree_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Nullifier Set Root</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(checkpoint.nullifier_set_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Revocation Tree Root</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(checkpoint.revocation_tree_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Ledger State Root</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(checkpoint.ledger_state_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Height</div>
        <div class="checkpoint-field__value">${api.formatNumber(checkpoint.height)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Timestamp</div>
        <div class="checkpoint-field__value">${api.formatTime(checkpoint.timestamp)}</div>
      </div>
    </div>
    <div style="margin-top: 12px; font-family: var(--mono); font-size: 10px; color: var(--text-muted);">
      Notes carry hidden asset types. Commitments = Poseidon2(value, asset_type, blinding). Nullifiers = BLAKE3(note_commitment, nullifier_key).
    </div>
  `;
}

// =============================================================================
// Apps
// =============================================================================

async function loadApps() {
  const grid = document.getElementById('apps-grid');
  try {
    const cells = await api.getCells();
    const programCells = cells.filter(c => c.has_program);
    const totalBalance = cells.reduce((sum, c) => sum + (c.balance || 0), 0);

    document.getElementById('app-gallery-status').textContent = programCells.length > 0 ? programCells.length + ' contracts' : 'available';
    document.getElementById('app-amm-status').textContent = totalBalance > 0 ? api.formatNumber(totalBalance) + ' locked' : 'available';
    document.getElementById('app-orderbook-status').textContent = 'available';
    document.getElementById('app-lending-status').textContent = 'available';
    document.getElementById('app-stablecoin-status').textContent = 'available';
    document.getElementById('app-identity-status').textContent = 'available';
  } catch {
    document.querySelectorAll('.app-card__status').forEach(el => { el.textContent = 'pending'; });
  }

  grid.querySelectorAll('.app-card').forEach(card => {
    card.onclick = () => renderAppDetail(card.dataset.app);
  });
}

function renderAppDetail(appName) {
  const panel = document.getElementById('app-detail');
  const content = document.getElementById('app-detail-content');
  panel.hidden = false;

  const apps = {
    gallery: { title: 'Gallery Auctions', desc: 'NFT auctions with ZK ownership proofs. Each auction cell holds an asset commitment and accepts sealed bids.', fields: [['Auction Type', 'English, Dutch'], ['Ownership Proof', 'STARK membership over note tree'], ['Bid Mechanism', 'Sealed-bid commit-reveal'], ['Settlement', 'Atomic swap via conditional turns']] },
    amm: { title: 'AMM Pools', desc: 'Constant-product (x*y=k) liquidity pools. LPs deposit paired assets and earn fees from swaps.', fields: [['Pool Type', 'Constant-product (Uniswap v2)'], ['LP Tokens', 'Minted on deposit, burned on withdrawal'], ['Fee Model', '0.3% swap fee to LP holders'], ['Reserves', 'Stored as sovereign cell commitments']] },
    orderbook: { title: 'Orderbook', desc: 'On-chain limit order book with price-time priority matching.', fields: [['Order Types', 'Limit, market, fill-or-kill'], ['Matching', 'Price-time priority (continuous)'], ['Settlement', 'Atomic multi-party turns'], ['Cancellation', 'Bearer-auth revocation']] },
    lending: { title: 'Lending Positions', desc: 'Collateralized debt positions with liquidation thresholds.', fields: [['Position Type', 'Isolated margin CDPs'], ['Collateral Ratio', 'Configurable per asset pair'], ['Liquidation', 'Triggered by price oracle conditionals'], ['Interest', 'Block-based accrual via sovereign witness']] },
    stablecoin: { title: 'Stablecoin CDPs', desc: 'Algorithmic stablecoin backed by over-collateralized positions.', fields: [['Peg', '1:1 USD target'], ['Collateral', 'Multi-asset, configurable ratios'], ['Stability Fee', 'Per-epoch, collected on position close'], ['Health Factor', 'Computed from oracle + collateral ratio']] },
    identity: { title: 'Anonymous Credentials', desc: 'RBAC-based datalog credentials with ZK presentation.', fields: [['Schema', 'Datalog rules (issuer defines)'], ['Presentation', 'STARK proof of attribute satisfaction'], ['Revocation', 'Merkle non-membership proof'], ['Privacy', 'Zero-knowledge (no identity linkage)']] },
  };

  const app = apps[appName] || { title: appName, desc: 'Details unavailable.', fields: [] };
  content.innerHTML = `
    <h4>${app.title}</h4>
    <p style="font-size: 12px; color: var(--text-dim); margin-bottom: 16px; line-height: 1.6;">${app.desc}</p>
    <div class="detail-grid">
      ${app.fields.map(([label, value]) => `
        <span class="detail-grid__label">${label}</span>
        <span class="detail-grid__value">${value}</span>
      `).join('')}
    </div>
  `;
  document.getElementById('app-detail-close').onclick = () => panel.hidden = true;
}

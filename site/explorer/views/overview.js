/**
 * Overview view — dashboard with stats cards, recent activity, checkpoint info.
 */

import { bus, state, navigateTo } from '../app.js';
import * as api from '../api.js';

export const name = 'overview';

let container = null;
let latestOverview = { checkpoint: null, blocks: [] };

export function init(el) {
  container = el;
  wireObjectMap();
  renderDevnetBrief(state.status, state.checkpoint, state.blocks);
  renderObjectMap({ intents: state.intents, conditionals: state.conditionals, blocks: state.blocks });

  bus.on('status:updated', (status) => {
    if (state.currentPage !== 'overview') return;
    renderStats(status);
    renderDevnetBrief(status, latestOverview.checkpoint, latestOverview.blocks);
  });

  bus.on('overview:updated', ({ intents, conditionals, checkpoint, blocks }) => {
    if (state.currentPage !== 'overview') return;
    latestOverview = { checkpoint, blocks };
    renderDevnetBrief(state.status, checkpoint, blocks);
    renderObjectMap({ intents, conditionals, checkpoint, blocks, cells: state.cells, receipts: state.receipts, tokens: state.tokens });
    renderIntentStats(intents, conditionals);
    renderCheckpoint(checkpoint);
    renderRecentRoots(blocks);
  });

  bus.on('connection:changed', () => {
    if (state.currentPage === 'overview') renderDevnetBrief(state.status, latestOverview.checkpoint, latestOverview.blocks);
  });

  bus.on('diagnostics:updated', () => {
    if (state.currentPage === 'overview') renderDevnetBrief(state.status, latestOverview.checkpoint, latestOverview.blocks);
  });
}

export function update(appState) {
  if (appState.status) {
    renderStats(appState.status);
    renderDevnetBrief(appState.status, appState.checkpoint, appState.blocks);
  }
}

export function destroy() {}

function renderStats(status) {
  if (!status) return;
  const el = (id) => document.getElementById(id);
  el('stat-height').textContent = api.formatNumber(api.statusHeight(status));
  el('stat-peers').textContent = api.formatNumber(api.statusPeers(status));
  el('stat-revocations').textContent = api.formatNumber(api.statusRevocations(status));
  el('stat-notes').textContent = api.formatNumber(api.statusNotes(status));
}

function renderIntentStats(intents, conditionals) {
  document.getElementById('stat-intents').textContent = api.formatNumber(intents?.length || 0);
  document.getElementById('stat-conditionals').textContent = api.formatNumber(conditionals?.length || 0);
}

function renderCheckpoint(cp) {
  if (!cp) {
    document.getElementById('checkpoint-info').innerHTML = '<div class="empty-state">No checkpoint available</div>';
    document.getElementById('checkpoint-badge').textContent = '--';
    return;
  }
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
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(cp.ledger_state_root || cp.merkle_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Note Tree</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(cp.note_tree_root || cp.note_root, 12, 6)}</div>
      </div>
      <div class="checkpoint-field">
        <div class="checkpoint-field__label">Nullifier Set</div>
        <div class="checkpoint-field__value checkpoint-field__value--hash">${api.shortHash(cp.nullifier_set_root || cp.nullifier_root, 12, 6)}</div>
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

function renderRecentRoots(blocks) {
  const container = document.getElementById('recent-roots');
  if (!blocks || !blocks.length) {
    container.innerHTML = '<div class="empty-state">No attested roots found</div>';
    return;
  }
  const roots = blocks.slice(-10).reverse();
  container.innerHTML = roots.map(r => `
    <button class="root-item root-item--button" type="button" data-root-height="${r.height}">
      <span class="root-item__height">#${r.height}</span>
      <span class="root-item__hash">${api.shortHash(api.blockRoot(r), 12, 6)}</span>
      <span class="root-item__sigs">${r.signatures} sigs</span>
      <span class="root-item__time">${api.relativeTime(r.timestamp)}</span>
    </button>
  `).join('');
  container.querySelectorAll('[data-root-height]').forEach(btn => {
    btn.addEventListener('click', () => {
      const height = parseInt(btn.dataset.rootHeight, 10);
      navigateTo('blocks');
      bus.emit('search:block', height);
    });
  });
}

function wireObjectMap() {
  container.querySelectorAll('[data-map-page]').forEach(btn => {
    btn.addEventListener('click', () => navigateTo(btn.dataset.mapPage));
  });
}

function renderDevnetBrief(status, checkpoint, blocks) {
  const nodeEl = document.getElementById('devnet-node-url');
  const metaEl = document.getElementById('devnet-node-meta');
  const heightEl = document.getElementById('devnet-fact-height');
  const rootEl = document.getElementById('devnet-fact-root');
  const checkpointEl = document.getElementById('devnet-fact-checkpoint');
  if (!nodeEl || !metaEl || !heightEl || !rootEl || !checkpointEl) return;

  nodeEl.textContent = api.getNodeUrl();
  if (!state.connected) {
    metaEl.textContent = diagnosticSummary(state.diagnostics);
    heightEl.textContent = '--';
    rootEl.textContent = '--';
    checkpointEl.textContent = checkpoint?.height ? `#${api.formatNumber(checkpoint.height)}` : '--';
    return;
  }

  const peers = api.statusPeers(status);
  const latestRoot = latestBlock(blocks);
  const latency = Number.isFinite(state.diagnostics?.latencyMs) ? ` / ${state.diagnostics.latencyMs} ms` : '';
  metaEl.textContent = `${api.healthLabel(status)} / ${api.formatNumber(peers)} peer${peers === 1 ? '' : 's'}${latency} / auto-refresh ${state.autoRefresh ? 'on' : 'off'}`;
  heightEl.textContent = api.formatNumber(api.statusHeight(status));
  rootEl.textContent = api.shortHash(api.blockRoot(latestRoot), 12, 6);
  checkpointEl.textContent = checkpoint?.height ? `#${api.formatNumber(checkpoint.height)}` : '--';
}

function renderObjectMap({ intents, conditionals, blocks, cells, receipts, tokens }) {
  setText('map-blocks-value', blocks?.length ? `${api.formatNumber(blocks.length)} roots` : 'no roots');
  setText('map-cells-value', cells?.length ? `${api.formatNumber(cells.length)} cells` : 'queryable');
  const intentCount = (intents?.length || 0) + (conditionals?.length || 0);
  setText('map-turns-value', intentCount ? `${api.formatNumber(intentCount)} queued` : 'pool empty');
  setText('map-receipts-value', receipts?.length ? `${api.formatNumber(receipts.length)} receipts` : 'proof chain');
  setText('map-delegations-value', tokens?.length ? `${api.formatNumber(tokens.length)} tokens` : 'authority');
}

function diagnosticSummary(diagnostic) {
  if (!diagnostic) return 'No status response from this node.';
  if (diagnostic.status) return `/status returned ${diagnostic.status} ${diagnostic.statusText || ''}`.trim();
  if (diagnostic.errorMessage) return `Browser could not read /status: ${diagnostic.errorMessage}`;
  return 'Browser could not read /status. Check node URL and CORS.';
}

function latestBlock(blocks) {
  if (!blocks || !blocks.length) return null;
  return [...blocks].sort((a, b) => (b.height || 0) - (a.height || 0))[0];
}

function setText(id, value) {
  const el = document.getElementById(id);
  if (el) el.textContent = value;
}

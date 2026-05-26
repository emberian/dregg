/**
 * Federation view — node health, finality levels, DAG state.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'federation';

export function init(el) {
  bus.on('federation:updated', (fedStatus) => {
    if (state.currentPage === 'federation') renderFederation(fedStatus);
  });
}

export function update(appState) {
  if (appState.status) {
    renderFederationStats(appState.status, appState.blocks, appState.checkpoint);
  }
}

export function destroy() {}

function renderFederation(fedStatus) {
  renderFederationStats(fedStatus, fedStatus.roots, fedStatus.checkpoint);
}

function renderFederationStats(status, blocks, checkpoint) {
  document.getElementById('fed-stat-nodes').textContent = api.formatNumber(api.statusPeers(status) + 1);
  document.getElementById('fed-stat-height').textContent = api.formatNumber(api.statusHeight(status));
  const health = api.healthLabel(status);
  document.getElementById('fed-stat-health').textContent = health;
  document.getElementById('fed-stat-health').style.color = health === 'degraded' ? 'var(--danger)' : 'var(--success)';

  if (blocks && blocks.length > 0) {
    const latest = [...blocks].sort((a, b) => (b.height || 0) - (a.height || 0))[0];
    document.getElementById('fed-stat-root').textContent = api.shortHash(api.blockRoot(latest), 8, 4);
  }

  renderFederationNodes(status, checkpoint);
  renderFederationRootHistory(blocks);
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
  for (let i = 0; i < api.statusPeers(status); i++) {
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
      <span class="root-item__hash">${api.shortHash(api.blockRoot(r), 12, 6)}</span>
      <span class="root-item__sigs">${r.signatures} sigs</span>
      <span class="root-item__time">${api.relativeTime(r.timestamp)}</span>
    </div>
  `).join('');
}

/**
 * Turns view — turn list derived from receipt chain with effect type breakdown.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'turns';

let focusedTurnHash = null;

export function init(el) {
  bus.on('receipts:updated', (receipts) => {
    if (state.currentPage === 'turns') renderTurnsFromReceipts(receipts);
  });
  bus.on('explorer:inspect', ({ kind, id }) => {
    if (kind === 'turn') focusTurn(id);
  });
}

export function update(appState) {
  if (appState.receipts) renderTurnsFromReceipts(appState.receipts);
}

export function destroy() {}

function renderTurnsFromReceipts(receipts) {
  const container = document.getElementById('turns-table');
  if (!receipts || !receipts.length) {
    container.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#8634;</div>No turns executed yet</div>';
    return;
  }
  container.innerHTML = `
    <table class="ex-table">
      <thead><tr><th>Turn Hash</th><th>Computrons</th><th>Time</th><th>Auth</th><th>Proof</th><th>Status</th></tr></thead>
      <tbody>
        ${receipts.map(r => `
          <tr data-turn-hash="${r.turn_hash}">
            <td class="cell-hash">${api.shortHash(r.turn_hash, 10, 6)}</td>
            <td class="cell-number">${api.formatNumber(r.computrons_used)}</td>
            <td>${api.relativeTime(r.timestamp)}</td>
            <td>${r.bearer_auth ? '<span class="cell-badge cell-badge--info">bearer</span>' : '<span class="cell-badge cell-badge--hosted">sig</span>'}</td>
            <td>${r.has_proof ? '<span class="cell-badge cell-badge--success">ZK</span>' : '--'}</td>
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
  if (focusedTurnHash) setTimeout(() => focusTurn(focusedTurnHash), 0);
}

function focusTurn(hash) {
  focusedTurnHash = hash;
  const row = document.querySelector(`tr[data-turn-hash="${hash}"]`);
  if (!row) return;
  row.classList.add('highlighted');
  row.scrollIntoView({ behavior: 'smooth', block: 'center' });
  row.click();
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
      <span class="detail-grid__label">Auth Mode</span>
      <span class="detail-grid__value">${receipt.bearer_auth ? '<span class="cell-badge cell-badge--info">bearer</span>' : '<span class="cell-badge cell-badge--hosted">signature</span>'}</span>
      <span class="detail-grid__label">Proof</span>
      <span class="detail-grid__value">${receipt.has_proof ? '<span class="cell-badge cell-badge--success">proof-carrying</span>' : 'none'}</span>
    </div>
  `;
  document.getElementById('turn-detail-close').onclick = () => panel.hidden = true;
}

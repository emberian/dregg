/**
 * Blocks view — attested roots table with detail panel.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'blocks';

let container = null;

export function init(el) {
  container = el;

  bus.on('blocks:updated', (blocks) => {
    if (state.currentPage === 'blocks') renderBlocksTable(blocks);
  });

  bus.on('search:block', (height) => {
    // Highlight the searched block
    setTimeout(() => {
      const row = container.querySelector(`tr[data-height="${height}"]`);
      if (row) {
        row.classList.add('highlighted');
        row.scrollIntoView({ behavior: 'smooth', block: 'center' });
      }
    }, 100);
  });
}

export function update(appState) {
  if (appState.blocks) renderBlocksTable(appState.blocks);
}

export function destroy() {}

function renderBlocksTable(blocks) {
  const tableContainer = document.getElementById('blocks-table');
  if (!blocks || !blocks.length) {
    tableContainer.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#9632;</div>No blocks found</div>';
    return;
  }
  const sorted = [...blocks].sort((a, b) => b.height - a.height);
  tableContainer.innerHTML = `
    <table class="ex-table">
      <thead><tr><th>Height</th><th>Merkle Root</th><th>Signatures</th><th>Time</th></tr></thead>
      <tbody>
        ${sorted.map(b => `
          <tr data-height="${b.height}">
            <td class="cell-number">${api.formatNumber(b.height)}</td>
            <td class="cell-hash">${api.shortHash(api.blockRoot(b), 12, 6)}</td>
            <td>${b.signatures}</td>
            <td>${api.relativeTime(b.timestamp)}</td>
          </tr>
        `).join('')}
      </tbody>
    </table>
  `;
  tableContainer.querySelectorAll('tr[data-height]').forEach(row => {
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
      <span class="detail-grid__value detail-grid__value--hash">${api.blockRoot(block) || '--'}</span>
      <span class="detail-grid__label">Signatures</span>
      <span class="detail-grid__value">${block.signatures}</span>
      <span class="detail-grid__label">Timestamp</span>
      <span class="detail-grid__value">${api.formatTime(block.timestamp)}</span>
    </div>
    <div class="block-detail__actions" style="margin-top: 16px;">
      <button class="btn btn-sm btn-secondary" onclick="document.getElementById('block-detail').hidden=true">Close</button>
    </div>
  `;
  document.getElementById('block-detail-close').onclick = () => panel.hidden = true;
}

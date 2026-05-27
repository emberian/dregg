/**
 * Cells view — cell listing with sovereign/hosted/factory badges.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'cells';

let container = null;

function starbridgeHref(uri) {
  return `../starbridge/?at=${encodeURIComponent(uri)}&runtime=remote`;
}

export function init(el) {
  container = el;

  bus.on('cells:updated', (cells) => {
    if (state.currentPage === 'cells') renderCellsTable(cells);
  });

  bus.on('cell:detail', (cell) => {
    renderCellDetail(cell);
  });

  bus.on('search:hash', (hash) => {
    // Will be handled by search component fetching the cell
  });

  bus.on('explorer:inspect', async ({ kind, id }) => {
    if (kind !== 'cell') return;
    try {
      const detail = await api.getCell(id);
      renderCellDetail(detail);
    } catch {
      const row = container?.querySelector(`tr[data-cell-id="${id}"]`);
      if (row) row.click();
    }
  });
}

export function update() {}
export function destroy() {}

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
  const tableContainer = document.getElementById('cells-table');
  if (!cells || !cells.length) {
    tableContainer.innerHTML = `
      <div class="empty-state">
        <div class="empty-state__icon">&#9673;</div>
        Cell listing requires the /api/cells endpoint.<br>
        Use the search bar to look up a specific cell by ID.
      </div>`;
    return;
  }

  tableContainer.innerHTML = `
    <table class="ex-table">
      <thead><tr><th>Cell ID</th><th>Mode</th><th>Balance</th><th>Nonce</th><th>Caps</th><th>Delegation</th><th>Program</th><th>IDE</th></tr></thead>
      <tbody>
        ${cells.map(c => {
          const mode = classifyCell(c);
          const cellUri = `dregg://cell/${c.id}`;
          return `
          <tr data-cell-id="${c.id}">
            <td class="cell-hash">${api.shortHash(c.id, 10, 6)}</td>
            <td>${renderCellMode(mode)}</td>
            <td class="cell-number">${api.formatNumber(c.balance)}</td>
            <td>${api.formatNumber(c.nonce)}</td>
            <td>${c.capability_count}</td>
            <td>${c.has_delegate ? '<span class="cell-badge cell-badge--info">delegated</span>' : '--'}</td>
            <td>${c.has_program ? '<span class="cell-badge cell-badge--success">active</span>' : '<span class="cell-badge cell-badge--warning">none</span>'}</td>
            <td><a class="ex-starbridge-link" href="${starbridgeHref(cellUri)}">Starbridge</a></td>
          </tr>`;
        }).join('')}
      </tbody>
    </table>
  `;

  tableContainer.querySelectorAll('tr[data-cell-id]').forEach(row => {
    row.addEventListener('click', async (event) => {
      if (event.target.closest('a')) return;
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
    <div class="block-detail__actions" style="margin-top: 16px;">
      <a class="btn btn-sm btn-primary" href="${starbridgeHref(`dregg://cell/${cell.id}`)}">Open cell in Starbridge</a>
      <button class="btn btn-sm btn-secondary" onclick="document.getElementById('cell-detail').hidden=true">Close</button>
    </div>
  `;
  document.getElementById('cell-detail-close').onclick = () => panel.hidden = true;
}

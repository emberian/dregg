/**
 * Receipts view — receipt chain visualization.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'receipts';

let focusedReceiptHash = null;

export function init(el) {
  bus.on('receipts:updated', (receipts) => {
    if (state.currentPage === 'receipts') renderReceiptChain(receipts);
  });
  bus.on('explorer:inspect', ({ kind, id }) => {
    if (kind === 'receipt') focusReceipt(id);
  });
}

export function update(appState) {
  if (appState.receipts) renderReceiptChain(appState.receipts);
}

export function destroy() {}

function starbridgeHref(uri) {
  return `../starbridge/?at=${encodeURIComponent(uri)}&runtime=remote`;
}

function renderReceiptChain(receipts) {
  const container = document.getElementById('receipts-chain');
  if (!receipts || !receipts.length) {
    container.innerHTML = '<div class="empty-state"><div class="empty-state__icon">&#9830;</div>No receipts in the chain yet</div>';
    return;
  }
  container.innerHTML = receipts.map(r => `
    <div class="receipt-item" data-receipt-hash="${r.receipt_hash}" data-turn-hash="${r.turn_hash}">
      <div class="receipt-item__header">
        <span class="receipt-item__hash">${api.shortHash(r.receipt_hash, 12, 6)}</span>
        <span class="receipt-item__time">${api.formatTime(r.timestamp)}</span>
        <span class="receipt-item__computrons">${api.formatNumber(r.computrons_used)} computrons</span>
      </div>
      <div class="receipt-item__proofs">
        <span class="cell-badge ${r.executor_signed ? 'cell-badge--success' : 'cell-badge--hosted'}">${r.executor_signed ? 'executor signed' : 'unsigned'}</span>
        <span class="cell-badge ${r.has_witness ? 'cell-badge--success' : 'cell-badge--info'}">${r.witness_count || 0} witness${(r.witness_count || 0) === 1 ? '' : 'es'}</span>
        <span class="cell-badge cell-badge--info">${r.finality || 'unknown'}</span>
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
      <div class="receipt-item__actions">
        <a class="ex-starbridge-link" href="${starbridgeHref(`dregg://receipt/${r.receipt_hash}`)}">Open receipt in Starbridge</a>
        <a class="ex-starbridge-link" href="${starbridgeHref(`dregg://turn/${r.turn_hash}`)}">Debug turn</a>
        <button class="ex-starbridge-link receipt-witness-button" type="button" data-witness-hash="${r.receipt_hash}">Inspect witnesses</button>
      </div>
      <pre class="receipt-item__witnesses" data-witness-panel="${r.receipt_hash}" hidden></pre>
    </div>
  `).join('');
  container.querySelectorAll('.receipt-witness-button').forEach(button => {
    button.addEventListener('click', () => inspectWitnesses(button.dataset.witnessHash));
  });
  if (focusedReceiptHash) setTimeout(() => focusReceipt(focusedReceiptHash), 0);
}

function focusReceipt(hash) {
  focusedReceiptHash = hash;
  const item = document.querySelector(`[data-receipt-hash="${hash}"], [data-turn-hash="${hash}"]`);
  if (!item) return;
  item.classList.add('highlighted');
  item.scrollIntoView({ behavior: 'smooth', block: 'center' });
}

async function inspectWitnesses(receiptHash) {
  const panel = document.querySelector(`[data-witness-panel="${receiptHash}"]`);
  if (!panel) return;
  panel.hidden = false;
  panel.textContent = 'Loading witnessed receipt artifacts...';
  try {
    const payload = await api.getReceiptWitnesses(receiptHash);
    panel.textContent = JSON.stringify({
      receipt_hash: payload.receipt_hash,
      witness_count: payload.witness_count,
      artifact_format: payload.artifact_format,
      witness_artifacts: payload.witness_artifacts,
      legacy_witnessed_receipts: payload.witness_artifacts.length ? undefined : payload.witnessed_receipts,
    }, null, 2);
  } catch (err) {
    panel.textContent = `Unable to load witnesses: ${err.message}`;
  }
}

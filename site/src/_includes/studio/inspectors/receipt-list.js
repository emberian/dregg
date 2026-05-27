/**
 * <dregg-receipt-list> — list of receipts.
 *
 * Optional `agent` attribute (numeric agent_index) is currently a no-op
 * because the wasm runtime does not expose per-agent filtering; we always
 * render the global chain. The attribute is reserved for when wasm grows a
 * `get_receipts_for_agent(handle, agent_idx)` getter.
 */

import { InspectorBase, dreggCodeLink, emptyState, shortHex } from './_base.js';

function receiptHash(r) {
  return r?.turn_hash || r?.receipt_hash || r?.hash || '';
}

function proofTier(r) {
  const pv = r?.proof_view;
  if (!pv) return 'scope-0';
  const bp = pv.bilateral_pi;
  return bp &&
    bp.outgoing_transfer_root &&
    bp.incoming_transfer_root &&
    bp.outgoing_grant_root &&
    bp.incoming_grant_root &&
    bp.outgoing_introduce_root &&
    bp.incoming_introduce_root
    ? 'golden'
    : 'silver';
}

function timestampLabel(ts) {
  if (ts == null || ts === '') return 'no timestamp';
  if (typeof ts === 'number') {
    const ms = ts > 10_000_000_000 ? ts : ts * 1000;
    const d = new Date(ms);
    return Number.isNaN(d.getTime()) ? String(ts) : d.toLocaleString();
  }
  const d = new Date(ts);
  return Number.isNaN(d.getTime()) ? String(ts) : d.toLocaleString();
}

class DreggReceiptList extends InspectorBase {
  static get observedAttributes() { return ['uri', 'mode', 'agent']; }
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const agentAttr = this.getAttribute('agent');
    const agentIdx = agentAttr == null ? null : Number(agentAttr);
    const sig = this._runtime.listReceipts(agentIdx);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const rs = sig.value || [];
      if (!rs.length) return emptyState(
        html,
        'No receipts yet',
        agentIdx != null
          ? html`Agent <code>#${agentIdx}</code> has no committed receipts in the current chain view.`
          : html`Execute a turn to populate the receipt chain.`,
      );
      const totalComputrons = rs.reduce((sum, r) => sum + Number(r.computrons_used || 0), 0);
      const totalActions = rs.reduce((sum, r) => sum + Number(r.action_count || 0), 0);
      const provenCount = rs.filter(r => r.proof_view).length;
      const head = rs[rs.length - 1];
      const headHash = receiptHash(head);
      return html`
        <div class="dregg-inspector dregg-inspector--cell-list">
          <header>
            <span class="dregg-inspector__kind">receipt chain</span>
            <span class="dregg-inspector__meta">${rs.length} receipt${rs.length === 1 ? '' : 's'}${agentIdx != null ? ` · requested agent #${agentIdx}` : ''}</span>
          </header>
          ${agentIdx != null ? html`
            <div class="dregg-inspector__notice">
              Runtime receipt lookup is currently global. Showing the full committed chain while preserving the requested agent filter.
            </div>` : null}
          <div class="dregg-inspector__summary">
            <div><span>Receipts</span><strong>${String(rs.length)}</strong></div>
            <div><span>Actions</span><strong>${String(totalActions)}</strong></div>
            <div><span>Computrons</span><strong>${String(totalComputrons)}</strong></div>
            <div><span>Proofs</span><strong>${String(provenCount)} / ${String(rs.length)}</strong></div>
            <div><span>Head</span><strong>${headHash ? dreggCodeLink(html, `dregg://receipt/${headHash}`, shortHex(headHash, 10), headHash) : 'none'}</strong></div>
            <div><span>Latest</span><strong title=${String(head?.timestamp || '')}>${timestampLabel(head?.timestamp)}</strong></div>
          </div>
          ${headHash ? html`
            <div class="dregg-inspector__actions">
              ${dreggCodeLink(html, `dregg://receipt/${headHash}`, 'open head receipt', headHash)}
              ${dreggCodeLink(html, `dregg://turn/${headHash}`, 'open matching turn', headHash)}
            </div>` : null}
          <div class="dregg-inspector__rows">
            ${rs.slice().reverse().map((r, idx) => {
              const hash = receiptHash(r);
              const actions = Number(r.action_count || 0);
              const computrons = Number(r.computrons_used || 0);
              return html`
              <div class="dregg-inspector__row">
                <span>#${String(rs.length - idx - 1)}</span>
                <strong>${hash ? dreggCodeLink(html, `dregg://receipt/${hash}`, shortHex(hash, 18), hash) : 'unidentified'}</strong>
                <code title=${String(r.timestamp || '')}>${String(actions)} action${actions === 1 ? '' : 's'} · ${String(computrons)} computrons · ${proofTier(r)}</code>
              </div>`;
            })}
          </div>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-receipt-list')) customElements.define('dregg-receipt-list', DreggReceiptList);

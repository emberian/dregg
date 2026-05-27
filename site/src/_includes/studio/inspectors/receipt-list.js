/**
 * <dregg-receipt-list> — list of receipts.
 *
 * Optional `agent` attribute (numeric agent_index) is currently a no-op
 * because the wasm runtime does not expose per-agent filtering; we always
 * render the global chain. The attribute is reserved for when wasm grows a
 * `get_receipts_for_agent(handle, agent_idx)` getter.
 */

import { InspectorBase, dreggCodeLink, emptyState, shortHex } from './_base.js';

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
      return html`
        <div class="dregg-inspector dregg-inspector--cell-list">
          <header>${rs.length} receipt${rs.length === 1 ? '' : 's'}${agentIdx != null ? ` (agent #${agentIdx})` : ''}</header>
          <div class="dregg-inspector__summary">
            <div><span>Receipts</span><strong>${String(rs.length)}</strong></div>
            <div><span>Actions</span><strong>${String(totalActions)}</strong></div>
            <div><span>Computrons</span><strong>${String(totalComputrons)}</strong></div>
            <div><span>Head</span><strong>${shortHex(rs[rs.length - 1]?.turn_hash, 10)}</strong></div>
          </div>
          <div class="dregg-inspector__rows">
            ${rs.slice().reverse().map((r, idx) => html`
              <div class="dregg-inspector__row">
                <span>${String(rs.length - idx - 1)}</span>
                <strong>${dreggCodeLink(html, `dregg://receipt/${r.turn_hash}`, shortHex(r.turn_hash, 18), r.turn_hash)}</strong>
                <code>${String(r.action_count ?? 0)} action(s) · ${String(r.computrons_used ?? 0)} computrons</code>
              </div>
            `)}
          </div>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-receipt-list')) customElements.define('dregg-receipt-list', DreggReceiptList);

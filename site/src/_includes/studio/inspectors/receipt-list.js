/**
 * <dregg-receipt-list> — list of receipts.
 *
 * Optional `agent` attribute (numeric agent_index) is currently a no-op
 * because the wasm runtime does not expose per-agent filtering; we always
 * render the global chain. The attribute is reserved for when wasm grows a
 * `get_receipts_for_agent(handle, agent_idx)` getter.
 */

import { InspectorBase, dreggCodeLink, emptyState } from './_base.js';

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
      return html`
        <div class="dregg-inspector dregg-inspector--cell-list">
          <header>${rs.length} receipt${rs.length === 1 ? '' : 's'}${agentIdx != null ? ` (agent #${agentIdx})` : ''}</header>
          <ul>
            ${rs.map(r => html`
              <li>
                ${dreggCodeLink(html, `dregg://receipt/${r.turn_hash}`, 'open')}
                <dregg-receipt uri=${`dregg://receipt/${r.turn_hash}`} mode="compact"></dregg-receipt>
              </li>
            `)}
          </ul>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-receipt-list')) customElements.define('dregg-receipt-list', DreggReceiptList);

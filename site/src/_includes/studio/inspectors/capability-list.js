/**
 * <dregg-capability-list agent="N"> — capabilities held by an agent.
 *
 * Reads `get_capability_tree(handle, agent_index)` from wasm.
 */

import { InspectorBase, dreggCodeLink, emptyState, shortHex } from './_base.js';

function capPerms(c) {
  if (Array.isArray(c.permissions)) return c.permissions.filter(Boolean).map(String);
  return String(c.permissions || '').split(/[,\s|]+/).map(s => s.trim()).filter(Boolean);
}

class DreggCapabilityList extends InspectorBase {
  static get observedAttributes() { return ['uri', 'mode', 'agent']; }
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const agentAttr = this.getAttribute('agent');
    if (agentAttr == null) {
      this.innerHTML = `<div class="dregg-inspector dregg-inspector--err">&lt;dregg-capability-list&gt; requires agent="N"</div>`;
      return;
    }
    const agentIdx = Number(agentAttr);
    const sig = this._runtime.listCapabilities(agentIdx);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const tree = sig.value;
      if (!tree) return emptyState(
        html,
        'No capability tree',
        html`Agent <code>#${agentIdx}</code> is not available in this runtime.`,
      );
      const caps = tree.capabilities || [];
      const withBreadstuff = caps.filter(c => c.has_breadstuff).length;
      const targetCount = new Set(caps.map(c => c.target || c.target_cell).filter(Boolean)).size;
      const permissionCount = new Set(caps.flatMap(capPerms)).size;
      if (!caps.length) return html`
        <div class="dregg-inspector dregg-inspector--cell-list">
          <header>0 capabilities (agent ${tree.agent_name || `#${agentIdx}`})</header>
          <div class="dregg-inspector dregg-inspector--empty">
            <div class="dregg-inspector__empty-title">No capabilities held</div>
            <div class="dregg-inspector__empty-body">
              ${tree.cell_id
                ? html`Holder cell ${dreggCodeLink(html, `dregg://cell/${tree.cell_id}`, shortHex(tree.cell_id, 16), tree.cell_id)} has no delegated capability slots.`
                : html`This agent has no delegated capability slots.`}
            </div>
          </div>
        </div>`;
      return html`
        <div class="dregg-inspector dregg-inspector--cell-list">
          <header>
            ${caps.length} capabilit${caps.length === 1 ? 'y' : 'ies'}
            · ${tree.agent_name || `agent #${agentIdx}`}
            · cell ${tree.cell_id ? dreggCodeLink(html, `dregg://cell/${tree.cell_id}`, shortHex(tree.cell_id), tree.cell_id) : html`<span class="dregg-inspector__meta">unavailable</span>`}
          </header>
          <div class="dregg-inspector__summary">
            <div><span>targets</span><strong>${String(targetCount)}</strong></div>
            <div><span>permissions</span><strong>${String(permissionCount)}</strong></div>
            <div><span>breadstuff</span><strong>${String(withBreadstuff)}</strong></div>
          </div>
          <ul>
            ${caps.map(c => html`
              <li>
                ${dreggCodeLink(html, `dregg://capability/${agentIdx}/${c.slot}`, `slot ${String(c.slot)}`)}
                <dregg-capability uri=${`dregg://capability/${agentIdx}/${c.slot}`} mode="compact"></dregg-capability>
              </li>
            `)}
          </ul>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-capability-list')) customElements.define('dregg-capability-list', DreggCapabilityList);

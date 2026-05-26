/**
 * <dregg-capability uri="dregg://capability/<agent_idx>/<slot_or_pos>">.
 *
 * Held capabilities in the sim runtime are addressed by (agent_index, slot).
 * The URI's `id` segment is the agent index, and the first `sub` path is the
 * slot or position. There is no global capability ID in the sim.
 *
 * Cap shape (from wasm/src/bindings.rs::get_capability_tree):
 *   { slot, target, permissions, has_breadstuff }
 * augmented in JS with: { agent_index, agent_name, cell_id }
 */

import { parseRef } from '../uri.js';
import { InspectorBase, dreggCodeLink, emptyState, renderParseError, shortHex } from './_base.js';

class DreggCapability extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'compact';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'capability')) return;

    const agentIdx = parsed.id;
    const slotOrIdx = parsed.sub[0];
    if (slotOrIdx == null) {
      this.innerHTML = `<div class="dregg-inspector dregg-inspector--err">capability URI missing slot: ${refAttr}</div>`;
      return;
    }

    const sig = this._runtime.getCapability(agentIdx, slotOrIdx);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const c = sig.value;
      if (!c) return emptyState(
        html,
        'Capability not found',
        html`Agent <code>#${agentIdx}</code> does not currently expose a capability at slot <code>${slotOrIdx}</code>.`,
      );
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code>slot ${String(c.slot)}</code>
            · target ${c.target
              ? dreggCodeLink(html, `dregg://cell/${c.target}`, shortHex(c.target), c.target)
              : html`<span class="dregg-inspector__meta">unavailable</span>`}
            · ${c.permissions}
          </span>`;
      }
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">capability</span>
            <code class="dregg-inspector__id">agent #${String(c.agent_index)} · slot ${String(c.slot)}</code>
            <span class="dregg-inspector__meta">${c.permissions || 'no permissions'}</span>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>agent</dt><dd>${c.agent_name || `#${String(c.agent_index)}`}</dd>
            <dt>holder cell</dt><dd>${c.cell_id ? dreggCodeLink(html, `dregg://cell/${c.cell_id}`, shortHex(c.cell_id, 24), c.cell_id) : html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>target cell</dt><dd>${c.target ? dreggCodeLink(html, `dregg://cell/${c.target}`, shortHex(c.target, 24), c.target) : html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>permissions</dt><dd><code>${c.permissions}</code></dd>
            <dt>breadstuff</dt><dd>${c.has_breadstuff ? 'attached' : 'none'}</dd>
          </dl>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-capability')) customElements.define('dregg-capability', DreggCapability);

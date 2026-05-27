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

function permissionParts(permissions) {
  if (Array.isArray(permissions)) return permissions.filter(Boolean).map(String);
  return String(permissions || '')
    .split(/[,\s|]+/)
    .map(s => s.trim())
    .filter(Boolean);
}

function permissionSummary(c) {
  const parts = permissionParts(c.permissions);
  if (!parts.length) return 'No permissions recorded';
  if (parts.includes('*')) return 'Full delegated access';
  return parts.join(', ');
}

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
      const parts = permissionParts(c.permissions);
      const target = c.target || c.target_cell || '';
      const holder = c.cell_id || c.holder_cell || '';
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code>slot ${String(c.slot)}</code>
            · target ${target
              ? dreggCodeLink(html, `dregg://cell/${target}`, shortHex(target), target)
              : html`<span class="dregg-inspector__meta">unavailable</span>`}
            · ${permissionSummary(c)}
          </span>`;
      }
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">capability</span>
            <code class="dregg-inspector__id">agent #${String(c.agent_index)} · slot ${String(c.slot)}</code>
            <span class="dregg-inspector__meta">${permissionSummary(c)}</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>permissions</span><strong>${parts.length || 0}</strong></div>
            <div><span>breadstuff</span><strong>${c.has_breadstuff ? 'attached' : 'none'}</strong></div>
            <div><span>target</span><strong title=${target}>${target ? shortHex(target, 12) : 'unavailable'}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            <dt>agent</dt><dd>${c.agent_name || `#${String(c.agent_index)}`}</dd>
            <dt>holder cell</dt><dd>${holder ? dreggCodeLink(html, `dregg://cell/${holder}`, shortHex(holder, 24), holder) : html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>target cell</dt><dd>${target ? dreggCodeLink(html, `dregg://cell/${target}`, shortHex(target, 24), target) : html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>permissions</dt><dd>${parts.length ? parts.map(p => html`<code>${p}</code> `) : html`<span class="dregg-inspector__meta">none recorded</span>`}</dd>
            <dt>breadstuff</dt><dd>${c.has_breadstuff ? 'attached' : 'none'}</dd>
            <dt>capability URI</dt><dd>${dreggCodeLink(html, `dregg://capability/${agentIdx}/${c.slot}`, `slot ${String(c.slot)}`)}</dd>
          </dl>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-capability')) customElements.define('dregg-capability', DreggCapability);

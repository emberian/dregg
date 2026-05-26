/**
 * <pyana-witnessed-predicate data-predicate="..." | uri=...>
 * Unified dispatcher per NEW-WORLD "Predicates everywhere".
 * Renders kind-specific: <pyana-dfa>, temporal, blinded-set, merkle-membership, custom-vk.
 * Used inside cell-program Witnessed variant and cap caveats.
 */
import { InspectorBase } from './_base.js';

class PyanaWitnessedPredicate extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const dataAttr = this.getAttribute('data-predicate');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let wp = null;
    if (dataAttr) { try { wp = JSON.parse(dataAttr); } catch {} }
    const root = document.createElement('div'); this.appendChild(root);
    const Component = () => {
      if (!wp) return html`<div class="pyana-inspector pyana-inspector--empty">no witnessed-predicate data</div>`;
      const kind = wp.predicate_kind || wp.kind || 'Custom';
      let sub = html`<span>${kind}</span>`;
      if (kind.toLowerCase().includes('dfa')) sub = html`<pyana-dfa data-dfa=${JSON.stringify(wp)} mode="compact"></pyana-dfa>`;
      return html`<div class="pyana-inspector pyana-inspector--cell pwp">Witnessed(${kind}) ${sub}</div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('pyana-witnessed-predicate')) customElements.define('pyana-witnessed-predicate', PyanaWitnessedPredicate);

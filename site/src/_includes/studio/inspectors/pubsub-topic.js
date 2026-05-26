/**
 * <pyana-pubsub-topic uri="pyana://cell/<id>">
 * Storage cell-program view for PubSubTopic (append-only log + Merkle subscribers).
 * Phase 4 (after DFA for filters). Reuses <pyana-dfa> for topic filters + cell-program for append constraints (Monotonic + WriteOnce on log root).
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError } from './_base.js';

class PyanaPubsubTopic extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let parsed = null; try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'cell')) return;
    const root = document.createElement('div'); this.appendChild(root);
    const Component = () => {
      const cell = parsed && this._runtime.getCell ? this._runtime.getCell(parsed.id).value : null;
      return html`
        <div class="pyana-inspector pyana-inspector--cell pps">
          <header><span class="pyana-inspector__kind">pubsub-topic</span></header>
          ${cell ? html`<pyana-cell uri=${`pyana://cell/${parsed.id}`} mode="compact"></pyana-cell>` : ''}
          <div style="font-size:0.75rem;">Append-only + Merkle root subscribers. DFA topic filters (Phase 4). See <pyana-dfa> + cell program for invariants.</div>
          ${cell && cell.program ? html`<pyana-cell-program data-program=${JSON.stringify(cell.program)} mode="compact"></pyana-cell-program>` : ''}
        </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('pyana-pubsub-topic')) customElements.define('pyana-pubsub-topic', PyanaPubsubTopic);

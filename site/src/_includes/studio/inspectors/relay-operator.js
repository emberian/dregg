/**
 * <pyana-relay-operator uri="pyana://cell/<id>">
 * Uses DFA caveats for dispatch (Phase 5, after DFA lane). Cell program + <pyana-dfa> for routing rules.
 * RateLimitBySum + SenderAuthorized + FieldLte for quota.
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError } from './_base.js';

class PyanaRelayOperator extends InspectorBase {
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
        <div class="pyana-inspector pyana-inspector--cell pro">
          <header><span class="pyana-inspector__kind">relay-operator</span> (DFA dispatch)</header>
          ${cell ? html`<pyana-cell uri=${`pyana://cell/${parsed.id}`} mode="compact"></pyana-cell><pyana-dfa mode="compact"></pyana-dfa>` : ''}
          <div style="font-size:0.7rem;">DFA caveat routing + quota cell-program. See STORAGE §3.5 + DFA-RATIONALIZATION.</div>
        </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('pyana-relay-operator')) customElements.define('pyana-relay-operator', PyanaRelayOperator);

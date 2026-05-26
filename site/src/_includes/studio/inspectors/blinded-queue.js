/**
 * <pyana-blinded-queue uri="pyana://cell/<id>">
 *
 * Storage-as-cell-program for BlindedQueue (privacy-voting canonical user, Phase 6 but Phase 1 predicate registry prerequisite).
 * Uses WitnessedPredicate::BlindedSet (or Custom vk) + conservation + rate limits.
 * Sovereign by default (per design).
 *
 * Renders the blinded spend commitments + the Witnessed predicate in the cell program.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaBlindedQueue extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'cell')) return;

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const cell = parsed && this._runtime.getCell ? this._runtime.getCell(parsed.id).value : null;
      if (!cell) return html`<div class="pyana-inspector pyana-inspector--empty">blinded-queue cell not found</div>`;

      const prog = cell.program;
      const hasWitnessed = prog && prog.kind === 'Predicate' && (prog.constraints || []).some(c => c.kind === 'Witnessed' || /BlindedSet/.test(JSON.stringify(c)));

      return html`
        <div class="pyana-inspector pyana-inspector--cell pbq">
          <header><span class="pyana-inspector__kind">blinded-queue</span> (sovereign)</header>
          <pyana-cell uri=${`pyana://cell/${parsed.id}`} mode="compact"></pyana-cell>
          ${hasWitnessed ? html`<div style="color:#c9a84c;font-size:0.8rem;">Contains Witnessed(BlindedSet) — Phase 1 predicate registry in use</div>` : ''}
          <details>
            <summary>Cell program (Blinded spend AIR + caveats)</summary>
            ${prog ? html`<pyana-cell-program data-program=${JSON.stringify(prog)}></pyana-cell-program>` : ''}
          </details>
          <div style="font-size:0.7rem;">Per STORAGE-AS-CELL-PROGRAMS §3.4: one new predicate kind (BlindedSet) registered against vk_hash. Private claims/votes.</div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('pyana-blinded-queue')) {
  customElements.define('pyana-blinded-queue', PyanaBlindedQueue);
}

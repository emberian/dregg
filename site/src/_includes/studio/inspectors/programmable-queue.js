/**
 * <pyana-programmable-queue uri="pyana://cell/<id>">
 *
 * The Phase 2 proof-of-pattern storage cell-program inspector (STORAGE-AS-CELL-PROGRAMS §3.2 / migration Phase 2).
 * Simpler case: slot-caveat vocabulary directly (no new WitnessedPredicate needed in base).
 * Uses MonotonicSequence, SenderAuthorized, BoundedBy / FieldLte, RateLimit etc.
 *
 * Reuses <pyana-cell-program> to surface the exact constraints that replaced the old
 * storage::programmable::QueueConstraint evaluator.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaProgrammableQueue extends InspectorBase {
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
      if (!cell) return html`<div class="pyana-inspector pyana-inspector--empty">programmable-queue cell not found</div>`;

      const fields = cell.fields || [];
      // Typical programmable queue slots: capacity, length (now root), owner, program_vk etc per audit.
      const len = fields[1] ? shortHex(fields[1], 10) : '— (use root post-migration)';

      return html`
        <div class="pyana-inspector pyana-inspector--cell ppq">
          <header>
            <span class="pyana-inspector__kind">programmable-queue</span>
            <pyana-cell uri=${`pyana://cell/${parsed.id}`} mode="compact"></pyana-cell>
          </header>
          <div>length/root: <code>${len}</code></div>
          <details>
            <summary>Program (the migration proof — constraints now live here)</summary>
            ${cell.program ? html`<pyana-cell-program data-program=${JSON.stringify(cell.program)}></pyana-cell-program>` : html`<em>no program</em>`}
          </details>
          <div style="font-size:0.7rem;color:var(--fg-dim);">Phase 2: this cell's StateConstraints *are* the queue. Old storage::programmable evaluator deleted. See queue.rs + programmable.rs.</div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('pyana-programmable-queue')) {
  customElements.define('pyana-programmable-queue', PyanaProgrammableQueue);
}

/**
 * <dregg-blinded-queue uri="dregg://cell/<id>">
 *
 * Storage-as-cell-program for BlindedQueue (privacy-voting canonical user, Phase 6 but Phase 1 predicate registry prerequisite).
 * Uses WitnessedPredicate::BlindedSet (or Custom vk) + conservation + rate limits.
 * Sovereign by default (per design).
 *
 * Renders the blinded spend commitments + the Witnessed predicate in the cell program.
 */

import { parseRef } from '../uri.js';
import {
  InspectorBase,
  caveatSummaries,
  cellIdFrom,
  dreggCodeLink,
  emptyState,
  fieldHex,
  hasConstraint,
  programBadge,
  programConstraints,
  renderParseError,
  shortHex,
} from './_base.js';

class DreggBlindedQueue extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'cell')) return;

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const cell = parsed && this._runtime.getCell ? this._runtime.getCell(parsed.id).value : null;
      if (!cell) return emptyState(html, 'Blinded queue unavailable', 'This runtime does not have a cell for the supplied blinded-queue URI.');

      const prog = cell.program;
      const fields = cell.fields || [];
      const constraints = programConstraints(prog);
      const hasWitnessed = hasConstraint(constraints, c => c.kind === 'Witnessed' || /BlindedSet|Custom/.test(JSON.stringify(c)));
      const hasAppendOnly = hasConstraint(constraints, c => c.kind === 'Monotonic' || c.kind === 'StrictMonotonic' || c.kind === 'MonotonicSequence');
      const caveats = caveatSummaries(constraints, ['Witnessed', 'BlindedSet', 'Custom', 'Monotonic']);
      const id = cellIdFrom(cell, parsed);

      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-storage-pattern pbq">
          <header class="dregg-storage-pattern__head">
            <div>
              <div class="dregg-storage-pattern__title">
                <span class="dregg-inspector__kind">blinded-queue</span>
                ${id ? dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id) : null}
              </div>
              <div class="dregg-storage-pattern__subtitle">Private consumption view over commitment and nullifier roots; spend validity comes from the attached witnessed predicate.</div>
            </div>
            <div class="dregg-storage-pattern__badges">
              <span class=${`dregg-storage-pattern__badge ${hasWitnessed ? 'dregg-storage-pattern__badge--ok' : 'dregg-storage-pattern__badge--warn'}`}>${hasWitnessed ? 'witnessed spend' : 'spend predicate unavailable'}</span>
              <span class=${`dregg-storage-pattern__badge ${prog && prog.kind !== 'None' ? 'dregg-storage-pattern__badge--ok' : 'dregg-storage-pattern__badge--warn'}`}>${programBadge(prog, constraints)}</span>
            </div>
          </header>

          <div class="dregg-storage-pattern__summary">
            <div><span>commitment root</span><strong><code title=${fields[0] || ''}>${fieldHex(fields, 0, 14)}</code></strong></div>
            <div><span>nullifier root</span><strong><code title=${fields[1] || ''}>${fieldHex(fields, 1, 14)}</code></strong></div>
            <div><span>spend auth</span><strong>${hasWitnessed ? 'registered' : 'unavailable'}</strong></div>
            <div><span>append-only</span><strong>${hasAppendOnly ? 'declared' : 'unavailable'}</strong></div>
          </div>

          <section class="dregg-storage-pattern__section">
            <h4>Program interpretation</h4>
            ${caveats.length ? html`<ul class="dregg-storage-pattern__caveats">${caveats.map(c => html`<li><code>${c.split(' ')[0]}</code><span>${c.replace(/^[^ ]+ ?/, '')}</span></li>`)}</ul>`
              : html`<div class="dregg-storage-pattern__unavailable">No blinded-spend caveat was found on this runtime cell. Roots are shown, but spend verification cannot be interpreted here.</div>`}
          </section>

          <details>
            <summary>Cell program (spend AIR + caveats)</summary>
            ${prog ? html`<dregg-cell-program data-program=${JSON.stringify(prog)}></dregg-cell-program>` : html`<div class="dregg-storage-pattern__unavailable">No program attached to this cell.</div>`}
          </details>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-blinded-queue')) {
  customElements.define('dregg-blinded-queue', DreggBlindedQueue);
}

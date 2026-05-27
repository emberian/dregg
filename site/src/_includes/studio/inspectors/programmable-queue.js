/**
 * <dregg-programmable-queue uri="dregg://cell/<id>">
 *
 * The Phase 2 proof-of-pattern storage cell-program inspector (STORAGE-AS-CELL-PROGRAMS §3.2 / migration Phase 2).
 * Simpler case: slot-caveat vocabulary directly (no new WitnessedPredicate needed in base).
 * Uses MonotonicSequence, SenderAuthorized, BoundedBy / FieldLte, RateLimit etc.
 *
 * Reuses <dregg-cell-program> to surface the exact constraints that replaced the old
 * storage::programmable::QueueConstraint evaluator.
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

class DreggProgrammableQueue extends InspectorBase {
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
      if (!cell) return emptyState(html, 'Programmable queue unavailable', 'This runtime does not have a cell for the supplied programmable-queue URI.');

      const fields = cell.fields || [];
      const prog = cell.program;
      const constraints = programConstraints(prog);
      const caveats = caveatSummaries(constraints, ['SenderAuthorized', 'RateLimit', 'RateLimitBySum', 'MonotonicSequence', 'FieldGte', 'FieldLte', 'TemporalGate', 'PreimageGate', 'Witnessed']);
      const id = cellIdFrom(cell, parsed);
      const root = fieldHex(fields, 1, 14);
      const hasAcl = hasConstraint(constraints, c => c.kind === 'SenderAuthorized');
      const hasSequence = hasConstraint(constraints, c => c.kind === 'MonotonicSequence' || c.kind === 'Monotonic' || c.kind === 'StrictMonotonic');
      const hasThrottle = hasConstraint(constraints, c => c.kind === 'RateLimit' || c.kind === 'RateLimitBySum');

      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-storage-pattern ppq">
          <header class="dregg-storage-pattern__head">
            <div>
              <div class="dregg-storage-pattern__title">
                <span class="dregg-inspector__kind">programmable-queue</span>
                ${id ? dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id) : null}
              </div>
              <div class="dregg-storage-pattern__subtitle">Queue policy is read from the cell program; this inspector does not run a JS queue evaluator.</div>
            </div>
            <div class="dregg-storage-pattern__badges">
              <span class=${`dregg-storage-pattern__badge ${prog && prog.kind !== 'None' ? 'dregg-storage-pattern__badge--ok' : 'dregg-storage-pattern__badge--warn'}`}>${programBadge(prog, constraints)}</span>
              ${hasAcl ? html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">authorized senders</span>` : html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--warn">ACL unavailable</span>`}
              ${hasThrottle ? html`<span class="dregg-storage-pattern__badge">rate limited</span>` : null}
            </div>
          </header>

          <div class="dregg-storage-pattern__summary">
            <div><span>queue root</span><strong><code title=${fields[1] || ''}>${root}</code></strong></div>
            <div><span>capacity slot</span><strong><code title=${fields[0] || ''}>${fieldHex(fields, 0, 12)}</code></strong></div>
            <div><span>program</span><strong>${prog?.kind || 'None'}</strong></div>
            <div><span>sequencing</span><strong>${hasSequence ? 'declared' : 'unavailable'}</strong></div>
          </div>

          <section class="dregg-storage-pattern__section">
            <h4>Interpreted caveats</h4>
            ${caveats.length ? html`<ul class="dregg-storage-pattern__caveats">${caveats.map(c => html`<li><code>${c.split(' ')[0]}</code><span>${c.replace(/^[^ ]+ ?/, '')}</span></li>`)}</ul>`
              : html`<div class="dregg-storage-pattern__unavailable">No queue-shaped caveats are available on this runtime cell.</div>`}
          </section>

          <details>
            <summary>Full cell program</summary>
            ${prog ? html`<dregg-cell-program data-program=${JSON.stringify(prog)}></dregg-cell-program>` : html`<div class="dregg-storage-pattern__unavailable">No program attached to this cell.</div>`}
          </details>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-programmable-queue')) {
  customElements.define('dregg-programmable-queue', DreggProgrammableQueue);
}

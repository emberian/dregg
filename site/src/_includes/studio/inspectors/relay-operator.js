/**
 * <dregg-relay-operator uri="dregg://cell/<id>">
 * Uses DFA caveats for dispatch (Phase 5, after DFA lane). Cell program + <dregg-dfa> for routing rules.
 * RateLimitBySum + SenderAuthorized + FieldLte for quota.
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

class DreggRelayOperator extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    let parsed = null; try { parsed = parseRef(refAttr); } catch {}
    if (refAttr && renderParseError(this, refAttr, parsed, 'cell')) return;
    const root = document.createElement('div'); this.appendChild(root);
    const Component = () => {
      const cell = parsed && this._runtime.getCell ? this._runtime.getCell(parsed.id).value : null;
      if (!cell) return emptyState(html, 'Relay operator unavailable', 'This runtime does not have a cell for the supplied relay-operator URI.');
      const fields = cell.fields || [];
      const prog = cell.program;
      const constraints = programConstraints(prog);
      const id = cellIdFrom(cell, parsed);
      const hasDfa = hasConstraint(constraints, c => c.kind === 'Witnessed' && /Dfa|DFA/i.test(String(c.predicate_kind || JSON.stringify(c))));
      const hasQuota = hasConstraint(constraints, c => c.kind === 'RateLimitBySum' || c.kind === 'RateLimit');
      const hasDisputes = hasConstraint(constraints, c => c.kind === 'Monotonic' || c.kind === 'StrictMonotonic' || c.kind === 'MonotonicSequence');
      const caveats = caveatSummaries(constraints, ['RateLimitBySum', 'RateLimit', 'BoundedBy', 'Monotonic', 'Witnessed', 'Dfa', 'FieldLte', 'SenderAuthorized']);
      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-storage-pattern pro">
          <header class="dregg-storage-pattern__head">
            <div>
              <div class="dregg-storage-pattern__title">
                <span class="dregg-inspector__kind">relay-operator</span>
                ${id ? dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id) : null}
              </div>
              <div class="dregg-storage-pattern__subtitle">Store-and-forward operator cell: quota, dispatch classification, bonded slash limits, and dispute counters are read from runtime state.</div>
            </div>
            <div class="dregg-storage-pattern__badges">
              <span class=${`dregg-storage-pattern__badge ${prog && prog.kind !== 'None' ? 'dregg-storage-pattern__badge--ok' : 'dregg-storage-pattern__badge--warn'}`}>${programBadge(prog, constraints)}</span>
              ${hasQuota ? html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">quota caveat</span>` : html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--warn">quota unavailable</span>`}
              ${hasDfa ? html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">DFA dispatch</span>` : null}
            </div>
          </header>

          <div class="dregg-storage-pattern__summary">
            <div><span>bond slot</span><strong><code title=${fields[0] || ''}>${fieldHex(fields, 0, 14)}</code></strong></div>
            <div><span>bytes epoch</span><strong><code title=${fields[1] || ''}>${fieldHex(fields, 1, 14)}</code></strong></div>
            <div><span>route root</span><strong><code title=${fields[2] || ''}>${fieldHex(fields, 2, 14)}</code></strong></div>
            <div><span>disputes</span><strong>${hasDisputes ? 'monotonic' : 'unavailable'}</strong></div>
          </div>

          <section class="dregg-storage-pattern__section">
            <h4>Interpreted caveats</h4>
            ${caveats.length ? html`<ul class="dregg-storage-pattern__caveats">${caveats.map(c => html`<li><code>${c.split(' ')[0]}</code><span>${c.replace(/^[^ ]+ ?/, '')}</span></li>`)}</ul>`
              : html`<div class="dregg-storage-pattern__unavailable">No relay-shaped caveats are available on this runtime cell.</div>`}
          </section>

          ${hasDfa ? html`<dregg-dfa mode="compact"></dregg-dfa>` : html`<div class="dregg-inspector__notice">DFA dispatch details are unavailable because no witnessed DFA caveat was found in the cell program.</div>`}

          <details>
            <summary>Full cell program</summary>
            ${prog ? html`<dregg-cell-program data-program=${JSON.stringify(prog)} mode="default"></dregg-cell-program>` : html`<div class="dregg-storage-pattern__unavailable">No program attached to this cell.</div>`}
          </details>
        </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-relay-operator')) customElements.define('dregg-relay-operator', DreggRelayOperator);

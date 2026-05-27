/**
 * <dregg-pubsub-topic uri="dregg://cell/<id>">
 * Storage cell-program view for PubSubTopic (append-only log + Merkle subscribers).
 * Phase 4 (after DFA for filters). Reuses <dregg-dfa> for topic filters + cell-program for append constraints (Monotonic + WriteOnce on log root).
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

class DreggPubsubTopic extends InspectorBase {
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
      if (!cell) return emptyState(html, 'Pub/sub topic unavailable', 'This runtime does not have a cell for the supplied pubsub-topic URI.');
      const fields = cell.fields || [];
      const prog = cell.program;
      const constraints = programConstraints(prog);
      const id = cellIdFrom(cell, parsed);
      const hasPublishers = hasConstraint(constraints, c => c.kind === 'SenderAuthorized');
      const hasDfa = hasConstraint(constraints, c => c.kind === 'Witnessed' && /Dfa|DFA/i.test(String(c.predicate_kind || JSON.stringify(c))));
      const hasRate = hasConstraint(constraints, c => c.kind === 'RateLimitBySum' || c.kind === 'RateLimit');
      const caveats = caveatSummaries(constraints, ['SenderAuthorized', 'Witnessed', 'Dfa', 'RateLimitBySum', 'WriteOnce', 'Monotonic']);
      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-storage-pattern pps">
          <header class="dregg-storage-pattern__head">
            <div>
              <div class="dregg-storage-pattern__title">
                <span class="dregg-inspector__kind">pubsub-topic</span>
                ${id ? dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id) : null}
              </div>
              <div class="dregg-storage-pattern__subtitle">Append-only event root with subscriber cursor and dedup roots; filters are interpreted from witnessed DFA caveats when present.</div>
            </div>
            <div class="dregg-storage-pattern__badges">
              <span class=${`dregg-storage-pattern__badge ${prog && prog.kind !== 'None' ? 'dregg-storage-pattern__badge--ok' : 'dregg-storage-pattern__badge--warn'}`}>${programBadge(prog, constraints)}</span>
              ${hasPublishers ? html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">publisher ACL</span>` : html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--warn">publisher ACL unavailable</span>`}
              ${hasDfa ? html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">DFA filters</span>` : null}
            </div>
          </header>

          <div class="dregg-storage-pattern__summary">
            <div><span>event root</span><strong><code title=${fields[0] || ''}>${fieldHex(fields, 0, 14)}</code></strong></div>
            <div><span>cursor root</span><strong><code title=${fields[1] || ''}>${fieldHex(fields, 1, 14)}</code></strong></div>
            <div><span>dedup root</span><strong><code title=${fields[7] || ''}>${fieldHex(fields, 7, 14)}</code></strong></div>
            <div><span>rate limit</span><strong>${hasRate ? 'declared' : 'unavailable'}</strong></div>
          </div>

          <section class="dregg-storage-pattern__section">
            <h4>Interpreted caveats</h4>
            ${caveats.length ? html`<ul class="dregg-storage-pattern__caveats">${caveats.map(c => html`<li><code>${c.split(' ')[0]}</code><span>${c.replace(/^[^ ]+ ?/, '')}</span></li>`)}</ul>`
              : html`<div class="dregg-storage-pattern__unavailable">No topic-shaped caveats are available. Slot roots are shown from the runtime cell.</div>`}
          </section>

          <details>
            <summary>Full cell program</summary>
            ${prog ? html`<dregg-cell-program data-program=${JSON.stringify(prog)} mode="default"></dregg-cell-program>` : html`<div class="dregg-storage-pattern__unavailable">No program attached to this cell.</div>`}
          </details>
        </div>`;
    };
    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-pubsub-topic')) customElements.define('dregg-pubsub-topic', DreggPubsubTopic);

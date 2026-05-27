/**
 * <dregg-cap-inbox uri="dregg://cell/<id>"> or data-inbox="..."
 *
 * Storage-as-cell-program inspector for CapInbox pattern (STORAGE-AS-CELL-PROGRAMS.md §3.1).
 * Renders a cell whose program uses WriteOnce + MonotonicSequence (head/tail) + SenderAuthorized
 * + FieldLte (capacity) + conservation as a verifiable inbox.
 *
 * Timed with Phase 1 (WitnessedPredicate) + Phase 3 migration.
 * Reuses heavily: <dregg-cell>, <dregg-cell-program>, <dregg-state-constraint> (via program tab).
 *
 * Slots (per design): 0=head_seq, 1=tail_seq, 2=capacity, 3=min_deposit, 4=owner_pk_hash,
 * 5=sender_set_root, 6=total_deposits, 7=message_root.
 *
 * Shows send/dequeue as Effect compositions under the cell program invariants.
 * No JS reimpl — reads cell.fields + program.constraints.
 */

import { parseRef } from '../uri.js';
import {
  InspectorBase,
  caveatSummaries,
  cellIdFrom,
  dreggCodeLink,
  emptyState,
  fieldU64,
  hasConstraint,
  programBadge,
  programConstraints,
  renderParseError,
  shortHex,
} from './_base.js';

class DreggCapInbox extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';
    const dataAttr = this.getAttribute('data-inbox');

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    let inboxData = null;
    if (dataAttr) {
      try { inboxData = JSON.parse(dataAttr); } catch {}
    } else if (refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'cell')) return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      let cell = null;
      if (parsed && this._runtime.getCell) {
        cell = this._runtime.getCell(parsed.id).value;
      } else if (inboxData) {
        cell = inboxData;
      }

      if (!cell) {
        return emptyState(html, 'Cap inbox unavailable', 'Supply a URI for a runtime cell or data-inbox JSON with fields/program data.');
      }

      const fields = cell.fields || [];
      const head = fieldU64(fields, 0);
      const tail = fieldU64(fields, 1);
      const cap = fieldU64(fields, 2);
      const minDep = fieldU64(fields, 3);
      const owner = fields[4] ? shortHex(fields[4], 8) : '—';
      const senderRoot = fields[5] ? shortHex(fields[5], 8) : '—';
      const totalDep = fieldU64(fields, 6);
      const msgRoot = fields[7] ? shortHex(fields[7], 8) : '—';
      const prog = cell.program;
      const constraints = programConstraints(prog);
      const caveats = caveatSummaries(constraints, ['MonotonicSequence', 'SenderAuthorized', 'FieldLte', 'FieldGte', 'WriteOnce', 'Immutable']);
      const id = cellIdFrom(cell, parsed);
      const inFlight = head != null && tail != null ? Math.max(0, head - tail) : null;
      const hasSenderAuth = hasConstraint(constraints, c => c.kind === 'SenderAuthorized');
      const hasSequence = hasConstraint(constraints, c => c.kind === 'MonotonicSequence' || c.kind === 'Monotonic');
      const capText = cap == null ? 'unavailable' : String(cap);

      if (mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">inbox H=${head ?? '—'} T=${tail ?? '—'} cap=${capText}</span>`;
      }

      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-storage-pattern pci">
          <header class="dregg-storage-pattern__head">
            <div>
              <div class="dregg-storage-pattern__title">
                <span class="dregg-inspector__kind">cap-inbox</span>
                ${id ? dreggCodeLink(html, `dregg://cell/${id}`, shortHex(id, 18), id) : null}
              </div>
              <div class="dregg-storage-pattern__subtitle">Capability delivery queue backed by live slots: head/tail sequencing, deposits, sender root, and message root.</div>
            </div>
            <div class="dregg-storage-pattern__badges">
              <span class=${`dregg-storage-pattern__badge ${prog && prog.kind !== 'None' ? 'dregg-storage-pattern__badge--ok' : 'dregg-storage-pattern__badge--warn'}`}>${programBadge(prog, constraints)}</span>
              ${hasSequence ? html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">sequenced</span>` : html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--warn">sequence caveat unavailable</span>`}
              ${hasSenderAuth ? html`<span class="dregg-storage-pattern__badge dregg-storage-pattern__badge--ok">sender gated</span>` : null}
            </div>
          </header>

          <div class="dregg-storage-pattern__summary">
            <div><span>in-flight</span><strong>${inFlight == null ? 'unavailable' : `${inFlight}${cap == null ? '' : ` / ${cap}`}`}</strong></div>
            <div><span>head / tail</span><strong>${head ?? '—'} / ${tail ?? '—'}</strong></div>
            <div><span>min deposit</span><strong>${minDep ?? 'unavailable'}</strong></div>
            <div><span>deposits</span><strong>${totalDep ?? 'unavailable'}</strong></div>
          </div>

          <dl class="pci__kv">
            <dt>head_seq (next send)</dt><dd>${head ?? html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>tail_seq (next dequeue)</dt><dd>${tail ?? html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>capacity</dt><dd>${capText}${cap != null ? ' (in-flight <= cap)' : ''}</dd>
            <dt>min_deposit</dt><dd>${minDep ?? html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>owner_pk_hash</dt><dd><code>${owner}</code></dd>
            <dt>sender_set_root</dt><dd><code>${senderRoot}</code> (SenderAuthorized)</dd>
            <dt>total_deposits</dt><dd>${totalDep ?? html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
            <dt>message_root</dt><dd><code>${msgRoot}</code></dd>
          </dl>

          <section class="dregg-storage-pattern__section">
            <h4>Interpreted caveats</h4>
            ${caveats.length ? html`<ul class="dregg-storage-pattern__caveats">${caveats.map(c => html`<li><code>${c.split(' ')[0]}</code><span>${c.replace(/^[^ ]+ ?/, '')}</span></li>`)}</ul>`
              : html`<div class="dregg-storage-pattern__unavailable">The cell fields are visible, but no inbox-shaped caveats are available in the program.</div>`}
          </section>

          <details open>
            <summary>Cell program (enforces inbox invariants)</summary>
            ${prog ? html`<dregg-cell-program data-program=${JSON.stringify(prog)} mode="default"></dregg-cell-program>`
              : html`<div class="dregg-storage-pattern__unavailable">No program attached; post-migration inbox cells declare sequencing, sender authorization, and immutable/root constraints here.</div>`}
          </details>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-cap-inbox')) {
  customElements.define('dregg-cap-inbox', DreggCapInbox);
}

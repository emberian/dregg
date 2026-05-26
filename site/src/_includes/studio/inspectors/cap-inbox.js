/**
 * <pyana-cap-inbox uri="pyana://cell/<id>"> or data-inbox="..."
 *
 * Storage-as-cell-program inspector for CapInbox pattern (STORAGE-AS-CELL-PROGRAMS.md §3.1).
 * Renders a cell whose program uses WriteOnce + MonotonicSequence (head/tail) + SenderAuthorized
 * + FieldLte (capacity) + conservation as a verifiable inbox.
 *
 * Timed with Phase 1 (WitnessedPredicate) + Phase 3 migration.
 * Reuses heavily: <pyana-cell>, <pyana-cell-program>, <pyana-state-constraint> (via program tab).
 *
 * Slots (per design): 0=head_seq, 1=tail_seq, 2=capacity, 3=min_deposit, 4=owner_pk_hash,
 * 5=sender_set_root, 6=total_deposits, 7=message_root.
 *
 * Shows send/dequeue as Effect compositions under the cell program invariants.
 * No JS reimpl — reads cell.fields + program.constraints.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaCapInbox extends InspectorBase {
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
        return html`<div class="pyana-inspector pyana-inspector--empty">cap-inbox cell not found (supply uri to real cell or data-inbox)</div>`;
      }

      const fields = cell.fields || [];
      const head = fields[0] ? parseInt(fields[0], 16) || 0 : 0;
      const tail = fields[1] ? parseInt(fields[1], 16) || 0 : 0;
      const cap = fields[2] ? parseInt(fields[2], 16) || 0 : 0;
      const minDep = fields[3] ? parseInt(fields[3], 16) || 0 : 0;
      const owner = fields[4] ? shortHex(fields[4], 8) : '—';
      const senderRoot = fields[5] ? shortHex(fields[5], 8) : '—';
      const totalDep = fields[6] ? parseInt(fields[6], 16) || 0 : 0;
      const msgRoot = fields[7] ? shortHex(fields[7], 8) : '—';

      const prog = cell.program;

      if (mode === 'compact') {
        return html`<span class="pyana-inspector pyana-inspector--compact">inbox H=${head} T=${tail} cap=${cap}</span>`;
      }

      return html`
        <div class="pyana-inspector pyana-inspector--cell pci">
          <header>
            <span class="pyana-inspector__kind">cap-inbox</span>
            <pyana-cell uri=${`pyana://cell/${cell.cell_id || parsed?.id}`} mode="compact"></pyana-cell>
          </header>

          <dl class="pci__kv">
            <dt>head_seq (next send)</dt><dd>${head}</dd>
            <dt>tail_seq (next dequeue)</dt><dd>${tail}</dd>
            <dt>capacity</dt><dd>${cap} (in-flight ≤ cap)</dd>
            <dt>min_deposit</dt><dd>${minDep}</dd>
            <dt>owner_pk_hash</dt><dd><code>${owner}</code></dd>
            <dt>sender_set_root</dt><dd><code>${senderRoot}</code> (SenderAuthorized)</dd>
            <dt>total_deposits</dt><dd>${totalDep}</dd>
            <dt>message_root</dt><dd><code>${msgRoot}</code></dd>
          </dl>

          <details open>
            <summary style="cursor:pointer;font-size:0.8rem;color:var(--fg-dim);">Cell program (enforces inbox invariants)</summary>
            ${prog ? html`<pyana-cell-program data-program=${JSON.stringify(prog)} mode="default"></pyana-cell-program>`
              : html`<div style="font-size:0.8rem;">no program (any change allowed — post-migration this cell declares WriteOnce/MonotonicSequence/SenderAuthorized etc)</div>`}
          </details>

          <div style="font-size:0.75rem;margin-top:6px;color:var(--fg-dim);">
            Operations are Effect::SetField(0/1/6/7) + Transfer(deposit) + EmitEvent("inbox.sent") under the cell program.
            This replaces storage::CapInbox + app-framework HTTP shim (Phase 3).
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('pyana-cap-inbox')) {
  customElements.define('pyana-cap-inbox', PyanaCapInbox);
}

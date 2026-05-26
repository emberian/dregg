/**
 * <pyana-note uri="pyana://note/<commitment-hex>"> — UTXO-style note (commitment + nullifier lifecycle).
 *
 * Replaces playground/sections/notes.js per Studio migration (Tier 2).
 *
 * URI form: pyana://note/<64-hex commitment>
 * data= form: JSON { commitment, value, asset_type, spent? }
 *
 * Modes: compact | default
 *
 * Uses canonical wasm: create_note, spend_note, get_notes (stubbed for now).
 * No JS crypto reimplementation. Visible placeholders for gaps (get_notes tracking).
 * Composes <pyana-cell> for owner cell deeplinks when agent known (future).
 *
 * Trust tier: n/a (notes are pre-proof commitments; conservation proved at spend time via turn).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaNote extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;
    const handle = this._runtime?._handle;
    const caps = this._runtime?.caps || { mutate: true };

    let parsed = null;
    let inlineData = null;

    if (dataAttr) {
      try { inlineData = JSON.parse(dataAttr); } catch {}
    }
    if (!inlineData && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'note')) return;
    }

    const noteSignal = (parsed && this._runtime?.getNotes)
      ? this._runtime.getNotes(0) // placeholder; real would derive agent from note or param
      : null;

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      let note = inlineData;
      if (!note && parsed && noteSignal) {
        const list = noteSignal.value || [];
        note = list.find(n => n.commitment === parsed.id) || { commitment: parsed.id, value: 0, asset_type: 0, spent: false };
      }
      if (!note) {
        // Demo / empty state with create affordance
        if (mode === 'compact') {
          return html`<span class="pyana-inspector pyana-inspector--compact">note (no data)</span>`;
        }
        return html`
          <div class="pyana-inspector pyana-inspector--note">
            <header>
              <span class="pyana-inspector__kind">note</span>
              <span style="color:var(--fg-dim);font-size:0.8rem;">(demo — use controls or data=)</span>
            </header>
            ${caps.mutate && wasm ? html`
              <div style="margin:8px 0;display:flex;gap:8px;flex-wrap:wrap;">
                <button data-act="create" style="font-size:0.75rem;padding:2px 6px;">Create Note (demo)</button>
                <button data-act="spend" style="font-size:0.75rem;padding:2px 6px;">Spend Last (demo)</button>
              </div>
              <div class="pyana-inspector__note-demo" style="font-size:0.75rem;color:var(--fg-dim);">
                Notes are commitments. Spend reveals nullifier (prevents double-spend). Full list tracking pending wasm get_notes impl.
              </div>
            ` : html`<div style="font-size:0.75rem;color:var(--fg-dim);">read-only runtime — no create/spend</div>`}
          </div>`;
      }

      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <code title=${note.commitment}>${shortHex(note.commitment)}</code>
            · ${String(note.value)} (asset ${String(note.asset_type)})
            ${note.spent ? '· spent' : ''}
          </span>`;
      }

      const actions = caps.mutate && wasm ? html`
        <div style="margin-top:8px;display:flex;gap:6px;flex-wrap:wrap;">
          <button data-act="spend" style="font-size:0.75rem;padding:3px 8px;">Spend (reveal nullifier)</button>
          <button data-act="create" style="font-size:0.75rem;padding:3px 8px;">Create another</button>
        </div>
        <div style="font-size:0.7rem;color:var(--fg-dim);margin-top:4px;">
          Note: create/spend here are demo calls; real flows use turns + <pyana-turn>.
        </div>
      ` : null;

      return html`
        <div class="pyana-inspector pyana-inspector--note">
          <header>
            <span class="pyana-inspector__kind">note</span>
            <code class="pyana-inspector__id" title=${note.commitment}>${shortHex(note.commitment, 24)}</code>
          </header>
          <dl class="pyana-inspector__kv">
            <dt>commitment</dt><dd><code title=${note.commitment}>${note.commitment}</code></dd>
            <dt>value</dt><dd>${String(note.value)}</dd>
            <dt>asset type</dt><dd>${String(note.asset_type)}</dd>
            <dt>status</dt><dd>${note.spent ? html`<span style="color:#b91c1c;">SPENT (nullifier published)</span>` : html`<span style="color:#166534;">unspent</span>`}</dd>
          </dl>
          ${actions}
          <details style="margin-top:6px;font-size:0.75rem;">
            <summary style="cursor:pointer;color:var(--fg-dim);">Lifecycle note (Houyhnhnm meta)</summary>
            <div style="color:var(--fg-dim);">Inspector reads receipts for spend events. Create is via Effect in turn; nullifier in NullifierSet.</div>
          </details>
        </div>`;
    };

    this._dispose = effect(() => {
      render(h(Component, {}), root);
    });

    // Wire demo buttons (delegated; survives re-render via root listener)
    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm || !handle) return;
      const act = btn.dataset.act;
      if (act === 'create') {
        try {
          const res = wasm.create_note(handle, 0, 100, 0); // agent 0, value 100, asset 0
          console.log('[pyana-note] created demo note', res);
          // trigger re-render via version bump if possible
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn('[pyana-note] create failed', err); }
      } else if (act === 'spend') {
        try {
          const res = wasm.spend_note(handle, 0, 100, 0);
          console.log('[pyana-note] spent demo note', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn('[pyana-note] spend failed', err); }
      }
    });
  }
}
if (!customElements.get('pyana-note')) customElements.define('pyana-note', PyanaNote);

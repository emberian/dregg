/**
 * <dregg-note uri="dregg://note/<commitment-hex>"> — UTXO-style note (commitment + nullifier lifecycle).
 *
 * Replaces playground/sections/notes.js per Studio migration (Tier 2).
 *
 * URI form: dregg://note/<64-hex commitment>
 * data= form: JSON { commitment, value, asset_type, spent? }
 *
 * Modes: compact | default | lab
 *
 * Uses canonical wasm: create_note, spend_note, get_notes when present.
 * No JS crypto reimplementation. Visible placeholders for missing note indexes.
 * Composes <dregg-cell> for owner cell deeplinks when agent known (future).
 *
 * Trust tier: n/a (notes are pre-proof commitments; conservation proved at spend time via turn).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, emptyState, renderParseError, shortHex } from './_base.js';

class DreggNote extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';
    const agentIndex = Number(this.getAttribute('agent-index') || 0);

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
      ? this._runtime.getNotes(agentIndex)
      : null;

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      let note = inlineData;
      if (!note && parsed && noteSignal) {
        const list = noteSignal.value || [];
        note = list.find(n => n.commitment === parsed.id) || null;
      }
      if (!note) {
        if (mode === 'compact') {
          return html`<span class="dregg-inspector dregg-inspector--compact">note (no data)</span>`;
        }
        return html`
          <div class="dregg-inspector dregg-inspector--note">
            <header>
              <span class="dregg-inspector__kind">note</span>
              ${parsed ? html`<code class="dregg-inspector__id" title=${parsed.id}>${shortHex(parsed.id, 24)}</code>` : null}
            </header>
            <div class="dregg-inspector__notice">
              ${parsed
                ? html`note not found for agent ${String(agentIndex)}; awaiting runtime note index or use <code>data=</code> with canonical note data.`
                : html`no note data; provide <code>uri="dregg://note/&lt;commitment&gt;"</code> or <code>data=</code>.`}
            </div>
            ${mode === 'lab' && caps.mutate && wasm ? html`
              <div class="dregg-inspector__controls">
                <button class="dregg-inspector__button" data-act="create">Create note via wasm</button>
              </div>
              <div class="dregg-inspector__note">
                Lab mode calls canonical wasm helpers and refreshes this inspector; it does not synthesize commitments in JS.
              </div>
            ` : null}
          </div>`;
      }

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code title=${note.commitment}>${shortHex(note.commitment)}</code>
            · ${String(note.value)} (asset ${String(note.asset_type)})
            ${note.spent ? '· spent' : ''}
          </span>`;
      }

      const spent = note.spent === true || note.status === 'spent' || note.nullifier;
      const actions = mode === 'lab' && caps.mutate && wasm ? html`
        <div class="dregg-inspector__controls">
          <button class="dregg-inspector__button" data-act="spend" disabled=${spent}>Spend via wasm</button>
          <button class="dregg-inspector__button" data-act="create">Create another via wasm</button>
        </div>
        <div class="dregg-inspector__note">
          Lab mode only. Production note lifecycle is observed through turns, receipts, and nullifier-set updates.
        </div>
      ` : null;

      return html`
        <div class="dregg-inspector dregg-inspector--note">
          <header>
            <span class="dregg-inspector__kind">note</span>
            <code class="dregg-inspector__id" title=${note.commitment}>${shortHex(note.commitment, 24)}</code>
            <span class="dregg-inspector__meta">${spent ? 'spent' : 'unspent'} · asset ${String(note.asset_type ?? 'unknown')}</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>Value</span><strong>${String(note.value ?? note.amount ?? 'unknown')}</strong></div>
            <div><span>Asset</span><strong>${String(note.asset_type ?? note.assetType ?? 'unknown')}</strong></div>
            <div><span>Status</span><strong>${spent ? 'spent' : 'unspent'}</strong></div>
            <div><span>Nullifier</span><strong>${note.nullifier ? shortHex(note.nullifier, 10) : 'not published'}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            <dt>commitment</dt><dd><code title=${note.commitment}>${note.commitment}</code></dd>
            <dt>nullifier</dt><dd>${note.nullifier ? html`<code title=${note.nullifier}>${note.nullifier}</code>` : html`<span style="opacity:0.6">(not spent)</span>`}</dd>
            <dt>status</dt><dd>${spent ? html`<span class="dregg-inspector__notice dregg-inspector__notice--warn">SPENT (nullifier published)</span>` : html`<span class="dregg-inspector__notice dregg-inspector__notice--ok">unspent</span>`}</dd>
          </dl>
          ${actions}
          <details class="dregg-inspector__section">
            <summary>Lifecycle</summary>
            <div class="dregg-inspector__section-body">Inspector reads receipts for spend events. Create is via Effect in turn; nullifier in NullifierSet.</div>
          </details>
        </div>`;
    };

    this._dispose = effect(() => {
      render(h(Component, {}), root);
    });

    // Wire lab buttons (delegated; survives re-render via root listener)
    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm || !handle || mode !== 'lab') return;
      const act = btn.dataset.act;
      if (act === 'create') {
        try {
          const res = wasm.create_note(handle, agentIndex, 100, 0);
          console.log('[dregg-note] created note via wasm', res);
          // trigger re-render via version bump if possible
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn('[dregg-note] create failed', err); }
      } else if (act === 'spend') {
        try {
          const res = wasm.spend_note(handle, agentIndex, 100, 0);
          console.log('[dregg-note] spent note via wasm', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn('[dregg-note] spend failed', err); }
      }
    });
  }
}
if (!customElements.get('dregg-note')) customElements.define('dregg-note', DreggNote);

/**
 * <dregg-encrypted-intent uri="dregg://encrypted-intent/<intent-id>" data="...">
 *
 * Per-validator share status + reveal-progress bar for threshold-encrypted intents.
 *
 * Canonical: EncryptedIntent + threshold-decryption flow (intent crate).
 * Paste-friendly for cross-tab reveal coordination.
 *
 * URI: dregg://encrypted-intent/<id>
 * data=: { intent_id, shares: [{validator, received, share_ct?}], threshold, progress, ... }
 *
 * Modes: compact (progress bar + count) | default (full share grid + reveal affordance when wasm supports it)
 *
 * Trust-tier: Placeholder until real STARK verifier for fulfillment (§5.8 blocked).
 * No JS crypto; delegates to wasm.decrypt_share etc when wired.
 *
 * Per STARBRIDGE-PLAN §4.5 + NEW-WORLD "encrypted intent" + §5.8.
 * Composes <dregg-proof> for reveal proofs when available.
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggEncryptedIntent extends InspectorBase {
  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;
    const caps = this._runtime?.caps || { mutate: true };

    let parsed = null;
    let data = null;
    if (dataAttr) {
      try { data = JSON.parse(dataAttr); } catch {}
    }
    if (!data && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'encrypted-intent')) return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const viewState = signal({ error: null });

    const Component = () => {
      const s = viewState.value;
      const intent = data || { intent_id: (parsed && parsed.id) || '', threshold: null, shares: [] };
      const shares = Array.isArray(intent.shares) ? intent.shares : [];
      const received = shares.filter(sh => sh && sh.received).length;
      const threshold = Number(intent.threshold || 0);
      const prog = threshold > 0 ? Math.min(100, Math.floor((received / threshold) * 100)) : 0;

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <span class="dregg-inspector__kind">encrypted-intent</span>
            <code>${shortHex(intent.intent_id, 8)}</code>
            <span style="display:inline-block;width:60px;height:6px;background:#e5e7eb;border-radius:3px;overflow:hidden;">
              <span style="display:block;height:100%;width:${prog}%;background:#3b82f6;"></span>
            </span>
            ${threshold ? `${received}/${threshold}` : 'awaiting threshold'}
          </span>`;
      }

      const shareRows = shares.map((sh, i) => html`
        <tr>
          <td><code>${shortHex(sh.validator || 'v' + i, 8)}</code></td>
          <td>${sh.received ? html`<span style="color:#166534;">received</span>` : html`<span style="color:#b91c1c;">pending</span>`}</td>
          <td><code>${sh.share_ct ? shortHex(sh.share_ct, 10) : '—'}</code></td>
        </tr>
      `);

      const revealAvailable = caps.mutate && wasm && typeof wasm.reveal_encrypted_intent === 'function';
      const form = revealAvailable ? html`
        <div style="margin-top:6px;font-size:0.75rem;">
          <button data-act="reveal" style="font-size:0.7rem;margin-left:4px;">Attempt reveal</button>
          ${s.error ? html`<div style="color:#b91c1c;">${s.error}</div>` : null}
        </div>
      ` : html`
        <div style="font-size:0.7rem;color:var(--fg-dim);margin-top:6px;">
          awaiting wasm32 support for threshold reveal; share rows are read from receipt/runtime data only.
        </div>`;

      return html`
        <div class="dregg-inspector dregg-inspector--eintent">
          <header>
            <span class="dregg-inspector__kind">encrypted-intent</span>
            <code class="dregg-inspector__id">${shortHex(intent.intent_id || '', 20)}</code>
          </header>
          <div style="margin:4px 0;">
            Progress: ${threshold ? `${received}/${threshold}` : 'awaiting threshold'} shares
            <span style="display:inline-block;width:120px;height:8px;background:#e5e7eb;border-radius:4px;vertical-align:middle;">
              <span style="display:block;height:100%;width:${prog}%;background:#3b82f6;border-radius:4px;"></span>
            </span>
            ${prog}%
          </div>
          <table style="font-size:0.7rem;border-collapse:collapse;">
            <tr><th>validator</th><th>status</th><th>share</th></tr>
            ${shareRows.length ? shareRows : html`<tr><td colspan="3" style="color:var(--fg-dim);">awaiting encrypted intent share data from runtime</td></tr>`}
          </table>
          ${form}
          <div style="font-size:0.65rem;color:var(--fg-dim);margin-top:4px;">
            Threshold decryption. Placeholder until real STARK verifier (§5.8). Reveal emits proof for <dregg-proof>.
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm) return;
      const act = btn.dataset.act;
      if (act === 'reveal') {
        try {
          if (typeof wasm.reveal_encrypted_intent !== 'function') {
            throw new Error('reveal_encrypted_intent wasm export is not available');
          }
          const res = wasm.reveal_encrypted_intent(0, (data && data.intent_id) || '');
          viewState.value = { ...viewState.value, error: null };
          console.log('[dregg-encrypted-intent] reveal result', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) {
          viewState.value = { ...viewState.value, error: 'reveal failed: ' + (err?.message || err) };
        }
      }
    });
  }
}
if (!customElements.get('dregg-encrypted-intent')) customElements.define('dregg-encrypted-intent', DreggEncryptedIntent);

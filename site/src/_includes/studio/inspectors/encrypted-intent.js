/**
 * <pyana-encrypted-intent uri="pyana://encrypted-intent/<intent-id>" data="...">
 *
 * Per-validator share status + reveal-progress bar for threshold-encrypted intents.
 *
 * Canonical: EncryptedIntent + threshold-decryption flow (intent crate).
 * Paste-friendly for cross-tab reveal coordination.
 *
 * URI: pyana://encrypted-intent/<id>
 * data=: { intent_id, shares: [{validator, received, share_ct?}], threshold, progress, ... }
 *
 * Modes: compact (progress bar + count) | default (full share grid + reveal demo)
 *
 * Trust-tier: Placeholder until real STARK verifier for fulfillment (§5.8 blocked).
 * No JS crypto; delegates to wasm.decrypt_share etc when wired.
 *
 * Per STARBRIDGE-PLAN §4.5 + NEW-WORLD "encrypted intent" + §5.8.
 * Composes <pyana-proof> for reveal proofs when available.
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaEncryptedIntent extends InspectorBase {
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
      data = { intent_id: parsed.id, shares: [], threshold: 2, progress: 0 };
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const demoState = signal({ shares: (data && data.shares) || [], progress: (data && data.progress) || 0, error: null });

    const Component = () => {
      const s = demoState.value;
      const intent = data || { intent_id: (parsed && parsed.id) || 'demo-intent', threshold: 2, shares: s.shares };
      const prog = Math.min(100, Math.floor((s.shares.length / Math.max(1, intent.threshold || 2)) * 100));

      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <span class="pyana-inspector__kind">encrypted-intent</span>
            <code>${shortHex(intent.intent_id, 8)}</code>
            <span style="display:inline-block;width:60px;height:6px;background:#e5e7eb;border-radius:3px;overflow:hidden;">
              <span style="display:block;height:100%;width:${prog}%;background:#3b82f6;"></span>
            </span>
            ${s.shares.length}/${intent.threshold || 2}
          </span>`;
      }

      const shareRows = (s.shares.length ? s.shares : (intent.shares || [])).map((sh, i) => html`
        <tr>
          <td><code>${shortHex(sh.validator || 'v' + i, 8)}</code></td>
          <td>${sh.received ? html`<span style="color:#166534;">✓ received</span>` : html`<span style="color:#b91c1c;">pending</span>`}</td>
          <td><code>${sh.share_ct ? shortHex(sh.share_ct, 10) : '—'}</code></td>
        </tr>
      `);

      const form = (caps.mutate && wasm) ? html`
        <div style="margin-top:6px;font-size:0.75rem;">
          <button data-act="add-share" style="font-size:0.7rem;">Simulate receive share (demo)</button>
          <button data-act="reveal" style="font-size:0.7rem;margin-left:4px;">Attempt reveal</button>
          ${s.error ? html`<div style="color:#b91c1c;">${s.error}</div>` : null}
        </div>
      ` : html`<div style="font-size:0.7rem;color:var(--fg-dim);">read-only — no reveal</div>`;

      return html`
        <div class="pyana-inspector pyana-inspector--eintent">
          <header>
            <span class="pyana-inspector__kind">encrypted-intent</span>
            <code class="pyana-inspector__id">${shortHex(intent.intent_id || '', 20)}</code>
          </header>
          <div style="margin:4px 0;">
            Progress: ${s.shares.length}/${intent.threshold || 2} shares
            <span style="display:inline-block;width:120px;height:8px;background:#e5e7eb;border-radius:4px;vertical-align:middle;">
              <span style="display:block;height:100%;width:${prog}%;background:#3b82f6;border-radius:4px;"></span>
            </span>
            ${prog}%
          </div>
          <table style="font-size:0.7rem;border-collapse:collapse;">
            <tr><th>validator</th><th>status</th><th>share</th></tr>
            ${shareRows}
          </table>
          ${form}
          <div style="font-size:0.65rem;color:var(--fg-dim);margin-top:4px;">
            Threshold decryption. Placeholder until real STARK verifier (§5.8). Reveal emits proof for <pyana-proof>.
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm) return;
      const act = btn.dataset.act;
      if (act === 'add-share') {
        const current = demoState.value.shares || [];
        const v = 'validator-' + current.length;
        demoState.value = { ...demoState.value, shares: [...current, { validator: v, received: true, share_ct: 'deadbeef'.repeat(4) }], error: null };
        if (this._runtime?.version) this._runtime.version.value++;
      } else if (act === 'reveal') {
        try {
          const res = wasm.reveal_encrypted_intent ? wasm.reveal_encrypted_intent(0, (data && data.intent_id) || 'demo') : { revealed: true, proof: 'demo' };
          demoState.value = { ...demoState.value, error: null };
          console.log('[pyana-encrypted-intent] reveal demo', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) {
          demoState.value = { ...demoState.value, error: 'reveal failed (wasm not fully wired): ' + err };
        }
      }
    });
  }
}
if (!customElements.get('pyana-encrypted-intent')) customElements.define('pyana-encrypted-intent', PyanaEncryptedIntent);

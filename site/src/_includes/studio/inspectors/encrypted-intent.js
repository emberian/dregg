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
import { InspectorBase, renderParseError, shortHex, emptyState } from './_base.js';

function pct(n) {
  return Math.max(0, Math.min(100, Number.isFinite(n) ? n : 0));
}

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
    let parseError = null;
    if (dataAttr) {
      try { data = JSON.parse(dataAttr); } catch (e) { parseError = e; }
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
      if (parseError) {
        return html`<div class="dregg-inspector dregg-inspector--err">bad encrypted intent data JSON: ${parseError.message}</div>`;
      }
      if (!data && !parsed) {
        return emptyState(
          html,
          'Encrypted intent unavailable',
          html`Provide a <code>uri</code> or <code>data</code> JSON with threshold and share status to inspect reveal progress.`
        );
      }
      const intent = data || { intent_id: parsed.id, threshold: null, shares: [] };
      const shares = Array.isArray(intent.shares) ? intent.shares : [];
      const received = shares.filter(sh => sh && sh.received).length;
      const threshold = Number(intent.threshold || intent.reveal_threshold || 0);
      const expected = Number(intent.validator_count || (Array.isArray(intent.validators) ? intent.validators.length : intent.validators) || shares.length || 0);
      const prog = threshold > 0 ? pct(Math.floor((received / threshold) * 100)) : 0;
      const complete = threshold > 0 && received >= threshold;
      const status = complete ? 'threshold met' : threshold ? 'collecting shares' : 'threshold unknown';

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <span class="dregg-inspector__kind">encrypted-intent</span>
            <code>${shortHex(intent.intent_id, 8)}</code>
            <span class="dregg-inspector__progress" style="width:60px;height:6px;">
              <span class="dregg-inspector__progress-fill" style=${`width:${prog}%;`}></span>
            </span>
            ${threshold ? `${received}/${threshold}` : 'awaiting threshold'}
          </span>`;
      }

      const shareRows = shares.map((sh, i) => html`
        <tr>
          <td><code>${shortHex(sh.validator || 'v' + i, 8)}</code></td>
          <td><span class=${`dregg-inspector__pill ${sh.received ? '' : 'dregg-inspector__meta'}`}>${sh.received ? 'received' : 'pending'}</span></td>
          <td>${sh.share_ct ? html`<code title=${sh.share_ct}>${shortHex(sh.share_ct, 10)}</code>` : html`<span class="dregg-inspector__meta">not supplied</span>`}</td>
          <td>${sh.proof ? html`<dregg-proof data-proof=${JSON.stringify(sh.proof)} mode="compact"></dregg-proof>` : html`<span class="dregg-inspector__meta">not supplied</span>`}</td>
        </tr>
      `);

      const revealAvailable = caps.mutate && wasm && typeof wasm.reveal_encrypted_intent === 'function';
      const form = revealAvailable ? html`
        <div class="dregg-inspector__panel">
          <button data-act="reveal">Attempt reveal</button>
          ${s.error ? html`<div style="color:#b91c1c;">${s.error}</div>` : null}
        </div>
      ` : html`
        <div class="dregg-inspector__note">
          Reveal action unavailable in this runtime. Share rows are read from supplied receipt/runtime data only.
        </div>`;

      return html`
        <div class="dregg-inspector dregg-inspector--eintent">
          <header>
            <span class="dregg-inspector__kind">encrypted-intent</span>
            <code class="dregg-inspector__id">${shortHex(intent.intent_id || '', 20)}</code>
            <span class="dregg-inspector__pill">${status}</span>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>shares</dt><dd>${threshold ? `${received}/${threshold} threshold` : `${received} received`}${expected ? html` · ${expected} expected` : ''}</dd>
            <dt>progress</dt><dd>
              <span class="dregg-inspector__progress">
                <span class="dregg-inspector__progress-fill" style=${`width:${prog}%;`}></span>
              </span>
              ${prog}%
            </dd>
            ${intent.ciphertext || intent.intent_ct ? html`<dt>ciphertext</dt><dd><code title=${intent.ciphertext || intent.intent_ct}>${shortHex(intent.ciphertext || intent.intent_ct, 18)}</code></dd>` : null}
            ${intent.reveal_epoch || intent.deadline ? html`<dt>reveal window</dt><dd>${intent.reveal_epoch || intent.deadline}</dd>` : null}
          </dl>
          <table class="dregg-inspector__table">
            <tr><th>validator</th><th>status</th><th>share</th><th>proof</th></tr>
            ${shareRows.length ? shareRows : html`<tr><td colspan="4" class="dregg-inspector__meta">no share rows supplied by runtime data</td></tr>`}
          </table>
          ${intent.reveal_proof ? html`
            <details class="dregg-inspector__section" open>
              <summary>Reveal proof</summary>
              <div class="dregg-inspector__section-body"><dregg-proof data-proof=${JSON.stringify(intent.reveal_proof)}></dregg-proof></div>
            </details>` : null}
          ${form}
          <div class="dregg-inspector__note">
            Threshold decryption status from supplied intent data. This inspector does not decrypt shares or verify fulfillment proofs in JavaScript.
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

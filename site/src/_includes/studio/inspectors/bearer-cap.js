/**
 * <pyana-bearer-cap uri="pyana://bearer-cap/<token-hex>" data="...">
 *
 * Bearer capability creator/verifier using canonical wasm privacy bindings.
 *
 * IMPORTANT (per STARBRIDGE-PLAN §5.1): current impl is Ed25519 shim (v2 binding hash + sig).
 * Real BearerCapProof { delegation_proof: SignedDelegation | StarkDelegation, ... } shape
 * awaits wasm rebase to produce/verify the executor-consumed canonical type.
 * Inspector shows "shim" badge until then (Silver/Placeholder trust implications).
 *
 * Modes: compact | default | demo (interactive create/verify)
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaBearerCap extends InspectorBase {
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
      if (renderParseError(this, refAttr, parsed, 'bearer-cap')) return;
      data = { bearer_token_hex: parsed.id };
    }

    const root = document.createElement('div');
    this.appendChild(root);

    // local demo state signal for create/verify form (no JS reimpl of crypto)
    const demoState = signal({ lastCreated: null, lastVerify: null, error: null });

    const Component = () => {
      const s = demoState.value;
      const isShim = true; // always until §5.1 real shape

      if (mode === 'compact') {
        const tok = data?.bearer_token_hex || (s.lastCreated && s.lastCreated.bearer_token_hex) || '';
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <span class="pyana-inspector__kind">bearer-cap${isShim ? ' (shim)' : ''}</span>
            <code>${shortHex(tok, 10)}</code>
          </span>`;
      }

      const created = s.lastCreated || data;
      const verifyRes = s.lastVerify;

      const shimNote = html`
        <div style="background:#fef3c7;border:1px solid #fcd34d;padding:4px 6px;font-size:0.7rem;border-radius:3px;margin:4px 0;">
          SHIM (see §5.1): Ed25519 sig over binding. Awaiting real BearerCapProof for canonical delegation_proof path.
        </div>`;

      const form = (caps.mutate && wasm) ? html`
        <div style="border-top:1px solid var(--line);margin-top:8px;padding-top:6px;font-size:0.8rem;">
          <div><strong>Demo create (uses current agent 0 signing key — demo only)</strong></div>
          <input id="bc-target" placeholder="target cell hex (32B)" style="width:220px;font-family:var(--mono);font-size:0.75rem;" value="0000000000000000000000000000000000000000000000000000000000000000" />
          <input id="bc-action" value="transfer" style="width:80px;font-size:0.75rem;" />
          <button data-act="create" style="font-size:0.7rem;">Create Bearer Cap</button>
          <div style="margin-top:4px;">
            <button data-act="verify" style="font-size:0.7rem;">Verify last / pasted</button>
          </div>
          ${s.error ? html`<div style="color:#b91c1c;font-size:0.7rem;">${s.error}</div>` : null}
        </div>
      ` : null;

      return html`
        <div class="pyana-inspector pyana-inspector--bearer">
          <header>
            <span class="pyana-inspector__kind">bearer-cap${isShim ? ' (shim)' : ''}</span>
            ${created ? html`<code class="pyana-inspector__id" title=${created.bearer_token_hex || ''}>${shortHex(created.bearer_token_hex || '', 16)}</code>` : ''}
          </header>
          ${shimNote}
          ${created ? html`
            <dl class="pyana-inspector__kv">
              <dt>token (sig)</dt><dd><code title=${created.bearer_token_hex}>${shortHex(created.bearer_token_hex, 20)}</code></dd>
              <dt>delegator pub</dt><dd><code>${shortHex(created.delegator_pubkey_hex || '', 12)}</code></dd>
              <dt>target</dt><dd><code>${shortHex(created.target_cell || '', 12)}</code></dd>
              <dt>action</dt><dd>${created.action || 'n/a'}</dd>
              <dt>expiry</dt><dd>${created.expiry || 0}</dd>
            </dl>
          ` : html`<div style="font-size:0.8rem;color:var(--fg-dim);">No cap loaded. Use form or data= attr.</div>`}
          ${verifyRes ? html`
            <div style="margin-top:6px;font-size:0.8rem;">
              Verify: <strong style="color:${verifyRes.valid ? '#166534' : '#b91c1c'}">${verifyRes.valid ? 'VALID' : 'INVALID'}</strong>
              (sig:${verifyRes.signature_valid} expired:${verifyRes.expired})
            </div>
          ` : null}
          ${form}
          <div style="font-size:0.65rem;color:var(--fg-dim);margin-top:4px;">
            Bearer caps are transferable proofs. Paste token between tabs. Real shape enables cross-sovereign without on-chain state update.
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    // Demo handlers (direct wasm privacy fns; no reimpl)
    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm) return;
      const act = btn.dataset.act;
      if (act === 'create') {
        try {
          const target = root.querySelector('#bc-target')?.value?.trim() || '00'.repeat(32);
          const action = root.querySelector('#bc-action')?.value?.trim() || 'transfer';
          // Use a demo 32B seed (in real use from cipherclerk held key; here illustrative)
          const demoSeed = '00'.repeat(31) + '01';
          const res = wasm.create_bearer_cap(demoSeed, target, action, 0);
          demoState.value = { ...demoState.value, lastCreated: res, lastVerify: null, error: null };
        } catch (err) {
          demoState.value = { ...demoState.value, error: String(err) };
        }
      } else if (act === 'verify') {
        const created = demoState.value.lastCreated || data;
        if (created && created.bearer_token_hex && created.delegator_pubkey_hex) {
          try {
            const now = Math.floor(Date.now() / 1000);
            const v = wasm.verify_bearer_cap(
              created.bearer_token_hex,
              created.delegator_pubkey_hex,
              created.target_cell || '00'.repeat(32),
              created.action || 'transfer',
              created.expiry || 0,
              now
            );
            demoState.value = { ...demoState.value, lastVerify: v, error: null };
          } catch (err) {
            demoState.value = { ...demoState.value, error: String(err) };
          }
        }
      }
    });
  }
}
if (!customElements.get('pyana-bearer-cap')) customElements.define('pyana-bearer-cap', PyanaBearerCap);

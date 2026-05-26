/**
 * <dregg-bearer-cap uri="dregg://bearer-cap/<token-hex>" data="...">
 *
 * Bearer capability creator/verifier using canonical wasm privacy bindings.
 * Supports both legacy shim (create_bearer_cap/verify_bearer_cap for compat)
 * and real BearerCapProof (create_bearer_cap_proof / verify_bearer_cap_proof_sig per
 * STARBRIDGE-PLAN §5.1 + FOLLOWUP-14). Real shape includes delegation_proof
 * (SignedDelegation | StarkDelegation), revocation_channel, allowed_effects,
 * AuthRequired permissions, fed binding. Used in Authorization::Bearer.
 *
 * UI: auto-detects shape; shows "real" (SignedDelegation path) or "(shim)" badge.
 * Visible Placeholder note only if using shim path. Reuses <dregg-revocation-channel>
 * for linked channels (data=). No JS crypto reimpl — all via wasm.
 *
 * Demo create uses real fns with [0;32] sim fed_id (or runtime fed if exposed).
 * Modes: compact | default | demo (interactive create/verify)
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggBearerCap extends InspectorBase {
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

      // Detect real BearerCapProof shape vs legacy shim (per FOLLOWUP-14)
      const created = s.lastCreated || data;
      const isReal = created && (created.delegation_proof || created.target || created.permissions);
      const isShim = !isReal && (created && created.bearer_token_hex);
      const kindLabel = `bearer-cap${isReal ? ' (real)' : isShim ? ' (shim)' : ''}`;

      if (mode === 'compact') {
        const tok = (created && (created.bearer_token_hex || created.delegation_proof ? 'real' : '')) || (created && created.bearer_token_hex) || '';
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <span class="dregg-inspector__kind">${kindLabel}</span>
            <code>${shortHex(tok || (created && created.target ? shortHex(created.target,8) : ''), 10)}</code>
          </span>`;
      }

      const verifyRes = s.lastVerify;

      const note = isReal
        ? html`<div style="background:#e6f4ea;border:1px solid #a3d9b1;padding:4px 6px;font-size:0.7rem;border-radius:3px;margin:4px 0;">
            REAL BearerCapProof (SignedDelegation path shown). Revocation/facet fields supported in substrate.
          </div>`
        : (isShim ? html`
        <div style="background:#fef3c7;border:1px solid #fcd34d;padding:4px 6px;font-size:0.7rem;border-radius:3px;margin:4px 0;">
          SHIM (compat): legacy binding. Prefer real create_bearer_cap_proof for canonical use in turns.
        </div>` : html`<div style="font-size:0.7rem;color:var(--fg-dim);">No cap data.</div>`);

      const form = (caps.mutate && wasm) ? html`
        <div style="border-top:1px solid var(--line);margin-top:8px;padding-top:6px;font-size:0.8rem;">
          <div><strong>Demo create (real BearerCapProof preferred; shim fallback)</strong></div>
          <input id="bc-target" placeholder="target cell hex (32B)" style="width:220px;font-family:var(--mono);font-size:0.75rem;" value="0000000000000000000000000000000000000000000000000000000000000000" />
          <select id="bc-perm" style="width:90px;font-size:0.75rem;"><option>Signature</option><option>None</option><option>Proof</option><option>Either</option></select>
          <input id="bc-bearer" placeholder="bearer pk (hex, optional)" style="width:140px;font-family:var(--mono);font-size:0.75rem;" value="" />
          <input id="bc-exp" value="0" style="width:60px;font-size:0.75rem;" title="expires unix (0=none)" />
          <button data-act="create" style="font-size:0.7rem;">Create (real)</button>
          <div style="margin-top:4px;">
            <button data-act="verify" style="font-size:0.7rem;">Verify last / pasted</button>
            <button data-act="create-shim" style="font-size:0.65rem;opacity:0.7;">Legacy shim</button>
          </div>
          ${s.error ? html`<div style="color:#b91c1c;font-size:0.7rem;">${s.error}</div>` : null}
        </div>
      ` : null;

      return html`
        <div class="dregg-inspector dregg-inspector--bearer">
          <header>
            <span class="dregg-inspector__kind">${kindLabel}</span>
            ${created ? html`<code class="dregg-inspector__id" title=${(created.bearer_token_hex || created.target || '')}>${shortHex((created.bearer_token_hex || (created.target ? created.target : '')), 16)}</code>` : ''}
          </header>
          ${note}
          ${created ? html`
            <dl class="dregg-inspector__kv">
              ${isReal ? html`
                <dt>target</dt><dd><code>${shortHex(created.target || '', 12)}</code></dd>
                <dt>permissions</dt><dd>${created.permissions || 'n/a'}</dd>
                <dt>delegation</dt><dd><code>${(created.delegation_proof && created.delegation_proof.SignedDelegation) ? 'SignedDelegation' : (created.delegation_proof ? 'StarkDelegation' : 'n/a')}</code></dd>
                <dt>expires_at</dt><dd>${created.expires_at || 0}</dd>
                <dt>revocation_channel</dt><dd>${created.revocation_channel ? html`<dregg-revocation-channel data=${JSON.stringify({channel_id: created.revocation_channel})} mode="compact"></dregg-revocation-channel>` : html`<em>none</em>`}</dd>
                <dt>allowed_effects</dt><dd><code>${created.allowed_effects ? JSON.stringify(created.allowed_effects) : 'unrestricted'}</code></dd>
              ` : html`
                <dt>token (sig)</dt><dd><code title=${created.bearer_token_hex}>${shortHex(created.bearer_token_hex, 20)}</code></dd>
                <dt>delegator pub</dt><dd><code>${shortHex(created.delegator_pubkey_hex || '', 12)}</code></dd>
                <dt>target</dt><dd><code>${shortHex(created.target_cell || '', 12)}</code></dd>
                <dt>action</dt><dd>${created.action || 'n/a'}</dd>
                <dt>expiry</dt><dd>${created.expiry || 0}</dd>
              `}
            </dl>
          ` : html`<div style="font-size:0.8rem;color:var(--fg-dim);">No cap loaded. Use form or data= attr (real proof JSON or shim shape).</div>`}
          ${verifyRes ? html`
            <div style="margin-top:6px;font-size:0.8rem;">
              Verify: <strong style="color:${(verifyRes.valid || verifyRes.valid_for_sig) ? '#166534' : '#b91c1c'}">${(verifyRes.valid || verifyRes.valid_for_sig) ? 'VALID' : 'INVALID'}</strong>
              (sig:${verifyRes.signature_valid || verifyRes.valid_for_sig} expired:${verifyRes.expired})
            </div>
          ` : null}
          ${form}
          <div style="font-size:0.65rem;color:var(--fg-dim);margin-top:4px;">
            Bearer caps are transferable proofs (paste between sovereign tabs). Real shape binds to executor + revocation channels for capability model.
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    // Demo handlers (direct wasm privacy fns; no reimpl; real preferred)
    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm) return;
      const act = btn.dataset.act;
      if (act === 'create' || act === 'create-shim') {
        try {
          const target = root.querySelector('#bc-target')?.value?.trim() || '00'.repeat(32);
          const perm = root.querySelector('#bc-perm')?.value || 'Signature';
          const bearer = root.querySelector('#bc-bearer')?.value?.trim() || '';
          const expStr = root.querySelector('#bc-exp')?.value?.trim() || '0';
          const expires = parseInt(expStr, 10) || 0;
          const demoSeed = '00'.repeat(31) + '01'; // delegator signing seed
          const bearerPk = bearer || demoSeed; // default bearer=delegator for demo (real use separate)
          const fed = '00'.repeat(32);
          let res;
          if (act === 'create') {
            // Prefer real canonical (FOLLOWUP-14, now supports rev_channel + facets via substrate improvement)
            res = wasm.create_bearer_cap_proof(demoSeed, target, perm, bearerPk, expires, fed, "", 0);
          } else {
            // explicit legacy shim (compat)
            const action = 'transfer'; // shim still uses action str
            res = wasm.create_bearer_cap(demoSeed, target, action, expires);
          }
          demoState.value = { ...demoState.value, lastCreated: res, lastVerify: null, error: null };
        } catch (err) {
          demoState.value = { ...demoState.value, error: String(err) };
        }
      } else if (act === 'verify') {
        const created = demoState.value.lastCreated || data;
        if (!created) return;
        try {
          const now = Math.floor(Date.now() / 1000);
          let v;
          if (created.delegation_proof || created.target) {
            // real shape
            const fed = '00'.repeat(32);
            const proofJson = JSON.stringify(created);
            v = wasm.verify_bearer_cap_proof_sig(proofJson, now, fed);
          } else if (created.bearer_token_hex && created.delegator_pubkey_hex) {
            const action = created.action || 'transfer';
            v = wasm.verify_bearer_cap(
              created.bearer_token_hex,
              created.delegator_pubkey_hex,
              created.target_cell || '00'.repeat(32),
              action,
              created.expiry || created.expires_at || 0,
              now
            );
          }
          if (v) demoState.value = { ...demoState.value, lastVerify: v, error: null };
        } catch (err) {
          demoState.value = { ...demoState.value, error: String(err) };
        }
      }
    });
  }
}
if (!customElements.get('dregg-bearer-cap')) customElements.define('dregg-bearer-cap', DreggBearerCap);

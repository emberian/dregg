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
import { InspectorBase, dreggCodeLink, emptyState, renderParseError, shortHex } from './_base.js';

function coerceJson(value) {
  if (typeof value !== 'string') return value;
  try { return JSON.parse(value); } catch { return value; }
}

function proofKind(proof) {
  if (!proof) return 'none';
  if (proof.SignedDelegation || proof.signed_delegation) return 'SignedDelegation';
  if (proof.StarkDelegation || proof.stark_delegation) return 'StarkDelegation';
  return Object.keys(proof)[0] || 'delegation';
}

function targetOf(cap) {
  return cap?.target || cap?.target_cell || cap?.targetCell || '';
}

function statusLabel(v) {
  if (!v) return null;
  const valid = Boolean(v.valid || v.valid_for_sig);
  if (valid && !v.expired) return 'valid';
  if (v.expired) return 'expired';
  return 'invalid';
}

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
      const created = coerceJson(s.lastCreated || data);
      const isReal = created && (created.delegation_proof || created.target || created.permissions);
      const isShim = !isReal && (created && created.bearer_token_hex);
      const kindLabel = `bearer-cap${isReal ? ' (real)' : isShim ? ' (shim)' : ''}`;
      const target = targetOf(created);

      if (mode === 'compact') {
        const tok = created ? (created.bearer_token_hex || target || proofKind(created.delegation_proof)) : '';
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <span class="dregg-inspector__kind">${kindLabel}</span>
            ${tok ? html`<code title=${tok}>${shortHex(tok, 12)}</code>` : html`<span class="dregg-inspector__meta">no data</span>`}
          </span>`;
      }

      const verifyRes = s.lastVerify;
      const verification = statusLabel(verifyRes);

      const note = isReal
        ? html`<div class="dregg-inspector__notice dregg-inspector__notice--ok">Canonical BearerCapProof. Delegation, expiry, and revocation fields are interpreted below.</div>`
        : (isShim ? html`
        <div class="dregg-inspector__notice dregg-inspector__notice--warn">Legacy bearer-cap shim. It is shown for compatibility; canonical turns should use BearerCapProof.</div>` : null);

      const canCreateReal = caps.mutate && wasm?.create_bearer_cap_proof;
      const canCreateShim = caps.mutate && wasm?.create_bearer_cap;
      const canVerifyReal = wasm?.verify_bearer_cap_proof_sig;
      const canVerifyShim = wasm?.verify_bearer_cap;
      const form = (wasm && (canCreateReal || canCreateShim || canVerifyReal || canVerifyShim)) ? html`
        <div class="dregg-inspector__controls">
          <input class="dregg-inspector__input" id="bc-target" placeholder="target cell hex (32B)" value=${target || '00'.repeat(32)} />
          <select class="dregg-inspector__select" id="bc-perm"><option>Signature</option><option>None</option><option>Proof</option><option>Either</option></select>
          <input class="dregg-inspector__input" id="bc-bearer" placeholder="bearer pk hex" />
          <input class="dregg-inspector__input" id="bc-exp" value="0" title="expires unix (0=none)" />
          <button class="dregg-inspector__button" data-act="create" disabled=${!canCreateReal}>Create proof</button>
          <button class="dregg-inspector__button" data-act="verify" disabled=${!(canVerifyReal || canVerifyShim)}>Verify</button>
          <button class="dregg-inspector__button" data-act="create-shim" disabled=${!canCreateShim}>Legacy shim</button>
          ${s.error ? html`<div class="dregg-inspector__notice dregg-inspector__notice--warn">${s.error}</div>` : null}
        </div>
      ` : html`<div class="dregg-inspector__notice">No bearer-cap wasm controls are exposed by this runtime.</div>`;

      if (!created && mode !== 'demo') return emptyState(
        html,
        'No bearer capability loaded',
        html`Pass a bearer-cap URI or <code>data</code> JSON, or switch to demo mode when wasm create/verify exports are available.`,
      );

      return html`
        <div class="dregg-inspector dregg-inspector--bearer">
          <header>
            <span class="dregg-inspector__kind">${kindLabel}</span>
            ${created ? html`<code class="dregg-inspector__id" title=${created.bearer_token_hex || target || ''}>${shortHex(created.bearer_token_hex || target || '', 16)}</code>` : ''}
          </header>
          ${note}
          ${created ? html`
            <div class="dregg-inspector__summary">
              <div><span>shape</span><strong>${isReal ? 'proof' : isShim ? 'shim' : 'unknown'}</strong></div>
              <div><span>delegation</span><strong>${proofKind(created.delegation_proof)}</strong></div>
              <div><span>expiry</span><strong>${String(created.expires_at || created.expiry || 0)}</strong></div>
            </div>
          ` : null}
          ${created ? html`
            <dl class="dregg-inspector__kv">
              ${isReal ? html`
                <dt>target</dt><dd>${target ? dreggCodeLink(html, `dregg://cell/${target}`, shortHex(target, 24), target) : html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
                <dt>permissions</dt><dd>${created.permissions || 'n/a'}</dd>
                <dt>delegation</dt><dd><code>${proofKind(created.delegation_proof)}</code></dd>
                <dt>expires_at</dt><dd>${created.expires_at || 0}</dd>
                <dt>revocation_channel</dt><dd>${created.revocation_channel ? html`<dregg-revocation-channel data=${JSON.stringify({channel_id: created.revocation_channel})} mode="compact"></dregg-revocation-channel>` : html`<em>none</em>`}</dd>
                <dt>allowed effects</dt><dd>${created.allowed_effects ? created.allowed_effects.map(e => html`<code>${String(e)}</code> `) : 'unrestricted'}</dd>
              ` : html`
                <dt>token (sig)</dt><dd><code title=${created.bearer_token_hex}>${shortHex(created.bearer_token_hex, 20)}</code></dd>
                <dt>delegator pub</dt><dd><code>${shortHex(created.delegator_pubkey_hex || '', 12)}</code></dd>
                <dt>target</dt><dd>${target ? dreggCodeLink(html, `dregg://cell/${target}`, shortHex(target, 24), target) : html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
                <dt>action</dt><dd>${created.action || 'n/a'}</dd>
                <dt>expiry</dt><dd>${created.expiry || 0}</dd>
              `}
            </dl>
          ` : null}
          ${verifyRes ? html`
            <div class=${`dregg-inspector__notice ${verification === 'valid' ? 'dregg-inspector__notice--ok' : 'dregg-inspector__notice--warn'}`}>
              Verify: <strong>${verification}</strong>
              · sig ${String(verifyRes.signature_valid || verifyRes.valid_for_sig || false)}
              · expired ${String(verifyRes.expired || false)}
            </div>
          ` : null}
          ${form}
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
          demoState.value = { ...demoState.value, lastCreated: coerceJson(res), lastVerify: null, error: null };
        } catch (err) {
          demoState.value = { ...demoState.value, error: String(err) };
        }
      } else if (act === 'verify') {
        const created = coerceJson(demoState.value.lastCreated || data);
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

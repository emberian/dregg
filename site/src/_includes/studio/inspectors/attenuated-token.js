/**
 * <dregg-attenuated-token uri="dregg://attenuated-token/<id-hex>" data="...">
 *
 * Token chain: each attenuation step + restrictions (caveats).
 * Can drill into DelegatedToken envelope.
 *
 * Canonical: cipherclerk.attenuate, HeldToken (token crate macaroon/biscuit backends
 * + dregg_caveats). Replaces playground bearer/attenuated bits.
 *
 * URI: dregg://attenuated-token/<token-id or root>
 * data=: JSON { root_token, chain: [{attenuator, restrictions, ...}] , ... }
 *
 * Modes: compact | default | lab (interactive attenuate when wasm supports it)
 *
 * Platform vocabulary: reuses <dregg-bearer-cap> concepts, <dregg-caveat> future.
 * No JS reimpl of macaroon/biscuit crypto — delegates to wasm.
 * Visible gap if no direct list_held_tokens binding yet (TODO in cipherclerk).
 *
 * Per STARBRIDGE-PLAN §4.5 + token/README.md + STORAGE cell-programs.
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggAttenuatedToken extends InspectorBase {
  _render() {
    const { h, render, html, effect, signal } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;
    const caps = this._runtime?.caps || { mutate: false };

    let parsed = null;
    let data = null;
    if (dataAttr) {
      try { data = JSON.parse(dataAttr); } catch {}
    }
    if (!data && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'attenuated-token')) return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const viewState = signal({ error: null });

    const Component = () => {
      const s = viewState.value;
      const tok = data || null;
      if (!tok) {
        return html`
          <div class="dregg-inspector dregg-inspector--empty">
            attenuated token data not available${parsed ? html`: <code>${shortHex(parsed.id, 16)}</code>` : ''};
            awaiting runtime/wasm support for held-token lookup.
          </div>`;
      }

      if (mode === 'compact') {
        const len = (tok.chain || []).length;
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <span class="dregg-inspector__kind">attenuated-token</span>
            <code>${shortHex(tok.root_token || '', 10)}</code>
            ${len ? html`· ${len} attenuation${len === 1 ? '' : 's'}` : ''}
          </span>`;
      }

      const chain = tok.chain || [];
      const chainView = chain.length
        ? html`
          <div style="margin-top:6px;font-size:0.75rem;">
            <div style="color:var(--fg-dim);margin-bottom:2px;">Attenuation chain:</div>
            <ol style="margin:0;padding-left:1.2em;">
              ${chain.map((step, i) => html`
                <li>
                  <code>${shortHex(step.attenuator || '', 8)}</code>
                  restrictions: <code>${JSON.stringify(step.restrictions || step.caveats || [])}</code>
                </li>
              `)}
            </ol>
          </div>`
        : html`<div style="font-size:0.75rem;color:var(--fg-dim);">No attenuations yet (root token).</div>`;

      const attenuateAvailable = mode === 'lab' && caps.mutate && wasm && (wasm.cipherclerk_attenuate || wasm.attenuate_token);
      const form = attenuateAvailable ? html`
        <div style="border-top:1px solid var(--line);margin-top:8px;padding-top:6px;font-size:0.75rem;">
          <div><strong>Lab attenuate via wasm token backend</strong></div>
          <input id="at-restrict" placeholder='e.g. {"kind":"time","until":123456}' style="width:260px;font-family:var(--mono);font-size:0.7rem;" />
          <button data-act="attenuate" style="font-size:0.7rem;margin-left:4px;">Attenuate</button>
          ${s.error ? html`<div style="color:#b91c1c;font-size:0.65rem;">${s.error}</div>` : null}
        </div>
      ` : html`<div style="font-size:0.65rem;color:var(--fg-dim);margin-top:4px;">awaiting first-class held-token attenuation runtime API</div>`;

      return html`
        <div class="dregg-inspector dregg-inspector--attoken">
          <header>
            <span class="dregg-inspector__kind">attenuated-token</span>
            <code class="dregg-inspector__id" title=${tok.root_token || ''}>${shortHex(tok.root_token || 'n/a', 20)}</code>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>root</dt><dd><code title=${tok.root_token}>${shortHex(tok.root_token || '', 24)}</code></dd>
            <dt>depth</dt><dd>${String(chain.length)}</dd>
          </dl>
          ${chainView}
          ${form}
          <div style="font-size:0.65rem;color:var(--fg-dim);margin-top:4px;">
            Attenuations are monotonic (token crate). Restrictions become caveats in cell-programs / bearer flows.
            Full list_held_tokens pending first-class wasm export (see cipherclerk TODO).
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm || mode !== 'lab') return;
      if (btn.dataset.act === 'attenuate') {
        try {
          const restrictStr = root.querySelector('#at-restrict')?.value?.trim() || '{}';
          let restrictions = {};
          try { restrictions = JSON.parse(restrictStr); } catch {}
          const attenuate = wasm.cipherclerk_attenuate || wasm.attenuate_token;
          if (!attenuate) throw new Error('attenuation wasm export is not available');
          attenuate(0, restrictions);
          viewState.value = { ...viewState.value, error: null };
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) {
          viewState.value = { ...viewState.value, error: String(err) };
        }
      }
    });
  }
}
if (!customElements.get('dregg-attenuated-token')) customElements.define('dregg-attenuated-token', DreggAttenuatedToken);

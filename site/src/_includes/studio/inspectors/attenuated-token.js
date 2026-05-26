/**
 * <pyana-attenuated-token uri="pyana://attenuated-token/<id-hex>" data="...">
 *
 * Token chain: each attenuation step + restrictions (caveats).
 * Can drill into DelegatedToken envelope.
 *
 * Canonical: cipherclerk.attenuate, HeldToken (token crate macaroon/biscuit backends
 * + pyana_caveats). Replaces playground bearer/attenuated bits.
 *
 * URI: pyana://attenuated-token/<token-id or root>
 * data=: JSON { root_token, chain: [{attenuator, restrictions, ...}] , ... }
 *
 * Modes: compact | default | demo (interactive attenuate)
 *
 * Platform vocabulary: reuses <pyana-bearer-cap> concepts, <pyana-caveat> future.
 * No JS reimpl of macaroon/biscuit crypto — delegates to wasm.
 * Visible gap if no direct list_held_tokens binding yet (TODO in cipherclerk).
 *
 * Per STARBRIDGE-PLAN §4.5 + token/README.md + STORAGE cell-programs.
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaAttenuatedToken extends InspectorBase {
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
      if (renderParseError(this, refAttr, parsed, 'attenuated-token')) return;
      data = { root_token: parsed.id, chain: [] };
    }

    const root = document.createElement('div');
    this.appendChild(root);

    // Demo state for interactive attenuation (no crypto in JS)
    const demoState = signal({ lastAttenuated: null, chain: [], error: null });

    const Component = () => {
      const s = demoState.value;
      const tok = data || s.lastAttenuated || { root_token: (parsed && parsed.id) || 'demo-root', chain: s.chain || [] };

      if (mode === 'compact') {
        const len = (tok.chain || []).length;
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <span class="pyana-inspector__kind">attenuated-token</span>
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

      const form = (caps.mutate && wasm) ? html`
        <div style="border-top:1px solid var(--line);margin-top:8px;padding-top:6px;font-size:0.75rem;">
          <div><strong>Demo attenuate (uses wasm token backend if exposed)</strong></div>
          <input id="at-restrict" placeholder='e.g. {"kind":"time","until":123456}' style="width:260px;font-family:var(--mono);font-size:0.7rem;" />
          <button data-act="attenuate" style="font-size:0.7rem;margin-left:4px;">Attenuate</button>
          ${s.error ? html`<div style="color:#b91c1c;font-size:0.65rem;">${s.error}</div>` : null}
        </div>
      ` : null;

      return html`
        <div class="pyana-inspector pyana-inspector--attoken">
          <header>
            <span class="pyana-inspector__kind">attenuated-token</span>
            <code class="pyana-inspector__id" title=${tok.root_token || ''}>${shortHex(tok.root_token || 'n/a', 20)}</code>
          </header>
          <dl class="pyana-inspector__kv">
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
      if (!btn || !wasm) return;
      if (btn.dataset.act === 'attenuate') {
        try {
          const restrictStr = root.querySelector('#at-restrict')?.value?.trim() || '{}';
          let restrictions = {};
          try { restrictions = JSON.parse(restrictStr); } catch {}
          // Prefer cipherclerk if present, else token shim (demo only; real via turns)
          const res = (wasm.cipherclerk_attenuate || wasm.attenuate_token || ((h, r) => ({ root: h, chain: [r] })))( /* handle? */ 0, restrictions);
          const newChain = [...(demoState.value.chain || []), { attenuator: 'demo', restrictions }];
          demoState.value = { ...demoState.value, lastAttenuated: { root_token: (data && data.root_token) || 'demo', chain: newChain }, chain: newChain, error: null };
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) {
          demoState.value = { ...demoState.value, error: String(err) };
        }
      }
    });
  }
}
if (!customElements.get('pyana-attenuated-token')) customElements.define('pyana-attenuated-token', PyanaAttenuatedToken);

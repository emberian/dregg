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
import { InspectorBase, emptyState, renderParseError, shortHex } from './_base.js';

function asList(value) {
  if (!value) return [];
  return Array.isArray(value) ? value : [value];
}

function tokenId(tok, parsed) {
  return tok?.token || tok?.encoded || tok?.root_token || tok?.token_id || parsed?.id || '';
}

function caveatsFor(step) {
  return asList(step?.restrictions || step?.caveats || step?.services || step?.actions);
}

function caveatLabel(caveat) {
  if (typeof caveat === 'string') return caveat;
  if (!caveat || typeof caveat !== 'object') return String(caveat ?? 'empty');
  if (caveat.kind) return `${caveat.kind}${caveat.until ? ` until ${caveat.until}` : ''}`;
  if (caveat.service) return `${caveat.service}${caveat.actions ? `:${caveat.actions}` : ''}`;
  return Object.entries(caveat).map(([k, v]) => `${k}=${Array.isArray(v) ? v.join(',') : String(v)}`).join(', ');
}

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
        return emptyState(
          html,
          'Token data not available',
          html`Held-token lookup is not exposed by this runtime yet${parsed ? html`; requested <code>${shortHex(parsed.id, 16)}</code>` : ''}.`,
        );
      }

      if (mode === 'compact') {
        const len = (tok.chain || []).length;
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <span class="dregg-inspector__kind">attenuated-token</span>
            <code title=${tokenId(tok, parsed)}>${shortHex(tokenId(tok, parsed), 10)}</code>
            ${len ? html`· ${len} attenuation${len === 1 ? '' : 's'}` : ''}
          </span>`;
      }

      const chain = tok.chain || [];
      const rootToken = tokenId(tok, parsed);
      const service = tok.service || tok.audience || '';
      const actionSet = asList(tok.actions || tok.allowed_actions).join(', ') || 'unspecified';
      const restrictionCount = chain.reduce((n, step) => n + caveatsFor(step).length, 0);
      const chainView = chain.length
        ? html`
          <div class="dregg-inspector__notice">
            <strong>Attenuation chain</strong>
            <ol>
              ${chain.map((step, i) => html`
                <li>
                  <code title=${step.attenuator || step.by || ''}>${shortHex(step.attenuator || step.by || `step-${i + 1}`, 12)}</code>
                  ${caveatsFor(step).length
                    ? html`limits ${caveatsFor(step).map(c => html`<code>${caveatLabel(c)}</code> `)}`
                    : html`<span class="dregg-inspector__meta">no caveats surfaced</span>`}
                </li>
              `)}
            </ol>
          </div>`
        : html`<div class="dregg-inspector__notice dregg-inspector__notice--ok">Root token: no attenuation steps are surfaced.</div>`;

      const attenuateAvailable = mode === 'lab' && caps.mutate && wasm && wasm.attenuate_token && rootToken;
      const form = attenuateAvailable ? html`
        <div class="dregg-inspector__controls">
          <input class="dregg-inspector__input" id="at-root-key" placeholder="32-byte root key hex" />
          <input class="dregg-inspector__input" id="at-service" placeholder="service" value=${service} />
          <input class="dregg-inspector__input" id="at-actions" placeholder="actions: read,write" value=${actionSet === 'unspecified' ? '' : actionSet} />
          <input class="dregg-inspector__input" id="at-exp" placeholder="expires secs" value="0" />
          <button class="dregg-inspector__button" data-act="attenuate">Attenuate via wasm</button>
          ${s.error ? html`<div class="dregg-inspector__notice dregg-inspector__notice--warn">${s.error}</div>` : null}
          ${s.last ? html`<div class="dregg-inspector__notice dregg-inspector__notice--ok">Created <code title=${s.last.token || ''}>${shortHex(s.last.token || '', 20)}</code></div>` : null}
        </div>
      ` : html`<div class="dregg-inspector__notice">Interactive attenuation needs lab mode, mutation access, token data, and the canonical <code>attenuate_token</code> wasm export.</div>`;

      return html`
        <div class="dregg-inspector dregg-inspector--attoken">
          <header>
            <span class="dregg-inspector__kind">attenuated-token</span>
            <code class="dregg-inspector__id" title=${rootToken}>${shortHex(rootToken || 'n/a', 20)}</code>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>depth</span><strong>${String(chain.length)}</strong></div>
            <div><span>caveats</span><strong>${String(restrictionCount)}</strong></div>
            <div><span>actions</span><strong title=${actionSet}>${actionSet}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            <dt>token</dt><dd><code title=${rootToken}>${shortHex(rootToken || '', 24)}</code></dd>
            <dt>service</dt><dd>${service ? html`<code>${service}</code>` : html`<span class="dregg-inspector__meta">unspecified</span>`}</dd>
            <dt>depth</dt><dd>${String(chain.length)}</dd>
          </dl>
          ${chainView}
          ${form}
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm || mode !== 'lab') return;
      if (btn.dataset.act === 'attenuate') {
        try {
          const keyHex = root.querySelector('#at-root-key')?.value?.trim() || '';
          const service = root.querySelector('#at-service')?.value?.trim() || '';
          const actions = root.querySelector('#at-actions')?.value?.trim() || '';
          const expires = parseInt(root.querySelector('#at-exp')?.value?.trim() || '0', 10) || 0;
          if (!/^[0-9a-fA-F]{64}$/.test(keyHex)) throw new Error('root key must be 32 bytes of hex');
          const key = new Uint8Array(keyHex.match(/../g).map(b => parseInt(b, 16)));
          const res = wasm.attenuate_token(tokenId(data, parsed), key, service, actions, expires);
          viewState.value = { ...viewState.value, last: res, error: null };
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) {
          viewState.value = { ...viewState.value, error: String(err) };
        }
      }
    });
  }
}
if (!customElements.get('dregg-attenuated-token')) customElements.define('dregg-attenuated-token', DreggAttenuatedToken);

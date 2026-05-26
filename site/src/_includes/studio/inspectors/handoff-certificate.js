/**
 * <dregg-handoff-certificate uri="dregg://handoff-certificate/<nonce-hex>" data="...">
 *
 * Compact dregg-handoff:<base58> form + structured view of HandoffCertSummary + fields.
 * From dregg_captp::handoff::HandoffCertificate surfaced via Authorization::CapTpDelivered.
 *
 * Composes inside <dregg-authorization> (CapTpDelivered variant).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggHandoffCertificate extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    let data = null;
    if (dataAttr) {
      try { data = JSON.parse(dataAttr); } catch {}
    }
    if (!data && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'handoff-certificate')) return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (!data) {
        return html`
          <div class="dregg-inspector dregg-inspector--empty">
            handoff certificate data not available${parsed ? html`: <code>${shortHex(parsed.id, 16)}</code>` : ''};
            awaiting runtime/wasm binding for full <code>HandoffCertificate</code> lookup.
          </div>`;
      }
      const cert = data.handoff_cert_summary || data; // support both shapes

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <span class="dregg-inspector__kind">handoff</span>
            <code title=${cert.nonce || ''}>${shortHex(cert.nonce || cert.recipient_pk || '', 8)}</code>
          </span>`;
      }

      return html`
        <div class="dregg-inspector dregg-inspector--handoff">
          <header>
            <span class="dregg-inspector__kind">handoff-certificate</span>
            <code class="dregg-inspector__id" title=${cert.nonce || ''}>${shortHex(cert.nonce || 'n/a', 16)}</code>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>introducer federation</dt><dd><code title=${cert.introducer_federation}>${shortHex(cert.introducer_federation, 16)}</code></dd>
            <dt>recipient pk</dt><dd><code title=${cert.recipient_pk}>${shortHex(cert.recipient_pk, 16)}</code></dd>
            <dt>nonce</dt><dd><code title=${cert.nonce}>${shortHex(cert.nonce, 16)}</code></dd>
            ${cert.introducer_pk ? html`<dt>introducer pk</dt><dd><code>${shortHex(cert.introducer_pk, 12)}</code></dd>` : ''}
          </dl>
          <div style="font-size:0.7rem;color:var(--fg-dim);">
            HandoffCertificate enables 3-party CapTP handoff (introducer → recipient). See Authorization::CapTpDelivered + dregg_captp handoff.
            Paste-friendly compact form: dregg-handoff:... (summary only; full cert oversized by design).
          </div>
          <div style="font-size:0.6rem;color:#888;margin-top:2px;">Full cert fields beyond the summary are shown only when supplied by runtime data.</div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-handoff-certificate')) customElements.define('dregg-handoff-certificate', DreggHandoffCertificate);

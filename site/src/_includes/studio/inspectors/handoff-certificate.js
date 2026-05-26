/**
 * <pyana-handoff-certificate uri="pyana://handoff-certificate/<nonce-hex>" data="...">
 *
 * Compact pyana-handoff:<base58> form + structured view of HandoffCertSummary + fields.
 * From pyana_captp::handoff::HandoffCertificate surfaced via Authorization::CapTpDelivered.
 *
 * Composes inside <pyana-authorization> (CapTpDelivered variant).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaHandoffCertificate extends InspectorBase {
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
      // For uri-only, show placeholder or expect data; real fetch not in bindings yet.
      data = { nonce: parsed.id, introducer_federation: 'unknown', recipient_pk: 'unknown' };
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (!data) {
        return html`<div class="pyana-inspector pyana-inspector--empty">no handoff cert data</div>`;
      }
      const cert = data.handoff_cert_summary || data; // support both shapes

      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <span class="pyana-inspector__kind">handoff</span>
            <code title=${cert.nonce || ''}>${shortHex(cert.nonce || cert.recipient_pk || '', 8)}</code>
          </span>`;
      }

      return html`
        <div class="pyana-inspector pyana-inspector--handoff">
          <header>
            <span class="pyana-inspector__kind">handoff-certificate</span>
            <code class="pyana-inspector__id" title=${cert.nonce || ''}>${shortHex(cert.nonce || 'n/a', 16)}</code>
          </header>
          <dl class="pyana-inspector__kv">
            <dt>introducer federation</dt><dd><code title=${cert.introducer_federation}>${shortHex(cert.introducer_federation, 16)}</code></dd>
            <dt>recipient pk</dt><dd><code title=${cert.recipient_pk}>${shortHex(cert.recipient_pk, 16)}</code></dd>
            <dt>nonce</dt><dd><code title=${cert.nonce}>${shortHex(cert.nonce, 16)}</code></dd>
          </dl>
          <div style="font-size:0.7rem;color:var(--fg-dim);">
            HandoffCertificate enables 3-party CapTP handoff (introducer → recipient). See Authorization::CapTpDelivered + pyana_captp handoff.
            Paste-friendly compact form: pyana-handoff:...
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('pyana-handoff-certificate')) customElements.define('pyana-handoff-certificate', PyanaHandoffCertificate);

/**
 * <dregg-handoff-certificate uri="dregg://handoff-certificate/<nonce-hex>" data="...">
 *
 * Compact dregg-handoff:<base58> form + structured view of HandoffCertSummary + fields.
 * From dregg_captp::handoff::HandoffCertificate surfaced via Authorization::CapTpDelivered.
 *
 * Composes inside <dregg-authorization> (CapTpDelivered variant).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex, emptyState } from './_base.js';

function compact(value, max = 180) {
  if (value == null || value === '') return '';
  const s = typeof value === 'string' ? value : JSON.stringify(value);
  return s.length > max ? s.slice(0, max) + '…' : s;
}

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
    let parseError = null;
    if (dataAttr) {
      try { data = JSON.parse(dataAttr); } catch (e) { parseError = e; }
    }
    if (!data && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'handoff-certificate')) return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (!data) {
        if (parseError) {
          return html`<div class="dregg-inspector dregg-inspector--err">bad handoff certificate data JSON: ${parseError.message}</div>`;
        }
        return emptyState(
          html,
          'Handoff certificate unavailable',
          parsed
            ? html`The URI parsed as <code>${shortHex(parsed.id, 16)}</code>, but this runtime cannot look up the full certificate. Supply <code>data</code> with a <code>handoff_cert_summary</code> or certificate object to inspect the handoff.`
            : html`Supply <code>data</code> with a <code>handoff_cert_summary</code> or certificate object to inspect the handoff.`
        );
      }
      const cert = data.handoff_cert_summary || data; // support both shapes
      const signatures = Array.isArray(cert.signatures) ? cert.signatures : Array.isArray(data.signatures) ? data.signatures : [];
      const expiry = cert.expires_at || cert.expiry || cert.not_after;
      const issued = cert.issued_at || cert.not_before;
      const status = cert.status || (expiry ? 'time-bound' : 'summary');

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
            <span class="dregg-inspector__pill">${status}</span>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>introducer federation</dt><dd>${cert.introducer_federation ? html`<code title=${cert.introducer_federation}>${shortHex(cert.introducer_federation, 16)}</code>` : html`<span class="dregg-inspector__meta">not supplied</span>`}</dd>
            <dt>recipient pk</dt><dd>${cert.recipient_pk ? html`<code title=${cert.recipient_pk}>${shortHex(cert.recipient_pk, 16)}</code>` : html`<span class="dregg-inspector__meta">not supplied</span>`}</dd>
            <dt>nonce</dt><dd>${cert.nonce ? html`<code title=${cert.nonce}>${shortHex(cert.nonce, 16)}</code>` : html`<span class="dregg-inspector__meta">not supplied</span>`}</dd>
            ${cert.introducer_pk ? html`<dt>introducer pk</dt><dd><code title=${cert.introducer_pk}>${shortHex(cert.introducer_pk, 16)}</code></dd>` : ''}
            ${issued ? html`<dt>issued</dt><dd>${issued}</dd>` : null}
            ${expiry ? html`<dt>expires</dt><dd>${expiry}</dd>` : null}
            <dt>signatures</dt><dd>${signatures.length}</dd>
          </dl>
          ${signatures.length ? html`
            <details class="dregg-inspector__section">
              <summary>Signature material</summary>
              <div class="dregg-inspector__section-body">
                <ul class="dregg-inspector__list">
                  ${signatures.map((sig, i) => html`<li><code>${compact(sig, 160)}</code></li>`)}
                </ul>
              </div>
            </details>` : null}
          <details class="dregg-inspector__section">
            <summary>Supplied certificate fields</summary>
            <div class="dregg-inspector__section-body"><code>${compact(cert, 900)}</code></div>
          </details>
          <div class="dregg-inspector__note">CapTP handoff summary. Verification and oversized full-certificate retrieval remain runtime responsibilities; this inspector only displays fields supplied by the caller.</div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-handoff-certificate')) customElements.define('dregg-handoff-certificate', DreggHandoffCertificate);

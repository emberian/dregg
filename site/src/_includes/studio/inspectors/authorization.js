/**
 * <dregg-authorization> — per-action authorization inspector.
 *
 * Attribute contract:
 *   data  — JSON-stringified AuthorizationView (required)
 *   mode  — "compact" | "default" (default: "compact")
 *
 * AuthorizationView shape (from wasm/src/bindings.rs, Refactor 3):
 *   { kind: "Signature",        r, s }
 *   { kind: "Proof",            bound_action, bound_resource, proof_bytes_len }
 *   { kind: "Breadstuff",       token_hash }
 *   { kind: "Bearer",           target, expires_at, delegation_kind }
 *   { kind: "Unchecked" }
 *   { kind: "CapTpDelivered",   introducer_pk, sender_pk, sender_signature,
 *                                handoff_cert_summary:
 *                                  { introducer_federation, recipient_pk, nonce } }
 *   { kind: "Custom",           predicate_kind, commitment, input_ref,
 *                                proof_witness_index }
 *   { kind: "OneOf",            num_candidates, proof_index }
 *
 * No runtime lookup is needed — data is passed in directly as a JSON attr.
 * This lets receipt.js / turn.js embed it inline without a dregg:// URI.
 *
 * Compact mode: colored badge showing the variant kind.
 * Default mode: KV grid with all fields for the variant.
 */

import { InspectorBase, dreggCodeLink, emptyState, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Color palette for authorization kinds
// ---------------------------------------------------------------------------
const KIND_COLORS = {
  Signature:      { bg: '#d1fae5', fg: '#065f46', border: '#6ee7b7' }, // green
  Proof:          { bg: '#dbeafe', fg: '#1e40af', border: '#93c5fd' }, // blue
  Breadstuff:     { bg: '#ede9fe', fg: '#5b21b6', border: '#c4b5fd' }, // violet
  Bearer:         { bg: '#fef3c7', fg: '#92400e', border: '#fcd34d' }, // yellow
  Unchecked:      { bg: '#fef9c3', fg: '#713f12', border: '#fde68a' }, // amber
  CapTpDelivered: { bg: '#e0f2fe', fg: '#075985', border: '#7dd3fc' }, // sky blue
  Custom:         { bg: '#fce7f3', fg: '#9d174d', border: '#f9a8d4' }, // pink
  OneOf:          { bg: '#f3f4f6', fg: '#1f2937', border: '#d1d5db' }, // gray
};

function kindStyle(kind) {
  const c = KIND_COLORS[kind] || KIND_COLORS.OneOf;
  return `background:${c.bg};color:${c.fg};border:1px solid ${c.border};` +
    `border-radius:3px;padding:1px 6px;font-size:0.8em;font-weight:600;white-space:nowrap;`;
}

// ---------------------------------------------------------------------------
// KV rows per variant (default mode)
// ---------------------------------------------------------------------------
function variantRows(auth, html) {
  const { kind } = auth;

  if (kind === 'Signature') {
    return html`
      <dt>r</dt><dd><code title=${auth.r}>${shortHex(auth.r, 16)}</code></dd>
      <dt>s</dt><dd><code title=${auth.s}>${shortHex(auth.s, 16)}</code></dd>
    `;
  }

  if (kind === 'Proof') {
    return html`
      <dt>bound action</dt><dd><code title=${auth.bound_action}>${shortHex(auth.bound_action, 16)}</code></dd>
      <dt>bound resource</dt><dd><code title=${auth.bound_resource}>${shortHex(auth.bound_resource, 16)}</code></dd>
      <dt>proof size</dt><dd>${String(auth.proof_bytes_len)} bytes</dd>
    `;
  }

  if (kind === 'Breadstuff') {
    return html`
      <dt>token hash</dt><dd><code title=${auth.token_hash}>${shortHex(auth.token_hash, 24)}</code></dd>
    `;
  }

  if (kind === 'Bearer') {
    return html`
      <dt>target</dt><dd>${auth.target ? dreggCodeLink(html, `dregg://cell/${auth.target}`, shortHex(auth.target, 24), auth.target) : html`<span class="dregg-inspector__meta">unavailable</span>`}</dd>
      <dt>expires at</dt><dd>${String(auth.expires_at)}</dd>
      <dt>delegation kind</dt><dd><code>${auth.delegation_kind}</code></dd>
    `;
  }

  if (kind === 'Unchecked') {
    return html`<dt>note</dt><dd>no authorization (sim / unchecked)</dd>`;
  }

  if (kind === 'CapTpDelivered') {
    const cert = auth.handoff_cert_summary || {};
    const certData = JSON.stringify({ handoff_cert_summary: cert });
    return html`
      <dt>introducer pk</dt><dd><code title=${auth.introducer_pk}>${shortHex(auth.introducer_pk, 16)}</code></dd>
      <dt>sender pk</dt><dd><code title=${auth.sender_pk}>${shortHex(auth.sender_pk, 16)}</code></dd>
      <dt>sender sig</dt><dd><code title=${auth.sender_signature}>${shortHex(auth.sender_signature, 16)}</code></dd>
      <dt>cert</dt><dd><dregg-handoff-certificate data=${certData} mode="compact"></dregg-handoff-certificate></dd>
    `;
  }

  if (kind === 'Custom') {
    return html`
      <dt>predicate kind</dt><dd><code>${auth.predicate_kind}</code></dd>
      <dt>commitment</dt><dd><code title=${auth.commitment}>${shortHex(auth.commitment, 16)}</code></dd>
      <dt>input ref</dt><dd>${typeof auth.input_ref === 'string' && auth.input_ref.startsWith('dregg://') ? dreggCodeLink(html, auth.input_ref, auth.input_ref) : html`<code>${auth.input_ref || 'n/a'}</code>`}</dd>
      <dt>proof witness idx</dt><dd>${String(auth.proof_witness_index)}</dd>
    `;
  }

  if (kind === 'OneOf') {
    return html`
      <dt>candidates</dt><dd>${String(auth.num_candidates)}</dd>
      <dt>proof index</dt><dd>${String(auth.proof_index)}</dd>
    `;
  }

  const keys = Object.keys(auth).filter(k => k !== 'kind');
  return html`
    <dt>fields</dt><dd>${keys.length ? keys.map(k => html`<code>${k}</code> `) : html`<span class="dregg-inspector__meta">none</span>`}</dd>
    <dt>note</dt><dd>Unknown authorization variant surfaced by runtime.</dd>
  `;
}

function variantSummary(auth) {
  switch (auth.kind) {
    case 'Signature': return { primary: 'signature', detail: auth.r && auth.s ? 'r/s present' : 'missing component', risk: 'direct signer proof' };
    case 'Proof': return { primary: 'zk proof', detail: `${auth.proof_bytes_len || 0} bytes`, risk: 'bound to action/resource' };
    case 'Breadstuff': return { primary: 'breadstuff', detail: shortHex(auth.token_hash || '', 12), risk: 'token hash auth' };
    case 'Bearer': return { primary: 'bearer', detail: auth.delegation_kind || 'delegation', risk: Number(auth.expires_at || 0) ? 'expires' : 'no expiry surfaced' };
    case 'Unchecked': return { primary: 'unchecked', detail: 'no proof', risk: 'simulation only' };
    case 'CapTpDelivered': return { primary: 'captp', detail: auth.handoff_cert_summary ? 'handoff cert' : 'no cert summary', risk: 'delivered authority' };
    case 'Custom': return { primary: 'custom', detail: auth.predicate_kind || 'predicate', risk: auth.proof_witness_index != null ? 'witnessed' : 'unwitnessed' };
    case 'OneOf': return { primary: 'one-of', detail: `${auth.num_candidates || 0} candidates`, risk: auth.proof_index != null ? `index ${auth.proof_index}` : 'no selected proof' };
    default: return { primary: auth.kind || 'unknown', detail: `${Object.keys(auth).length} fields`, risk: 'unknown variant' };
  }
}

// ---------------------------------------------------------------------------
// Custom element
// ---------------------------------------------------------------------------

class DreggAuthorization extends InspectorBase {
  static get observedAttributes() { return ['data', 'mode']; }

  _render() {
    const { h, render, html, effect } = this._api;
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'compact';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    // Parse the data attribute — no runtime lookup needed.
    let auth = null;
    try {
      auth = dataAttr ? JSON.parse(dataAttr) : null;
    } catch (e) {
      this.innerHTML = `<div class="dregg-inspector dregg-inspector--err">dregg-authorization: bad data attr: ${e.message}</div>`;
      return;
    }
    if (!auth || typeof auth.kind !== 'string') {
      this.replaceChildren();
      const root = document.createElement('div');
      this.appendChild(root);
      this._dispose = effect(() => render(emptyState(html, 'Authorization missing', html`No authorization variant was provided in the <code>data</code> attribute.`), root));
      return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const summary = variantSummary(auth);
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact dregg-authorization--badge"
                style=${kindStyle(auth.kind)}>
            ${auth.kind}${summary.detail ? html` · ${summary.detail}` : ''}
          </span>`;
      }

      // Default: header + KV grid
      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-authorization">
          <header>
            <span class="dregg-inspector__kind">authorization</span>
            <span class="dregg-authorization--badge" style=${kindStyle(auth.kind)}>${auth.kind}</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>variant</span><strong>${summary.primary}</strong></div>
            <div><span>detail</span><strong title=${summary.detail}>${summary.detail}</strong></div>
            <div><span>interpretation</span><strong title=${summary.risk}>${summary.risk}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            ${variantRows(auth, html)}
          </dl>
        </div>`;
    };

    // DreggAuthorization doesn't consume a runtime signal — auth is static
    // from the data attr. We still wrap in effect() to match the base pattern
    // and enable teardown; the effect doesn't subscribe to any signal so it
    // only runs once.
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('dregg-authorization')) {
  customElements.define('dregg-authorization', DreggAuthorization);
}

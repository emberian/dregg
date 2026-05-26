/**
 * <pyana-authorization> — per-action authorization inspector.
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
 * This lets receipt.js / turn.js embed it inline without a pyana:// URI.
 *
 * Compact mode: colored badge showing the variant kind.
 * Default mode: KV grid with all fields for the variant.
 */

import { InspectorBase, shortHex } from './_base.js';

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
      <dt>target</dt><dd><code title=${auth.target}>${shortHex(auth.target, 24)}</code></dd>
      <dt>expires at</dt><dd>${String(auth.expires_at)}</dd>
      <dt>delegation kind</dt><dd><code>${auth.delegation_kind}</code></dd>
    `;
  }

  if (kind === 'Unchecked') {
    return html`<dt>note</dt><dd>no authorization (sim / unchecked)</dd>`;
  }

  if (kind === 'CapTpDelivered') {
    const cert = auth.handoff_cert_summary || {};
    return html`
      <dt>introducer pk</dt><dd><code title=${auth.introducer_pk}>${shortHex(auth.introducer_pk, 16)}</code></dd>
      <dt>sender pk</dt><dd><code title=${auth.sender_pk}>${shortHex(auth.sender_pk, 16)}</code></dd>
      <dt>sender sig</dt><dd><code title=${auth.sender_signature}>${shortHex(auth.sender_signature, 16)}</code></dd>
      <dt>cert: introducer fed</dt><dd><code title=${cert.introducer_federation}>${shortHex(cert.introducer_federation, 16)}</code></dd>
      <dt>cert: recipient pk</dt><dd><code title=${cert.recipient_pk}>${shortHex(cert.recipient_pk, 16)}</code></dd>
      <dt>cert: nonce</dt><dd><code title=${cert.nonce}>${shortHex(cert.nonce, 16)}</code></dd>
    `;
  }

  if (kind === 'Custom') {
    return html`
      <dt>predicate kind</dt><dd><code>${auth.predicate_kind}</code></dd>
      <dt>commitment</dt><dd><code title=${auth.commitment}>${shortHex(auth.commitment, 16)}</code></dd>
      <dt>input ref</dt><dd><code>${auth.input_ref}</code></dd>
      <dt>proof witness idx</dt><dd>${String(auth.proof_witness_index)}</dd>
    `;
  }

  if (kind === 'OneOf') {
    return html`
      <dt>candidates</dt><dd>${String(auth.num_candidates)}</dd>
      <dt>proof index</dt><dd>${String(auth.proof_index)}</dd>
    `;
  }

  // Unknown variant — dump raw JSON
  return html`<dt>raw</dt><dd><code>${JSON.stringify(auth)}</code></dd>`;
}

// ---------------------------------------------------------------------------
// Custom element
// ---------------------------------------------------------------------------

class PyanaAuthorization extends InspectorBase {
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
      auth = JSON.parse(dataAttr);
    } catch (e) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">pyana-authorization: bad data attr: ${e.message}</div>`;
      return;
    }
    if (!auth || typeof auth.kind !== 'string') {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">pyana-authorization: data missing "kind" field</div>`;
      return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact pyana-authorization--badge"
                style=${kindStyle(auth.kind)}>
            ${auth.kind}
          </span>`;
      }

      // Default: header + KV grid
      return html`
        <div class="pyana-inspector pyana-inspector--cell pyana-authorization">
          <header>
            <span class="pyana-inspector__kind">authorization</span>
            <span class="pyana-authorization--badge" style=${kindStyle(auth.kind)}>${auth.kind}</span>
          </header>
          <dl class="pyana-inspector__kv">
            ${variantRows(auth, html)}
          </dl>
        </div>`;
    };

    // PyanaAuthorization doesn't consume a runtime signal — auth is static
    // from the data attr. We still wrap in effect() to match the base pattern
    // and enable teardown; the effect doesn't subscribe to any signal so it
    // only runs once.
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('pyana-authorization')) {
  customElements.define('pyana-authorization', PyanaAuthorization);
}

// starbridge-apps/shared/inspectors/index.js
//
// Inspector registry for starbridge-apps. Each app contributes its
// domain inspectors (web components published as ES modules — see
// site/STUDIO.md §6) and registers them via `window.pyana.register`.
//
// This module also publishes two cross-app primitive components:
//
//   <pyana-token-cap>  — visual representation of a capability /
//                        receipt token. Renders the cap's target,
//                        action, expiry, and tag bytes as a tangible
//                        artifact. Used by every app's success-state.
//
//   <pyana-status-bar> — inline loading / error / success status bar.
//                        Apps drive it via `setAttribute('state', ...)`
//                        with one of `idle | loading | error | success`.
//
// Both elements are namespaced under `.pyana-shared-*` so they don't
// collide with per-app styles.

// =========================================================================
// <pyana-token-cap>
// =========================================================================
//
// Tangible visual representation of a capability. Attributes:
//   target  — pyana://cell/... URI
//   action  — string method/topic the cap authorizes
//   expiry  — u64 block height (or epoch); 0 / unset == "no expiry"
//   tag     — short hex of the cap-bytes (for visual fingerprint)
//   issuer  — short hex of the issuer pk
//   kind    — "bearer" | "delegated" | "receipt"  (default "receipt")
//
// Apps that hand a cap or receipt back from a turn render
// <pyana-token-cap ...> as the success badge.

class PyanaTokenCapElement extends HTMLElement {
  static get observedAttributes() {
    return ['target', 'action', 'expiry', 'tag', 'issuer', 'kind', 'label'];
  }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
  }
  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const target = this.getAttribute('target') || '';
    const action = this.getAttribute('action') || '';
    const expiry = this.getAttribute('expiry') || '';
    const tag    = this.getAttribute('tag') || '';
    const issuer = this.getAttribute('issuer') || '';
    const kind   = (this.getAttribute('kind') || 'receipt').toLowerCase();
    const label  = this.getAttribute('label') || kind.toUpperCase();
    const shortTarget = target.length > 32
      ? `${target.slice(0, 16)}…${target.slice(-8)}`
      : target;
    const shortTag = tag.length > 16 ? `${tag.slice(0, 8)}…${tag.slice(-4)}` : tag;
    const shortIssuer = issuer.length > 16 ? `${issuer.slice(0, 8)}…` : issuer;

    this.shadowRoot.innerHTML = `
      <style>
        :host {
          display: inline-block;
          font-family: ui-monospace, SFMono-Regular, monospace;
        }
        .pyana-shared-cap {
          display: inline-grid;
          grid-template-columns: max-content 1fr;
          gap: 0.1rem 0.6rem;
          padding: 0.55rem 0.8rem;
          border: 1px solid #6b7cff;
          border-radius: 8px;
          background: linear-gradient(135deg, #f3f5ff, #e7ecff);
          box-shadow: 0 1px 0 #fff inset, 0 1px 3px rgba(40, 50, 120, 0.12);
          min-width: 18rem;
          font-size: 0.85rem;
          color: #1a2350;
        }
        .pyana-shared-cap-header {
          grid-column: 1 / -1;
          display: flex;
          align-items: center;
          gap: 0.5rem;
          margin-bottom: 0.35rem;
          padding-bottom: 0.35rem;
          border-bottom: 1px dashed #aab3e8;
        }
        .pyana-shared-cap-kind {
          background: #303a85;
          color: #fff;
          padding: 0.05rem 0.45rem;
          border-radius: 3px;
          font-size: 0.7rem;
          font-weight: 700;
          letter-spacing: 0.06em;
        }
        .pyana-shared-cap-label { font-weight: 600; }
        .pyana-shared-cap-key   { color: #50609e; font-size: 0.75rem; }
        .pyana-shared-cap-val   { word-break: break-all; }
        .pyana-shared-cap-tag   {
          font-size: 0.78rem;
          background: #fff;
          padding: 0.05rem 0.35rem;
          border-radius: 3px;
          border: 1px solid #d0d8f5;
        }
      </style>
      <span class="pyana-shared-cap">
        <span class="pyana-shared-cap-header">
          <span class="pyana-shared-cap-kind">${escapeHtml(kind)}</span>
          <span class="pyana-shared-cap-label">${escapeHtml(label)}</span>
          ${tag ? `<span class="pyana-shared-cap-tag">${escapeHtml(shortTag)}</span>` : ''}
        </span>
        ${target ? `
          <span class="pyana-shared-cap-key">target</span>
          <span class="pyana-shared-cap-val">${escapeHtml(shortTarget)}</span>` : ''}
        ${action ? `
          <span class="pyana-shared-cap-key">action</span>
          <span class="pyana-shared-cap-val">${escapeHtml(action)}</span>` : ''}
        ${issuer ? `
          <span class="pyana-shared-cap-key">issuer</span>
          <span class="pyana-shared-cap-val">${escapeHtml(shortIssuer)}</span>` : ''}
        ${expiry && expiry !== '0' ? `
          <span class="pyana-shared-cap-key">expiry</span>
          <span class="pyana-shared-cap-val">${escapeHtml(expiry)}</span>` : ''}
      </span>
    `;
  }
}

// =========================================================================
// <pyana-status-bar>
// =========================================================================
//
// Inline status bar driven by attributes:
//   state    — idle | loading | error | success
//   message  — text body
//   receipt  — short receipt-hash; if present, rendered as a chip
//
// Used by every app's mutation forms.

class PyanaStatusBarElement extends HTMLElement {
  static get observedAttributes() {
    return ['state', 'message', 'receipt'];
  }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
  }
  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const state = (this.getAttribute('state') || 'idle').toLowerCase();
    const message = this.getAttribute('message') || '';
    const receipt = this.getAttribute('receipt') || '';
    const colors = {
      idle:    { bg: 'transparent', fg: '#666', border: 'transparent' },
      loading: { bg: '#fff8e6',     fg: '#8a5a00', border: '#f0d080' },
      error:   { bg: '#ffecec',     fg: '#a02020', border: '#f0a0a0' },
      success: { bg: '#e8faea',     fg: '#206030', border: '#a0d0a8' },
    }[state] ?? { bg: 'transparent', fg: '#666', border: 'transparent' };

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; }
        .pyana-shared-status {
          display: flex;
          gap: 0.5rem;
          align-items: center;
          min-height: 1.6rem;
          padding: ${state === 'idle' ? '0' : '0.4rem 0.6rem'};
          background: ${colors.bg};
          color: ${colors.fg};
          border: 1px solid ${colors.border};
          border-radius: 4px;
          font: 0.85rem ui-monospace, SFMono-Regular, monospace;
        }
        .pyana-shared-status-spin {
          width: 0.8rem;
          height: 0.8rem;
          border: 2px solid rgba(0,0,0,0.15);
          border-top-color: currentColor;
          border-radius: 50%;
          animation: pyana-shared-spin 0.7s linear infinite;
        }
        @keyframes pyana-shared-spin { to { transform: rotate(360deg); } }
        .pyana-shared-status-receipt {
          margin-left: auto;
          padding: 0.05rem 0.4rem;
          background: rgba(0,0,0,0.06);
          border-radius: 3px;
          font-size: 0.8em;
        }
      </style>
      ${state === 'idle' ? '' : `
        <div class="pyana-shared-status" role="status">
          ${state === 'loading' ? '<span class="pyana-shared-status-spin" aria-hidden="true"></span>' : ''}
          ${state === 'success' ? '<span aria-hidden="true">✓</span>' : ''}
          ${state === 'error'   ? '<span aria-hidden="true">✗</span>' : ''}
          <span>${escapeHtml(message)}</span>
          ${receipt ? `<code class="pyana-shared-status-receipt">${escapeHtml(receipt)}</code>` : ''}
        </div>
      `}
    `;
  }
}

// =========================================================================
// Tiny helpers
// =========================================================================

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

// =========================================================================
// Element registration
// =========================================================================

if (typeof customElements !== 'undefined') {
  if (!customElements.get('pyana-token-cap')) {
    customElements.define('pyana-token-cap', PyanaTokenCapElement);
  }
  if (!customElements.get('pyana-status-bar')) {
    customElements.define('pyana-status-bar', PyanaStatusBarElement);
  }
}

if (typeof window !== 'undefined' && window.pyana?.register) {
  window.pyana.register('pyana-token-cap', PyanaTokenCapElement);
  window.pyana.register('pyana-status-bar', PyanaStatusBarElement);
}

// =========================================================================
// Per-app self-registering imports
// =========================================================================

// Identity inspectors (pages/ for high-quality additional demo; §4.8 FOLLOWUP-05 creep fix).
import('/starbridge-apps/identity/pages/inspectors.js').catch(() => {});

// Subscription inspectors (pages/ for additional demo).
import('/starbridge-apps/subscription/pages/inspectors.js').catch(() => {});

// Nameservice inspectors + turn-builders.
// Canonical per-app inspectors now in shared/ (STARBRIDGE-PLAN §4.8) — reuses
// platform <pyana-cell>, <pyana-capability> etc. Legacy pages/ version kept
// for standalone fragment compatibility.
import('/starbridge-apps/shared/inspectors/name.js').catch(() => {});
import('/starbridge-apps/shared/turn-builders/nameservice.js').catch(() => {});
// Legacy (full form + actions) for /starbridge-apps/nameservice/ standalone page.
import('/starbridge-apps/nameservice/inspectors.js').catch(() => {});
import('/starbridge-apps/nameservice/pages/turn-builders.js').catch(() => {});

// Governed-namespace inspectors + turn-builders (pages/ path fix for §4.8).
import('/starbridge-apps/governed-namespace/pages/inspectors.js').catch(() => {});
import('/starbridge-apps/governed-namespace/pages/turn-builders.js').catch(() => {});

// =========================================================================
// JS-side registry mirror
// =========================================================================

export const registry = {
  // app-name -> { tag-name -> component }
};

export function register(app, tag, component) {
  if (!registry[app]) registry[app] = {};
  registry[app][tag] = component;
  if (typeof window !== 'undefined' && window.pyana?.register) {
    window.pyana.register(tag, component);
  }
}

export { PyanaTokenCapElement, PyanaStatusBarElement, escapeHtml };

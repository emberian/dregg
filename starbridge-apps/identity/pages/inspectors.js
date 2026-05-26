// starbridge-apps/identity/pages/inspectors.js
//
// Web components for the identity starbridge-app's four UI surfaces.
// All policy lives in Rust (starbridge-apps/identity/src/lib.rs); the
// JS is the thinnest possible UX layer.
//
//   <dregg-credential uri="dregg://credential/..."/>
//     Read-only credential view: schema, holder id, status, claim list
//     (the holder's local cleartext copy — public network sees only
//     commitments), expiry countdown, revoke button when the viewer is
//     the issuer.
//
//   <dregg-credential-issue-form issuer-uri="dregg://cell/..." schema="kyc-v1"/>
//     Issuer UI: schema picker, dynamic claim inputs, subject pk,
//     signed-turn submission via the cipherclerk-named
//     `window.dregg.builders.identity.issue_credential(...)` builder.
//
//   <dregg-credential-present-form credential-uri="dregg://credential/..."/>
//     Holder UI: per-claim selective-disclosure checklist, predicate
//     builder ("verification_level Gte 1"), anonymous toggle, emits a
//     signed presentation.
//
//   <dregg-credential-verifier verifier-uri="dregg://cell/..."/>
//     Verifier UI: paste a presentation, configure expectations, see
//     accept/reject + revealed facts.
//
// CSS classes are namespaced .dregg-identity-* so peer apps don't
// collide.

const TAGS = [
  'dregg-credential',
  'dregg-credential-issue-form',
  'dregg-credential-present-form',
  'dregg-credential-verifier',
];

const POLL_INTERVAL_MS = 7_000;

// Slot indices — mirror src/lib.rs.
const SCHEMA_COMMITMENT_SLOT  = 2;
const ISSUANCE_COUNTER_SLOT   = 3;
const REVOCATION_ROOT_SLOT    = 4;
const ISSUER_AUTH_ROOT_SLOT   = 5;

// ─── helpers ─────────────────────────────────────────────────────────────

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

function shortId(s, head = 8, tail = 6) {
  if (!s) return '—';
  const str = String(s);
  if (str.length <= head + tail + 1) return str;
  return `${str.slice(0, head)}…${str.slice(-tail)}`;
}

function fmtTime(v) {
  if (v == null || v === '') return '—';
  if (typeof v === 'number' || /^\d+$/.test(String(v))) {
    // Treat as unix seconds.
    try {
      return new Date(Number(v) * 1000).toISOString().slice(0, 19).replace('T', ' ');
    } catch { return String(v); }
  }
  return String(v);
}

function countdown(toUnix, now = Date.now() / 1000) {
  if (!toUnix) return '';
  const d = Number(toUnix) - now;
  if (d <= 0) return 'expired';
  const days = Math.floor(d / 86_400);
  if (days > 1) return `in ${days}d`;
  const hrs = Math.floor(d / 3_600);
  if (hrs > 1) return `in ${hrs}h`;
  const mins = Math.floor(d / 60);
  return `in ${Math.max(mins, 1)}m`;
}

const SCHEMA_DEFS = {
  'kyc-v1':        ['given_name', 'family_name', 'dob', 'verification_level'],
  'gov-id-v1':     ['id_number', 'country', 'expires_on'],
  'employment-v1': ['employer', 'role', 'start_date'],
};

// ─── <dregg-credential> ──────────────────────────────────────────────────

class DreggCredentialElement extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._data = null;
    this._error = null;
    this._loading = true;
    this._busy = null;
    this._lastReceipt = null;
    this._poll = null;
  }

  connectedCallback() {
    this.refresh();
    this._poll = setInterval(() => this.refresh(), POLL_INTERVAL_MS);
  }
  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
    this._poll = null;
  }
  attributeChangedCallback() { this.refresh(); }

  async refresh() {
    const uri = this.getAttribute('uri') || '';
    try {
      this._data = await this.#fetch(uri);
      this._error = null;
    } catch (e) {
      this._error = String(e);
    }
    this._loading = false;
    this.render();
  }

  render() {
    const uri = this.getAttribute('uri') || '';
    const d = this._data ?? {};
    const revoked = !!d.revoked;
    const attrs = Array.isArray(d.attributes) ? d.attributes : [];
    const expiresCountdown = countdown(d.not_after);

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-identity-credential-card {
          border: 1px solid #ddd;
          border-radius: 6px;
          padding: 1rem;
          background: linear-gradient(180deg, #fff 0%, #fafbff 100%);
          max-width: 480px;
        }
        .dregg-identity-credential-schema {
          font-size: 0.75rem;
          color: #557;
          text-transform: uppercase;
          letter-spacing: 0.08em;
        }
        .dregg-identity-credential-row {
          display: flex;
          justify-content: space-between;
          gap: 0.5rem;
          padding: 0.25rem 0;
        }
        .dregg-identity-credential-label { color: #555; }
        code { font-family: ui-monospace, monospace; }
        .dregg-identity-credential-status-ok  { color: #2a8a3e; font-weight: 600; }
        .dregg-identity-credential-status-bad { color: #c43030; font-weight: 600; }
        .dregg-identity-credential-claims {
          margin-top: 0.6rem;
          border-top: 1px solid #eee;
          padding-top: 0.6rem;
        }
        .dregg-identity-credential-claim {
          display: flex;
          justify-content: space-between;
          gap: 0.5rem;
          padding: 0.2rem 0;
          font-size: 0.9rem;
        }
        .dregg-identity-credential-claim code {
          background: #eef;
          padding: 0.05rem 0.35rem;
          border-radius: 3px;
        }
        .dregg-identity-credential-actions {
          margin-top: 0.6rem;
          display: flex;
          gap: 0.4rem;
        }
        button {
          padding: 0.4rem 0.7rem;
          font: inherit;
          background: #eef;
          border: 1px solid #ccd;
          border-radius: 3px;
          cursor: pointer;
        }
        button[disabled] { opacity: 0.5; cursor: not-allowed; }
        .dregg-identity-credential-error {
          color: #a02020;
          background: #fff0f0;
          padding: 0.5rem;
          border: 1px solid #f0c0c0;
          border-radius: 4px;
        }
      </style>
      <div class="dregg-identity-credential-card">
        ${this._error ? `<div class="dregg-identity-credential-error">${escapeHtml(this._error)}</div>` : ''}
        ${this._loading
          ? `<dregg-status-bar state="loading" message="fetching credential…"></dregg-status-bar>`
          : ''}
        <div class="dregg-identity-credential-schema">${escapeHtml(d.schema || '(no schema)')}</div>
        <h3 style="margin: 0.2rem 0 0.5rem 0;">Credential ${escapeHtml(shortId(d.id || d.id_short || uri))}</h3>
        <div class="dregg-identity-credential-row">
          <span class="dregg-identity-credential-label">Holder</span>
          <code>${escapeHtml(shortId(d.holder_id))}</code>
        </div>
        <div class="dregg-identity-credential-row">
          <span class="dregg-identity-credential-label">Issued</span>
          <span>${escapeHtml(fmtTime(d.issued_at))}</span>
        </div>
        <div class="dregg-identity-credential-row">
          <span class="dregg-identity-credential-label">Expires</span>
          <span>${escapeHtml(fmtTime(d.not_after))}${expiresCountdown ? ` <em>(${escapeHtml(expiresCountdown)})</em>` : ''}</span>
        </div>
        <div class="dregg-identity-credential-row">
          <span class="dregg-identity-credential-label">Status</span>
          <span class="${revoked ? 'dregg-identity-credential-status-bad' : 'dregg-identity-credential-status-ok'}">
            ${revoked ? 'REVOKED' : 'VALID'}
          </span>
        </div>
        ${attrs.length ? `
          <div class="dregg-identity-credential-claims">
            <strong>Claims (${attrs.length})</strong>
            ${attrs.map((a) => `
              <div class="dregg-identity-credential-claim">
                <span>${escapeHtml(a.name)}</span>
                <code>${escapeHtml(a.value ?? '')}</code>
              </div>
            `).join('')}
          </div>
        ` : ''}
        <div class="dregg-identity-credential-actions">
          <button data-action="present" ${revoked ? 'disabled' : ''}>Present…</button>
          <button data-action="revoke" ${revoked ? 'disabled' : ''}>Revoke</button>
          <button data-action="refresh">↻</button>
        </div>
        <dregg-status-bar
          state="${this._busy ? 'loading' : (this._lastReceipt ? 'success' : 'idle')}"
          message="${escapeHtml(this._busy?.message ?? (this._lastReceipt ? 'submitted' : ''))}"
          receipt="${escapeHtml(this._lastReceipt?.id ?? this._lastReceipt?.turnId ?? '')}"
        ></dregg-status-bar>
        ${this._lastReceipt ? `
          <div style="margin-top:0.5rem;">
            <dregg-token-cap
              kind="receipt"
              label="credential-action"
              target="${escapeHtml(uri)}"
              action="${escapeHtml(this._lastReceipt.method || '')}"
              tag="${escapeHtml(this._lastReceipt.id ?? this._lastReceipt.turnId ?? '')}"
            ></dregg-token-cap>
          </div>
        ` : ''}
      </div>
    `;
    this.shadowRoot.querySelector('button[data-action=present]')?.addEventListener('click', () => {
      this.dispatchEvent(new CustomEvent('present-requested', {
        bubbles: true, composed: true, detail: { uri },
      }));
    });
    this.shadowRoot.querySelector('button[data-action=refresh]')?.addEventListener('click', () => {
      this._loading = true;
      this.render();
      this.refresh();
    });
    this.shadowRoot.querySelector('button[data-action=revoke]')?.addEventListener('click', () =>
      this.#onRevoke(uri),
    );
  }

  async #onRevoke(credentialUri) {
    const builder = window.dregg?.builders?.identity?.revoke_credential;
    if (!builder) {
      this.dispatchEvent(new CustomEvent('revoke-requested', {
        bubbles: true, composed: true, detail: { uri: credentialUri },
      }));
      return;
    }
    this._busy = { message: 'revoking credential…' };
    this.render();
    try {
      // Issuer-cell uri is typically the parent factory cell; without
      // host context we look up via a runtime helper, falling back to
      // the credential uri itself (the host will surface an error if
      // that's not the right target).
      const issuerCell = this._data?.issuer_cell_uri || credentialUri;
      const credId = this._data?.id || credentialUri;
      const newRoot = new Array(32).fill(0); // host should override.
      const receipt = await builder(issuerCell, credId, newRoot);
      this._busy = null;
      this._lastReceipt = { ...(receipt ?? {}), method: 'revoke_credential' };
      this.refresh();
    } catch (e) {
      this._busy = null;
      this._error = `revoke failed: ${String(e)}`;
      this.render();
    }
  }

  async #fetch(uri) {
    if (typeof window === 'undefined') return null;
    if (window.dregg?.fetchCredential) {
      return await window.dregg.fetchCredential(uri);
    }
    if (window.dregg?.credentials?.read) {
      return await window.dregg.credentials.read(uri);
    }
    // No runtime helper — return a marker so the UI shows "(no
    // credential)" rather than fake data.
    return null;
  }
}

// ─── <dregg-credential-issue-form> ───────────────────────────────────────

class DreggCredentialIssueFormElement extends HTMLElement {
  static get observedAttributes() { return ['issuer-uri', 'schema']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._busy = null;
    this._lastError = null;
    this._lastReceipt = null;
  }
  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const issuerUri = this.getAttribute('issuer-uri') || '';
    const schemaName = this.getAttribute('schema') || 'kyc-v1';
    const attrs = SCHEMA_DEFS[schemaName] ?? [];

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-identity-issue-form {
          display: grid;
          gap: 0.75rem;
          max-width: 420px;
        }
        .dregg-identity-issue-form label {
          display: grid;
          gap: 0.25rem;
        }
        .dregg-identity-issue-form input,
        .dregg-identity-issue-form select {
          padding: 0.4rem;
          font: inherit;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        .dregg-identity-issue-form button[type=submit] {
          padding: 0.55rem;
          font-weight: 600;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        .dregg-identity-issue-form button[type=submit][disabled] {
          opacity: 0.5; cursor: wait;
        }
        .dregg-identity-issue-form-target {
          font-size: 0.85rem;
          color: #666;
        }
      </style>
      <form class="dregg-identity-issue-form">
        <div class="dregg-identity-issue-form-target">
          Issuer cell: <code>${escapeHtml(issuerUri)}</code>
        </div>
        <label>
          Schema
          <select name="schema">
            ${Object.keys(SCHEMA_DEFS).map((s) => `
              <option value="${s}" ${s === schemaName ? 'selected' : ''}>${s}</option>
            `).join('')}
          </select>
        </label>
        <label>
          Subject (holder cell id / hex pubkey)
          <input name="subject" placeholder="0x…" required />
        </label>
        ${attrs.map((a) => `
          <label>${escapeHtml(a)}<input name="attr_${escapeHtml(a)}" required /></label>
        `).join('')}
        <button type="submit" ${this._busy ? 'disabled' : ''}>
          ${this._busy ? 'issuing…' : 'Issue credential'}
        </button>
      </form>
      <dregg-status-bar
        state="${this._busy ? 'loading' : (this._lastError ? 'error' : (this._lastReceipt ? 'success' : 'idle'))}"
        message="${escapeHtml(this._busy?.message ?? this._lastError ?? (this._lastReceipt ? 'credential issued' : ''))}"
        receipt="${escapeHtml(this._lastReceipt?.id ?? this._lastReceipt?.turnId ?? '')}"
      ></dregg-status-bar>
      ${this._lastReceipt ? `
        <div style="margin-top:0.5rem;">
          <dregg-token-cap
            kind="credential"
            label="${escapeHtml(this._lastReceipt.credential?.schema || schemaName)}"
            target="${escapeHtml(issuerUri)}"
            action="issue_credential"
            tag="${escapeHtml(this._lastReceipt.credential?.id || this._lastReceipt.id || '')}"
            issuer="${escapeHtml(shortId(issuerUri))}"
          ></dregg-token-cap>
        </div>
      ` : ''}
    `;

    this.shadowRoot.querySelector('select[name=schema]')?.addEventListener('change', (e) => {
      this.setAttribute('schema', e.target.value);
    });
    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      const fd = new FormData(e.target);
      const claims = {};
      for (const [k, v] of fd.entries()) {
        if (k.startsWith('attr_')) claims[k.slice(5)] = v;
      }
      this.#issue({
        issuerUri,
        schema: fd.get('schema'),
        subject: fd.get('subject'),
        claims,
      });
    });
  }

  async #issue({ issuerUri, schema, subject, claims }) {
    this._busy = { message: `issuing ${schema} to ${shortId(subject)}…` };
    this._lastError = null;
    this._lastReceipt = null;
    this.render();
    const builder = window.dregg?.builders?.identity?.issue_credential;
    if (!builder) {
      this._busy = null;
      this._lastError = 'no issue_credential builder loaded (check turn-builders.js)';
      this.dispatchEvent(new CustomEvent('issue-requested', {
        bubbles: true, composed: true,
        detail: { issuerUri, schema, subject, claims },
      }));
      this.render();
      return;
    }
    try {
      const receipt = await builder(issuerUri, schema, subject, claims);
      this._busy = null;
      this._lastReceipt = receipt ?? { ok: true };
      this.dispatchEvent(new CustomEvent('credential-issued', {
        bubbles: true, composed: true, detail: { receipt },
      }));
    } catch (e) {
      this._busy = null;
      this._lastError = `issue failed: ${String(e)}`;
    }
    this.render();
  }
}

// ─── <dregg-credential-present-form> ─────────────────────────────────────

class DreggCredentialPresentFormElement extends HTMLElement {
  static get observedAttributes() { return ['credential-uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._credential = null;
    this._loading = true;
    this._busy = null;
    this._lastError = null;
    this._presentation = null;
  }
  connectedCallback() { this.refresh(); }
  attributeChangedCallback() { this.refresh(); }

  async refresh() {
    this._credential = await this.#loadCredential(this.getAttribute('credential-uri') || '');
    this._loading = false;
    this.render();
  }

  render() {
    const credentialUri = this.getAttribute('credential-uri') || '';
    const attrs = this._credential?.attributes ?? [];

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-identity-present-form {
          display: grid;
          gap: 0.75rem;
          max-width: 540px;
        }
        .dregg-identity-present-form fieldset {
          border: 1px solid #ddd;
          border-radius: 4px;
          padding: 0.75rem;
          background: #fafbff;
        }
        .dregg-identity-present-form legend {
          font-weight: 600;
          padding: 0 0.4rem;
        }
        .dregg-identity-present-form-row {
          display: flex;
          gap: 0.5rem;
          align-items: center;
          padding: 0.2rem 0;
        }
        .dregg-identity-present-form-predicate {
          display: grid;
          grid-template-columns: 1fr 80px 1fr;
          gap: 0.4rem;
        }
        .dregg-identity-present-form input,
        .dregg-identity-present-form select {
          padding: 0.4rem;
          font: inherit;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        .dregg-identity-present-form button[type=submit] {
          padding: 0.55rem;
          font-weight: 600;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        .dregg-identity-present-form button[type=submit][disabled] {
          opacity: 0.5; cursor: wait;
        }
        .dregg-identity-present-form-empty {
          color: #888; font-style: italic;
        }
        .dregg-identity-present-form-output {
          margin-top: 0.6rem;
          padding: 0.6rem;
          background: #f7f7fa;
          border: 1px solid #ddd;
          border-radius: 4px;
          font: 0.8rem ui-monospace, monospace;
          max-height: 16rem;
          overflow: auto;
          white-space: pre-wrap;
          word-break: break-all;
        }
      </style>
      <form class="dregg-identity-present-form">
        <div>Credential: <code>${escapeHtml(credentialUri || '(none)')}</code></div>
        ${this._loading
          ? `<dregg-status-bar state="loading" message="loading credential…"></dregg-status-bar>`
          : ''}
        <fieldset>
          <legend>Selective disclosure</legend>
          ${attrs.length === 0
            ? `<div class="dregg-identity-present-form-empty">(no attributes available)</div>`
            : attrs.map((a) => `
              <label class="dregg-identity-present-form-row">
                <input type="checkbox" name="disclose_${escapeHtml(a.name)}" />
                <span>${escapeHtml(a.name)}</span>
                <code style="margin-left:auto">${escapeHtml(a.value ?? '')}</code>
              </label>
            `).join('')}
        </fieldset>
        <fieldset>
          <legend>Predicate (zero-knowledge range proof)</legend>
          <div class="dregg-identity-present-form-predicate">
            <select name="pred_attr">
              <option value="">(no predicate)</option>
              ${attrs.map((a) => `<option value="${escapeHtml(a.name)}">${escapeHtml(a.name)}</option>`).join('')}
            </select>
            <select name="pred_op">
              <option value="Gte">≥</option>
              <option value="Lte">≤</option>
              <option value="Eq">=</option>
            </select>
            <input name="pred_val" type="number" placeholder="value" />
          </div>
        </fieldset>
        <label class="dregg-identity-present-form-row">
          <input type="checkbox" name="anonymous" />
          <span>Anonymous (unlinkable multi-show)</span>
        </label>
        <button type="submit" ${this._busy ? 'disabled' : ''}>
          ${this._busy ? 'generating…' : 'Generate presentation'}
        </button>
      </form>
      <dregg-status-bar
        state="${this._busy ? 'loading' : (this._lastError ? 'error' : (this._presentation ? 'success' : 'idle'))}"
        message="${escapeHtml(this._busy?.message ?? this._lastError ?? (this._presentation ? 'presentation generated' : ''))}"
      ></dregg-status-bar>
      ${this._presentation ? `
        <div class="dregg-identity-present-form-output">${escapeHtml(JSON.stringify(this._presentation, null, 2))}</div>
        <dregg-token-cap
          kind="presentation"
          label="${escapeHtml(this._credential?.schema || 'credential-presentation')}"
          target="${escapeHtml(credentialUri)}"
          action="present_credential"
          tag="${escapeHtml((this._presentation.id || '').toString().slice(0, 16))}"
        ></dregg-token-cap>
      ` : ''}
    `;

    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      const fd = new FormData(e.target);
      const disclose = [];
      for (const [k] of fd.entries()) {
        if (k.startsWith('disclose_')) disclose.push(k.slice(9));
      }
      const predAttr = fd.get('pred_attr');
      const predicates = predAttr ? [{
        attribute: predAttr,
        op: fd.get('pred_op'),
        value: Number(fd.get('pred_val')),
      }] : [];
      this.#present({
        credentialUri,
        disclose,
        predicates,
        anonymous: !!fd.get('anonymous'),
      });
    });
  }

  async #loadCredential(uri) {
    if (typeof window === 'undefined') return null;
    if (window.dregg?.fetchCredential) {
      try { return await window.dregg.fetchCredential(uri); } catch { return null; }
    }
    return null;
  }

  async #present(detail) {
    this._busy = { message: 'generating presentation…' };
    this._lastError = null;
    this._presentation = null;
    this.render();
    const builder = window.dregg?.builders?.identity?.present_credential;
    if (!builder) {
      this._busy = null;
      this._lastError = 'no present_credential builder loaded';
      this.dispatchEvent(new CustomEvent('present-requested', {
        bubbles: true, composed: true, detail,
      }));
      this.render();
      return;
    }
    try {
      const out = await builder(detail);
      this._busy = null;
      this._presentation = out?.presentation ?? out;
      this.dispatchEvent(new CustomEvent('presentation-ready', {
        bubbles: true, composed: true, detail: { presentation: this._presentation },
      }));
    } catch (e) {
      this._busy = null;
      this._lastError = `present failed: ${String(e)}`;
    }
    this.render();
  }
}

// ─── <dregg-credential-verifier> ─────────────────────────────────────────

class DreggCredentialVerifierElement extends HTMLElement {
  static get observedAttributes() { return ['verifier-uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._busy = null;
    this._result = null;
    this._error = null;
  }
  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const verifierUri = this.getAttribute('verifier-uri') || '';
    const result = this._result;
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-identity-verifier-form {
          display: grid;
          gap: 0.75rem;
          max-width: 540px;
        }
        .dregg-identity-verifier-form label {
          display: grid;
          gap: 0.25rem;
        }
        .dregg-identity-verifier-form textarea {
          width: 100%;
          min-height: 7rem;
          font: 0.85rem ui-monospace, monospace;
          padding: 0.4rem;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        .dregg-identity-verifier-form input {
          padding: 0.4rem;
          font: inherit;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        .dregg-identity-verifier-form button[type=submit] {
          padding: 0.55rem;
          font-weight: 600;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        .dregg-identity-verifier-form button[type=submit][disabled] {
          opacity: 0.5; cursor: wait;
        }
        .dregg-identity-verifier-result {
          border: 1px solid #ddd;
          padding: 0.75rem;
          border-radius: 4px;
          background: #fafbfc;
        }
        .dregg-identity-verifier-accept {
          color: #1f6b30;
          font-weight: 700;
          font-size: 1.05rem;
        }
        .dregg-identity-verifier-reject {
          color: #a02020;
          font-weight: 700;
          font-size: 1.05rem;
        }
        pre {
          background: #f5f5f7;
          padding: 0.5rem;
          border-radius: 3px;
          overflow: auto;
          max-height: 14rem;
        }
      </style>
      <form class="dregg-identity-verifier-form">
        <div>Verifier cell: <code>${escapeHtml(verifierUri)}</code></div>
        <label>
          Presentation (wire JSON)
          <textarea name="presentation" placeholder='{"proof": ..., "disclosed": [...]}'></textarea>
        </label>
        <label>
          Expected schema
          <input name="schema" placeholder="kyc-v1" />
        </label>
        <label>
          Required disclosure (comma-separated)
          <input name="disclose" placeholder="verification_level" />
        </label>
        <label>
          Required predicate (e.g. "verification_level Gte 1")
          <input name="predicate" placeholder="verification_level Gte 1" />
        </label>
        <button type="submit" ${this._busy ? 'disabled' : ''}>
          ${this._busy ? 'verifying…' : 'Verify'}
        </button>
      </form>
      <dregg-status-bar
        state="${this._busy ? 'loading' : (this._error ? 'error' : (result ? 'success' : 'idle'))}"
        message="${escapeHtml(this._busy?.message ?? this._error ?? '')}"
      ></dregg-status-bar>
      ${result ? `
        <div class="dregg-identity-verifier-result">
          <div class="${result.accept ? 'dregg-identity-verifier-accept' : 'dregg-identity-verifier-reject'}">
            ${result.accept ? 'ACCEPT ✓' : 'REJECT ✗'}
          </div>
          ${result.error ? `<div><em>${escapeHtml(result.error)}</em></div>` : ''}
          ${result.disclosed ? `
            <h4 style="margin: 0.6rem 0 0.3rem 0;">Revealed</h4>
            <pre>${escapeHtml(JSON.stringify(result.disclosed, null, 2))}</pre>
          ` : ''}
          <dregg-token-cap
            kind="${result.accept ? 'verified' : 'rejected'}"
            label="${result.accept ? 'ACCEPT' : 'REJECT'}"
            target="${escapeHtml(verifierUri)}"
            action="verify_presentation"
            tag="${escapeHtml(result.commitment ?? '')}"
          ></dregg-token-cap>
        </div>
      ` : ''}
    `;

    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      const fd = new FormData(e.target);
      this.#verify({
        verifierUri,
        presentationJson: fd.get('presentation'),
        schema: fd.get('schema'),
        disclose: String(fd.get('disclose') || '')
          .split(',').map((s) => s.trim()).filter(Boolean),
        predicate: fd.get('predicate'),
      });
    });
  }

  async #verify(detail) {
    this._busy = { message: 'verifying presentation…' };
    this._error = null;
    this._result = null;
    this.render();
    const builder = window.dregg?.builders?.identity?.verify_presentation;
    if (!builder) {
      this._busy = null;
      this._error = 'no verify_presentation builder loaded';
      this.dispatchEvent(new CustomEvent('verify-requested', {
        bubbles: true, composed: true, detail,
      }));
      this.render();
      return;
    }
    try {
      const result = await builder(detail);
      this._busy = null;
      this._result = result;
      this.dispatchEvent(new CustomEvent('presentation-verified', {
        bubbles: true, composed: true, detail: { result },
      }));
    } catch (e) {
      this._busy = null;
      this._error = `verify failed: ${String(e)}`;
    }
    this.render();
  }
}

// ─── Registration ────────────────────────────────────────────────────────

const COMPONENTS = {
  'dregg-credential':              DreggCredentialElement,
  'dregg-credential-issue-form':   DreggCredentialIssueFormElement,
  'dregg-credential-present-form': DreggCredentialPresentFormElement,
  'dregg-credential-verifier':     DreggCredentialVerifierElement,
};

for (const [tag, ctor] of Object.entries(COMPONENTS)) {
  if (typeof customElements !== 'undefined' && !customElements.get(tag)) {
    customElements.define(tag, ctor);
  }
  if (typeof window !== 'undefined' && window.dreggUi?.register) {
    window.dreggUi.register(tag, ctor);
  }
}

export {
  DreggCredentialElement,
  DreggCredentialIssueFormElement,
  DreggCredentialPresentFormElement,
  DreggCredentialVerifierElement,
  TAGS,
  SCHEMA_COMMITMENT_SLOT,
  ISSUANCE_COUNTER_SLOT,
  REVOCATION_ROOT_SLOT,
  ISSUER_AUTH_ROOT_SLOT,
};

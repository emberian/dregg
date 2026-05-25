// starbridge-apps/identity/pages/inspectors.js
//
// Web components for the identity starbridge-app's four UI surfaces.
// These are pure custom-element shells: they query window.pyana for the
// underlying credential data, render disclosure pickers / predicate
// builders / accept-reject results, and dispatch turn requests via
// window.pyana.signTurn().
//
// All policy lives in Rust (starbridge-apps/identity/src/lib.rs); the
// JS is the thinnest possible UX layer. The four components are:
//
//   <pyana-credential uri="pyana://credential/..."/>
//     Read-only view: schema, holder id, status, attribute list (with a
//     reveal toggle that does NOT leak the cleartext — the toggle only
//     shows the holder their own attributes locally).
//
//   <pyana-credential-issue-form issuer-uri="pyana://cell/..." schema="kyc-v1"/>
//     Issuer UI: collects attribute values for the selected schema,
//     dispatches `build_issue_credential_action` via the turn-builder
//     bridge.
//
//   <pyana-credential-present-form credential-uri="pyana://credential/..."/>
//     Holder UI: lets the holder pick which attributes to reveal,
//     add predicate requests ("age ≥ 18"), choose anonymous mode,
//     and emit the presentation bytes.
//
//   <pyana-credential-verifier verifier-uri="pyana://cell/..."/>
//     Verifier UI: paste a presentation, configure expectations
//     (schema, disclosure, predicate, revocation root), display
//     accept / reject + the revealed-facts.
//
// Each component dispatches CustomEvents so a host page can wire its
// own analytics or persistence without forking these.

const TAGS = [
  'pyana-credential',
  'pyana-credential-issue-form',
  'pyana-credential-present-form',
  'pyana-credential-verifier',
];

// ─── <pyana-credential> ──────────────────────────────────────────────────

class PyanaCredentialElement extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
  }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  async render() {
    const uri = this.getAttribute('uri') || '';
    const data = await this.#fetch(uri);
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .card { border: 1px solid #ddd; border-radius: 6px; padding: 1rem; }
        .schema { font-size: 0.85rem; color: #666; }
        .attr { display: flex; justify-content: space-between; padding: 0.25rem 0; }
        .status-ok  { color: #2a8a3e; font-weight: 600; }
        .status-bad { color: #c43030; font-weight: 600; }
        button { margin-top: 0.5rem; }
      </style>
      <div class="card">
        <div class="schema">${data.schema || '(no schema)'}</div>
        <h3>Credential ${data.id_short || ''}</h3>
        <div class="attr"><span>Holder</span><code>${data.holder_id || '—'}</code></div>
        <div class="attr"><span>Issued</span><span>${data.issued_at || '—'}</span></div>
        <div class="attr"><span>Expires</span><span>${data.not_after || '—'}</span></div>
        <div class="attr">
          <span>Status</span>
          <span class="${data.revoked ? 'status-bad' : 'status-ok'}">
            ${data.revoked ? 'REVOKED' : 'VALID'}
          </span>
        </div>
        ${data.attributes ? `
          <details>
            <summary>Attributes (${data.attributes.length})</summary>
            ${data.attributes.map(a => `<div class="attr"><span>${a.name}</span><code>${a.value}</code></div>`).join('')}
          </details>
        ` : ''}
        <button id="present">Present this credential…</button>
      </div>
    `;
    this.shadowRoot.getElementById('present')?.addEventListener('click', () => {
      this.dispatchEvent(new CustomEvent('present-requested', {
        bubbles: true, composed: true, detail: { uri },
      }));
    });
  }

  async #fetch(uri) {
    if (typeof window === 'undefined' || !window.pyana?.fetchCredential) {
      return { id_short: '(stub)', schema: 'kyc-v1', revoked: false, attributes: [] };
    }
    try {
      return await window.pyana.fetchCredential(uri);
    } catch (e) {
      return { id_short: 'error', schema: '(unknown)', revoked: false, attributes: [],
               error: String(e) };
    }
  }
}

// ─── <pyana-credential-issue-form> ───────────────────────────────────────

class PyanaCredentialIssueFormElement extends HTMLElement {
  static get observedAttributes() { return ['issuer-uri', 'schema']; }

  constructor() { super(); this.attachShadow({ mode: 'open' }); }
  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const issuerUri = this.getAttribute('issuer-uri') || '';
    const schemaName = this.getAttribute('schema') || 'kyc-v1';
    const attrs = this.#attrsFor(schemaName);

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        form { display: grid; gap: 0.75rem; max-width: 420px; }
        label { display: grid; gap: 0.25rem; }
        input, select { padding: 0.4rem; font-size: 1rem; }
        button { padding: 0.5rem; font-weight: 600; }
        .target { font-size: 0.85rem; color: #666; }
      </style>
      <form>
        <div class="target">Issuer cell: <code>${issuerUri}</code></div>
        <label>
          Schema
          <select name="schema">
            <option value="kyc-v1"        ${schemaName === 'kyc-v1'        ? 'selected' : ''}>KYC v1</option>
            <option value="gov-id-v1"     ${schemaName === 'gov-id-v1'     ? 'selected' : ''}>Government ID v1</option>
            <option value="employment-v1" ${schemaName === 'employment-v1' ? 'selected' : ''}>Employment v1</option>
          </select>
        </label>
        <label>
          Subject (holder cell id / hex pubkey)
          <input name="subject" placeholder="0x…" required />
        </label>
        ${attrs.map(a => `
          <label>${a}<input name="attr_${a}" required /></label>
        `).join('')}
        <button type="submit">Issue credential</button>
      </form>
    `;
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
    // Update the schema attribute on change so the input list refreshes.
    this.shadowRoot.querySelector('select[name=schema]')
      ?.addEventListener('change', (e) => {
        this.setAttribute('schema', e.target.value);
      });
  }

  #attrsFor(schemaName) {
    return ({
      'kyc-v1':        ['given_name', 'family_name', 'dob', 'verification_level'],
      'gov-id-v1':     ['id_number', 'country', 'expires_on'],
      'employment-v1': ['employer', 'role', 'start_date'],
    })[schemaName] || [];
  }

  async #issue({ issuerUri, schema, subject, claims }) {
    if (!window.pyana?.signTurn) {
      this.dispatchEvent(new CustomEvent('issue-stubbed', {
        bubbles: true, composed: true,
        detail: { issuerUri, schema, subject, claims },
      }));
      return;
    }
    // The builder bridge (turn-builders.js) shapes the right turnSpec for
    // build_issue_credential_action — keep this UI dumb.
    const builder = window.pyana?.builders?.identity?.issue_credential;
    if (!builder) {
      console.warn('[identity] missing turn-builder; falling back to event');
      this.dispatchEvent(new CustomEvent('issue-requested', {
        bubbles: true, composed: true,
        detail: { issuerUri, schema, subject, claims },
      }));
      return;
    }
    const receipt = await builder(issuerUri, schema, subject, claims);
    this.dispatchEvent(new CustomEvent('credential-issued', {
      bubbles: true, composed: true, detail: { receipt },
    }));
  }
}

// ─── <pyana-credential-present-form> ─────────────────────────────────────

class PyanaCredentialPresentFormElement extends HTMLElement {
  static get observedAttributes() { return ['credential-uri']; }

  constructor() { super(); this.attachShadow({ mode: 'open' }); }
  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  async render() {
    const credentialUri = this.getAttribute('credential-uri') || '';
    const credential = await this.#loadCredential(credentialUri);
    const attrs = credential?.attributes ?? [];

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        form { display: grid; gap: 0.75rem; max-width: 480px; }
        .row { display: flex; gap: 0.5rem; align-items: center; }
        fieldset { border: 1px solid #ddd; border-radius: 4px; padding: 0.75rem; }
        .predicate { display: grid; grid-template-columns: 1fr 100px 1fr; gap: 0.4rem; }
        button { padding: 0.5rem; font-weight: 600; }
      </style>
      <form>
        <div>Credential: <code>${credentialUri || '(none)'}</code></div>
        <fieldset>
          <legend>Selective disclosure</legend>
          ${attrs.length === 0 ? '<em>(no attributes)</em>' : ''}
          ${attrs.map(a => `
            <label class="row">
              <input type="checkbox" name="disclose_${a.name}" />
              <span>${a.name}</span>
              <code style="margin-left:auto">${a.value ?? ''}</code>
            </label>
          `).join('')}
        </fieldset>
        <fieldset>
          <legend>Predicate requests</legend>
          <div class="predicate">
            <select name="pred_attr">
              <option value="">(no predicate)</option>
              ${attrs.map(a => `<option value="${a.name}">${a.name}</option>`).join('')}
            </select>
            <select name="pred_op">
              <option value="Gte">≥</option>
              <option value="Lte">≤</option>
              <option value="Eq">=</option>
            </select>
            <input name="pred_val" type="number" placeholder="value" />
          </div>
        </fieldset>
        <label class="row">
          <input type="checkbox" name="anonymous" />
          <span>Anonymous (unlinkable multi-show)</span>
        </label>
        <button type="submit">Generate presentation</button>
      </form>
    `;
    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      const fd = new FormData(e.target);
      const disclose = [];
      for (const [k, _] of fd.entries()) {
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
    if (!window.pyana?.fetchCredential) {
      return { attributes: [
        { name: 'given_name', value: '(stub)' },
        { name: 'family_name', value: '(stub)' },
        { name: 'verification_level', value: '2' },
      ] };
    }
    try { return await window.pyana.fetchCredential(uri); } catch { return null; }
  }

  async #present(detail) {
    const builder = window.pyana?.builders?.identity?.present_credential;
    if (!builder) {
      this.dispatchEvent(new CustomEvent('present-requested', {
        bubbles: true, composed: true, detail,
      }));
      return;
    }
    const presentation = await builder(detail);
    this.dispatchEvent(new CustomEvent('presentation-ready', {
      bubbles: true, composed: true, detail: { presentation },
    }));
  }
}

// ─── <pyana-credential-verifier> ─────────────────────────────────────────

class PyanaCredentialVerifierElement extends HTMLElement {
  static get observedAttributes() { return ['verifier-uri']; }

  constructor() { super(); this.attachShadow({ mode: 'open' }); }
  connectedCallback() { this.render(null); }
  attributeChangedCallback() { this.render(null); }

  render(result) {
    const verifierUri = this.getAttribute('verifier-uri') || '';
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        form { display: grid; gap: 0.75rem; max-width: 500px; }
        textarea { width: 100%; min-height: 7rem; font-family: monospace; }
        button { padding: 0.5rem; font-weight: 600; }
        .accept { color: #2a8a3e; font-weight: 700; }
        .reject { color: #c43030; font-weight: 700; }
        .result { border: 1px solid #ddd; padding: 0.75rem; border-radius: 4px; }
      </style>
      <form>
        <div>Verifier cell: <code>${verifierUri}</code></div>
        <label>
          Presentation (wire JSON)
          <textarea name="presentation" placeholder='{"proof": ..., "disclosed": [...]}'></textarea>
        </label>
        <label>
          Expected schema
          <input name="schema" placeholder="kyc-v1" />
        </label>
        <label>
          Required disclosure (comma-separated attribute names)
          <input name="disclose" placeholder="verification_level" />
        </label>
        <label>
          Required predicate (e.g. "verification_level Gte 1")
          <input name="predicate" placeholder="verification_level Gte 1" />
        </label>
        <button type="submit">Verify</button>
      </form>
      ${result ? `
        <div class="result">
          Result: <span class="${result.accept ? 'accept' : 'reject'}">${result.accept ? 'ACCEPT' : 'REJECT'}</span>
          ${result.error ? `<div><em>${result.error}</em></div>` : ''}
          ${result.disclosed ? `
            <h4>Revealed</h4>
            <pre>${JSON.stringify(result.disclosed, null, 2)}</pre>
          ` : ''}
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
          .split(',').map(s => s.trim()).filter(Boolean),
        predicate: fd.get('predicate'),
      });
    });
  }

  async #verify(detail) {
    const builder = window.pyana?.builders?.identity?.verify_presentation;
    if (!builder) {
      this.dispatchEvent(new CustomEvent('verify-requested', {
        bubbles: true, composed: true, detail,
      }));
      // Render a stub accept for demo purposes.
      this.render({ accept: true, disclosed: { _stub: true } });
      return;
    }
    try {
      const result = await builder(detail);
      this.render(result);
      this.dispatchEvent(new CustomEvent('presentation-verified', {
        bubbles: true, composed: true, detail: { result },
      }));
    } catch (e) {
      this.render({ accept: false, error: String(e) });
    }
  }
}

// ─── Registration ────────────────────────────────────────────────────────

const COMPONENTS = {
  'pyana-credential':              PyanaCredentialElement,
  'pyana-credential-issue-form':   PyanaCredentialIssueFormElement,
  'pyana-credential-present-form': PyanaCredentialPresentFormElement,
  'pyana-credential-verifier':     PyanaCredentialVerifierElement,
};

for (const [tag, ctor] of Object.entries(COMPONENTS)) {
  if (typeof customElements !== 'undefined' && !customElements.get(tag)) {
    customElements.define(tag, ctor);
  }
  if (typeof window !== 'undefined' && window.pyana?.register) {
    window.pyana.register(tag, ctor);
  }
}

// Also export the constructors so a host can subclass them.
export {
  PyanaCredentialElement,
  PyanaCredentialIssueFormElement,
  PyanaCredentialPresentFormElement,
  PyanaCredentialVerifierElement,
  TAGS,
};

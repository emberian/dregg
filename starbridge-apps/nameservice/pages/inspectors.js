// starbridge-apps/nameservice/pages/inspectors.js
//
// Web components for the nameservice starbridge-app's three UI surfaces.
//
//   <dregg-name uri="dregg://cell/..."/>
//     Live-binding view of a single name cell — owner, expiry, target,
//     revocation status, transfer/revoke action buttons.
//
//   <dregg-name-registry uri="dregg://cell/..." child-inspector="name"/>
//     Filterable + paginated list of registered names. Polls the
//     runtime's nameservice.listEntries(uri) helper.
//
//   <dregg-name-register-form registry-uri="dregg://cell/..."/>
//     Mutation surface — register / renew / transfer / revoke /
//     set-target — wired to window.dregg.builders.nameservice.* (the
//     "cipherclerk-named" Action presets in ./turn-builders.js, all of
//     which terminate in window.dregg.signTurn for cclerk-side signing).
//
// All policy lives in Rust (starbridge-apps/nameservice/src/lib.rs); the
// JS is the thinnest possible UX layer.
//
// CSS classes are namespaced under `.dregg-nameservice-*` so they don't
// collide with peer apps when multiple inspectors mount in the same DOM.

// Slot indices — mirror constants in src/lib.rs.
const NAME_HASH_SLOT       = 2;
const OWNER_HASH_SLOT      = 3;
const EXPIRY_SLOT          = 4;
const REVOKED_SLOT         = 5;
const RESOLVE_TARGET_SLOT  = 6;

const POLL_INTERVAL_MS = 5_000;

const TAGS = [
  'dregg-name',
  'dregg-name-registry',
  'dregg-name-register-form',
];

// ─── helpers ─────────────────────────────────────────────────────────────

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

function hex32(bytes) {
  if (bytes == null) return '—';
  if (typeof bytes === 'string') return bytes.length > 16 ? `${bytes.slice(0, 8)}…${bytes.slice(-8)}` : bytes;
  if (Array.isArray(bytes) || bytes instanceof Uint8Array) {
    const arr = Array.from(bytes);
    const h = arr.map((b) => b.toString(16).padStart(2, '0')).join('');
    return h.length > 16 ? `${h.slice(0, 8)}…${h.slice(-8)}` : h;
  }
  return String(bytes);
}

function hexFull(bytes) {
  if (!bytes) return '';
  if (typeof bytes === 'string') return bytes;
  if (Array.isArray(bytes) || bytes instanceof Uint8Array) {
    return Array.from(bytes).map((b) => b.toString(16).padStart(2, '0')).join('');
  }
  return '';
}

function u64FromBE32(bytes) {
  if (!bytes) return 0n;
  const arr = Array.isArray(bytes) || bytes instanceof Uint8Array ? Array.from(bytes) : null;
  if (!arr) return 0n;
  let v = 0n;
  for (let i = 24; i < 32; i += 1) {
    v = (v << 8n) | BigInt(arr[i] ?? 0);
  }
  return v;
}

function isZero32(bytes) {
  if (!bytes) return true;
  const arr = Array.isArray(bytes) || bytes instanceof Uint8Array ? Array.from(bytes) : null;
  if (!arr) return true;
  return arr.every((b) => b === 0);
}

async function previewNameHash(name) {
  if (!name) return '';
  try {
    if (typeof window !== 'undefined' && window.dregg?.blake3) {
      const out = await window.dregg.blake3(new TextEncoder().encode(String(name)));
      return hexFull(out);
    }
    const buf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(String(name)));
    return hexFull(new Uint8Array(buf));
  } catch {
    return '';
  }
}

// Format an expiry block height as a relative countdown if a tip-height
// is exposed by the runtime; otherwise just print the absolute height.
function fmtExpiry(expiryBlock, tipBlock) {
  const e = Number(expiryBlock ?? 0);
  if (!e) return '—';
  if (tipBlock == null) return `block ${e}`;
  const t = Number(tipBlock);
  const delta = e - t;
  if (delta <= 0) return `expired (block ${e})`;
  return `block ${e}  (+${delta})`;
}

async function tipHeight() {
  if (typeof window === 'undefined') return null;
  if (window.dregg?.blockHeight) {
    try { return Number(await window.dregg.blockHeight()); } catch { return null; }
  }
  if (window.dregg?.federationStatus) {
    try {
      const s = await window.dregg.federationStatus();
      return Number(s?.height ?? null);
    } catch { return null; }
  }
  return null;
}

// ─── <dregg-name> ────────────────────────────────────────────────────────

class DreggNameElement extends HTMLElement {
  static get observedAttributes() { return ['uri', 'name']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._poll = null;
    this._busy = null;       // { mode, message } for in-flight actions
    this._lastReceipt = null;
    this._lastError = null;
  }

  connectedCallback() {
    this.render();
    this._poll = setInterval(() => this.render(), POLL_INTERVAL_MS);
  }
  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
    this._poll = null;
  }
  attributeChangedCallback() { this.render(); }

  async render() {
    const uri = this.getAttribute('uri') || '';
    const nameAttr = this.getAttribute('name') || '';
    const [data, tip] = await Promise.all([this.#load(uri), tipHeight()]);
    const revoked = !isZero32(data.revoked);
    const expiry = u64FromBE32(data.expiry);
    const expiryDisp = fmtExpiry(expiry, tip);

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-nameservice-name-card {
          border: 1px solid #ddd;
          border-radius: 6px;
          padding: 1rem;
          max-width: 480px;
          background: #fff;
        }
        .dregg-nameservice-name-row {
          display: flex;
          justify-content: space-between;
          gap: 0.5rem;
          padding: 0.25rem 0;
        }
        .dregg-nameservice-name-label { color: #555; }
        code { font-family: ui-monospace, monospace; }
        .dregg-nameservice-name-status-ok  { color: #2a8a3e; font-weight: 600; }
        .dregg-nameservice-name-status-bad { color: #c43030; font-weight: 600; }
        .dregg-nameservice-name-actions {
          margin-top: 0.5rem;
          display: flex;
          gap: 0.4rem;
          flex-wrap: wrap;
        }
        button {
          padding: 0.4rem 0.7rem;
          background: #eef;
          border: 1px solid #ccd;
          border-radius: 3px;
          cursor: pointer;
          font: inherit;
        }
        button[disabled] { opacity: 0.45; cursor: not-allowed; }
        button:hover:not([disabled]) { background: #dde; }
      </style>
      <div class="dregg-nameservice-name-card">
        <h3>${escapeHtml(nameAttr || '(name)')}</h3>
        <div class="dregg-nameservice-name-row">
          <span class="dregg-nameservice-name-label">cell</span>
          <code>${escapeHtml(hex32(uri))}</code>
        </div>
        <div class="dregg-nameservice-name-row">
          <span class="dregg-nameservice-name-label">name-hash</span>
          <code>${escapeHtml(hex32(data.name_hash))}</code>
        </div>
        <div class="dregg-nameservice-name-row">
          <span class="dregg-nameservice-name-label">owner-hash</span>
          <code>${escapeHtml(hex32(data.owner_hash))}</code>
        </div>
        <div class="dregg-nameservice-name-row">
          <span class="dregg-nameservice-name-label">expiry</span>
          <code>${escapeHtml(expiryDisp)}</code>
        </div>
        <div class="dregg-nameservice-name-row">
          <span class="dregg-nameservice-name-label">target</span>
          <code>${isZero32(data.target) ? '—' : escapeHtml(hex32(data.target))}</code>
        </div>
        <div class="dregg-nameservice-name-row">
          <span class="dregg-nameservice-name-label">status</span>
          <span class="${revoked ? 'dregg-nameservice-name-status-bad' : 'dregg-nameservice-name-status-ok'}">
            ${revoked ? 'REVOKED' : 'ACTIVE'}
          </span>
        </div>
        <div class="dregg-nameservice-name-actions">
          <button data-action="renew"      ${revoked ? 'disabled' : ''}>Renew</button>
          <button data-action="transfer"   ${revoked ? 'disabled' : ''}>Transfer</button>
          <button data-action="set_target" ${revoked ? 'disabled' : ''}>Set target</button>
          <button data-action="revoke"     ${revoked ? 'disabled' : ''}>Revoke</button>
        </div>
        <dregg-status-bar
          state="${this._busy ? 'loading' : (this._lastError ? 'error' : (this._lastReceipt ? 'success' : 'idle'))}"
          message="${escapeHtml(this._busy?.message ?? this._lastError ?? (this._lastReceipt ? 'submitted' : ''))}"
          receipt="${escapeHtml(this._lastReceipt?.id ?? '')}"
        ></dregg-status-bar>
        ${this._lastReceipt ? `
          <div style="margin-top:0.5rem;">
            <dregg-token-cap
              kind="receipt"
              label="${escapeHtml(this._lastReceipt.method ?? 'name-action')}"
              target="${escapeHtml(uri)}"
              action="${escapeHtml(this._lastReceipt.method ?? '')}"
              tag="${escapeHtml(this._lastReceipt.id ?? '')}"
            ></dregg-token-cap>
          </div>
        ` : ''}
      </div>
    `;

    this.shadowRoot.querySelectorAll('button[data-action]').forEach((btn) => {
      btn.addEventListener('click', () => this.#onAction(btn.dataset.action, uri, nameAttr, data));
    });
  }

  async #onAction(action, uri, name, data) {
    // For mutating actions that need more input (transfer, set_target),
    // surface a CustomEvent so the host can route to the form. For renew
    // and revoke we can submit immediately.
    if (action === 'transfer' || action === 'set_target') {
      this.dispatchEvent(new CustomEvent('name-action', {
        bubbles: true, composed: true,
        detail: { action, uri, name },
      }));
      return;
    }
    const builders = (typeof window !== 'undefined') ? window.dregg?.builders?.nameservice : null;
    const fn = builders?.[action];
    if (!fn) {
      // Host has no builder wired — fall back to a CustomEvent so the
      // page can route the request.
      this.dispatchEvent(new CustomEvent('name-action', {
        bubbles: true, composed: true,
        detail: { action, uri, name },
      }));
      return;
    }
    this._busy = { mode: action, message: `${action}ing ${name}…` };
    this._lastError = null;
    this._lastReceipt = null;
    this.render();
    try {
      let receipt;
      if (action === 'renew') {
        const currentExpiry = u64FromBE32(data?.expiry);
        // Default renew: bump by 100_000 blocks. Hosts wanting a custom
        // expiry should use <dregg-name-register-form mode="renew"/>.
        const newExpiry = Number(currentExpiry + 100_000n);
        receipt = await fn(uri, { name, expiry: newExpiry });
      } else if (action === 'revoke') {
        receipt = await fn(uri, { name });
      } else {
        receipt = await fn(uri, { name });
      }
      this._lastReceipt = { ...(receipt ?? {}), method: action };
      this._busy = null;
    } catch (e) {
      this._busy = null;
      this._lastError = `${action} failed: ${String(e)}`;
    }
    this.render();
  }

  async #load(uri) {
    const empty = () => ({
      name_hash: null, owner_hash: null, expiry: null,
      revoked: null, target: null,
    });
    if (typeof window === 'undefined' || !window.dregg?.cell?.readField) {
      // Fallback: try readCell which returns full state.
      if (typeof window !== 'undefined' && window.dregg?.readCell) {
        try {
          const cell = await window.dregg.readCell(uri);
          const f = cell?.state?.fields ?? [];
          return {
            name_hash: f[NAME_HASH_SLOT] ?? null,
            owner_hash: f[OWNER_HASH_SLOT] ?? null,
            expiry: f[EXPIRY_SLOT] ?? null,
            revoked: f[REVOKED_SLOT] ?? null,
            target: f[RESOLVE_TARGET_SLOT] ?? null,
          };
        } catch { /* fall through */ }
      }
      return empty();
    }
    try {
      const [name_hash, owner_hash, expiry, revoked, target] = await Promise.all([
        window.dregg.cell.readField(uri, NAME_HASH_SLOT),
        window.dregg.cell.readField(uri, OWNER_HASH_SLOT),
        window.dregg.cell.readField(uri, EXPIRY_SLOT),
        window.dregg.cell.readField(uri, REVOKED_SLOT),
        window.dregg.cell.readField(uri, RESOLVE_TARGET_SLOT),
      ]);
      return { name_hash, owner_hash, expiry, revoked, target };
    } catch (_) {
      return empty();
    }
  }
}

// ─── <dregg-name-registry> ──────────────────────────────────────────────

class DreggNameRegistryElement extends HTMLElement {
  static get observedAttributes() { return ['uri', 'page-size']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._filter = '';
    this._page = 0;
    this._poll = null;
    this._entries = [];
    this._loading = true;
    this._error = null;
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
      this._entries = await this.#load(uri);
      this._error = null;
    } catch (e) {
      this._error = String(e);
    }
    this._loading = false;
    this.render();
  }

  render() {
    const uri = this.getAttribute('uri') || '';
    const pageSize = Math.max(1, Number(this.getAttribute('page-size') || 25));
    const filter = this._filter.trim().toLowerCase();
    const filtered = filter
      ? this._entries.filter((e) => (e.name || '').toLowerCase().includes(filter))
      : this._entries;
    const pages = Math.max(1, Math.ceil(filtered.length / pageSize));
    if (this._page >= pages) this._page = pages - 1;
    if (this._page < 0) this._page = 0;
    const start = this._page * pageSize;
    const slice = filtered.slice(start, start + pageSize);

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-nameservice-registry-toolbar {
          display: flex;
          gap: 0.5rem;
          align-items: center;
          margin-bottom: 0.5rem;
          flex-wrap: wrap;
        }
        .dregg-nameservice-registry-toolbar input[type=search] {
          padding: 0.4rem;
          min-width: 240px;
          font: inherit;
        }
        .dregg-nameservice-registry-list {
          border-collapse: collapse;
          width: 100%;
          max-width: 760px;
        }
        .dregg-nameservice-registry-list th,
        .dregg-nameservice-registry-list td {
          border-bottom: 1px solid #eee;
          padding: 0.35rem 0.5rem;
          text-align: left;
        }
        .dregg-nameservice-registry-list th { background: #fafafa; }
        .dregg-nameservice-registry-list tr.revoked td {
          color: #888;
          text-decoration: line-through;
        }
        .dregg-nameservice-registry-list a {
          color: #25439a;
          text-decoration: none;
        }
        .dregg-nameservice-registry-list a:hover { text-decoration: underline; }
        .dregg-nameservice-registry-pager {
          margin-top: 0.5rem;
          display: flex;
          gap: 0.4rem;
          align-items: center;
        }
        .dregg-nameservice-registry-empty {
          color: #888;
          padding: 0.75rem;
          border: 1px dashed #ddd;
          border-radius: 4px;
          background: #fafbfc;
        }
        .dregg-nameservice-registry-error {
          color: #a02020;
          padding: 0.5rem;
          background: #fff0f0;
          border: 1px solid #f0c0c0;
          border-radius: 4px;
        }
        button {
          padding: 0.3rem 0.6rem;
          background: #eef;
          border: 1px solid #ccd;
          border-radius: 3px;
          cursor: pointer;
        }
        button[disabled] { opacity: 0.4; cursor: not-allowed; }
      </style>
      <div class="dregg-nameservice-registry-toolbar">
        <input type="search" placeholder="Filter by name…" value="${escapeHtml(filter)}" />
        <span>${filtered.length} / ${this._entries.length}</span>
        <button data-action="register-new">Register new…</button>
        <button data-action="refresh">↻ Refresh</button>
      </div>
      ${this._error ? `<div class="dregg-nameservice-registry-error">error: ${escapeHtml(this._error)}</div>` : ''}
      ${this._loading ? `<dregg-status-bar state="loading" message="loading registry…"></dregg-status-bar>` : ''}
      ${slice.length === 0
        ? `<div class="dregg-nameservice-registry-empty">No names registered${filter ? ' match the filter.' : '.'}</div>`
        : `
        <table class="dregg-nameservice-registry-list">
          <thead>
            <tr><th>Name</th><th>Owner</th><th>Expiry (block)</th><th>Status</th></tr>
          </thead>
          <tbody>
            ${slice.map((e) => `
              <tr class="${e.revoked ? 'revoked' : ''}">
                <td>
                  <a href="#" data-uri="${escapeHtml(e.uri || uri)}" data-name="${escapeHtml(e.name || '')}">
                    ${escapeHtml(e.name || '(unnamed)')}
                  </a>
                </td>
                <td><code>${escapeHtml(hex32(e.owner_hash))}</code></td>
                <td><code>${e.expiry?.toString() ?? '—'}</code></td>
                <td>${e.revoked ? 'REVOKED' : 'ACTIVE'}</td>
              </tr>
            `).join('')}
          </tbody>
        </table>
        <div class="dregg-nameservice-registry-pager">
          <button data-action="prev" ${this._page === 0 ? 'disabled' : ''}>‹ Prev</button>
          <span>Page ${this._page + 1} / ${pages}</span>
          <button data-action="next" ${this._page >= pages - 1 ? 'disabled' : ''}>Next ›</button>
        </div>
      `}
    `;
    const inp = this.shadowRoot.querySelector('input[type=search]');
    inp?.addEventListener('input', (e) => {
      this._filter = e.target.value;
      this._page = 0;
      this.render();
    });
    this.shadowRoot.querySelector('button[data-action=prev]')?.addEventListener('click', () => {
      this._page -= 1;
      this.render();
    });
    this.shadowRoot.querySelector('button[data-action=next]')?.addEventListener('click', () => {
      this._page += 1;
      this.render();
    });
    this.shadowRoot.querySelector('button[data-action=refresh]')?.addEventListener('click', () => {
      this._loading = true;
      this.render();
      this.refresh();
    });
    this.shadowRoot.querySelector('button[data-action=register-new]')?.addEventListener('click', () => {
      this.dispatchEvent(new CustomEvent('register-requested', {
        bubbles: true, composed: true, detail: { registryUri: uri },
      }));
    });
    this.shadowRoot.querySelectorAll('a[data-uri]').forEach((a) => {
      a.addEventListener('click', (e) => {
        e.preventDefault();
        this.dispatchEvent(new CustomEvent('name-selected', {
          bubbles: true, composed: true,
          detail: { uri: a.dataset.uri, name: a.dataset.name },
        }));
      });
    });
  }

  async #load(uri) {
    if (typeof window === 'undefined') return [];
    if (window.dregg?.nameservice?.listEntries) {
      const entries = await window.dregg.nameservice.listEntries(uri);
      return Array.isArray(entries) ? entries : [];
    }
    // No runtime-side enumerator: surface an empty list rather than
    // making up names. Hosts that want the registry view to populate
    // must implement `window.dregg.nameservice.listEntries(cellUri)`.
    return [];
  }
}

// ─── <dregg-name-register-form> ─────────────────────────────────────────

class DreggNameRegisterFormElement extends HTMLElement {
  static get observedAttributes() { return ['registry-uri', 'mode']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._busy = null;
    this._lastError = null;
    this._lastReceipt = null;
    this._lastMethod = null;
    this._namePreview = '';
    this._pendingName = '';
  }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const registryUri = this.getAttribute('registry-uri') || '';
    const mode = this.getAttribute('mode') || 'register';
    const showFields = {
      register:   ['name', 'owner', 'expiry'],
      renew:      ['name', 'expiry'],
      transfer:   ['name', 'old_owner', 'new_owner'],
      revoke:     ['name'],
      set_target: ['name', 'target'],
    }[mode] ?? ['name'];

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-nameservice-form {
          display: grid;
          gap: 0.75rem;
          max-width: 420px;
        }
        .dregg-nameservice-form label {
          display: grid;
          gap: 0.25rem;
        }
        .dregg-nameservice-form input,
        .dregg-nameservice-form select {
          padding: 0.4rem;
          font-size: 1rem;
          font-family: inherit;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        .dregg-nameservice-form button[type=submit] {
          padding: 0.55rem;
          font-weight: 600;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        .dregg-nameservice-form button[type=submit][disabled] {
          opacity: 0.5;
          cursor: wait;
        }
        .dregg-nameservice-form-target {
          font-size: 0.85rem;
          color: #666;
        }
        .dregg-nameservice-form-nav {
          display: flex;
          gap: 0.4rem;
          margin-bottom: 0.5rem;
          flex-wrap: wrap;
        }
        .dregg-nameservice-form-nav button {
          padding: 0.3rem 0.6rem;
          font-weight: 400;
          background: #f4f4f8;
          border: 1px solid #ddd;
          border-radius: 3px;
          cursor: pointer;
        }
        .dregg-nameservice-form-nav button[aria-current=true] {
          background: #d0d6f5;
          border-color: #889;
          font-weight: 600;
        }
        .dregg-nameservice-form-hash-preview {
          font-family: ui-monospace, monospace;
          font-size: 0.75rem;
          color: #557;
          word-break: break-all;
        }
      </style>
      <nav class="dregg-nameservice-form-nav">
        ${['register', 'renew', 'transfer', 'revoke', 'set_target'].map((m) => `
          <button type="button" data-mode="${m}" aria-current="${m === mode}">${m}</button>
        `).join('')}
      </nav>
      <form class="dregg-nameservice-form">
        <div class="dregg-nameservice-form-target">
          Registry: <code>${escapeHtml(registryUri || '(none)')}</code>
        </div>
        ${showFields.includes('name') ? `
          <label>Name
            <input name="name" required placeholder="alice.dregg" value="${escapeHtml(this._pendingName)}" />
            <span class="dregg-nameservice-form-hash-preview">
              blake3 = ${this._namePreview
                ? escapeHtml(this._namePreview.slice(0, 16) + '…' + this._namePreview.slice(-8))
                : '—'}
            </span>
          </label>
        ` : ''}
        ${showFields.includes('owner') ? `
          <label>Owner pubkey (hex)
            <input name="owner" required placeholder="0x… or raw hex (64 chars)" />
          </label>
        ` : ''}
        ${showFields.includes('old_owner') ? `
          <label>Old owner pubkey (hex)
            <input name="old_owner" required placeholder="0x…" />
          </label>
        ` : ''}
        ${showFields.includes('new_owner') ? `
          <label>New owner pubkey (hex)
            <input name="new_owner" required placeholder="0x…" />
          </label>
        ` : ''}
        ${showFields.includes('expiry') ? `
          <label>Expiry (block height)
            <input name="expiry" type="number" required min="1" placeholder="e.g. 1000000" />
          </label>
        ` : ''}
        ${showFields.includes('target') ? `
          <label>Target URI
            <input name="target" placeholder="dregg://cell/…" />
          </label>
        ` : ''}
        <button type="submit" ${this._busy ? 'disabled' : ''}>
          ${this._busy ? `${mode}ing…` : mode}
        </button>
      </form>
      <dregg-status-bar
        state="${this._busy ? 'loading' : (this._lastError ? 'error' : (this._lastReceipt ? 'success' : 'idle'))}"
        message="${escapeHtml(this._busy?.message ?? this._lastError ?? (this._lastReceipt ? `${this._lastMethod} submitted` : ''))}"
        receipt="${escapeHtml(this._lastReceipt?.id ?? '')}"
      ></dregg-status-bar>
      ${this._lastReceipt ? `
        <div style="margin-top:0.5rem;">
          <dregg-token-cap
            kind="receipt"
            label="${escapeHtml(this._lastMethod)}"
            target="${escapeHtml(registryUri)}"
            action="${escapeHtml(this._lastMethod)}"
            tag="${escapeHtml(this._lastReceipt.id ?? this._lastReceipt.turnId ?? '')}"
          ></dregg-token-cap>
        </div>
      ` : ''}
    `;

    this.shadowRoot.querySelectorAll('nav button[data-mode]').forEach((b) => {
      b.addEventListener('click', () => {
        this._lastError = null;
        this._lastReceipt = null;
        this.setAttribute('mode', b.dataset.mode);
      });
    });

    const nameInput = this.shadowRoot.querySelector('input[name=name]');
    nameInput?.addEventListener('input', async (e) => {
      this._pendingName = e.target.value;
      this._namePreview = await previewNameHash(this._pendingName);
      // Re-render the preview span only — full re-render would lose focus.
      const span = this.shadowRoot.querySelector('.dregg-nameservice-form-hash-preview');
      if (span) {
        span.textContent = this._namePreview
          ? `blake3 = ${this._namePreview.slice(0, 16)}…${this._namePreview.slice(-8)}`
          : 'blake3 = —';
      }
    });

    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      const fd = new FormData(e.target);
      const data = Object.fromEntries(fd.entries());
      this.#dispatch(mode, registryUri, data);
    });
  }

  async #dispatch(mode, registryUri, data) {
    this._busy = { mode, message: `submitting ${mode}…` };
    this._lastError = null;
    this._lastReceipt = null;
    this._lastMethod = mode;
    this.render();

    const builders = (typeof window !== 'undefined') ? window.dregg?.builders?.nameservice : null;
    const builder = builders?.[`${mode}_name`] ?? builders?.[mode];
    if (!builder) {
      this._busy = null;
      this._lastError = `no builder for "${mode}"; check that turn-builders.js loaded`;
      this.dispatchEvent(new CustomEvent(`${mode}-requested`, {
        bubbles: true, composed: true,
        detail: { registryUri, ...data },
      }));
      this.render();
      return;
    }
    try {
      const receipt = await builder(registryUri, data);
      this._busy = null;
      this._lastReceipt = receipt ?? { ok: true };
      this.dispatchEvent(new CustomEvent(`${mode}-submitted`, {
        bubbles: true, composed: true, detail: { receipt },
      }));
    } catch (err) {
      this._busy = null;
      this._lastError = `${mode} failed: ${String(err)}`;
      this.dispatchEvent(new CustomEvent(`${mode}-failed`, {
        bubbles: true, composed: true, detail: { error: String(err) },
      }));
    }
    this.render();
  }
}

// ─── Registration ────────────────────────────────────────────────────────

const COMPONENTS = {
  'dregg-name':                   DreggNameElement,
  'dregg-name-registry':          DreggNameRegistryElement,
  'dregg-name-register-form':     DreggNameRegisterFormElement,
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
  DreggNameElement,
  DreggNameRegistryElement,
  DreggNameRegisterFormElement,
  TAGS,
  NAME_HASH_SLOT,
  OWNER_HASH_SLOT,
  EXPIRY_SLOT,
  REVOKED_SLOT,
  RESOLVE_TARGET_SLOT,
};

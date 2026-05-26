// starbridge-apps/shared/inspectors/name.js
//
// First per-app inspectors for starbridge-apps (STARBRIDGE-PLAN §4.8).
// Exports and registers:
//   <dregg-name>          — domain view of a name cell (reuses <dregg-cell> + <dregg-capability>)
//   <dregg-name-registry> — list view (reuses platform list patterns)
//
// These are the canonical versions for Studio / <dregg-app-list> / /starbridge/.
// The legacy full impl (with forms + actions) remains in
// nameservice/pages/inspectors.js for the standalone fragment.
//
// Reuses platform vocabulary per the hard rule in STUDIO.md and STARBRIDGE-PLAN:
// never fork <dregg-cell>, <dregg-capability> etc.

const NAME_HASH_SLOT = 2;
const OWNER_HASH_SLOT = 3;
const EXPIRY_SLOT = 4;
const REVOKED_SLOT = 5;
const RESOLVE_TARGET_SLOT = 6;

const POLL_INTERVAL_MS = 5000;

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

function isZero32(bytes) {
  if (!bytes) return true;
  const arr = Array.isArray(bytes) || bytes instanceof Uint8Array ? Array.from(bytes) : null;
  if (!arr) return true;
  return arr.every((b) => b === 0);
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

async function tipHeight() {
  if (typeof window === 'undefined') return null;
  if (window.dregg?.blockHeight) {
    try { return Number(await window.dregg.blockHeight()); } catch { return null; }
  }
  return null;
}

// ─── <dregg-name> (reuses platform <dregg-cell> and capability views) ───

class DreggNameElement extends HTMLElement {
  static get observedAttributes() { return ['uri', 'name']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._poll = null;
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
    const tip = await tipHeight();

    // Embed the canonical cell inspector for the underlying state.
    // The domain-specific name fields are derived + shown alongside.
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; }
        .dregg-name-card { border: 1px solid #ddd; border-radius: 6px; padding: 0.75rem; background: #fff; }
        .dregg-name-header { font-weight: 600; margin-bottom: 0.5rem; }
        .dregg-name-meta { font-size: 0.85rem; color: #555; margin: 0.25rem 0; }
        code { font-family: ui-monospace, monospace; }
        .dregg-name-embed { margin-top: 0.5rem; border-top: 1px solid #eee; padding-top: 0.5rem; }
      </style>
      <div class="dregg-name-card">
        <div class="dregg-name-header">${escapeHtml(nameAttr || '(name cell)')}</div>
        <div class="dregg-name-meta">uri: <code>${escapeHtml(uri)}</code></div>
        <div class="dregg-name-embed">
          <!-- Reuse the platform cell inspector (full fidelity, including program + caps) -->
          <dregg-app data-embedded-runtime>
            <dregg-cell uri="${escapeHtml(uri)}" mode="default"></dregg-cell>
          </dregg-app>
        </div>
        <div class="dregg-name-meta">name-hash slot ${NAME_HASH_SLOT}, owner ${OWNER_HASH_SLOT}, expiry ${EXPIRY_SLOT}, revoked ${REVOKED_SLOT}, target ${RESOLVE_TARGET_SLOT}</div>
        ${tip != null ? `<div class="dregg-name-meta">tip height: ${tip}</div>` : ''}
      </div>
    `;
    const app = this.shadowRoot.querySelector('dregg-app[data-embedded-runtime]');
    if (app && window.__starbridgeAppRuntime) app.runtime = window.__starbridgeAppRuntime;
  }
}

// ─── <dregg-name-registry> (light list; can embed name inspectors) ───

class DreggNameRegistryElement extends HTMLElement {
  static get observedAttributes() { return ['uri', 'page-size']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._entries = [];
    this._filter = '';
    this._page = 0;
    this._poll = null;
    this._loading = true;
  }

  connectedCallback() {
    this.refresh();
    this._poll = setInterval(() => this.refresh(), POLL_INTERVAL_MS);
  }
  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
  }
  attributeChangedCallback() { this.refresh(); }

  async refresh() {
    const uri = this.getAttribute('uri') || '';
    this._loading = true;
    try {
      if (window.dregg?.nameservice?.listEntries) {
        this._entries = await window.dregg.nameservice.listEntries(uri) || [];
      } else {
        // Fallback: empty (host must provide enumerator or use cell list + filter)
        this._entries = [];
      }
    } catch (e) {
      console.warn('[dregg-name-registry] load failed', e);
      this._entries = [];
    }
    this._loading = false;
    this.render();
  }

  render() {
    const uri = this.getAttribute('uri') || '';
    const pageSize = Math.max(1, Number(this.getAttribute('page-size') || 10));
    const filter = this._filter.trim().toLowerCase();
    const filtered = filter
      ? this._entries.filter(e => (e.name || '').toLowerCase().includes(filter))
      : this._entries;
    const pages = Math.max(1, Math.ceil(filtered.length / pageSize));
    if (this._page >= pages) this._page = pages - 1;
    if (this._page < 0) this._page = 0;
    const start = this._page * pageSize;
    const slice = filtered.slice(start, start + pageSize);

    this.shadowRoot.innerHTML = `
      <style>
        :host { display:block; font-family:system-ui,sans-serif; }
        .toolbar { display:flex; gap:0.5rem; align-items:center; margin-bottom:0.5rem; flex-wrap:wrap; }
        input { padding:0.3rem; min-width:200px; }
        table { width:100%; border-collapse:collapse; font-size:0.9rem; }
        th,td { border-bottom:1px solid #eee; padding:0.3rem; text-align:left; }
        th { background:#fafafa; }
        a { color:#25439a; text-decoration:none; }
        a:hover { text-decoration:underline; }
        .empty { color:#888; padding:0.5rem; border:1px dashed #ddd; }
        button { padding:0.25rem 0.5rem; }
      </style>
      <div class="toolbar">
        <input type="search" placeholder="Filter names…" value="${escapeHtml(this._filter)}" />
        <span>${filtered.length} names</span>
        <button data-act="refresh">↻</button>
      </div>
      ${this._loading ? '<div class="empty">loading registry…</div>' : ''}
      ${slice.length === 0 ? `<div class="empty">No names${filter ? ' match filter' : ''}.</div>` : `
        <table>
          <thead><tr><th>Name</th><th>Owner</th><th>Expiry</th><th>Status</th></tr></thead>
          <tbody>
            ${slice.map(e => `
              <tr>
                <td><a href="#" data-uri="${escapeHtml(e.uri || uri)}" data-name="${escapeHtml(e.name || '')}">${escapeHtml(e.name || '(unnamed)')}</a></td>
                <td><code>${escapeHtml(hex32(e.owner_hash))}</code></td>
                <td><code>${e.expiry ?? '—'}</code></td>
                <td>${e.revoked ? 'REVOKED' : 'ACTIVE'}</td>
              </tr>
            `).join('')}
          </tbody>
        </table>
      `}
      <div style="margin-top:0.25rem;">
        <button data-act="prev" ${this._page === 0 ? 'disabled' : ''}>‹</button>
        <span> ${this._page + 1}/${pages} </span>
        <button data-act="next" ${this._page >= pages-1 ? 'disabled' : ''}>›</button>
      </div>
    `;

    // wire events (search, pager, clicks)
    const inp = this.shadowRoot.querySelector('input[type=search]');
    inp?.addEventListener('input', e => { this._filter = e.target.value; this._page=0; this.render(); });
    this.shadowRoot.querySelector('[data-act=refresh]')?.addEventListener('click', () => this.refresh());
    this.shadowRoot.querySelector('[data-act=prev]')?.addEventListener('click', () => { this._page--; this.render(); });
    this.shadowRoot.querySelector('[data-act=next]')?.addEventListener('click', () => { this._page++; this.render(); });
    this.shadowRoot.querySelectorAll('a[data-uri]').forEach(a => {
      a.addEventListener('click', ev => {
        ev.preventDefault();
        this.dispatchEvent(new CustomEvent('name-selected', {
          bubbles:true, composed:true,
          detail: { uri: a.dataset.uri, name: a.dataset.name }
        }));
      });
    });
  }
}

// Register
const TAGS = ['dregg-name', 'dregg-name-registry'];

for (const tag of TAGS) {
  const Ctor = tag === 'dregg-name' ? DreggNameElement : DreggNameRegistryElement;
  if (typeof customElements !== 'undefined' && !customElements.get(tag)) {
    customElements.define(tag, Ctor);
  }
  if (typeof window !== 'undefined' && window.dreggUi?.register) {
    window.dreggUi.register(tag, Ctor);
  }
}

export { DreggNameElement, DreggNameRegistryElement, TAGS, NAME_HASH_SLOT, OWNER_HASH_SLOT, EXPIRY_SLOT, REVOKED_SLOT, RESOLVE_TARGET_SLOT };

// starbridge-apps/subscription/pages/inspectors.js
//
// Web components for the starbridge-subscription app:
//
//   <dregg-subscription uri="...">
//     Live head/tail/capacity summary view. Polls every 5s and also
//     subscribes to subscription-published / subscription-consumed
//     events for instant updates.
//
//   <dregg-subscription-publish-form uri="...">
//     Compose-and-send UI; submits via
//     window.dregg.builders.subscription.publish (the cipherclerk-named
//     Action preset that terminates in window.dregg.signTurn).
//
//   <dregg-subscription-feed uri="...">
//     Consumer's live message feed driven by the
//     subscription-published event stream. Includes a Consume button
//     that advances tail by 1 via the consume builder.
//
//   <dregg-subscription-grant-form uri="...">
//     Owner UI for adding publishers / consumers (extends the
//     authorized-set merkle root via grant_publisher / grant_consumer).
//
// All policy lives in Rust (starbridge-apps/subscription/src/lib.rs);
// the JS layer is a thin shim that assembles turn specs and renders
// state. Slot indices mirror constants in src/lib.rs.

const SEQ_HEAD_SLOT = 0;
const SEQ_TAIL_SLOT = 1;
const CAPACITY_SLOT = 2;
const PUBLISHERS_ROOT_SLOT = 3;
const CONSUMERS_ROOT_SLOT = 4;
const OWNER_PK_HASH_SLOT = 5;
const MESSAGE_ROOT_SLOT = 6;
const LATEST_PAYLOAD_SLOT = 7;

const POLL_INTERVAL_MS = 5_000;
const MAX_FEED_ITEMS = 50;

// ─── helpers ─────────────────────────────────────────────────────────────

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

function fieldToU64BE(bytes) {
  let v = 0n;
  for (let i = 24; i < 32; i++) {
    v = (v << 8n) | BigInt(bytes?.[i] ?? 0);
  }
  return Number(v);
}

function hex(bytes) {
  return Array.from(bytes ?? [], (b) => b.toString(16).padStart(2, '0')).join('');
}

function shortHex(bytes, head = 8, tail = 4) {
  const h = hex(bytes);
  if (h.length <= head + tail + 1) return h;
  return `${h.slice(0, head)}…${h.slice(-tail)}`;
}

async function previewPayloadHash(text) {
  if (!text) return '';
  try {
    if (typeof window !== 'undefined' && window.dregg?.blake3) {
      const out = await window.dregg.blake3(new TextEncoder().encode(String(text)));
      return Array.from(out).map((b) => b.toString(16).padStart(2, '0')).join('');
    }
    const buf = await crypto.subtle.digest('SHA-256', new TextEncoder().encode(String(text)));
    return hex(new Uint8Array(buf));
  } catch {
    return '';
  }
}

// =========================================================================
// <dregg-subscription> — live head-of-queue summary
// =========================================================================

class SubscriptionInspector extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._state = null;
    this._error = null;
    this._loading = true;
    this._poll = null;
    this._unsubPublished = null;
    this._unsubConsumed = null;
  }

  connectedCallback() {
    this.refresh();
    this._poll = setInterval(() => this.refresh(), POLL_INTERVAL_MS);
    this.#bindEvents();
  }

  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
    this._poll = null;
    this._unsubPublished?.();
    this._unsubConsumed?.();
  }

  attributeChangedCallback() {
    this._unsubPublished?.();
    this._unsubConsumed?.();
    this.refresh();
    this.#bindEvents();
  }

  #bindEvents() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.dregg?.subscribeEvents) return;
    this._unsubPublished = window.dregg.subscribeEvents(uri, 'subscription-published', () => this.refresh());
    this._unsubConsumed  = window.dregg.subscribeEvents(uri, 'subscription-consumed',  () => this.refresh());
  }

  async refresh() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.dregg?.readCell) {
      this._loading = false;
      this.render();
      return;
    }
    try {
      const cell = await window.dregg.readCell(uri);
      this._state = cell?.state ?? null;
      this._error = null;
    } catch (e) {
      this._error = String(e);
    }
    this._loading = false;
    this.render();
  }

  render() {
    const f = this._state?.fields;
    const head = f ? fieldToU64BE(f[SEQ_HEAD_SLOT]) : '—';
    const tail = f ? fieldToU64BE(f[SEQ_TAIL_SLOT]) : '—';
    const cap = f ? fieldToU64BE(f[CAPACITY_SLOT]) : '—';
    const inflight = (typeof head === 'number' && typeof tail === 'number') ? head - tail : '—';
    const inflightPct = (typeof inflight === 'number' && typeof cap === 'number' && cap > 0)
      ? Math.min(100, Math.round((inflight / cap) * 100)) : 0;

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; padding: 1em; }
        .dregg-subscription-summary-row {
          display: grid;
          grid-template-columns: 240px 1fr;
          gap: 4px;
          margin: 2px 0;
        }
        .dregg-subscription-summary-label { color: #666; }
        .dregg-subscription-summary-error  { color: #c00; }
        .dregg-subscription-summary-gauge {
          background: #eef;
          border-radius: 3px;
          height: 1.2rem;
          position: relative;
          overflow: hidden;
          max-width: 240px;
        }
        .dregg-subscription-summary-gauge-fill {
          background: linear-gradient(90deg, #6b86ee, #3c5cd6);
          height: 100%;
          transition: width 0.3s ease;
        }
        .dregg-subscription-summary-gauge-label {
          position: absolute;
          inset: 0;
          display: grid;
          place-items: center;
          color: #fff;
          font-size: 0.78rem;
          font-weight: 600;
          mix-blend-mode: difference;
        }
        code { font-family: ui-monospace, monospace; }
      </style>
      <article>
        <h3>Subscription</h3>
        ${this._loading ? `<dregg-status-bar state="loading" message="reading cell…"></dregg-status-bar>` : ''}
        ${this._error ? `<div class="dregg-subscription-summary-error">error: ${escapeHtml(this._error)}</div>` : ''}
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">URI</span>
          <code>${escapeHtml(this.getAttribute('uri') ?? '')}</code>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">head (next publish seq)</span>
          <span>${head}</span>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">tail (next consume seq)</span>
          <span>${tail}</span>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">in-flight / capacity</span>
          <div>
            <div class="dregg-subscription-summary-gauge">
              <div class="dregg-subscription-summary-gauge-fill" style="width:${inflightPct}%"></div>
              <div class="dregg-subscription-summary-gauge-label">${inflight} / ${cap}</div>
            </div>
          </div>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">owner (prefix)</span>
          <code>${escapeHtml(f ? shortHex(f[OWNER_PK_HASH_SLOT]) : '—')}</code>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">publishers_root</span>
          <code>${escapeHtml(f ? shortHex(f[PUBLISHERS_ROOT_SLOT]) : '—')}</code>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">consumers_root</span>
          <code>${escapeHtml(f ? shortHex(f[CONSUMERS_ROOT_SLOT]) : '—')}</code>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">message_root</span>
          <code>${escapeHtml(f ? shortHex(f[MESSAGE_ROOT_SLOT]) : '—')}</code>
        </div>
        <div class="dregg-subscription-summary-row">
          <span class="dregg-subscription-summary-label">latest_payload</span>
          <code>${escapeHtml(f ? shortHex(f[LATEST_PAYLOAD_SLOT]) : '—')}</code>
        </div>
      </article>
    `;
  }
}

// =========================================================================
// <dregg-subscription-publish-form>
// =========================================================================

class SubscriptionPublishForm extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._busy = null;
    this._lastReceipt = null;
    this._lastError = null;
    this._hashPreview = '';
  }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const uri = this.getAttribute('uri') ?? '';
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; padding: 1em; }
        .dregg-subscription-publish-form-textarea {
          width: 100%;
          min-height: 6em;
          font: 0.9rem ui-monospace, monospace;
          padding: 0.4rem;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        button {
          margin-top: 0.5em;
          padding: 0.5em 1em;
          font: inherit;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        button[disabled] { opacity: 0.5; cursor: wait; }
        .dregg-subscription-publish-form-hash {
          font: 0.75rem ui-monospace, monospace;
          color: #557;
          word-break: break-all;
          margin-top: 0.4rem;
        }
      </style>
      <article>
        <h3>Publish</h3>
        <p>Send a payload into <code>${escapeHtml(uri)}</code>.
           The cipherclerk publish builder composes
           <code>SetField(head, +1)</code>,
           <code>SetField(message_root, fold(old, payload))</code>,
           <code>SetField(latest_payload, payload_hash)</code>, and
           <code>EmitEvent("subscription-published")</code> into a single
           signed turn.</p>
        <textarea class="dregg-subscription-publish-form-textarea"
                  id="payload"
                  placeholder="payload bytes (utf-8 or hex)"></textarea>
        <div class="dregg-subscription-publish-form-hash">
          blake3(payload) = ${this._hashPreview
            ? escapeHtml(this._hashPreview.slice(0, 16) + '…' + this._hashPreview.slice(-8))
            : '—'}
        </div>
        <button id="send" ${this._busy ? 'disabled' : ''}>${this._busy ? 'publishing…' : 'Publish'}</button>
        <dregg-status-bar
          state="${this._busy ? 'loading' : (this._lastError ? 'error' : (this._lastReceipt ? 'success' : 'idle'))}"
          message="${escapeHtml(this._busy?.message ?? this._lastError ?? (this._lastReceipt ? 'published' : ''))}"
          receipt="${escapeHtml(this._lastReceipt?.id ?? this._lastReceipt?.turnId ?? '')}"
        ></dregg-status-bar>
        ${this._lastReceipt ? `
          <div style="margin-top:0.5rem;">
            <dregg-token-cap
              kind="receipt"
              label="publish"
              target="${escapeHtml(uri)}"
              action="publish"
              tag="${escapeHtml(this._lastReceipt.id ?? this._lastReceipt.turnId ?? '')}"
            ></dregg-token-cap>
          </div>
        ` : ''}
      </article>
    `;

    const payloadEl = this.shadowRoot.getElementById('payload');
    payloadEl?.addEventListener('input', async (e) => {
      this._hashPreview = await previewPayloadHash(e.target.value);
      const hashEl = this.shadowRoot.querySelector('.dregg-subscription-publish-form-hash');
      if (hashEl) {
        hashEl.textContent = `blake3(payload) = ${this._hashPreview
          ? this._hashPreview.slice(0, 16) + '…' + this._hashPreview.slice(-8)
          : '—'}`;
      }
    });
    this.shadowRoot.getElementById('send').onclick = () => this.publish();
  }

  async publish() {
    const uri = this.getAttribute('uri');
    const payload = this.shadowRoot.getElementById('payload').value;
    if (!payload) {
      this._lastError = 'payload is empty';
      this.render();
      return;
    }
    this._busy = { message: 'publishing payload…' };
    this._lastError = null;
    this._lastReceipt = null;
    this.render();
    try {
      const builder = window.dregg?.builders?.subscription?.publish;
      let receipt;
      if (builder) {
        receipt = await builder(uri, payload);
      } else {
        // Fallback inline path (signTurn directly) — kept for hosts
        // that don't preload turn-builders.js.
        const cell = await window.dregg.readCell(uri);
        const oldHead = fieldToU64BE(cell.state.fields[SEQ_HEAD_SLOT]);
        const newHead = new Uint8Array(32);
        const bn = BigInt(oldHead + 1);
        for (let i = 0; i < 8; i += 1) newHead[31 - i] = Number((bn >> BigInt(i * 8)) & 0xffn);
        const payloadBytes = new TextEncoder().encode(payload);
        const payloadHash = new Uint8Array(await crypto.subtle.digest('SHA-256', payloadBytes));
        const rootInput = new Uint8Array(64);
        rootInput.set(cell.state.fields[MESSAGE_ROOT_SLOT], 0);
        rootInput.set(payloadHash, 32);
        const newRoot = new Uint8Array(await crypto.subtle.digest('SHA-256', rootInput));
        receipt = await window.dregg.signTurn({
          target: uri,
          method: 'publish',
          effects: [
            { kind: 'SetField', cell: uri, index: SEQ_HEAD_SLOT,       value: Array.from(newHead) },
            { kind: 'SetField', cell: uri, index: MESSAGE_ROOT_SLOT,   value: Array.from(newRoot) },
            { kind: 'SetField', cell: uri, index: LATEST_PAYLOAD_SLOT, value: Array.from(payloadHash) },
            { kind: 'EmitEvent', cell: uri, topic: 'subscription-published',
              data: [Array.from(newHead), Array.from(newRoot), Array.from(payloadHash)] },
          ],
        });
      }
      this._busy = null;
      this._lastReceipt = receipt ?? { ok: true };
    } catch (e) {
      this._busy = null;
      this._lastError = `publish failed: ${String(e)}`;
    }
    this.render();
  }
}

// =========================================================================
// <dregg-subscription-feed> — live consumer feed
// =========================================================================

class SubscriptionFeed extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._messages = [];
    this._unsubscribe = null;
    this._busy = null;
    this._lastReceipt = null;
    this._lastError = null;
  }

  connectedCallback() {
    this.render();
    this.subscribe();
  }
  disconnectedCallback() {
    this._unsubscribe?.();
  }
  attributeChangedCallback() {
    this._unsubscribe?.();
    this._unsubscribe = null;
    this.subscribe();
  }

  subscribe() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.dregg?.subscribeEvents) return;
    this._unsubscribe = window.dregg.subscribeEvents(
      uri,
      'subscription-published',
      (event) => {
        this._messages.unshift({
          seq: fieldToU64BE(event.data?.[0]),
          root: shortHex(event.data?.[1]),
          payload: shortHex(event.data?.[2]),
          received_at: Date.now(),
        });
        if (this._messages.length > MAX_FEED_ITEMS) this._messages.length = MAX_FEED_ITEMS;
        this.render();
      },
    );
  }

  async consume() {
    const uri = this.getAttribute('uri');
    this._busy = { message: 'consuming next…' };
    this._lastError = null;
    this._lastReceipt = null;
    this.render();
    try {
      const builder = window.dregg?.builders?.subscription?.consume;
      const receipt = builder
        ? await builder(uri)
        : await window.dregg.signTurn({ target: uri, method: 'consume', effects: [] });
      this._busy = null;
      this._lastReceipt = receipt ?? { ok: true };
    } catch (e) {
      this._busy = null;
      this._lastError = `consume failed: ${String(e)}`;
    }
    this.render();
  }

  render() {
    const uri = this.getAttribute('uri') ?? '';
    const rows = this._messages.map((m) => `
      <tr>
        <td>${m.seq}</td>
        <td><code>${escapeHtml(m.root)}</code></td>
        <td><code>${escapeHtml(m.payload)}</code></td>
        <td>${new Date(m.received_at).toLocaleTimeString()}</td>
      </tr>
    `).join('');

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; padding: 1em; }
        .dregg-subscription-feed-table {
          width: 100%;
          border-collapse: collapse;
          margin-top: 0.5em;
        }
        .dregg-subscription-feed-table th,
        .dregg-subscription-feed-table td {
          text-align: left;
          padding: 4px 8px;
          border-bottom: 1px solid #eee;
        }
        .dregg-subscription-feed-table th {
          background: #fafafa;
          font-size: 0.85rem;
        }
        button {
          margin: 0.5em 0;
          padding: 0.5em 1em;
          font: inherit;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        button[disabled] { opacity: 0.5; cursor: wait; }
        .dregg-subscription-feed-empty {
          color: #999;
          padding: 1em;
          text-align: center;
          border: 1px dashed #ddd;
          border-radius: 4px;
        }
        code { font-family: ui-monospace, monospace; }
      </style>
      <article>
        <h3>Feed</h3>
        <p>Live <code>subscription-published</code> events from
           <code>${escapeHtml(uri)}</code>. Click <em>Consume</em> to
           advance tail by 1.</p>
        <button id="consume" ${this._busy ? 'disabled' : ''}>
          ${this._busy ? 'consuming…' : 'Consume next'}
        </button>
        <dregg-status-bar
          state="${this._busy ? 'loading' : (this._lastError ? 'error' : (this._lastReceipt ? 'success' : 'idle'))}"
          message="${escapeHtml(this._busy?.message ?? this._lastError ?? (this._lastReceipt ? 'consumed' : ''))}"
          receipt="${escapeHtml(this._lastReceipt?.id ?? this._lastReceipt?.turnId ?? '')}"
        ></dregg-status-bar>
        ${rows ? `
          <table class="dregg-subscription-feed-table">
            <thead>
              <tr><th>seq</th><th>message_root</th><th>payload</th><th>received</th></tr>
            </thead>
            <tbody>${rows}</tbody>
          </table>
        ` : `<div class="dregg-subscription-feed-empty">(no events yet — waiting for publishers)</div>`}
      </article>
    `;
    const btn = this.shadowRoot.getElementById('consume');
    if (btn) btn.onclick = () => this.consume();
  }
}

// =========================================================================
// <dregg-subscription-grant-form>
// =========================================================================

class SubscriptionGrantForm extends HTMLElement {
  static get observedAttributes() { return ['uri', 'role']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._busy = null;
    this._lastReceipt = null;
    this._lastError = null;
  }
  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    const uri = this.getAttribute('uri') || '';
    const role = (this.getAttribute('role') || 'publisher').toLowerCase();
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; padding: 1em; }
        .dregg-subscription-grant-form {
          display: grid;
          gap: 0.75rem;
          max-width: 420px;
        }
        .dregg-subscription-grant-form label {
          display: grid;
          gap: 0.25rem;
        }
        .dregg-subscription-grant-form input,
        .dregg-subscription-grant-form select {
          padding: 0.4rem;
          font: inherit;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        button[type=submit] {
          padding: 0.55rem;
          font-weight: 600;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        button[disabled] { opacity: 0.5; cursor: wait; }
      </style>
      <form class="dregg-subscription-grant-form">
        <h3 style="margin: 0;">Grant ${escapeHtml(role)} access</h3>
        <div>Subscription: <code>${escapeHtml(uri)}</code></div>
        <label>Role
          <select name="role">
            <option value="publisher" ${role === 'publisher' ? 'selected' : ''}>publisher</option>
            <option value="consumer" ${role === 'consumer' ? 'selected' : ''}>consumer</option>
          </select>
        </label>
        <label>Public key (32 bytes, hex)
          <input name="pk" required placeholder="0x… or 64 hex chars" />
        </label>
        <button type="submit" ${this._busy ? 'disabled' : ''}>
          ${this._busy ? 'granting…' : `Grant ${role}`}
        </button>
      </form>
      <dregg-status-bar
        state="${this._busy ? 'loading' : (this._lastError ? 'error' : (this._lastReceipt ? 'success' : 'idle'))}"
        message="${escapeHtml(this._busy?.message ?? this._lastError ?? (this._lastReceipt ? 'granted' : ''))}"
        receipt="${escapeHtml(this._lastReceipt?.id ?? this._lastReceipt?.turnId ?? '')}"
      ></dregg-status-bar>
      ${this._lastReceipt ? `
        <dregg-token-cap
          kind="cap"
          label="grant_${escapeHtml(role)}"
          target="${escapeHtml(uri)}"
          action="grant_${escapeHtml(role)}"
          tag="${escapeHtml(this._lastReceipt.id ?? this._lastReceipt.turnId ?? '')}"
        ></dregg-token-cap>
      ` : ''}
    `;

    this.shadowRoot.querySelector('select[name=role]')?.addEventListener('change', (e) => {
      this.setAttribute('role', e.target.value);
    });
    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      const fd = new FormData(e.target);
      this.#grant(fd.get('role'), fd.get('pk'));
    });
  }

  async #grant(role, pkHex) {
    const uri = this.getAttribute('uri');
    this._busy = { message: `granting ${role}…` };
    this._lastError = null;
    this._lastReceipt = null;
    this.render();
    try {
      const method = role === 'consumer' ? 'grant_consumer' : 'grant_publisher';
      const builder = window.dregg?.builders?.subscription?.[method];
      if (!builder) throw new Error(`no ${method} builder loaded`);
      const pk = parseHex(pkHex);
      const receipt = await builder(uri, pk);
      this._busy = null;
      this._lastReceipt = receipt ?? { ok: true };
    } catch (e) {
      this._busy = null;
      this._lastError = `grant failed: ${String(e)}`;
    }
    this.render();
  }
}

function parseHex(s) {
  const t = (s || '').trim().replace(/^0x/, '');
  if (!/^[0-9a-fA-F]+$/.test(t)) throw new Error('invalid hex');
  const out = new Uint8Array(t.length / 2);
  for (let i = 0; i < out.length; i += 1) {
    out[i] = parseInt(t.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

// =========================================================================
// Register components
// =========================================================================

const COMPONENTS = {
  'dregg-subscription':              SubscriptionInspector,
  'dregg-subscription-publish-form': SubscriptionPublishForm,
  'dregg-subscription-feed':         SubscriptionFeed,
  'dregg-subscription-grant-form':   SubscriptionGrantForm,
};

if (typeof window !== 'undefined' && typeof customElements !== 'undefined') {
  for (const [tag, ctor] of Object.entries(COMPONENTS)) {
    if (!customElements.get(tag)) customElements.define(tag, ctor);
    window.dreggUi?.register?.(tag, ctor);
  }
}

export {
  SubscriptionInspector,
  SubscriptionPublishForm,
  SubscriptionFeed,
  SubscriptionGrantForm,
};

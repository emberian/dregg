// starbridge-apps/subscription/pages/inspectors.js
//
// Web components for the starbridge-subscription app:
//
//   <pyana-subscription uri="...">             — head-of-queue summary view
//   <pyana-subscription-publish-form>          — publisher's compose-and-send UI
//   <pyana-subscription-feed>                  — consumer's live feed
//
// All three components resolve URIs through `window.pyana` (the in-browser
// PyanaRuntime — see wasm/src/runtime.rs) and produce signed turns via
// `window.pyana.signTurn(turnSpec)` (the extension wallet API — see
// extension/src/page.ts). No app-domain enforcement runs here; the
// cell-program (`subscription_program` in src/lib.rs) is the enforcement
// loop. The web components only assemble turn specs and render state.
//
// Slot indices mirror the constants in `src/lib.rs`. Keep in sync:
//   SEQ_HEAD_SLOT          = 0
//   SEQ_TAIL_SLOT          = 1
//   CAPACITY_SLOT          = 2
//   PUBLISHERS_ROOT_SLOT   = 3
//   CONSUMERS_ROOT_SLOT    = 4
//   OWNER_PK_HASH_SLOT     = 5
//   MESSAGE_ROOT_SLOT      = 6
//   LATEST_PAYLOAD_SLOT    = 7

const SEQ_HEAD_SLOT = 0;
const SEQ_TAIL_SLOT = 1;
const CAPACITY_SLOT = 2;
const PUBLISHERS_ROOT_SLOT = 3;
const CONSUMERS_ROOT_SLOT = 4;
const OWNER_PK_HASH_SLOT = 5;
const MESSAGE_ROOT_SLOT = 6;
const LATEST_PAYLOAD_SLOT = 7;

function u64BE(n) {
  // Big-endian-padded 32-byte field element. Matches the Rust
  // `u64_field` helper in src/lib.rs and pyana_cell::program::field_from_u64_be.
  const out = new Uint8Array(32);
  let v = BigInt(n);
  for (let i = 31; i >= 24 && v > 0n; i--) {
    out[i] = Number(v & 0xffn);
    v >>= 8n;
  }
  return out;
}

function fieldToU64BE(bytes) {
  // Decode a big-endian-padded u64 field element back to a Number.
  let v = 0n;
  for (let i = 24; i < 32; i++) {
    v = (v << 8n) | BigInt(bytes[i] ?? 0);
  }
  return Number(v);
}

function hex(bytes) {
  return Array.from(bytes ?? [], (b) => b.toString(16).padStart(2, '0')).join('');
}

// =========================================================================
// <pyana-subscription> — head-of-queue summary view
// =========================================================================

class SubscriptionInspector extends HTMLElement {
  static get observedAttributes() {
    return ['uri'];
  }
  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._state = null;
    this._unsubscribe = null;
  }
  connectedCallback() {
    this.render();
    this.refresh();
  }
  disconnectedCallback() {
    if (this._unsubscribe) this._unsubscribe();
  }
  attributeChangedCallback() {
    this.refresh();
  }
  async refresh() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.pyana?.readCell) return;
    try {
      const cell = await window.pyana.readCell(uri);
      this._state = cell?.state ?? null;
      this.render();
    } catch (e) {
      this._error = String(e);
      this.render();
    }
  }
  render() {
    const f = this._state?.fields;
    const head = f ? fieldToU64BE(f[SEQ_HEAD_SLOT]) : '—';
    const tail = f ? fieldToU64BE(f[SEQ_TAIL_SLOT]) : '—';
    const cap = f ? fieldToU64BE(f[CAPACITY_SLOT]) : '—';
    const inflight = typeof head === 'number' && typeof tail === 'number' ? head - tail : '—';
    const owner = f ? hex(f[OWNER_PK_HASH_SLOT]).slice(0, 16) : '—';
    const mroot = f ? hex(f[MESSAGE_ROOT_SLOT]).slice(0, 16) : '—';
    const latest = f ? hex(f[LATEST_PAYLOAD_SLOT]).slice(0, 16) : '—';
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; padding: 1em; }
        .row { display: grid; grid-template-columns: 200px 1fr; gap: 4px; margin: 2px 0; }
        .label { color: #666; }
        .err { color: #c00; }
      </style>
      <article>
        <h3>Subscription</h3>
        ${this._error ? `<div class="err">error: ${this._error}</div>` : ''}
        <div class="row"><span class="label">URI</span><code>${this.getAttribute('uri') ?? ''}</code></div>
        <div class="row"><span class="label">head (next publish seq)</span><span>${head}</span></div>
        <div class="row"><span class="label">tail (next consume seq)</span><span>${tail}</span></div>
        <div class="row"><span class="label">in-flight</span><span>${inflight} / ${cap}</span></div>
        <div class="row"><span class="label">owner (prefix)</span><code>${owner}…</code></div>
        <div class="row"><span class="label">message_root (prefix)</span><code>${mroot}…</code></div>
        <div class="row"><span class="label">latest_payload (prefix)</span><code>${latest}…</code></div>
      </article>
    `;
  }
}

// =========================================================================
// <pyana-subscription-publish-form> — publisher's compose-and-send UI
// =========================================================================

class SubscriptionPublishForm extends HTMLElement {
  static get observedAttributes() {
    return ['uri'];
  }
  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
  }
  connectedCallback() {
    this.render();
  }
  attributeChangedCallback() {
    this.render();
  }
  render() {
    const uri = this.getAttribute('uri') ?? '';
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; padding: 1em; }
        textarea { width: 100%; min-height: 6em; font-family: ui-monospace, monospace; }
        button { margin-top: 0.5em; padding: 0.5em 1em; }
        .status { margin-top: 0.5em; min-height: 1.2em; }
        .ok { color: #060; }
        .err { color: #c00; }
      </style>
      <article>
        <h3>Publish</h3>
        <p>Send a payload into <code>${uri}</code>. The turn-builder
           composes <code>SetField(head, +1)</code> +
           <code>SetField(message_root, …)</code> +
           <code>SetField(latest_payload, …)</code> +
           <code>EmitEvent("subscription-published")</code> into a
           single signed Action.</p>
        <textarea id="payload" placeholder="payload bytes (utf-8 or hex)"></textarea>
        <button id="send">Publish</button>
        <div class="status" id="status"></div>
      </article>
    `;
    this.shadowRoot.getElementById('send').onclick = () => this.publish();
  }
  async publish() {
    const uri = this.getAttribute('uri');
    const statusEl = this.shadowRoot.getElementById('status');
    const payload = this.shadowRoot.getElementById('payload').value;
    statusEl.className = '';
    statusEl.textContent = 'publishing…';
    try {
      // Read cell to compute the new head + message_root.
      const cell = await window.pyana.readCell(uri);
      const oldHead = fieldToU64BE(cell.state.fields[SEQ_HEAD_SLOT]);
      const newHead = u64BE(oldHead + 1);
      // The browser doesn't have Poseidon2 wired; we use a BLAKE3-style
      // fold for the placeholder root (matches the Rust test helper).
      const payloadBytes = new TextEncoder().encode(payload);
      const payloadHash = new Uint8Array(
        await crypto.subtle.digest('SHA-256', payloadBytes),
      );
      const rootInput = new Uint8Array(64);
      rootInput.set(cell.state.fields[MESSAGE_ROOT_SLOT], 0);
      rootInput.set(payloadHash, 32);
      const newRoot = new Uint8Array(
        await crypto.subtle.digest('SHA-256', rootInput),
      );
      // Hand the assembled turnSpec to the extension wallet.
      const receipt = await window.pyana.signTurn({
        target: uri,
        method: 'publish',
        effects: [
          { kind: 'SetField', cell: uri, index: SEQ_HEAD_SLOT, value: Array.from(newHead) },
          { kind: 'SetField', cell: uri, index: MESSAGE_ROOT_SLOT, value: Array.from(newRoot) },
          { kind: 'SetField', cell: uri, index: LATEST_PAYLOAD_SLOT, value: Array.from(payloadHash) },
          {
            kind: 'EmitEvent',
            cell: uri,
            topic: 'subscription-published',
            data: [Array.from(newHead), Array.from(newRoot), Array.from(payloadHash)],
          },
        ],
      });
      statusEl.className = 'ok';
      statusEl.textContent = `published (receipt: ${hex(receipt?.id ?? []).slice(0, 16)}…)`;
    } catch (e) {
      statusEl.className = 'err';
      statusEl.textContent = `error: ${e}`;
    }
  }
}

// =========================================================================
// <pyana-subscription-feed> — consumer's live feed
// =========================================================================

class SubscriptionFeed extends HTMLElement {
  static get observedAttributes() {
    return ['uri'];
  }
  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._messages = [];
    this._unsubscribe = null;
  }
  connectedCallback() {
    this.render();
    this.subscribe();
  }
  disconnectedCallback() {
    if (this._unsubscribe) this._unsubscribe();
  }
  attributeChangedCallback() {
    if (this._unsubscribe) {
      this._unsubscribe();
      this._unsubscribe = null;
    }
    this.subscribe();
  }
  subscribe() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.pyana?.subscribeEvents) return;
    this._unsubscribe = window.pyana.subscribeEvents(
      uri,
      'subscription-published',
      (event) => {
        this._messages.unshift({
          seq: fieldToU64BE(event.data[0]),
          root: hex(event.data[1]).slice(0, 16),
          payload: hex(event.data[2]).slice(0, 16),
        });
        if (this._messages.length > 50) this._messages.length = 50;
        this.render();
      },
    );
  }
  async consume() {
    const uri = this.getAttribute('uri');
    const statusEl = this.shadowRoot.getElementById('status');
    statusEl.className = '';
    statusEl.textContent = 'consuming…';
    try {
      const cell = await window.pyana.readCell(uri);
      const oldTail = fieldToU64BE(cell.state.fields[SEQ_TAIL_SLOT]);
      const newTail = u64BE(oldTail + 1);
      const latestPayload = cell.state.fields[LATEST_PAYLOAD_SLOT];
      const receipt = await window.pyana.signTurn({
        target: uri,
        method: 'consume',
        effects: [
          { kind: 'SetField', cell: uri, index: SEQ_TAIL_SLOT, value: Array.from(newTail) },
          {
            kind: 'EmitEvent',
            cell: uri,
            topic: 'subscription-consumed',
            data: [Array.from(newTail), Array.from(latestPayload)],
          },
        ],
      });
      statusEl.className = 'ok';
      statusEl.textContent = `consumed (receipt: ${hex(receipt?.id ?? []).slice(0, 16)}…)`;
    } catch (e) {
      statusEl.className = 'err';
      statusEl.textContent = `error: ${e}`;
    }
  }
  render() {
    const uri = this.getAttribute('uri') ?? '';
    const rows = this._messages
      .map(
        (m) => `<tr><td>${m.seq}</td><td><code>${m.root}…</code></td><td><code>${m.payload}…</code></td></tr>`,
      )
      .join('');
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: system-ui, sans-serif; padding: 1em; }
        table { width: 100%; border-collapse: collapse; margin-top: 0.5em; }
        th, td { text-align: left; padding: 4px 8px; border-bottom: 1px solid #eee; }
        button { margin: 0.5em 0; padding: 0.5em 1em; }
        .status { min-height: 1.2em; }
        .ok { color: #060; }
        .err { color: #c00; }
        .empty { color: #999; padding: 1em; text-align: center; }
      </style>
      <article>
        <h3>Feed</h3>
        <p>Live <code>subscription-published</code> events from <code>${uri}</code>.
           Click <em>Consume</em> to advance tail by 1 (the consume
           turn-builder writes <code>SetField(tail, +1)</code> +
           <code>EmitEvent("subscription-consumed")</code>).</p>
        <button id="consume">Consume next</button>
        <div class="status" id="status"></div>
        ${
          rows
            ? `<table><thead><tr><th>seq</th><th>message_root</th><th>payload</th></tr></thead><tbody>${rows}</tbody></table>`
            : '<div class="empty">(no events yet)</div>'
        }
      </article>
    `;
    const btn = this.shadowRoot.getElementById('consume');
    if (btn) btn.onclick = () => this.consume();
  }
}

// =========================================================================
// Register components
// =========================================================================

if (typeof window !== 'undefined' && typeof customElements !== 'undefined') {
  if (!customElements.get('pyana-subscription')) {
    customElements.define('pyana-subscription', SubscriptionInspector);
  }
  if (!customElements.get('pyana-subscription-publish-form')) {
    customElements.define('pyana-subscription-publish-form', SubscriptionPublishForm);
  }
  if (!customElements.get('pyana-subscription-feed')) {
    customElements.define('pyana-subscription-feed', SubscriptionFeed);
  }
  // Mirror into the shared inspector registry so the Studio's
  // <pyana-app> can resolve URIs to these components.
  window.pyana?.register?.('pyana-subscription', SubscriptionInspector);
  window.pyana?.register?.('pyana-subscription-publish-form', SubscriptionPublishForm);
  window.pyana?.register?.('pyana-subscription-feed', SubscriptionFeed);
}

export {
  SubscriptionInspector,
  SubscriptionPublishForm,
  SubscriptionFeed,
};

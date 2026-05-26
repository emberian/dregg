/**
 * <dregg-stealth-address> — stealth address inspector + demo (FOLLOWUP-14).
 *
 * Strictly follows _base.js + cell patterns: data= support, signals for state,
 * <dregg-*> reuse where avail (placeholders for pedersen etc), ZERO JS reimplementation
 * of dregg stealth/privacy logic (all crypto via wasm privacy fns or explicit
 * "stub - placeholder" visible badges; no DH, no blake sims in fallbacks).
 *
 * Two modes:
 *   Read (uri=...) + data attrs for announcements/view keys.
 *   Demo (mode=demo): progressive steps calling wasm only (derive, create_stealth,
 *     create_value_commitment, scan, verify_conservation). Range/conservation show
 *     visible Placeholder when wasm stub (per plan: use <dregg-pedersen-commitment>
 *     when it lands).
 *
 * Privacy badges adjusted toward Placeholder/Silver (no fake "Fully Private" on sims).
 *
 * Wasm via _runtime._wasm escape (consistent with merkle etc). Houyhnhnm: inspectors
 * read, never reimpl.
 */

import { InspectorBase, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Crypto helpers
// ---------------------------------------------------------------------------

function randomBytes(n) {
  const b = new Uint8Array(n);
  crypto.getRandomValues(b);
  return b;
}

function bytesToHex(bytes) {
  return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
}

function hexToBytes(hex) {
  if (!hex || hex.length % 2 !== 0) return new Uint8Array(0);
  const out = new Uint8Array(hex.length / 2);
  for (let i = 0; i < hex.length; i += 2) {
    out[i / 2] = parseInt(hex.slice(i, i + 2), 16);
  }
  return out;
}

/**
 * Strict wasm-only attempt. Never reimplements stealth/DH/blake/pedersen in JS.
 * Missing bindings return a visible Placeholder result; callers must not invent
 * protocol-looking bytes.
 */
function tryWasm(fn) {
  try {
    const result = fn();
    if (result == null) throw new Error('wasm export returned no value');
    return { result, stub: false };
  } catch (e) {
    return {
      result: null,
      stub: true,
      error: e?.message || String(e),
    };
  }
}

// ---------------------------------------------------------------------------
// Privacy badge helpers
// ---------------------------------------------------------------------------

const PRIVACY_META = {
  'Fully Private': {
    label: 'Fully Private',
    color: '#3a7a3a',
    textColor: '#a0d4a0',
    title: 'All crypto operations used verified wasm implementations',
  },
  'Selective': {
    label: 'Selective',
    color: '#6a4820',
    textColor: '#d4a060',
    title: 'Some operations are missing wasm support and are shown as placeholders',
  },
  'Trusted': {
    label: 'Trusted',
    color: '#2a2a4a',
    textColor: '#8888cc',
    title: 'No wasm support for this flow — no cryptographic claim is made',
  },
};

function privacyLevel(stubCount, total) {
  if (stubCount === 0) return 'Fully Private';
  if (stubCount < total) return 'Selective';
  return 'Trusted';
}

// ---------------------------------------------------------------------------
// Styles (injected once)
// ---------------------------------------------------------------------------

const STYLES = `
.dregg-stealth {
  font-family: ui-monospace, monospace;
  font-size: 0.875rem;
  background: var(--bg-raised, #0d1410);
  border: 1px solid var(--line, #2a302d);
  border-radius: 8px;
  overflow: hidden;
}
.dregg-stealth__header {
  display: flex;
  align-items: center;
  gap: 10px;
  padding: 10px 14px;
  border-bottom: 1px solid var(--line, #2a302d);
  flex-wrap: wrap;
}
.dregg-stealth__kind {
  padding: 2px 8px;
  background: var(--accent, #5b8a5a);
  color: #0a0f0d;
  border-radius: 3px;
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  font-weight: 700;
}
.dregg-stealth__badge {
  display: inline-block;
  padding: 2px 8px;
  border-radius: 3px;
  font-size: 0.7rem;
  font-weight: 700;
  letter-spacing: 0.05em;
  text-transform: uppercase;
}
.dregg-stealth__meta-addr {
  color: var(--fg-dim, #6a8070);
  font-size: 0.8rem;
  margin-left: auto;
}
.dregg-stealth__body {
  padding: 12px 14px;
  display: flex;
  flex-direction: column;
  gap: 12px;
}

/* KV grid */
.dregg-stealth__kv {
  display: grid;
  grid-template-columns: 130px 1fr;
  gap: 5px 14px;
  margin: 0;
}
.dregg-stealth__kv dt { color: var(--fg-dim, #6a8070); }
.dregg-stealth__kv dd { margin: 0; word-break: break-all; }
.dregg-stealth__kv code { font-size: 0.8rem; word-break: break-all; }

/* Received panel */
.dregg-stealth__received {
  border: 1px solid var(--line, #2a302d);
  border-radius: 5px;
  overflow: hidden;
}
.dregg-stealth__received-header {
  padding: 6px 10px;
  background: var(--bg, #0a0f0d);
  border-bottom: 1px solid var(--line, #2a302d);
  font-size: 0.78rem;
  color: var(--fg-dim, #6a8070);
  display: flex;
  align-items: center;
  gap: 8px;
}
.dregg-stealth__received-count {
  padding: 1px 6px;
  border-radius: 3px;
  background: #1a2e1a;
  color: #5b8a5a;
  font-size: 0.7rem;
  font-weight: 700;
}
.dregg-stealth__received-list {
  list-style: none;
  margin: 0;
  padding: 0;
}
.dregg-stealth__received-item {
  padding: 7px 10px;
  border-bottom: 1px solid var(--line, #2a302d);
  display: flex;
  align-items: center;
  gap: 10px;
  font-size: 0.8rem;
}
.dregg-stealth__received-item:last-child { border-bottom: none; }
.dregg-stealth__received-item--hidden {
  color: var(--fg-dim, #6a8070);
  font-style: italic;
}
.dregg-stealth__received-item--ours {
  color: #a0d4a0;
}
.dregg-stealth__detected-badge {
  padding: 1px 5px;
  border-radius: 2px;
  background: #1a3a1a;
  border: 1px solid #3a5a3a;
  color: #5b8a5a;
  font-size: 0.68rem;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  flex-shrink: 0;
}
.dregg-stealth__hidden-badge {
  padding: 1px 5px;
  border-radius: 2px;
  background: #1e1208;
  border: 1px solid #4a3010;
  color: #8a6a30;
  font-size: 0.68rem;
  text-transform: uppercase;
  letter-spacing: 0.05em;
  flex-shrink: 0;
}
.dregg-stealth__empty-received {
  padding: 14px 10px;
  color: var(--fg-dim, #6a8070);
  font-size: 0.8rem;
  text-align: center;
}

/* Demo mode */
.dregg-stealth-demo {
  font-family: ui-monospace, monospace;
  font-size: 0.875rem;
  display: flex;
  flex-direction: column;
  gap: 0;
}
.dregg-stealth-demo__step {
  border: 1px solid var(--line, #2a302d);
  border-radius: 6px;
  overflow: hidden;
  margin-bottom: 10px;
}
.dregg-stealth-demo__step-header {
  padding: 8px 12px;
  background: var(--bg-raised, #0d1410);
  border-bottom: 1px solid var(--line, #2a302d);
  display: flex;
  align-items: center;
  gap: 10px;
}
.dregg-stealth-demo__step-num {
  padding: 1px 7px;
  background: #2a302d;
  color: var(--fg-dim, #6a8070);
  border-radius: 3px;
  font-size: 0.7rem;
  font-weight: 700;
}
.dregg-stealth-demo__step-num--done {
  background: #1a3a1a;
  color: #5b8a5a;
}
.dregg-stealth-demo__step-num--err {
  background: #3a1818;
  color: #d4685c;
}
.dregg-stealth-demo__step-title {
  font-size: 0.82rem;
  color: var(--fg, #c8d4cc);
}
.dregg-stealth-demo__step-body {
  padding: 10px 12px;
  background: var(--bg, #0a0f0d);
}
.dregg-stealth-demo__kv {
  display: grid;
  grid-template-columns: 140px 1fr;
  gap: 4px 12px;
  margin: 0;
  font-size: 0.8rem;
}
.dregg-stealth-demo__kv dt { color: var(--fg-dim, #6a8070); }
.dregg-stealth-demo__kv dd { margin: 0; word-break: break-all; }
.dregg-stealth-demo__kv code { font-size: 0.77rem; }
.dregg-stealth-demo__controls {
  padding: 10px 12px;
  background: var(--bg-raised, #0d1410);
  border-top: 1px solid var(--line, #2a302d);
  display: flex;
  align-items: center;
  gap: 10px;
  flex-wrap: wrap;
}
.dregg-stealth-demo__btn {
  padding: 6px 14px;
  border: 1px solid var(--line, #2a302d);
  border-radius: 4px;
  background: var(--bg, #0a0f0d);
  color: var(--fg, #c8d4cc);
  font: inherit;
  font-size: 0.82rem;
  cursor: pointer;
  transition: border-color 0.12s;
}
.dregg-stealth-demo__btn:hover:not(:disabled) { border-color: var(--accent, #5b8a5a); color: #a0d4a0; }
.dregg-stealth-demo__btn:disabled { opacity: 0.4; cursor: not-allowed; }
.dregg-stealth-demo__btn--primary {
  background: #1a3a1a;
  border-color: #3a5a3a;
  color: #a0d4a0;
}
.dregg-stealth-demo__btn--primary:hover:not(:disabled) { background: #244a24; border-color: #5b8a5a; }
.dregg-stealth-demo__input {
  padding: 5px 9px;
  border: 1px solid var(--line, #2a302d);
  border-radius: 4px;
  background: var(--bg, #0a0f0d);
  color: var(--fg, #c8d4cc);
  font: inherit;
  font-size: 0.82rem;
}
.dregg-stealth-demo__input:focus { outline: none; border-color: var(--accent, #5b8a5a); }
.dregg-stealth-demo__label {
  font-size: 0.78rem;
  color: var(--fg-dim, #6a8070);
  white-space: nowrap;
}
.dregg-stealth-demo__stub-warn {
  font-size: 0.75rem;
  color: #a07830;
  background: #1e1208;
  border: 1px solid #4a3010;
  border-radius: 3px;
  padding: 3px 7px;
  margin-top: 6px;
}
.dregg-stealth-demo__conservation {
  padding: 8px 10px;
  border-radius: 4px;
  font-size: 0.82rem;
}
.dregg-stealth-demo__conservation--valid   { background: #0d200d; border: 1px solid #3a5a3a; color: #a0d4a0; }
.dregg-stealth-demo__conservation--stub    { background: #1e1208; border: 1px solid #6a4020; color: #d4a060; }
.dregg-stealth-demo__conservation--invalid { background: #200d0d; border: 1px solid #6a2020; color: #d4908c; }
.dregg-stealth-demo__timeline {
  display: flex;
  flex-direction: column;
  gap: 3px;
  font-size: 0.78rem;
}
.dregg-stealth-demo__timeline-entry { display: flex; gap: 8px; }
.dregg-stealth-demo__timeline-entry--info    { color: var(--fg-dim, #6a8070); }
.dregg-stealth-demo__timeline-entry--success { color: #a0d4a0; }
.dregg-stealth-demo__timeline-entry--warn    { color: #d4a060; }
.dregg-stealth-demo__timeline-actor {
  min-width: 80px;
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.04em;
  padding-top: 1px;
  flex-shrink: 0;
}
.dregg-stealth-demo__range-proof {
  font-size: 0.78rem;
  color: var(--fg-dim, #6a8070);
  padding: 4px 0;
}
`;

let _stylesInjected = false;
function injectStyles() {
  if (_stylesInjected) return;
  _stylesInjected = true;
  const el = document.createElement('style');
  el.id = 'dregg-stealth-address-styles';
  el.textContent = STYLES;
  document.head.appendChild(el);
}

if (typeof window !== 'undefined') injectStyles();

// ---------------------------------------------------------------------------
// Escaping helpers
// ---------------------------------------------------------------------------

function escHtml(s) {
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;');
}

// ---------------------------------------------------------------------------
// Demo state machine
// ---------------------------------------------------------------------------

/**
 * DemoState holds the progressive state for mode="demo".
 * Steps are executed one at a time; each step returns data appended
 * to a shared timeline. This is a plain object so Preact signals can
 * hold it by reference.
 */
function makeDemoState() {
  return {
    step: 0,            // 0=idle, 1=keysReady, 2=addrReady, 3=commitReady, 4=scanned, 5=conservation
    mnemonic: 'correct horse battery staple',
    passphrase: 'dregg-demo',
    amount: 500,
    stubCount: 0,
    callCount: 0,

    // Derived values from each step
    recipientKeys: null,
    stealthAddr: null,
    commitment: null,
    blinding: null,
    rangeProof: null,
    announcements: [],
    scanResult: null,
    conservResult: null,
    timeline: [],
  };
}

// ---------------------------------------------------------------------------
// Custom element
// ---------------------------------------------------------------------------

class DreggStealth extends InspectorBase {
  constructor() {
    super();
    this._demoState = null; // lazily created in demo mode
  }

  _render() {
    const { h, render, html, signal, effect } = this._api;
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;

    if (mode === 'compact') {
      this._renderCompact(h, render, effect, wasm);
      return;
    }

    if (mode === 'demo') {
      this._renderDemo(h, render, html, signal, effect, wasm);
      return;
    }

    // Default / read mode
    this._renderDefault(h, render, html, effect, wasm);
  }

  // -------------------------------------------------------------------------
  // Compact mode
  // -------------------------------------------------------------------------
  _renderCompact(h, render, effect, wasm) {
    const refAttr = this.getAttribute('uri') || '';
    // Extract meta_address from URI segment (dregg://stealth/<meta_address>)
    let metaAddr = '';
    try {
      const m = /^dregg:\/\/stealth\/([^/?#]+)/.exec(refAttr.trim());
      if (m) metaAddr = m[1];
    } catch {}

    const root = document.createElement('span');
    this.appendChild(root);

    const Component = () =>
      h('span', { class: 'dregg-inspector dregg-inspector--compact' },
        h('span', { class: 'dregg-inspector__kind' }, 'stealth'),
        ' ',
        metaAddr
          ? h('code', { title: metaAddr }, 'meta=' + shortHex(metaAddr, 8) + '…')
          : h('em', { style: 'opacity:0.5;' }, 'no uri'),
        ' · ',
        h('em', { style: 'color:var(--fg-dim);font-size:0.8rem;' }, 'demo mode only')
      );

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }

  // -------------------------------------------------------------------------
  // Default (read) mode
  // -------------------------------------------------------------------------
  _renderDefault(h, render, html, effect, wasm) {
    const refAttr = this.getAttribute('uri') || '';
    let metaAddr = '';
    try {
      const m = /^dregg:\/\/stealth\/([^/?#]+)/.exec(refAttr.trim());
      if (m) metaAddr = m[1];
    } catch {}

    // Derive display keys from the meta address (treat as spend_pubkey hex)
    // In a real system, the meta_address encodes both keys. For the inspector
    // we split the hex in half as a deterministic (display-only) approximation.
    const spendPubHex = metaAddr.length >= 64 ? metaAddr.slice(0, 64) : metaAddr || ('0'.repeat(64));
    const viewPubHex  = metaAddr.length >= 128 ? metaAddr.slice(64, 128)
                      : metaAddr.length >= 64   ? metaAddr.slice(0, 64).split('').reverse().join('')
                      : ('f'.repeat(64));

    // Scan for received announcements (none in read mode without a view_privkey)
    // The inspector shows "N received" when a view_privkey is passed as data attr.
    const viewPrivAttr = this.getAttribute('view-privkey') || '';
    const spendPubAttr = this.getAttribute('spend-pubkey') || spendPubHex;

    // Simulated announcements (none by default in read mode)
    const announcementsAttr = this.getAttribute('announcements') || '[]';
    let announcements = [];
    try { announcements = JSON.parse(announcementsAttr); } catch {}

    // Scan using wasm if view_privkey provided
    let receivedItems = [];
    let privacyLevel = 'Trusted';

    if (viewPrivAttr && wasm && announcements.length > 0) {
      try {
        const viewPrivBytes = hexToBytes(viewPrivAttr);
        const spendPubBytes = hexToBytes(spendPubAttr);
        const matched = wasm.scan_stealth_announcements(
          viewPrivBytes, spendPubBytes, JSON.stringify(announcements)
        );
        const matchedSet = new Set(Array.isArray(matched) ? matched : []);
        receivedItems = announcements.map((ann, i) => ({
          index: i,
          ours: matchedSet.has(i),
          ephemeralPubHex: ann.ephemeral_pubkey
            ? bytesToHex(new Uint8Array(ann.ephemeral_pubkey))
            : (ann.ephemeral_pubkey_hex || ''),
        }));
        privacyLevel = 'Fully Private';
      } catch {
        // Wasm scan failed — show all as hidden
        receivedItems = announcements.map((ann, i) => ({
          index: i, ours: false,
          ephemeralPubHex: ann.ephemeral_pubkey
            ? bytesToHex(new Uint8Array(ann.ephemeral_pubkey))
            : '',
        }));
        privacyLevel = 'Selective';
      }
    } else if (announcements.length > 0) {
      receivedItems = announcements.map((ann, i) => ({
        index: i, ours: false,
        ephemeralPubHex: ann.ephemeral_pubkey
          ? bytesToHex(new Uint8Array(ann.ephemeral_pubkey))
          : '',
      }));
    }

    const ownedCount = receivedItems.filter(r => r.ours).length;
    const privMeta = PRIVACY_META[privacyLevel] || PRIVACY_META['Trusted'];

    const root = document.createElement('div');
    this.appendChild(root);

    const ReceivedItem = ({ item }) => {
      if (!item.ours) {
        return h('li', {
          class: 'dregg-stealth__received-item dregg-stealth__received-item--hidden',
        },
          h('span', { class: 'dregg-stealth__hidden-badge' }, 'hidden'),
          'ephemeral ',
          h('code', { title: item.ephemeralPubHex }, shortHex(item.ephemeralPubHex, 12)),
          ' — not addressed to this key'
        );
      }
      return h('li', {
        class: 'dregg-stealth__received-item dregg-stealth__received-item--ours',
      },
        h('span', { class: 'dregg-stealth__detected-badge' }, 'detected'),
        'ephemeral ',
        h('code', { title: item.ephemeralPubHex }, shortHex(item.ephemeralPubHex, 12)),
        ' — ownership confirmed'
      );
    };

    const ReceivedPanel = () => {
      return h('div', { class: 'dregg-stealth__received' },
        h('div', { class: 'dregg-stealth__received-header' },
          'received',
          h('span', { class: 'dregg-stealth__received-count' }, String(ownedCount))
        ),
        receivedItems.length === 0
          ? h('div', { class: 'dregg-stealth__empty-received' }, 'no announcements to scan')
          : h('ul', { class: 'dregg-stealth__received-list' },
              ...receivedItems.map(item => h(ReceivedItem, { key: item.index, item }))
            )
      );
    };

    const Component = () =>
      h('div', { class: 'dregg-inspector dregg-stealth' },
        h('div', { class: 'dregg-stealth__header' },
          h('span', { class: 'dregg-stealth__kind' }, 'stealth address'),
          h('span', {
            class: 'dregg-stealth__badge',
            title: privMeta.title,
            style: `background:${privMeta.color};color:${privMeta.textColor};`,
          }, privMeta.label),
          metaAddr
            ? h('code', { class: 'dregg-stealth__meta-addr', title: metaAddr },
                shortHex(metaAddr, 16))
            : null
        ),
        h('div', { class: 'dregg-stealth__body' },
          h('dl', { class: 'dregg-stealth__kv' },
            h('dt', null, 'spend pubkey'),
            h('dd', null, h('code', { title: spendPubHex }, shortHex(spendPubHex, 24))),
            h('dt', null, 'view pubkey'),
            h('dd', null, h('code', { title: viewPubHex }, shortHex(viewPubHex, 24))),
            h('dt', null, 'meta address'),
            h('dd', null,
              metaAddr
                ? h('code', { title: metaAddr }, shortHex(metaAddr, 32))
                : h('em', { style: 'color:var(--fg-dim);' }, 'no uri')
            )
          ),
          h(ReceivedPanel, {})
        )
      );

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }

  // -------------------------------------------------------------------------
  // Demo mode — full interactive flow
  // -------------------------------------------------------------------------
  _renderDemo(h, render, html, signal, effect, wasm) {
    if (!this._demoState) {
      this._demoState = makeDemoState();
    }
    const ds = this._demoState;

    // Use a signal to trigger re-renders when demo state mutates
    const tick = signal(0);
    const bump = () => { tick.value = tick.value + 1; };

    const root = document.createElement('div');
    this.appendChild(root);

    // ---- Wasm call wrappers ------------------------------------------------

    const doStep1 = () => {
      ds.stubCount = 0;
      ds.callCount = 0;
      ds.timeline = [];
      ds.recipientKeys = null;
      ds.stealthAddr = null;
      ds.commitment = null;
      ds.blinding = null;
      ds.rangeProof = null;
      ds.announcements = [];
      ds.scanResult = null;
      ds.conservResult = null;

      const tw = tryWasm(() => wasm && wasm.derive_stealth_keys(ds.mnemonic, ds.passphrase));
      const result = tw.result || {};
      const stub = tw.stub;
      ds.callCount++;
      if (stub) {
        ds.stubCount++;
        ds.timeline.push({ actor: 'recipient', type: 'warn', text: `derive stealth keys: awaiting wasm32 support (${tw.error || 'missing export'})` });
        bump();
        return;
      }
      const sp = result.spend_pubkey;
      const spp = result.spend_privkey;
      const vp = result.view_pubkey;
      const vpp = result.view_privkey;
      ds.recipientKeys = {
        spendPub:  new Uint8Array(sp),
        spendPriv: new Uint8Array(spp),
        viewPub:   new Uint8Array(vp),
        viewPriv:  new Uint8Array(vpp),
      };
      ds.timeline.push(
        { actor: 'recipient', type: 'success', text: 'derived stealth keys from mnemonic' },
        { actor: '', type: 'info', text: `  view pubkey:  ${bytesToHex(ds.recipientKeys.viewPub).slice(0, 32)}…` },
        { actor: '', type: 'info', text: `  spend pubkey: ${bytesToHex(ds.recipientKeys.spendPub).slice(0, 32)}…` },
        { actor: '', type: 'info', text: `  (private keys kept secret — never shared)` },
      );
      ds.step = 1;
      bump();
    };

    const doStep2 = () => {
      if (!ds.recipientKeys) return;

      // Create stealth address
      const { result: addrResult, stub: addrStub } = tryWasm(
        () => wasm && wasm.create_stealth_address(ds.recipientKeys.spendPub, ds.recipientKeys.viewPub)
      );
      ds.callCount++;
      if (addrStub) {
        ds.stubCount++;
        ds.timeline.push({ actor: 'sender', type: 'warn', text: 'create stealth address: awaiting wasm32 support' });
        bump();
        return;
      }
      ds.stealthAddr = {
        oneTimePubkey:  new Uint8Array(addrResult.one_time_pubkey),
        ephemeralPubkey: new Uint8Array(addrResult.ephemeral_pubkey),
      };

      // Create value commitment
      ds.blinding = randomBytes(32);
      const { result: commitResult, stub: commitStub } = tryWasm(
        () => wasm && wasm.create_value_commitment(BigInt(ds.amount), ds.blinding)
      );
      ds.callCount++;
      if (commitStub) {
        ds.stubCount++;
        ds.timeline.push({ actor: 'sender', type: 'warn', text: 'value commitment: awaiting wasm32 support' });
        bump();
        return;
      }
      ds.commitment = new Uint8Array(commitResult.commitment);

      // Record announcement
      const viewTag = ds.stealthAddr.ephemeralPubkey[0] & 0xFF;
      ds.announcements.push({
        ephemeral_pubkey: Array.from(ds.stealthAddr.ephemeralPubkey),
        one_time_pubkey:  Array.from(ds.stealthAddr.oneTimePubkey),
        view_tag: viewTag,
      });

      ds.timeline.push(
        { actor: 'sender', type: 'success', text: 'created one-time stealth address' },
        { actor: '', type: 'info', text: `  one-time pubkey:  ${bytesToHex(ds.stealthAddr.oneTimePubkey).slice(0, 32)}…` },
        { actor: '', type: 'info', text: `  ephemeral pubkey: ${bytesToHex(ds.stealthAddr.ephemeralPubkey).slice(0, 32)}…` },
        { actor: 'sender', type: 'success', text: `committed transfer: ${ds.amount} (hidden)` },
        { actor: '', type: 'info', text: `  commitment: ${bytesToHex(ds.commitment).slice(0, 32)}…` },
        { actor: '', type: 'info', text: `  (amount and blinding factor are secret)` },
      );
      ds.step = 2;
      bump();
    };

    const doStep3 = () => {
      if (!ds.recipientKeys || !ds.commitment) return;

      // Range proof (graceful stub if not available)
      // wasm signature: generate_range_proof(amount, blinding, commitment)
      const { result: rpResult, stub: rpStub } = tryWasm(
        () => wasm && wasm.generate_range_proof(BigInt(ds.amount), ds.blinding, ds.commitment)
      );
      ds.callCount++;
      if (rpStub) {
        ds.stubCount++;
        ds.rangeProof = null;
        ds.timeline.push({ actor: 'sender', type: 'warn', text: 'range proof: awaiting wasm32 support; no proof bytes generated' });
        bump();
        return;
      }
      ds.rangeProof = {
        bytes: new Uint8Array(rpResult.proof_bytes || []),
        stub: !!rpResult.stub,
      };

      ds.timeline.push(
        { actor: 'sender', type: rpStub ? 'warn' : 'success',
          text: rpStub
            ? `range proof: stub (${ds.rangeProof.bytes.length} B placeholder)`
            : `range proof generated (${ds.rangeProof.bytes.length} B bulletproof)` },
        { actor: '', type: 'info', text: `  proves amount ∈ [0, 2^64) without revealing value` },
      );
      ds.step = 3;
      bump();
    };

    const doStep4 = () => {
      if (!ds.recipientKeys || ds.announcements.length === 0) return;

      const { result: scanResult, stub: scanStub } = tryWasm(
        () => wasm && wasm.scan_stealth_announcements(
          ds.recipientKeys.viewPriv,
          ds.recipientKeys.spendPub,
          JSON.stringify(ds.announcements)
        )
      );
      ds.callCount++;
      if (scanStub) {
        ds.stubCount++;
        ds.scanResult = null;
        ds.timeline.push({ actor: 'recipient', type: 'warn', text: 'scan announcements: awaiting wasm32 support; no matches inferred in JS' });
        bump();
        return;
      }
      ds.scanResult = {
        matched: Array.isArray(scanResult) ? scanResult : [],
        stub: scanStub,
      };

      const found = ds.scanResult.matched.length;
      ds.timeline.push(
        { actor: 'recipient', type: 'info', text: `scanning ${ds.announcements.length} announcement(s)…` },
        { actor: 'recipient', type: 'success', text: `found ${found} payment(s) addressed to us` },
        { actor: '', type: 'info', text: `  matched indices: [${ds.scanResult.matched.join(', ')}]` },
        { actor: '', type: 'info', text: `  can now derive spending key and claim funds` },
      );
      ds.step = 4;
      bump();
    };

    const doStep5 = () => {
      if (!ds.commitment) return;
      const conservProbe = tryWasm(() => wasm && wasm.verify_conservation_proof);
      ds.callCount++;
      ds.stubCount++;
      ds.conservResult = {
        valid: false,
        not_implemented: true,
        input_count: 0,
        output_count: 1,
        reason: conservProbe.stub
          ? 'verify_conservation_proof wasm export missing'
          : 'inspector lacks canonical input commitment set for this transfer',
      };

      ds.timeline.push(
        { actor: 'verifier', type: 'warn', text: 'conservation proof: awaiting canonical input/output commitment set from runtime' },
        { actor: '', type: 'info', text: '  no JS-side commitment set was fabricated' },
      );
      ds.step = 5;
      bump();
    };

    // ---- Component --------------------------------------------------------

    const Component = () => {
      // Force dependency on tick
      tick.value;

      const s = ds;
      const privLevel = privacyLevel(s.stubCount, s.callCount);
      const privMeta  = PRIVACY_META[privLevel] || PRIVACY_META['Trusted'];

      // Step status helpers
      const stepDone = (n) => s.step >= n;

      const StepBadge = ({ n }) =>
        h('span', {
          class: 'dregg-stealth-demo__step-num' + (stepDone(n) ? ' dregg-stealth-demo__step-num--done' : ''),
        }, stepDone(n) ? '✓ ' + n : String(n));

      const Timeline = () => {
        if (!s.timeline.length) return null;
        return h('div', { class: 'dregg-stealth-demo__timeline' },
          ...s.timeline.map((entry, i) =>
            h('div', {
              key: i,
              class: 'dregg-stealth-demo__timeline-entry dregg-stealth-demo__timeline-entry--' + entry.type,
            },
              entry.actor
                ? h('span', { class: 'dregg-stealth-demo__timeline-actor' }, '[' + entry.actor + ']')
                : h('span', { class: 'dregg-stealth-demo__timeline-actor' }),
              h('span', null, entry.text)
            )
          )
        );
      };

      const StubWarn = ({ msg }) =>
        h('div', { class: 'dregg-stealth-demo__stub-warn' }, msg);

      // --- Step 1: Derive Keys ---
      const Step1 = () =>
        h('div', { class: 'dregg-stealth-demo__step' },
          h('div', { class: 'dregg-stealth-demo__step-header' },
            h(StepBadge, { n: 1 }),
            h('span', { class: 'dregg-stealth-demo__step-title' }, 'Derive Stealth Keys')
          ),
          h('div', { class: 'dregg-stealth-demo__step-body' },
            s.recipientKeys
              ? h('dl', { class: 'dregg-stealth-demo__kv' },
                  h('dt', null, 'view pubkey'),
                  h('dd', null, h('code', { title: bytesToHex(s.recipientKeys.viewPub) },
                    shortHex(bytesToHex(s.recipientKeys.viewPub), 24))),
                  h('dt', null, 'spend pubkey'),
                  h('dd', null, h('code', { title: bytesToHex(s.recipientKeys.spendPub) },
                    shortHex(bytesToHex(s.recipientKeys.spendPub), 24))),
                  h('dt', null, 'scheme'),
                  h('dd', null, 'X25519 Diffie-Hellman')
                )
              : h('div', { style: 'color:var(--fg-dim);font-size:0.8rem;' },
                  'Enter a mnemonic + passphrase to derive the recipient\'s key pair.')
          ),
          h('div', { class: 'dregg-stealth-demo__controls' },
            h('span', { class: 'dregg-stealth-demo__label' }, 'mnemonic'),
            h('input', {
              class: 'dregg-stealth-demo__input',
              style: 'width:240px;',
              value: s.mnemonic,
              spellcheck: 'false',
              onInput: (e) => { s.mnemonic = e.target.value; },
            }),
            h('span', { class: 'dregg-stealth-demo__label' }, 'passphrase'),
            h('input', {
              class: 'dregg-stealth-demo__input',
              style: 'width:100px;',
              value: s.passphrase,
              spellcheck: 'false',
              onInput: (e) => { s.passphrase = e.target.value; },
            }),
            h('button', {
              class: 'dregg-stealth-demo__btn dregg-stealth-demo__btn--primary',
              onClick: doStep1,
            }, 'Derive Keys')
          )
        );

      // --- Step 2: Create Stealth Address + Commitment ---
      const Step2 = () =>
        h('div', { class: 'dregg-stealth-demo__step' },
          h('div', { class: 'dregg-stealth-demo__step-header' },
            h(StepBadge, { n: 2 }),
            h('span', { class: 'dregg-stealth-demo__step-title' },
              'Create Stealth Address + Value Commitment')
          ),
          h('div', { class: 'dregg-stealth-demo__step-body' },
            s.stealthAddr && s.commitment
              ? h('dl', { class: 'dregg-stealth-demo__kv' },
                  h('dt', null, 'one-time pubkey'),
                  h('dd', null, h('code', { title: bytesToHex(s.stealthAddr.oneTimePubkey) },
                    shortHex(bytesToHex(s.stealthAddr.oneTimePubkey), 24))),
                  h('dt', null, 'ephemeral pubkey'),
                  h('dd', null, h('code', { title: bytesToHex(s.stealthAddr.ephemeralPubkey) },
                    shortHex(bytesToHex(s.stealthAddr.ephemeralPubkey), 24))),
                  h('dt', null, 'commitment'),
                  h('dd', null, h('code', { title: bytesToHex(s.commitment) },
                    shortHex(bytesToHex(s.commitment), 24))),
                  h('dt', null, 'amount (hidden)'),
                  h('dd', null, h('code', null, String(s.amount) + ' (committed)'))
                )
              : h('div', { style: 'color:var(--fg-dim);font-size:0.8rem;' },
                  stepDone(1)
                    ? 'Ready — sender derives a one-time address and commits the transfer amount.'
                    : 'Complete step 1 first.')
          ),
          h('div', { class: 'dregg-stealth-demo__controls' },
            h('span', { class: 'dregg-stealth-demo__label' }, 'amount'),
            h('input', {
              class: 'dregg-stealth-demo__input',
              style: 'width:80px;',
              type: 'number',
              min: '1',
              max: '1000',
              value: String(s.amount),
              onInput: (e) => { s.amount = parseInt(e.target.value) || 500; },
            }),
            h('button', {
              class: 'dregg-stealth-demo__btn dregg-stealth-demo__btn--primary',
              disabled: !stepDone(1),
              onClick: doStep2,
            }, 'Send Private Transfer')
          )
        );

      // --- Step 3: Range Proof ---
      const Step3 = () =>
        h('div', { class: 'dregg-stealth-demo__step' },
          h('div', { class: 'dregg-stealth-demo__step-header' },
            h(StepBadge, { n: 3 }),
            h('span', { class: 'dregg-stealth-demo__step-title' }, 'Generate Range Proof')
          ),
          h('div', { class: 'dregg-stealth-demo__step-body' },
            s.rangeProof
              ? h('div', null,
                  h('dl', { class: 'dregg-stealth-demo__kv' },
                    h('dt', null, 'proof size'),
                    h('dd', null, h('code', null, s.rangeProof.bytes.length + ' bytes')),
                    h('dt', null, 'range'),
                    h('dd', null, h('code', null, '[0, 2^64)')),
                    h('dt', null, 'scheme'),
                    h('dd', null, h('code', null, s.rangeProof.stub ? 'stub (bulletproof planned)' : 'bulletproof'))
                  ),
                  s.rangeProof.stub
                    ? h(StubWarn, { msg: 'generate_range_proof: wasm stub — not a real bulletproof' })
                    : null
                )
              : h('div', { style: 'color:var(--fg-dim);font-size:0.8rem;' },
                  stepDone(2)
                    ? 'Ready — prove amount is in [0, 2^64) without revealing value.'
                    : 'Complete step 2 first.')
          ),
          h('div', { class: 'dregg-stealth-demo__controls' },
            h('button', {
              class: 'dregg-stealth-demo__btn dregg-stealth-demo__btn--primary',
              disabled: !stepDone(2),
              onClick: doStep3,
            }, 'Generate Range Proof')
          )
        );

      // --- Step 4: Recipient Scan ---
      const Step4 = () =>
        h('div', { class: 'dregg-stealth-demo__step' },
          h('div', { class: 'dregg-stealth-demo__step-header' },
            h(StepBadge, { n: 4 }),
            h('span', { class: 'dregg-stealth-demo__step-title' }, 'Recipient Scans Announcements')
          ),
          h('div', { class: 'dregg-stealth-demo__step-body' },
            s.scanResult
              ? h('dl', { class: 'dregg-stealth-demo__kv' },
                  h('dt', null, 'scanned'),
                  h('dd', null, h('code', null, String(s.announcements.length))),
                  h('dt', null, 'owned'),
                  h('dd', null, h('code', null, String(s.scanResult.matched.length))),
                  h('dt', null, 'matched indices'),
                  h('dd', null, h('code', null, '[' + s.scanResult.matched.join(', ') + ']')),
                  h('dt', null, 'view tag filter'),
                  h('dd', null, h('code', null, '1-byte pre-filter — O(1) rejection'))
                )
              : h('div', { style: 'color:var(--fg-dim);font-size:0.8rem;' },
                  stepDone(2)
                    ? 'Ready — recipient scans with view key to detect owned payments.'
                    : 'Complete step 2 first.')
          ),
          h('div', { class: 'dregg-stealth-demo__controls' },
            h('button', {
              class: 'dregg-stealth-demo__btn dregg-stealth-demo__btn--primary',
              disabled: !stepDone(2),
              onClick: doStep4,
            }, 'Scan Announcements')
          )
        );

      // --- Step 5: Conservation Proof ---
      const Step5 = () => {
        const cr = s.conservResult;
        const conservClass = !cr ? ''
          : cr.not_implemented ? 'dregg-stealth-demo__conservation--stub'
          : cr.valid ? 'dregg-stealth-demo__conservation--valid'
          : 'dregg-stealth-demo__conservation--invalid';

        return h('div', { class: 'dregg-stealth-demo__step' },
          h('div', { class: 'dregg-stealth-demo__step-header' },
            h(StepBadge, { n: 5 }),
            h('span', { class: 'dregg-stealth-demo__step-title' }, 'Verify Conservation (Sum-to-Zero)')
          ),
          h('div', { class: 'dregg-stealth-demo__step-body' },
            cr
              ? h('div', null,
                  h('div', { class: 'dregg-stealth-demo__conservation ' + conservClass },
                    cr.not_implemented
                      ? 'STUB — verify_conservation_proof not yet implemented in wasm; sum-to-zero check deferred'
                      : (cr.valid
                          ? `VALID — inputs (${cr.input_count}) == outputs (${cr.output_count}); no value created`
                          : `INVALID — conservation check failed (${cr.input_count}→${cr.output_count})`)
                  ),
                  h('dl', { class: 'dregg-stealth-demo__kv', style: 'margin-top:8px;' },
                    h('dt', null, 'input commits'),  h('dd', null, h('code', null, String(cr.input_count ?? 1))),
                    h('dt', null, 'output commits'), h('dd', null, h('code', null, String(cr.output_count ?? 2))),
                    h('dt', null, 'property'), h('dd', null, h('code', null, 'Pedersen homomorphic sum'))
                  )
                )
              : h('div', { style: 'color:var(--fg-dim);font-size:0.8rem;' },
                  stepDone(2)
                    ? 'Ready — verifier checks that inputs == outputs without seeing amounts.'
                    : 'Complete step 2 first.')
          ),
          h('div', { class: 'dregg-stealth-demo__controls' },
            h('button', {
              class: 'dregg-stealth-demo__btn dregg-stealth-demo__btn--primary',
              disabled: !stepDone(2),
              onClick: doStep5,
            }, 'Verify Conservation')
          )
        );
      };

      // --- Timeline + Privacy summary ---
      const SummaryHeader = () =>
        h('div', { class: 'dregg-stealth__header', style: 'border-radius:8px 8px 0 0;border-bottom:1px solid var(--line,#2a302d);' },
          h('span', { class: 'dregg-stealth__kind' }, 'stealth address'),
          h('span', {
            class: 'dregg-stealth__badge',
            title: privMeta.title,
            style: `background:${privMeta.color};color:${privMeta.textColor};`,
          }, privMeta.label),
          h('span', { style: 'margin-left:auto;color:var(--fg-dim);font-size:0.78rem;' },
            `${s.callCount} crypto ops · ${s.stubCount} stub${s.stubCount !== 1 ? 's' : ''}`)
        );

      return h('div', { class: 'dregg-inspector dregg-stealth' },
        h(SummaryHeader, {}),
        h('div', { class: 'dregg-stealth__body' },
          h('div', { class: 'dregg-stealth-demo' },
            h(Step1, {}),
            h(Step2, {}),
            h(Step3, {}),
            h(Step4, {}),
            h(Step5, {})
          ),
          s.timeline.length > 0
            ? h('details', { open: true },
                h('summary', { style: 'cursor:pointer;color:var(--fg-dim);font-size:0.8rem;margin-bottom:6px;user-select:none;' },
                  'Transfer timeline'),
                h(Timeline, {})
              )
            : null
        )
      );
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('dregg-stealth-address')) {
  customElements.define('dregg-stealth-address', DreggStealth);
}

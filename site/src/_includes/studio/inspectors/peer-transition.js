/**
 * <pyana-peer-transition> — structured view of a PeerStateTransition.
 *
 * Attributes (one of):
 *   bytes  — base64-encoded raw postcard bytes; element decodes via
 *            `runtime._wasm.decode_peer_transition(uint8Array)`.
 *   data   — JSON-stringified decoded shape (already decoded externally).
 *
 * Decoded shape (returned by wasm):
 *   { cell_id, old_commitment, new_commitment, effects_hash,
 *     timestamp, sequence, signature, has_transition_proof }
 *
 * Modes (via `mode` attribute):
 *   default  — full KV grid with header
 *   compact  — single line: seq=N cell=abc… newC=def…
 *
 * Pattern note (STARBRIDGE FOLLOWUP 09): Imports InspectorBase/shortHex but extends
 * HTMLElement directly (data/bytes-driven, used standalone in studio.html:87 peer-paste UX
 * and cross-tab Discord flows; does not require <pyana-app> uri). See cell.js style in
 * inspectors.js:23 (uses base + signals + preact). For full runtime integration see
 * runtime-in-memory.js:453 (decodePeerTransition wrapper), wasm/src/bindings.rs:1451
 * (create/verify/decode_peer_transition), wasm/src/runtime.rs (PeerExchange via cipherclerk).
 * Real peer/fed surfaces in pyana_federation + node net/gossip; no JS reimpl of transitions.
 * See STARBRIDGE-PLAN §11.4 success + §4.5 for <pyana-peer-transition> + blocklace peer.
 */

import { InspectorBase, shortHex } from './_base.js';

function b64decode(str) {
  const bin = atob(str.trim());
  const out = new Uint8Array(bin.length);
  for (let i = 0; i < bin.length; i++) out[i] = bin.charCodeAt(i);
  return out;
}

function tsToISO(ts) {
  // timestamp is i64 Unix seconds (not ms)
  if (!ts && ts !== 0) return '(none)';
  try { return new Date(Number(ts) * 1000).toISOString(); } catch { return String(ts); }
}

class PyanaPeerTransition extends HTMLElement {
  static get observedAttributes() { return ['bytes', 'data', 'mode']; }

  constructor() {
    super();
    this._expanded = {};
    this._decoded = null;
    this._err = null;
    this._wasm = null;
  }

  async connectedCallback() {
    // Wait for pyanaUi ready — gives us h/render/html/effect.
    if (window.pyanaUi) {
      this._api = window.pyanaUi;
    } else {
      this._api = await new Promise(resolve => {
        window.addEventListener('pyanaUi:ready', e => resolve(e.detail), { once: true });
      });
    }
    this._tryFindWasm();
    this._decode();
    this._renderSelf();
  }

  _tryFindWasm() {
    if (this._wasm) return;
    // Walk ancestors to find pyana-app which has .runtime set after wasm init.
    let el = this.parentElement;
    while (el && !el.runtime) el = el.parentElement;
    this._runtime = el?.runtime || null;
    this._wasm = this._runtime?._wasm || null;
  }

  attributeChangedCallback() {
    // Runtime may have been set after initial connectedCallback — retry.
    this._tryFindWasm();
    this._decode();
    this._renderSelf();
  }

  _decode() {
    this._err = null;
    this._decoded = null;

    const dataAttr = this.getAttribute('data');
    if (dataAttr) {
      try { this._decoded = JSON.parse(dataAttr); } catch (e) { this._err = 'bad data attr: ' + e.message; }
      return;
    }

    const bytesAttr = this.getAttribute('bytes');
    if (!bytesAttr) return;

    // Need wasm for decode; if not ready yet, connectedCallback will re-call.
    if (!this._wasm?.decode_peer_transition) {
      this._err = '(waiting for wasm…)';
      return;
    }

    try {
      const uint8 = b64decode(bytesAttr);
      const result = this._wasm.decode_peer_transition(uint8);
      this._decoded = result;
    } catch (e) {
      this._err = 'decode failed: ' + (e?.message || String(e));
    }
  }

  _toggle(key) {
    this._expanded[key] = !this._expanded[key];
    this._renderSelf();
  }

  _renderSelf() {
    const mode = this.getAttribute('mode') || 'default';

    if (!this._decoded && !this._err) {
      // Nothing to show yet (no attrs set)
      this.innerHTML = '';
      return;
    }

    if (this._err) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err" style="padding:4px 8px;font-size:0.8rem;">${this._err}</div>`;
      return;
    }

    const d = this._decoded;

    if (mode === 'compact') {
      this.innerHTML =
        `<span class="pyana-inspector pyana-inspector--compact" style="font-size:0.8rem;">` +
        `seq=${d.sequence} ` +
        `cell=<code title="${d.cell_id}">${shortHex(d.cell_id)}</code> ` +
        `newC=<code title="${d.new_commitment}">${shortHex(d.new_commitment)}</code>` +
        `</span>`;
      return;
    }

    // Full default view — build DOM imperatively (no preact dep needed here).
    const proofIndicator = d.has_transition_proof
      ? `<span style="color:#4ade80;font-weight:600;font-size:0.75rem;">&#x2714; has STARK proof</span>`
      : `<span style="color:var(--fg-dim);font-size:0.75rem;opacity:0.55;">no STARK proof</span>`;

    const kv = (label, value, key) => {
      const isExpandable = value && value.length > 16;
      const expanded = this._expanded[key];
      const display = isExpandable && !expanded ? shortHex(value, 12) + '…' : value;
      const btn = isExpandable
        ? ` <button data-expand="${key}" style="font-size:0.7rem;padding:0 4px;cursor:pointer;background:transparent;border:1px solid var(--line);border-radius:2px;color:var(--fg-dim);">${expanded ? 'collapse' : 'expand'}</button>`
        : '';
      return `<dt style="opacity:0.65;padding-right:8px;">${label}</dt>` +
             `<dd><code title="${value}">${display}</code>${btn}</dd>`;
    };

    this.innerHTML =
      `<div class="pyana-inspector pyana-inspector--cell" style="font-size:0.8rem;">` +
        `<header style="display:flex;align-items:center;gap:8px;margin-bottom:6px;">` +
          `<span class="pyana-inspector__kind">PeerStateTransition</span>` +
          `<code class="pyana-inspector__id" style="font-size:1rem;font-weight:700;">seq&nbsp;${d.sequence}</code>` +
          `<span style="margin-left:auto;">${proofIndicator}</span>` +
        `</header>` +
        `<dl class="pyana-inspector__kv" style="display:grid;grid-template-columns:max-content 1fr;gap:2px 8px;word-break:break-all;">` +
          kv('cell_id',         d.cell_id,         'cell_id') +
          kv('old_commitment',  d.old_commitment,  'old_commitment') +
          kv('new_commitment',  d.new_commitment,  'new_commitment') +
          kv('effects_hash',    d.effects_hash,    'effects_hash') +
          `<dt style="opacity:0.65;">timestamp</dt><dd>${tsToISO(d.timestamp)}</dd>` +
          kv('signature',       d.signature,       'signature') +
        `</dl>` +
      `</div>`;

    // Wire expand/collapse buttons after setting innerHTML.
    this.querySelectorAll('[data-expand]').forEach(btn => {
      btn.addEventListener('click', () => this._toggle(btn.dataset.expand));
    });
  }
}

if (!customElements.get('pyana-peer-transition')) {
  customElements.define('pyana-peer-transition', PyanaPeerTransition);
}

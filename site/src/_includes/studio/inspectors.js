/**
 * Inspector custom elements (initial set).
 *
 * Each inspector:
 *  - Reads `ref` attribute (a pyana:// URI).
 *  - Finds its <pyana-app> ancestor and reads `.runtime`.
 *  - Renders via Preact + htm into its own light DOM (no shadow).
 *  - Subscribes to the relevant runtime signal so it re-renders on state change.
 *
 * Initial set: <pyana-cell>, <pyana-cell-list>. More to come as the vertical
 * proves out.
 */

import { parseRef } from './uri.js';
import { findRuntime } from './context.js';

function ready() {
  return new Promise(resolve => {
    if (window.pyanaUi) return resolve(window.pyanaUi);
    window.addEventListener('pyanaUi:ready', e => resolve(e.detail), { once: true });
  });
}

class InspectorBase extends HTMLElement {
  static get observedAttributes() { return ['uri', 'mode']; }
  constructor() {
    super();
    this._unmount = null;
    this._dispose = null;
  }
  async connectedCallback() {
    const [api, runtime] = await Promise.all([ready(), findRuntime(this)]);
    this._runtime = runtime;
    this._api = api;
    this._render();
  }
  attributeChangedCallback() {
    if (this._api) this._render();
  }
  disconnectedCallback() {
    if (this._dispose) this._dispose();
    if (this._unmount) this._unmount();
  }
  _render() {
    // Subclasses override
  }
}

// --- <pyana-cell> -----------------------------------------------------------

class PyanaCell extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    // Tear down any previous render
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed;
    try { parsed = parseRef(refAttr); }
    catch (e) {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">bad ref: ${e.message}</div>`;
      return;
    }
    if (parsed.kind !== 'cell') {
      this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">wrong kind: ${parsed.kind} (expected cell)</div>`;
      return;
    }

    const cellSignal = this._runtime.getCell(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    // Re-render on signal change. We re-render via Preact render(); the effect
    // gives us a teardown handle.
    const Component = () => {
      const c = cellSignal.value;
      if (!c) return html`<div class="pyana-inspector pyana-inspector--empty">cell not in this runtime: <code>${parsed.id.slice(0, 16)}…</code></div>`;
      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <code title=${parsed.id}>${parsed.id.slice(0, 8)}…</code>
            balance ${String(c.balance)} · ${String(c.num_capabilities)} caps
          </span>`;
      }
      // Program section: render <pyana-cell-program> if a program is present.
      // We pass data-program as a JSON attribute (the element supports this).
      const hasProg = c.program && c.program.kind !== 'None';
      const progDataAttr = hasProg ? JSON.stringify(c.program) : null;
      const progSection = hasProg
        ? html`
          <details style="margin-top:var(--s3,8px);">
            <summary style="cursor:pointer;color:var(--fg-dim);font-size:0.82rem;user-select:none;">Program</summary>
            <pyana-cell-program mode="default" data-program=${progDataAttr}></pyana-cell-program>
          </details>`
        : html`
          <details style="margin-top:var(--s3,8px);">
            <summary style="cursor:pointer;color:var(--fg-dim);font-size:0.82rem;user-select:none;">Program</summary>
            <div style="color:var(--fg-dim);font-size:0.82rem;padding:4px 0;">no program — any authorized state change is valid.</div>
          </details>`;

      return html`
        <div class="pyana-inspector pyana-inspector--cell">
          <header>
            <span class="pyana-inspector__kind">cell</span>
            <code class="pyana-inspector__id" title=${parsed.id}>${parsed.id.slice(0, 24)}…</code>
          </header>
          <dl class="pyana-inspector__kv">
            <dt>balance</dt><dd>${String(c.balance)}</dd>
            <dt>nonce</dt><dd>${String(c.nonce)}</dd>
            <dt>capabilities</dt><dd>${String(c.num_capabilities)}</dd>
            <dt>proved state</dt><dd>${String(c.proved_state)}</dd>
            <dt>delegation epoch</dt><dd>${String(c.delegation_epoch)}</dd>
            <dt>permissions</dt><dd><code>${JSON.stringify(c.permissions)}</code></dd>
          </dl>
          ${progSection}
        </div>`;
    };

    this._dispose = effect(() => {
      render(h(Component, {}), root);
    });
  }
}
if (!customElements.get('pyana-cell')) customElements.define('pyana-cell', PyanaCell);

// --- <pyana-cell-list> ------------------------------------------------------

class PyanaCellList extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const listSignal = this._runtime.listCells();
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const cells = listSignal.value || [];
      if (!cells.length) return html`<div class="pyana-inspector pyana-inspector--empty">no cells in this runtime</div>`;
      return html`
        <div class="pyana-inspector pyana-inspector--cell-list">
          <header>${cells.length} cell${cells.length === 1 ? '' : 's'}</header>
          <ul>
            ${cells.map(c => html`
              <li>
                <pyana-cell uri=${`pyana://cell/${c.cell_id}`} mode="compact"></pyana-cell>
              </li>
            `)}
          </ul>
        </div>`;
    };

    this._dispose = effect(() => {
      render(h(Component, {}), root);
    });
  }
}
if (!customElements.get('pyana-cell-list')) customElements.define('pyana-cell-list', PyanaCellList);

// --- Barrel: register inspector custom elements defined in inspectors/ ------
// Each module self-registers via `customElements.define` on import.
import './inspectors/turn.js';
import './inspectors/receipt.js';
import './inspectors/receipt-list.js';
import './inspectors/capability.js';
import './inspectors/capability-list.js';
import './inspectors/intent.js';
import './inspectors/federation.js';
import './inspectors/block.js';
import './inspectors/delegation-graph.js';
import './inspectors/authorization.js';
import './inspectors/cell-program.js';
import './inspectors/turn-debugger.js';
import './inspectors/peer-transition.js';
import './inspectors/proof.js';
import './inspectors/merkle-tree.js';
import './inspectors/stealth-address.js';

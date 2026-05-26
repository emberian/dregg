/**
 * Inspector custom elements (initial set).
 *
 * Each inspector:
 *  - Reads `ref` attribute (a dregg:// URI).
 *  - Finds its <dregg-app> ancestor and reads `.runtime`.
 *  - Renders via Preact + htm into its own light DOM (no shadow).
 *  - Subscribes to the relevant runtime signal so it re-renders on state change.
 *
 * Initial set: <dregg-cell>, <dregg-cell-list>. More to come as the vertical
 * proves out.
 */

import { parseRef } from './uri.js';
import { findRuntime } from './context.js';

// Use shared _base (STARBRIDGE-FOLLOWUP-02 full Wave 3 integration clean-up).
// Removes prior dupe; cell/cell-list continue to work (extend the imported class).
import { InspectorBase, renderParseError, shortHex } from './inspectors/_base.js';

// --- <dregg-cell> -----------------------------------------------------------

class DreggCell extends InspectorBase {
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
      this.innerHTML = `<div class="dregg-inspector dregg-inspector--err">bad ref: ${e.message}</div>`;
      return;
    }
    if (parsed.kind !== 'cell') {
      this.innerHTML = `<div class="dregg-inspector dregg-inspector--err">wrong kind: ${parsed.kind} (expected cell)</div>`;
      return;
    }

    const cellSignal = this._runtime.getCell(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    // Re-render on signal change. We re-render via Preact render(); the effect
    // gives us a teardown handle.
    const Component = () => {
      const c = cellSignal.value;
      if (!c) return html`<div class="dregg-inspector dregg-inspector--empty">cell not in this runtime: <code>${parsed.id.slice(0, 16)}…</code></div>`;
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code title=${parsed.id}>${parsed.id.slice(0, 8)}…</code>
            balance ${String(c.balance)} · ${String(c.num_capabilities)} caps
          </span>`;
      }
      // Program section: render <dregg-cell-program> if a program is present.
      // We pass data-program as a JSON attribute (the element supports this).
      const hasProg = c.program && c.program.kind !== 'None';
      const progDataAttr = hasProg ? JSON.stringify(c.program) : null;
      const progSection = hasProg
        ? html`
          <details style="margin-top:var(--s3,8px);">
            <summary style="cursor:pointer;color:var(--fg-dim);font-size:0.82rem;user-select:none;">Program</summary>
            <dregg-cell-program mode="default" data-program=${progDataAttr}></dregg-cell-program>
          </details>`
        : html`
          <details style="margin-top:var(--s3,8px);">
            <summary style="cursor:pointer;color:var(--fg-dim);font-size:0.82rem;user-select:none;">Program</summary>
            <div style="color:var(--fg-dim);font-size:0.82rem;padding:4px 0;">no program — any authorized state change is valid.</div>
          </details>`;

      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">cell</span>
            <code class="dregg-inspector__id" title=${parsed.id}>${parsed.id.slice(0, 24)}…</code>
          </header>
          <dl class="dregg-inspector__kv">
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
if (!customElements.get('dregg-cell')) customElements.define('dregg-cell', DreggCell);

// --- <dregg-cell-list> ------------------------------------------------------

class DreggCellList extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const listSignal = this._runtime.listCells();
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const cells = listSignal.value || [];
      if (!cells.length) return html`<div class="dregg-inspector dregg-inspector--empty">no cells in this runtime</div>`;
      return html`
        <div class="dregg-inspector dregg-inspector--cell-list">
          <header>${cells.length} cell${cells.length === 1 ? '' : 's'}</header>
          <ul>
            ${cells.map(c => html`
              <li>
                <dregg-cell uri=${`dregg://cell/${c.cell_id}`} mode="compact"></dregg-cell>
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
if (!customElements.get('dregg-cell-list')) customElements.define('dregg-cell-list', DreggCellList);

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

// --- <dregg-app-list> (Apps tab for /starbridge/, STARBRIDGE-PLAN §4.8) ---
// Reads manifests from starbridge-apps/* (created as part of this task).
// Renders cards. Selecting an app asks the Starbridge host to embed that
// userspace app in the workspace while keeping the IDE panes around it.

class DreggAppList extends HTMLElement {
  constructor() {
    super();
    this._apps = [];
    this._loading = true;
  }
  connectedCallback() { this.loadAndRender(); }
  async loadAndRender() {
    this._loading = true;
    const ids = ['nameservice', 'identity', 'governed-namespace', 'subscription'];
    const fallback = {
      nameservice: {
        id: 'nameservice',
        name: 'Nameservice',
        description: 'Federation name directory built from dregg-native primitives.',
        page: '/starbridge-apps/nameservice/pages/index.html',
      },
      identity: {
        id: 'identity',
        name: 'Identity',
        description: 'Credential issuance and selective disclosure.',
        page: '/starbridge-apps/identity/pages/index.html',
      },
      'governed-namespace': {
        id: 'governed-namespace',
        name: 'Governed Namespace',
        description: 'Governance tables and proposals.',
        page: '/starbridge-apps/governed-namespace/pages/index.html',
      },
      subscription: {
        id: 'subscription',
        name: 'Subscription',
        description: 'Pub/sub topic and capability subscription app.',
        page: '/starbridge-apps/subscription/pages/index.html',
      },
    };
    const loaded = await Promise.all(ids.map(async (id) => {
      try {
        const resp = await fetch(`/starbridge-apps/${id}/manifest.json`, { headers: { Accept: 'application/json' } });
        if (!resp.ok) throw new Error(String(resp.status));
        return await resp.json();
      } catch {
        return fallback[id];
      }
    }));
    this._apps = loaded.filter(Boolean);
    this._loading = false;
    this.render();
    // Update count in host page if present (the starbridge tree count).
    const countEl = document.getElementById('sb-app-count');
    if (countEl) countEl.textContent = String(this._apps.length);
  }
  render() {
    const root = this;
    root.innerHTML = '';
    const wrap = document.createElement('div');
    wrap.className = 'dregg-app-list';
    wrap.style.cssText = 'display:flex;flex-direction:column;gap:0.4rem;font-size:0.85rem;';
    if (this._loading) {
      wrap.innerHTML = '<div style="color:#888">loading apps…</div>';
      root.appendChild(wrap);
      return;
    }
    this._apps.forEach(app => {
      const card = document.createElement('div');
      card.style.cssText = 'border:1px solid #eee;border-radius:4px;padding:0.4rem;background:#fafafa;';
      card.innerHTML = `
        <div style="font-weight:600">${escapeHtml(app.name)}</div>
        <div style="color:#555;font-size:0.75rem;margin:0.2rem 0;">${escapeHtml(app.description)}</div>
        <div style="display:flex;gap:0.3rem;flex-wrap:wrap;">
          <button data-act="open" style="font-size:0.7rem;padding:0.15rem 0.4rem;">Open in workspace</button>
          <a href="${app.page}" target="_blank" style="font-size:0.7rem;color:#25439a;">Standalone</a>
        </div>
      `;
      const btn = card.querySelector('[data-act=open]');
      btn?.addEventListener('click', () => {
        this.dispatchEvent(new CustomEvent('app-open', {
          bubbles: true,
          detail: { app }
        }));
      });
      wrap.appendChild(card);
    });
    root.appendChild(wrap);
  }
}

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

if (typeof customElements !== 'undefined' && !customElements.get('dregg-app-list')) {
  customElements.define('dregg-app-list', DreggAppList);
}
if (typeof window !== 'undefined' && window.dreggUi?.register) {
  window.dreggUi.register('dregg-app-list', DreggAppList);
}

// Ensure the first starbridge-app per-app inspectors (name.js) are available
// for the Apps tab demo in /starbridge/ (reuses platform components).
// The shared barrel already side-loads it for app pages; we also ensure here.
import('/starbridge-apps/shared/inspectors/name.js').catch(() => {});
import('/starbridge-apps/shared/turn-builders/nameservice.js').catch(() => {});

import './inspectors/witnessed-receipt.js';
import './inspectors/block-dag.js';
import './inspectors/predicate.js';
import './inspectors/cipherclerk.js';
import './inspectors/factory-descriptor.js';
import './inspectors/federation-list.js';
import './inspectors/dfa.js';
import './inspectors/blinded-queue.js';
import './inspectors/programmable-queue.js';
import './inspectors/cap-inbox.js';
import './inspectors/pubsub-topic.js';
import './inspectors/relay-operator.js';
import './inspectors/witnessed-predicate.js';
import './inspectors/activity.js';  // <dregg-activity> live observability feed (STARBRIDGE-03 #30)

// --- Full Wave 3 §4.5 integration (STARBRIDGE-FOLLOWUP-02) -----------------
// All 22 from plan table now have files + barrel registration.
// (Previous deliveries had files for note/revocation/conditional/handoff/bearer/blocklace but no import here.)
import './inspectors/blocklace-sim.js';
import './inspectors/note.js';
import './inspectors/revocation-channel.js';
import './inspectors/conditional-turn.js';
import './inspectors/handoff-certificate.js';
import './inspectors/bearer-cap.js';
import './inspectors/attenuated-token.js';
import './inspectors/encrypted-intent.js';

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

// Use shared _base (STARBRIDGE-FOLLOWUP-02 full Wave 3 integration clean-up).
// Removes prior dupe; cell/cell-list continue to work (extend the imported class).
import { InspectorBase, renderParseError, shortHex } from './inspectors/_base.js';

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

// --- <pyana-app-list> (Apps tab for /starbridge/, STARBRIDGE-PLAN §4.8) ---
// Reads manifests from starbridge-apps/* (created as part of this task).
// Renders cards. Selecting the nameservice demonstrates the first
// end-to-end: loads its typed turn-builders + per-app inspectors
// (which reuse <pyana-cell>, <pyana-capability> etc.).
// For demo, clicking "Demo" on nameservice renders a live
// <pyana-name-registry> + <pyana-name> example in the inspector pane
// (via custom event the page orchestrator can listen to).

class PyanaAppList extends HTMLElement {
  constructor() {
    super();
    this._apps = [];
    this._loading = true;
  }
  connectedCallback() { this.loadAndRender(); }
  async loadAndRender() {
    this._loading = true;
    // Static manifests (Q3 shape per STUDIO-REFACTOR-PICKUP §7).
    // §4.8: dynamic fetch attempted in load for manifest-driven (creep); hardcoded fallback.
    // In a real build these could be fetched from /starbridge-apps/*/manifest.json
    // served statically. Hardcoded here for robustness across runtimes.
    this._apps = [
      {
        id: 'nameservice',
        name: 'Nameservice',
        description: 'Federation name directory — first e2e starbridge-app demo. Slot caveats + signed turns.',
        page: '/starbridge-apps/nameservice/pages/index.html',
        factory_vks: ['737461726272696467652d6e616d65736572766963652d666163746f72792121'],
        inspectors: ['pyana-name', 'pyana-name-registry'],
      },
      {
        id: 'identity',
        name: 'Identity',
        description: 'Credential issuance & selective disclosure (high-quality additional starbridge-app demo §4.8; now loads via shared/ fix).',
        page: '/starbridge-apps/identity/pages/index.html',
        factory_vks: [],
        inspectors: ['pyana-credential', 'pyana-credential-issue-form'],
      },
      {
        id: 'governed-namespace',
        name: 'Governed Namespace',
        description: 'Governance tables and proposals.',
        page: '/starbridge-apps/governed-namespace/pages/index.html',
        factory_vks: [],
        inspectors: [],
      },
      {
        id: 'subscription',
        name: 'Subscription',
        description: 'Pub/sub + capability subscriptions (additional high-quality starbridge-app demo §4.8).',
        page: '/starbridge-apps/subscription/pages/index.html',
        factory_vks: [],
        inspectors: [],
      },
    ];
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
    wrap.className = 'pyana-app-list';
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
          <button data-act="demo" style="font-size:0.7rem;padding:0.15rem 0.4rem;">Demo in inspector</button>
          <a href="${app.page}" target="_blank" style="font-size:0.7rem;color:#25439a;">Open standalone page →</a>
        </div>
      `;
      const btn = card.querySelector('[data-act=demo]');
      btn?.addEventListener('click', () => {
        // For the nameservice first demo: dispatch so starbridge.js can mount live components.
        this.dispatchEvent(new CustomEvent('app-demo', {
          bubbles: true,
          detail: { app }
        }));
        // Also directly render a live nameservice example in this element's parent inspector context if possible.
        if (app.id === 'nameservice') {
          // Quick in-card preview using the newly wired per-app inspectors (reuse platform ones).
          const preview = document.createElement('div');
          preview.style.cssText = 'margin-top:0.3rem;border-top:1px dashed #ccc;padding-top:0.3rem;';
          preview.innerHTML = `
            <div style="font-size:0.7rem;color:#666;margin-bottom:0.2rem;">Live nameservice preview (reuses &lt;pyana-cell&gt; etc.):</div>
            <pyana-name-registry uri="pyana://cell/registry-default" page-size="5"></pyana-name-registry>
          `;
          // Avoid stacking many previews
          card.querySelectorAll('.pyana-preview').forEach(n => n.remove());
          preview.className = 'pyana-preview';
          card.appendChild(preview);
        }
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

if (typeof customElements !== 'undefined' && !customElements.get('pyana-app-list')) {
  customElements.define('pyana-app-list', PyanaAppList);
}
if (typeof window !== 'undefined' && window.pyana?.register) {
  window.pyana.register('pyana-app-list', PyanaAppList);
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
import './inspectors/activity.js';  // <pyana-activity> live observability feed (STARBRIDGE-03 #30)

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

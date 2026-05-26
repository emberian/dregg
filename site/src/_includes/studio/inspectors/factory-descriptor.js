/**
 * <pyana-factory-descriptor uri="pyana://factory/<vk>" | data-factory="...">
 *
 * Inspector for pyana_cell::factory::FactoryDescriptor — the constructor
 * transparency record. Renders the factory's identity, child program (via
 * embedded <pyana-cell-program>), allowed cap templates, field/state
 * constraints, mode, and provenance notes.
 *
 * Heavy reuse of platform vocabulary (per Houyhnhnm / STARBRIDGE-PLAN §4.5):
 *   - Embeds <pyana-cell-program> for the child program + its StateConstraints
 *     (the storage-as-cell-program patterns live here: MonotonicSequence +
 *     WriteOnce + SenderAuthorized etc for queues/inboxes).
 *   - Composes with <pyana-cell> for owner deeplinks in provenance.
 *
 * Aligns with STORAGE-AS-CELL-PROGRAMS.md Phase 1 (WitnessedPredicate registry
 * + cell-program migrations): factories declare the perpetual StateConstraints
 * that turn storage primitives into inspectable cell programs. The descriptor
 * VK is the stable name for the pattern.
 *
 * URI form (future): pyana://factory/<32-byte-vk-hex>
 * Data form (today, for inline from deploy_factory result or app manifests):
 *   data-factory='{"factory_vk":"...","child_program_vk":null,"state_constraints":[...],...}'
 *
 * Modes: compact (one-line VK + mode + #constraints), default (full KV + sub-inspectors).
 *
 * Substrate rule: no JS reimplementation of factory validation or VK hashing.
 * All semantics come from the CellProgramView + descriptor JSON passed from wasm.
 * Placeholder notes for missing runtime.getFactoryDescriptor until binding added.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

// --- Helpers ---------------------------------------------------------------

function esc(s) {
  if (s == null) return '';
  return String(s).replace(/&/g, '&amp;').replace(/</g, '&lt;').replace(/>/g, '&gt;');
}

function modeLabel(m) {
  if (!m) return 'hosted';
  return String(m).toLowerCase() === 'sovereign' ? 'sovereign' : 'hosted';
}

// --- <pyana-factory-descriptor> --------------------------------------------

class PyanaFactoryDescriptor extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';
    const dataAttr = this.getAttribute('data-factory');

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    let descriptor = null;

    if (dataAttr) {
      try {
        descriptor = JSON.parse(dataAttr);
      } catch (e) {
        this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">bad data-factory JSON: ${esc(e.message)}</div>`;
        return;
      }
    } else if (refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'factory')) return;
      // For now, no runtime.getFactory yet — surface placeholder + allow data override.
      // When wasm binding lands (list/get deployed factories), wire runtime.getFactory(parsed.id)
      descriptor = null; // will render awaiting
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (!descriptor) {
        return html`
          <div class="pyana-inspector pyana-inspector--factory pfd">
            <div class="pfd__header">
              <span class="pyana-inspector__kind">factory-descriptor</span>
              ${parsed ? html`<code class="pyana-inspector__id" title=${parsed.id}>${shortHex(parsed.id, 16)}</code>` : ''}
            </div>
            <div class="pfd__placeholder" style="font-size:0.82rem;color:var(--fg-dim);padding:8px 0;">
              awaiting wasm binding for deployed factories (deploy_factory_descriptor exists; get/list pending per §5.7/STORAGE-AS-CELL-PROGRAMS Phase 1).<br>
              Pass <code>data-factory="..."</code> JSON (from deploy result or app manifest) to render.
            </div>
          </div>`;
      }

      const vk = descriptor.factory_vk || descriptor.vk || '';
      const childVk = descriptor.child_program_vk || (descriptor.child_vk_strategy ? 'derived' : null);
      const childStrategy = descriptor.child_vk_strategy ? JSON.stringify(descriptor.child_vk_strategy) : null;
      const stateConstraints = descriptor.state_constraints || descriptor.constraints || [];
      const fieldConstraints = descriptor.field_constraints || [];
      const capTemplates = descriptor.allowed_cap_templates || descriptor.cap_templates || [];
      const defMode = modeLabel(descriptor.default_mode || descriptor.mode);
      const creationBudget = descriptor.creation_budget;

      const progData = descriptor.child_program
        ? JSON.stringify(descriptor.child_program)
        : (childVk ? JSON.stringify({ kind: 'Circuit', circuit_hash: childVk }) : null);

      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact pfd pfd--compact" title=${'factory ' + shortHex(vk, 8)}>
            <span class="pyana-inspector__kind">factory</span>
            <code>${shortHex(vk, 8)}</code>
            · ${defMode}
            · ${stateConstraints.length} constraints
            ${capTemplates.length ? '· ' + capTemplates.length + ' caps' : ''}
          </span>`;
      }

      return html`
        <div class="pyana-inspector pyana-inspector--cell pfd" data-testid="pfd-root">
          <header class="pfd__header">
            <span class="pyana-inspector__kind">factory-descriptor</span>
            <code class="pyana-inspector__id" title=${vk}>${shortHex(vk, 24)}</code>
            <span class="pfd__mode-badge">${defMode}</span>
          </header>

          <dl class="pfd__kv">
            <dt>VK (content hash)</dt><dd><code title=${vk}>${shortHex(vk, 16)}…</code></dd>
            <dt>Child program VK</dt>
            <dd>
              ${childVk
                ? html`<code title=${childVk}>${shortHex(childVk, 12)}…</code>`
                : html`<em>derived / from-set (see strategy)</em>`}
              ${childStrategy ? html`<div style="font-size:0.7rem;color:var(--fg-dim)">strategy: ${esc(childStrategy)}</div>` : ''}
            </dd>
            <dt>Default mode</dt><dd>${defMode}</dd>
            ${creationBudget != null ? html`<dt>Creation budget</dt><dd>${creationBudget}/epoch</dd>` : ''}
            <dt>Cap templates</dt><dd>${capTemplates.length || 0}</dd>
            <dt>Field constraints (creation)</dt><dd>${fieldConstraints.length || 0}</dd>
            <dt>State constraints (perpetual)</dt><dd>${stateConstraints.length || 0} — these are the cell-program invariants</dd>
          </dl>

          ${capTemplates.length > 0 ? html`
            <details class="pfd__section" open>
              <summary class="pfd__summary">Allowed capability templates</summary>
              <div class="pfd__sub">
                <ul style="margin:4px 0 0;padding-left:18px;font-size:0.8rem;">
                  ${capTemplates.map(t => html`<li><code>${esc(JSON.stringify(t).slice(0,120))}</code></li>`)}
                </ul>
              </div>
            </details>` : ''}

          ${fieldConstraints.length > 0 ? html`
            <details class="pfd__section">
              <summary class="pfd__summary">Field constraints (creation-time)</summary>
              <div class="pfd__sub" style="font-family:monospace;font-size:0.78rem;">
                ${fieldConstraints.map(fc => html`<div>${esc(JSON.stringify(fc))}</div>`)}
              </div>
            </details>` : ''}

          <details class="pfd__section" open style="margin-top:8px;">
            <summary class="pfd__summary">Child cell program (perpetual StateConstraints)</summary>
            <div class="pfd__sub">
              ${progData
                ? html`<pyana-cell-program data-program=${progData} mode="default"></pyana-cell-program>`
                : html`<div style="color:var(--fg-dim);font-size:0.82rem;">No inline child program view. Constraints shown via state_constraints above (storage patterns: WriteOnce + MonotonicSequence + SenderAuthorized etc per STORAGE-AS-CELL-PROGRAMS §3).</div>`}
              ${stateConstraints.length > 0 ? html`
                <div style="margin-top:6px;font-size:0.75rem;color:var(--fg-dim);">
                  ${stateConstraints.length} perpetual constraints govern every transition on cells minted from this factory.
                  This is how <strong>storage primitives become cell programs</strong>: CapInbox, ProgrammableQueue etc are expressed as compositions of these 21 variants + WitnessedPredicate (Phase 1).
                </div>` : ''}
            </div>
          </details>

          <div class="pfd__footer" style="margin-top:8px;font-size:0.7rem;color:var(--fg-dim);">
            Constructor transparency: anyone with the factory_vk can re-derive the exact invariants.
            Provenance recorded on created cells via <code>Provenance.created_by_factory</code>.
          </div>
        </div>`;
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('pyana-factory-descriptor')) {
  customElements.define('pyana-factory-descriptor', PyanaFactoryDescriptor);
}

// Inject minimal styles (idempotent)
(function inject() {
  if (document.getElementById('pyana-factory-descriptor-styles')) return;
  const s = document.createElement('style');
  s.id = 'pyana-factory-descriptor-styles';
  s.textContent = `
.pfd { font-family: var(--font-mono, ui-monospace, monospace); font-size:0.85rem; }
.pfd--compact { display:inline-flex; gap:6px; align-items:center; padding:2px 8px; background:var(--bg-raised); border:1px solid var(--line); border-radius:3px; }
.pfd__header { display:flex; align-items:center; gap:8px; margin-bottom:6px; padding-bottom:4px; border-bottom:1px solid var(--line); }
.pfd__mode-badge { font-size:0.7rem; padding:1px 6px; background:var(--accent); color:#0a0f0d; border-radius:2px; text-transform:uppercase; }
.pfd__kv { display:grid; grid-template-columns: 140px 1fr; gap:2px 8px; font-size:0.82rem; margin:6px 0; }
.pfd__kv dt { color:var(--fg-dim); }
.pfd__section { border:1px solid var(--line); border-radius:4px; margin:4px 0; }
.pfd__summary { cursor:pointer; padding:4px 8px; font-size:0.78rem; color:var(--fg-dim); user-select:none; }
.pfd__sub { padding:6px 8px; border-top:1px solid var(--line); background:var(--bg); font-size:0.82rem; }
.pfd__footer { font-style:italic; }
`;
  document.head.appendChild(s);
})();

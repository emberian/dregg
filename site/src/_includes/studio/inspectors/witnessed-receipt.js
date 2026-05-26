/**
 * <pyana-witnessed-receipt uri="pyana://receipt/<hex32>"> — unified receipt view.
 *
 * Composes <pyana-receipt> + <pyana-proof> and surfaces the scope-0/1/2 distinction
 * prominently.
 *
 * Scope determination (from NEW-WORLD.md + STARBRIDGE-PLAN.md § 4.5):
 *   Scope-0 — proof_view is null/absent: sim runtime, no STARK generated.
 *   Scope-1 — proof_view present, no inline witness_bundle: the standard
 *              verifiable shape (ALL current non-null proof_views fall here;
 *              the binding does not yet surface witness bundles separately).
 *   Scope-2 — proof_view present AND receipt carries an inline witness_bundle
 *              field: any verifier can re-execute the AIR end-to-end.
 *
 * Trust-tier badge is derived by the same heuristic as <pyana-proof>:
 *   Placeholder — scope-0
 *   Silver      — proof present, bilateral_pi absent
 *   Golden      — proof present, bilateral_pi fully populated (6 roots)
 *
 * Modes:
 *   default — two sub-panes ("Receipt fields" + "Proof") with header showing
 *             scope badge + trust-tier badge.
 *   compact — one line: "Scope-N · Tier · turn=abc…"
 *
 * Pattern: modeled on inspectors/cell.js (InspectorBase + Preact/htm effect loop).
 * Does NOT touch wasm/, inspectors.js (barrel), runtime-in-memory.js, or other
 * inspector files.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

// ---------------------------------------------------------------------------
// Scope + tier derivation
// ---------------------------------------------------------------------------

/**
 * Determine scope number from a receipt object.
 *
 * @param {object|null} r  Receipt value (from runtime.getReceipt(hash).value)
 * @returns {0|1|2}
 */
function receiptScope(r) {
  if (!r) return 0;
  const pv = r.proof_view;
  if (!pv) return 0;
  // Scope-2: inline witness_bundle present on the receipt
  if (r.witness_bundle != null) return 2;
  return 1;
}

/**
 * Determine trust tier from proof_view.
 * Mirrors the same logic in proof.js so the two components agree.
 *
 * @param {object|null} pv  proof_view field (may be null)
 * @returns {'Placeholder'|'Silver'|'Golden'}
 */
function trustTier(pv) {
  if (!pv) return 'Placeholder';
  const bp = pv.bilateral_pi;
  if (
    bp &&
    bp.outgoing_transfer_root &&
    bp.incoming_transfer_root &&
    bp.outgoing_grant_root &&
    bp.incoming_grant_root &&
    bp.outgoing_introduce_root &&
    bp.incoming_introduce_root
  ) return 'Golden';
  return 'Silver';
}

// ---------------------------------------------------------------------------
// Visual metadata tables
// ---------------------------------------------------------------------------

const SCOPE_META = {
  0: {
    label: 'Scope-0',
    color: '#6b7b74',        // grey — no proof
    bg: 'color-mix(in srgb, #6b7b74 20%, var(--bg-raised))',
    title: 'no proof attached — sim runtime; execution trusted, not proven',
    desc: 'Sim runtime — no STARK proof generated.',
  },
  1: {
    label: 'Scope-1',
    color: '#3aa8b0',        // teal — standard verifiable
    bg: 'color-mix(in srgb, #3aa8b0 22%, var(--bg-raised))',
    title: 'STARK proof attached — standard verifiable shape',
    desc: 'Proof verifies — receipt + STARK proof.',
  },
  2: {
    label: 'Scope-2',
    color: '#c9a84c',        // gold — full re-executable
    bg: 'color-mix(in srgb, #c9a84c 22%, var(--bg-raised))',
    title: 'inline WitnessBundle present — any verifier can re-execute the AIR end-to-end',
    desc: 'Inline WitnessBundle — full AIR re-execution by any verifier.',
  },
};

const TIER_META = {
  Placeholder: { color: '#6b7b74', title: 'scope-0: no STARK proof — sim runtime' },
  Silver:      { color: '#a0b8c0', title: 'executor-trusted boundaries remain' },
  Golden:      { color: '#c9a84c', title: 'full gamma.2 bilateral PI: all 6 accumulator roots present' },
};

const BADGE_BASE = [
  'display:inline-block',
  'padding:2px 10px',
  'border-radius:3px',
  'font-size:0.72rem',
  'font-weight:700',
  'letter-spacing:0.06em',
  'text-transform:uppercase',
  'color:#0a0f0d',
  'white-space:nowrap',
].join(';') + ';';

// ---------------------------------------------------------------------------
// <pyana-witnessed-receipt>
// ---------------------------------------------------------------------------

class PyanaWitnessedReceipt extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    // Tear down any previous render
    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch { /* fall through to renderParseError */ }
    if (renderParseError(this, refAttr, parsed, 'receipt')) return;

    const sig = this._runtime.getReceipt(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    // ── Badge helpers ──────────────────────────────────────────────────────

    const ScopeBadge = ({ scope }) => {
      const m = SCOPE_META[scope] || SCOPE_META[0];
      return h('span', {
        class: 'pwr__scope-badge pwr__scope-badge--' + scope,
        title: m.title,
        style: BADGE_BASE + 'background:' + m.color + ';font-size:0.78rem;',
      }, m.label);
    };

    const TierBadge = ({ tier }) => {
      const m = TIER_META[tier] || TIER_META.Placeholder;
      return h('span', {
        class: 'pwr__tier-badge pwr__tier-badge--' + tier.toLowerCase(),
        title: m.title,
        style: BADGE_BASE + 'background:' + m.color + ';',
      }, tier + ' tier');
    };

    // ── Scope-2 witness bundle summary ────────────────────────────────────

    const WitnessBundlePane = ({ wb }) => {
      // wb: the witness_bundle object from the receipt (shape TBD when wired)
      const entries = wb && typeof wb === 'object' ? Object.entries(wb) : [];
      if (!entries.length) {
        return h('div', {
          class: 'pwr__wb pwr__wb--empty',
          style: 'color:var(--fg-dim);font-size:0.8rem;padding:8px;border:1px dashed var(--line);border-radius:4px;',
        }, 'WitnessBundle present (empty / not yet decoded)');
      }
      return h('div', { class: 'pwr__wb' },
        h('div', {
          style: 'color:var(--fg-dim);font-size:0.78rem;margin-bottom:4px;text-transform:uppercase;letter-spacing:0.05em;',
        }, 'Inline WitnessBundle'),
        h('dl', { class: 'pyana-inspector__kv', style: 'font-size:0.78rem;' },
          ...entries.map(([k, v]) => [
            h('dt', null, _esc(k)),
            h('dd', null, h('code', null, _esc(String(v)).slice(0, 64))),
          ]).flat()
        )
      );
    };

    // ── Scope descriptor strip ────────────────────────────────────────────

    const ScopeStrip = ({ scope, tier }) => {
      const sm = SCOPE_META[scope] || SCOPE_META[0];
      return h('div', {
        class: 'pwr__scope-strip',
        style: `padding:8px 12px;background:${sm.bg};border-radius:4px;margin-bottom:10px;` +
               'display:flex;align-items:center;gap:10px;flex-wrap:wrap;',
      },
        h(ScopeBadge, { scope }),
        h(TierBadge, { tier }),
        h('span', {
          style: 'font-size:0.82rem;color:var(--fg-dim);flex:1;min-width:180px;',
        }, sm.desc)
      );
    };

    // ── Main component ────────────────────────────────────────────────────

    const Component = () => {
      const r = sig.value;

      if (!r) {
        return html`<div class="pyana-inspector pyana-inspector--empty">
          witnessed-receipt not found: <code>${shortHex(parsed.id, 16)}</code>
        </div>`;
      }

      const scope = receiptScope(r);
      const tier = trustTier(r.proof_view || null);
      const proofUri = `pyana://receipt/${r.turn_hash}`;

      // ── Compact mode ───────────────────────────────────────────────────

      if (mode === 'compact') {
        return h('span', {
          class: 'pyana-inspector pyana-inspector--compact pwr pwr--compact',
          title: SCOPE_META[scope].title,
        },
          h(ScopeBadge, { scope }),
          ' · ',
          h(TierBadge, { tier }),
          ' · turn=',
          h('code', { title: r.turn_hash }, shortHex(r.turn_hash, 10))
        );
      }

      // ── Default mode ───────────────────────────────────────────────────

      return h('div', { class: 'pyana-inspector pyana-inspector--cell pwr' },
        // ── Header ──────────────────────────────────────────────────────
        h('header', { class: 'pwr__header' },
          h('span', { class: 'pyana-inspector__kind' }, 'Receipt'),
          h('code', { class: 'pyana-inspector__id', title: parsed.id }, shortHex(parsed.id, 24)),
          h(ScopeBadge, { scope }),
          h(TierBadge, { tier })
        ),

        // ── Scope strip ──────────────────────────────────────────────────
        h(ScopeStrip, { scope, tier }),

        // ── Scope-2 witness bundle pane (only when scope-2) ──────────────
        scope === 2
          ? h('div', { class: 'pwr__section', style: 'margin-bottom:10px;' },
              h('div', { class: 'pwr__section-label' }, 'Witness Bundle'),
              h(WitnessBundlePane, { wb: r.witness_bundle })
            )
          : null,

        // ── Receipt fields sub-pane ──────────────────────────────────────
        h('details', { class: 'pwr__details', open: true },
          h('summary', { class: 'pwr__summary' }, 'Receipt fields'),
          h('div', { class: 'pwr__sub-pane' },
            // Embed <pyana-receipt> — the existing inspector handles its own
            // signal subscription and re-render cycle.  Passing uri= as an
            // attribute keeps the element self-contained and avoids a
            // second getReceipt() call (they share the same signal).
            h('pyana-receipt', { uri: `pyana://receipt/${parsed.id}`, mode: 'default' })
          )
        ),

        // ── Proof sub-pane ───────────────────────────────────────────────
        h('details', { class: 'pwr__details', style: 'margin-top:6px;', open: scope > 0 },
          h('summary', { class: 'pwr__summary' }, 'Proof'),
          h('div', { class: 'pwr__sub-pane' },
            // <pyana-proof> uses the turn_hash as its receipt id, matching
            // how proof.js resolves proof_view.
            h('pyana-proof', { uri: proofUri, mode: 'default' })
          )
        )
      );
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('pyana-witnessed-receipt')) {
  customElements.define('pyana-witnessed-receipt', PyanaWitnessedReceipt);
}

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

function _esc(s) {
  if (s == null) return '';
  return String(s)
    .replace(/&/g, '&amp;')
    .replace(/</g, '&lt;')
    .replace(/>/g, '&gt;')
    .replace(/"/g, '&quot;');
}

// ---------------------------------------------------------------------------
// Styles — injected once into document head.
// Uses site-palette tokens throughout.
// ---------------------------------------------------------------------------

(function injectStyles() {
  if (document.getElementById('pyana-witnessed-receipt-styles')) return;
  const s = document.createElement('style');
  s.id = 'pyana-witnessed-receipt-styles';
  s.textContent = `
/* ---- <pyana-witnessed-receipt> ---- */
.pwr {
  font-family: var(--font-mono, ui-monospace, monospace);
  font-size: 0.85rem;
}
.pwr__header {
  display: flex;
  align-items: center;
  flex-wrap: wrap;
  gap: 8px;
  margin-bottom: 10px;
  padding-bottom: 8px;
  border-bottom: 1px solid var(--line);
}
.pwr--compact {
  display: inline-flex;
  align-items: center;
  gap: 6px;
  padding: 3px 10px;
  background: var(--bg-raised);
  border: 1px solid var(--line);
  border-radius: 4px;
  font-size: 0.80rem;
  color: var(--fg);
}
.pwr__scope-badge,
.pwr__tier-badge {
  cursor: default;
}
.pwr__section {
  border: 1px solid var(--line);
  border-radius: 4px;
  padding: 8px 10px;
  background: var(--bg-raised);
}
.pwr__section-label {
  font-size: 0.72rem;
  text-transform: uppercase;
  letter-spacing: 0.06em;
  color: var(--fg-dim);
  margin-bottom: 6px;
}
.pwr__details {
  border: 1px solid var(--line);
  border-radius: 4px;
  overflow: hidden;
}
.pwr__summary {
  cursor: pointer;
  padding: 6px 10px;
  font-size: 0.80rem;
  color: var(--fg-dim);
  background: var(--bg-raised);
  user-select: none;
  list-style: none;
  display: flex;
  align-items: center;
  gap: 6px;
}
.pwr__summary::-webkit-details-marker { display: none; }
.pwr__summary::before {
  content: '▶';
  font-size: 0.65rem;
  transition: transform 0.15s;
}
details[open] > .pwr__summary::before {
  transform: rotate(90deg);
}
.pwr__sub-pane {
  padding: 8px 10px;
  border-top: 1px solid var(--line);
  background: var(--bg);
}
/* Scope strip accent border — left-side color follows scope */
.pwr__scope-badge--0 { opacity: 0.9; }
.pwr__scope-badge--1 { opacity: 1; }
.pwr__scope-badge--2 { opacity: 1; }
`;
  document.head.appendChild(s);
})();

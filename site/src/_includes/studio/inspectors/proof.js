/**
 * <pyana-proof uri="pyana://receipt/<hex32>"> — per-receipt proof metadata + γ.2 bilateral PI.
 *
 * Reads the `proof_view` field on a receipt from `get_receipt_chain(handle)`.
 *
 * Trust-tier heuristic (Houyhnhnm directive / NEW-WORLD.md "blame is sub-additive"):
 *   - Placeholder  — proof_view is null/undefined (scope-0: sim runtime, no STARK generated)
 *   - Silver       — proof_view is present with kind + public_inputs, but bilateral_pi is absent
 *                    (executor-trusted boundaries still exist; section 1/6 of What's not done)
 *   - Golden       — proof_view present AND bilateral_pi present with all six accumulator roots
 *                    (outgoing_X/incoming_X for transfer/grant/introduce): full gamma.2 bilateral binding
 *
 * The 9 PI placeholder variants and 3 executor-trusted boundary cuts are the reason this
 * badge must be visible: the UI must not hide scope-reduction.
 *
 * URI: the <id> segment is the turn_hash hex (same as pyana-receipt).
 * Attributes:
 *   uri  — pyana://receipt/<turn_hash>
 *   mode — default | compact
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

/** Derive trust tier from a proof_view value (may be null/undefined). */
function trustTier(proofView) {
  if (!proofView) return 'Placeholder';
  const bp = proofView.bilateral_pi;
  if (
    bp &&
    bp.outgoing_transfer_root &&
    bp.incoming_transfer_root &&
    bp.outgoing_grant_root &&
    bp.incoming_grant_root &&
    bp.outgoing_introduce_root &&
    bp.incoming_introduce_root
  ) {
    return 'Golden';
  }
  return 'Silver';
}

/** Visual label + color for a trust tier. */
const TIER_META = {
  Placeholder: { label: 'Placeholder', color: '#6b7b74', title: 'scope-0: no STARK proof — sim runtime' },
  Silver:      { label: 'Silver',      color: '#a0b8c0', title: 'executor-trusted boundaries remain (section 1/6)' },
  Golden:      { label: 'Golden',      color: '#c9a84c', title: 'full gamma.2 bilateral PI: all 6 accumulator roots present' },
};

const BADGE_STYLE = 'display:inline-block;padding:2px 10px;border-radius:3px;font-size:0.72rem;font-weight:700;letter-spacing:0.06em;text-transform:uppercase;color:#0a0f0d;';

class PyanaProof extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'receipt')) return;

    const sig = this._runtime.getReceipt(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    const TierBadge = ({ tier }) => {
      const meta = TIER_META[tier] || TIER_META.Placeholder;
      return h('span', {
        class: 'pyana-proof__tier-badge pyana-proof__tier-badge--' + tier.toLowerCase(),
        title: meta.title,
        style: BADGE_STYLE + 'background:' + meta.color + ';',
      }, meta.label + ' tier');
    };

    const BilateralPiSection = ({ bp }) => {
      if (!bp) {
        return h('div', { class: 'pyana-proof__bilateral-absent', style: 'color:var(--fg-dim);font-size:0.8rem;margin-top:8px;' },
          'bilateral PI: ',
          h('em', null, 'absent'),
          ' — cross-cell accumulator roots not present'
        );
      }
      return h('div', { class: 'pyana-proof__bilateral', style: 'margin-top:8px;' },
        h('div', { class: 'pyana-proof__bilateral-label', style: 'color:var(--fg-dim);font-size:0.8rem;margin-bottom:4px;' },
          'γ.2 bilateral PI'
        ),
        h('dl', { class: 'pyana-inspector__kv', style: 'font-size:0.8rem;' },
          h('dt', null, 'outgoing transfer'), h('dd', null, h('code', { title: bp.outgoing_transfer_root }, shortHex(bp.outgoing_transfer_root, 16))),
          h('dt', null, 'incoming transfer'), h('dd', null, h('code', { title: bp.incoming_transfer_root }, shortHex(bp.incoming_transfer_root, 16))),
          h('dt', null, 'outgoing grant'),    h('dd', null, h('code', { title: bp.outgoing_grant_root },    shortHex(bp.outgoing_grant_root, 16))),
          h('dt', null, 'incoming grant'),    h('dd', null, h('code', { title: bp.incoming_grant_root },    shortHex(bp.incoming_grant_root, 16))),
          h('dt', null, 'outgoing introduce'),h('dd', null, h('code', { title: bp.outgoing_introduce_root },shortHex(bp.outgoing_introduce_root, 16))),
          h('dt', null, 'incoming introduce'),h('dd', null, h('code', { title: bp.incoming_introduce_root },shortHex(bp.incoming_introduce_root, 16)))
        )
      );
    };

    const Scope0Box = ({ tier }) => {
      const meta = TIER_META[tier] || TIER_META.Placeholder;
      return h('div', {
        class: 'pyana-proof__scope0',
        style: 'padding:12px;border:1px dashed var(--line);border-radius:6px;color:var(--fg-dim);font-size:0.85rem;line-height:1.6;margin-top:8px;',
      },
        h('strong', null, 'No proof — scope-0'),
        h('br', null),
        'The sim runtime does not run the Effect VM STARK. Receipts from in-browser simulation are scope-0: execution is trusted, not proven. A real proof would be present when a remote runtime attaches a ',
        h('code', null, 'WitnessedReceipt'),
        '.',
        h('br', null),
        h('br', null),
        h('span', { title: meta.title, style: 'opacity:0.75;' },
          'Trust tier: ', tier, ' — ', meta.title
        )
      );
    };

    const ProofDetail = ({ pv }) => {
      const piList = pv.public_inputs && pv.public_inputs.length
        ? h('ul', { style: 'list-style:none;padding:0;margin:0;display:flex;flex-direction:column;gap:2px;' },
            ...pv.public_inputs.map((pi, i) =>
              h('li', { style: 'font-size:0.78rem;' },
                h('code', null, String(i).padStart(2, '0') + ': ' + shortHex(pi, 24))
              )
            )
          )
        : h('span', { style: 'opacity:0.6;' }, '(none)');

      return h('div', null,
        h('dl', { class: 'pyana-inspector__kv', style: 'margin-bottom:12px;' },
          h('dt', null, 'kind'),           h('dd', null, pv.kind),
          h('dt', null, 'is agent cell'),  h('dd', null, pv.is_agent_cell ? 'yes' : 'no'),
          h('dt', null, 'is sovereign cell'), h('dd', null, pv.is_sovereign_cell ? 'yes' : 'no'),
          h('dt', null, 'public inputs'), h('dd', null, piList)
        ),
        h(BilateralPiSection, { bp: pv.bilateral_pi || null })
      );
    };

    const Component = () => {
      const r = sig.value;
      if (!r) return html`
        <div class="pyana-inspector pyana-inspector--empty">
          receipt not found: <code>${shortHex(parsed.id, 16)}</code>
        </div>`;

      const pv = r.proof_view || null;
      const tier = trustTier(pv);

      if (mode === 'compact') {
        return h('span', { class: 'pyana-inspector pyana-inspector--compact' },
          h('span', { class: 'pyana-inspector__kind' }, 'proof'),
          ' ',
          h('code', { title: parsed.id }, shortHex(parsed.id)),
          ' · ',
          h(TierBadge, { tier }),
          pv ? (' · ' + pv.kind) : h('em', { style: 'opacity:0.6;' }, ' · no proof — scope-0')
        );
      }

      return h('div', { class: 'pyana-inspector pyana-inspector--cell pyana-proof' },
        h('header', null,
          h('span', { class: 'pyana-inspector__kind' }, 'proof'),
          ' ',
          h('code', { class: 'pyana-inspector__id', title: parsed.id }, shortHex(parsed.id, 24)),
          ' ',
          h(TierBadge, { tier })
        ),
        pv ? h(ProofDetail, { pv }) : h(Scope0Box, { tier })
      );
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('pyana-proof')) customElements.define('pyana-proof', PyanaProof);

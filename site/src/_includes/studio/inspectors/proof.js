/**
 * <dregg-proof uri="dregg://receipt/<hex32>"> — per-receipt proof metadata + γ.2 bilateral PI.
 *
 * Reads the `proof_view` field on a receipt from `get_receipt_chain(handle)`.
 *
 * Trust-tier heuristic (Houyhnhnm directive / NEW-WORLD.md "blame is sub-additive"):
 *   - Placeholder  — proof_view is null/undefined: the turn has no STARK proof
 *                    generated yet (scope-0). For sim-runtime receipts this is a
 *                    transient state — see the lazy-prove step below — and is only
 *                    final if proving genuinely failed.
 *   - Silver       — proof_view is present with kind + public_inputs, but bilateral_pi is absent
 *                    (executor-trusted boundaries still exist; section 1/6 of What's not done).
 *                    This is what an honest EffectVM STARK over the sim runtime produces:
 *                    a real proof binding the net-delta + commitment transition, with the
 *                    γ.2 bilateral accumulator roots still executor-trusted (zero sentinels).
 *   - Golden       — proof_view present AND bilateral_pi present with all six accumulator roots
 *                    (outgoing_X/incoming_X for transfer/grant/introduce): full gamma.2 bilateral binding
 *
 * Lazy proving (perf): STARK proving is expensive in wasm, so the runtime does
 * NOT prove on commit or at boot. On first view of a sim-runtime receipt with
 * no proof_view, this inspector triggers `wasm.prove_turn(handle, turnHash)`
 * once (idempotent + cached in the runtime) and bumps the runtime version so
 * the receipt-chain signal re-fetches with the real proof_view. Subsequent
 * renders read the cache — no re-proving.
 *
 * The 9 PI placeholder variants and 3 executor-trusted boundary cuts are the reason this
 * badge must be visible: the UI must not hide scope-reduction.
 *
 * URI: the <id> segment is the turn_hash hex (same as dregg-receipt).
 * Attributes:
 *   uri  — dregg://receipt/<turn_hash>
 *   mode — default | compact
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

/**
 * Derive trust tier from a proof_view value (may be null/undefined).
 *
 * GOLDEN is reached two ways, both REAL (never a flag flip):
 *   1. A per-receipt proof_view carrying all six γ.2 bilateral accumulator
 *      roots in `bilateral_pi` (full single-proof bilateral binding), OR
 *   2. A real cross-cell bilateral *aggregate* proof attached as
 *      `proof_view.bilateral_aggregate` whose outer STARK self-verified
 *      (`bilateral_consistent`) AND whose sender + receiver are bound to the
 *      same transfer (`roots_matched`: both transfer roots present + the
 *      Turn-derived schedule re-check passed inside verify_aggregated_bundle).
 *      The OUTGOING/INCOMING roots are domain-separated and intentionally not
 *      byte-equal; the binding is the shared transfer_id both absorb. This is
 *      the γ.2 aggregator's cross-cell agreement.
 *
 * SILVER is a present proof_view without either of those (the single-turn
 * EffectVM STARK with executor-trusted cross-cell boundaries).
 */
function trustTier(proofView) {
  if (!proofView) return 'Placeholder';
  const agg = proofView.bilateral_aggregate;
  if (agg && agg.bilateral_consistent && agg.roots_matched) {
    return 'Golden';
  }
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
  Golden:      { label: 'Golden',      color: '#c9a84c', title: 'real γ.2 cross-cell bilateral aggregate: verified outer STARK binds sender + receiver to the same transfer_id' },
};

const BADGE_STYLE = 'display:inline-block;padding:2px 10px;border-radius:3px;font-size:0.72rem;font-weight:700;letter-spacing:0.06em;text-transform:uppercase;color:#0a0f0d;';

class DreggProof extends InspectorBase {
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

    // Lazy, cached, non-blocking STARK proving. The sim runtime does not prove
    // on commit (perf); we trigger one real EffectVM proof on first view of a
    // proofless receipt, then bump the runtime version so the receipt-chain
    // signal re-fetches with the real proof_view. Guarded so we attempt at
    // most once per turn hash on this element.
    const rt = this._runtime;
    const maybeProve = (receipt) => {
      if (!receipt || receipt.proof_view) return;       // nothing to do
      if (!rt || !rt._wasm || rt._handle == null) return; // sim only
      if (typeof rt._wasm.prove_turn !== 'function') return;
      this._proveAttempts = this._proveAttempts || new Set();
      if (this._proveAttempts.has(parsed.id)) return;
      this._proveAttempts.add(parsed.id);
      // Defer off the render tick so we never block the inspector paint.
      Promise.resolve().then(() => {
        try {
          rt._wasm.prove_turn(rt._handle, parsed.id);
          if (rt.version) rt.version.value = rt.version.value + 1; // refresh signal
        } catch (e) {
          // Genuine proving failure: leave Placeholder (honest scope-0).
          console.warn('[dregg-proof] prove_turn failed for', parsed.id, e?.message || e);
        }
      });
    };

    // Lazily produce the REAL γ.2 cross-cell bilateral *aggregate* (GOLDEN
    // tier) and stash it on the element. This is a standalone verified
    // artifact (a two-cell transfer aggregate), surfaced alongside the seeded
    // turn's single-turn SILVER proof — NOT a flag flip. We attempt it once,
    // after the single-turn proof exists, and re-trigger a render via the
    // signal bump so the merged Golden view paints.
    const maybeProveAggregate = () => {
      if (this._aggregate !== undefined) return;          // already attempted
      if (!rt || !rt._wasm || rt._handle == null) return; // sim only
      if (typeof rt._wasm.prove_bilateral_aggregate !== 'function') return;
      this._aggregate = null; // mark attempted
      Promise.resolve().then(() => {
        try {
          this._aggregate = rt._wasm.prove_bilateral_aggregate(rt._handle);
          if (rt.version) rt.version.value = rt.version.value + 1; // refresh signal
        } catch (e) {
          // Genuine aggregate proving/verification failure: leave it absent;
          // the tier stays honestly Silver.
          console.warn('[dregg-proof] prove_bilateral_aggregate failed', e?.message || e);
        }
      });
    };

    const TierBadge = ({ tier }) => {
      const meta = TIER_META[tier] || TIER_META.Placeholder;
      return h('span', {
        class: 'dregg-proof__tier-badge dregg-proof__tier-badge--' + tier.toLowerCase(),
        title: meta.title,
        style: BADGE_STYLE + 'background:' + meta.color + ';',
      }, meta.label + ' tier');
    };

    const BilateralPiSection = ({ bp }) => {
      if (!bp) {
        return h('div', { class: 'dregg-proof__bilateral-absent', style: 'color:var(--fg-dim);font-size:0.8rem;margin-top:8px;' },
          'bilateral PI: ',
          h('em', null, 'absent'),
          ' — cross-cell accumulator roots not present'
        );
      }
      return h('div', { class: 'dregg-proof__bilateral', style: 'margin-top:8px;' },
        h('div', { class: 'dregg-proof__bilateral-label', style: 'color:var(--fg-dim);font-size:0.8rem;margin-bottom:4px;' },
          'γ.2 bilateral PI'
        ),
        h('dl', { class: 'dregg-inspector__kv', style: 'font-size:0.8rem;' },
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
        class: 'dregg-proof__scope0',
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

    const BilateralAggregateSection = ({ agg }) => {
      if (!agg) return null;
      const matched = agg.bilateral_consistent && agg.roots_matched;
      return h('div', { class: 'dregg-proof__aggregate', style: 'margin-top:12px;padding:10px;border:1px solid var(--line);border-radius:6px;' },
        h('div', { style: 'color:#c9a84c;font-size:0.82rem;font-weight:700;margin-bottom:6px;letter-spacing:0.04em;' },
          'γ.2 cross-cell bilateral aggregate'
        ),
        h('dl', { class: 'dregg-inspector__kv', style: 'font-size:0.8rem;' },
          h('dt', null, 'aggregate AIR'), h('dd', null, h('code', null, agg.kind)),
          h('dt', null, 'cells'),         h('dd', null, String(agg.n_cells)),
          h('dt', null, 'consistent'),    h('dd', null, agg.bilateral_consistent ? 'yes (outer STARK pinned)' : 'no'),
          h('dt', null, 'sender (outgoing)'), h('dd', null, h('code', { title: agg.sender_cell }, shortHex(agg.sender_cell, 16))),
          h('dt', null, 'receiver (incoming)'), h('dd', null, h('code', { title: agg.receiver_cell }, shortHex(agg.receiver_cell, 16))),
          h('dt', null, 'OUTGOING transfer root'), h('dd', null, h('code', { title: agg.outgoing_transfer_root }, shortHex(agg.outgoing_transfer_root, 16))),
          h('dt', null, 'INCOMING transfer root'), h('dd', null, h('code', { title: agg.incoming_transfer_root }, shortHex(agg.incoming_transfer_root, 16))),
          h('dt', null, 'shared transfer_id'), h('dd', null, h('code', { title: agg.shared_transfer_id }, shortHex(agg.shared_transfer_id, 16))),
          h('dt', null, 'cross-cell binding'),
          h('dd', null, h('strong', { style: 'color:' + (matched ? '#c9a84c' : 'var(--fg-dim)') + ';' },
            matched ? 'BOUND — both sides fold the same transfer_id (verified aggregate)' : 'no'
          ))
        ),
        h('div', { style: 'color:var(--fg-dim);font-size:0.72rem;margin-top:6px;line-height:1.5;' },
          'The OUTGOING and INCOMING roots are domain-separated (salts OTX2 / ITX2) so they are not byte-equal by design; the cross-cell binding is the shared transfer_id both absorb, attested by the verified outer aggregate STARK.'
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
        h('dl', { class: 'dregg-inspector__kv', style: 'margin-bottom:12px;' },
          h('dt', null, 'kind'),           h('dd', null, pv.kind),
          h('dt', null, 'is agent cell'),  h('dd', null, pv.is_agent_cell ? 'yes' : 'no'),
          h('dt', null, 'is sovereign cell'), h('dd', null, pv.is_sovereign_cell ? 'yes' : 'no'),
          h('dt', null, 'public inputs'), h('dd', null, piList)
        ),
        h(BilateralPiSection, { bp: pv.bilateral_pi || null }),
        h(BilateralAggregateSection, { agg: pv.bilateral_aggregate || null })
      );
    };

    const Component = () => {
      const r = sig.value;
      if (!r) return html`
        <div class="dregg-inspector dregg-inspector--empty">
          receipt not found: <code>${shortHex(parsed.id, 16)}</code>
        </div>`;

      let pv = r.proof_view || null;
      // Kick off lazy proving on first sight of a proofless receipt.
      if (!pv) maybeProve(r);
      // Once the single-turn (Silver) proof exists, lazily produce the real
      // γ.2 cross-cell bilateral aggregate (Golden) and merge it in. The
      // aggregate is a standalone verified artifact, not a tier flip.
      if (pv) {
        maybeProveAggregate();
        if (this._aggregate) {
          pv = { ...pv, bilateral_aggregate: this._aggregate };
        }
      }
      const tier = trustTier(pv);

      if (mode === 'compact') {
        return h('span', { class: 'dregg-inspector dregg-inspector--compact' },
          h('span', { class: 'dregg-inspector__kind' }, 'proof'),
          ' ',
          h('code', { title: parsed.id }, shortHex(parsed.id)),
          ' · ',
          h(TierBadge, { tier }),
          pv ? (' · ' + pv.kind) : h('em', { style: 'opacity:0.6;' }, ' · no proof — scope-0')
        );
      }

      return h('div', { class: 'dregg-inspector dregg-inspector--cell dregg-proof' },
        h('header', null,
          h('span', { class: 'dregg-inspector__kind' }, 'proof'),
          ' ',
          h('code', { class: 'dregg-inspector__id', title: parsed.id }, shortHex(parsed.id, 24)),
          ' ',
          h(TierBadge, { tier })
        ),
        pv ? h(ProofDetail, { pv }) : h(Scope0Box, { tier })
      );
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('dregg-proof')) customElements.define('dregg-proof', DreggProof);

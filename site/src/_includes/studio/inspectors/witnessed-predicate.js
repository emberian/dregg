/**
 * <dregg-witnessed-predicate data="..." | uri="dregg://witnessed-predicate/...">
 * Unified dispatcher per NEW-WORLD "Predicates everywhere" + cell::predicate::WitnessedPredicate.
 * Renders kind-specific using platform <dregg-*> where available (dfa), visible
 * Placeholders for others (temporal, blinded-set, merkle, pedersen, custom, bridge).
 * Follows _base + data= + signals + reuse (no JS reimpl of predicate eval).
 * Used inside <dregg-authorization> Custom, cell-program caveats etc.
 * Trust tier surface via kind badges (Placeholder for missing sub-inspectors).
 */
import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggWitnessedPredicate extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let wp = null;
    if (dataAttr) {
      try { wp = JSON.parse(dataAttr); } catch {}
    }
    if (!wp && refAttr) {
      let parsed;
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'witnessed-predicate')) return;
      // uri-only: expect data or placeholder
      wp = { kind: 'Placeholder', predicate_kind: 'Unknown' };
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (!wp) return html`<div class="dregg-inspector dregg-inspector--empty">no witnessed-predicate data</div>`;
      const kind = wp.predicate_kind || wp.kind || wp.type || 'Custom';
      const lower = kind.toLowerCase();

      let sub;
      if (lower.includes('dfa')) {
        sub = html`<dregg-dfa data-dfa=${JSON.stringify(wp)} mode="compact"></dregg-dfa>`;
      } else if (lower.includes('temporal')) {
        sub = html`<span class="dregg-inspector--placeholder">&lt;dregg-temporal&gt; awaiting wasm/runtime support (Placeholder)</span>`;
      } else if (lower.includes('blinded') || lower.includes('set')) {
        sub = html`<span class="dregg-inspector--placeholder">&lt;dregg-blinded-set&gt; awaiting wasm/runtime support (Placeholder for ${kind})</span>`;
      } else if (lower.includes('merkle') || lower.includes('membership')) {
        sub = html`<span class="dregg-inspector--placeholder">&lt;dregg-merkle-membership&gt; awaiting runtime proof data (Placeholder; see &lt;dregg-merkle-tree&gt;)</span>`;
      } else if (lower.includes('pedersen')) {
        sub = html`<span class="dregg-inspector--placeholder">&lt;dregg-pedersen-commitment&gt; awaiting wasm/runtime support (Placeholder; see stealth value-commit)</span>`;
      } else if (lower.includes('bridge')) {
        sub = html`<span class="dregg-inspector--placeholder">BridgePredicate awaiting wasm/runtime support (Placeholder)</span>`;
      } else {
        sub = html`<code>${shortHex(wp.commitment || '', 8)}</code> (custom vk: ${shortHex(wp.vk_hash || '', 8)})`;
      }

      if (mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">W(${kind}) ${sub}</span>`;
      }
      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-witnessed-predicate">
          <header>
            <span class="dregg-inspector__kind">witnessed-predicate</span>
            <span class="dregg-inspector__id">${kind}</span>
          </header>
          <div style="font-size:0.8rem;">${sub}</div>
          <div style="font-size:0.65rem;color:var(--fg-dim);margin-top:4px;">
            commitment: <code>${shortHex(wp.commitment || '', 16)}</code> · input_ref: ${wp.input_ref || 'n/a'} · proof_idx: ${wp.proof_witness_index ?? '?'}
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-witnessed-predicate')) customElements.define('dregg-witnessed-predicate', DreggWitnessedPredicate);

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
import { InspectorBase, renderParseError, shortHex, emptyState } from './_base.js';

function readJson(s) {
  try { return { value: JSON.parse(s), error: null }; } catch (error) { return { value: null, error }; }
}

function compactJson(value, max = 120) {
  if (value == null) return '';
  const s = typeof value === 'string' ? value : JSON.stringify(value);
  return s.length > max ? s.slice(0, max) + '…' : s;
}

class DreggWitnessedPredicate extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let wp = null;
    let parsed = null;
    let parseError = null;
    if (dataAttr) {
      const parsedData = readJson(dataAttr);
      wp = parsedData.value;
      parseError = parsedData.error;
    }
    if (!wp && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'witnessed-predicate')) return;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (parseError) {
        return html`<div class="dregg-inspector dregg-inspector--err">bad witnessed-predicate data JSON: ${parseError.message}</div>`;
      }
      if (!wp) {
        return emptyState(
          html,
          'Witnessed predicate unavailable',
          parsed
            ? html`The URI parsed as <code>${shortHex(parsed.id, 16)}</code>, but this runtime has no witnessed-predicate lookup. Provide <code>data</code> JSON from an authorization, caveat, or receipt to inspect the predicate witness.`
            : html`Provide <code>data</code> JSON from an authorization, caveat, or receipt to inspect the predicate witness.`
        );
      }
      const kind = wp.predicate_kind || wp.kind || wp.type || 'Custom';
      const lower = kind.toLowerCase();
      const commitment = wp.commitment || wp.predicate_commitment || wp.hash || '';
      const inputRef = wp.input_ref || wp.input || wp.subject || '';
      const proofIndex = wp.proof_witness_index ?? wp.witness_index ?? wp.proof_idx;
      const trustTier = wp.trust_tier || wp.trust || wp.tier || (wp.proof ? 'proof supplied' : 'witness metadata only');

      let sub;
      if (lower.includes('dfa')) {
        sub = html`<dregg-dfa data-dfa=${JSON.stringify(wp.dfa || wp.route_table || wp)} mode="compact"></dregg-dfa>`;
      } else if (lower.includes('temporal')) {
        sub = html`<div class="dregg-inspector__note">Temporal predicate metadata is available, but temporal evaluation is not reproduced in JavaScript. Inspect the supplied window/clock fields below.</div>`;
      } else if (lower.includes('blinded') || lower.includes('set')) {
        sub = html`<div class="dregg-inspector__note">Blinded-set predicate. Membership semantics require the runtime proof/witness; this view shows only supplied commitments and witness references.</div>`;
      } else if (lower.includes('merkle') || lower.includes('membership')) {
        sub = wp.merkle_tree || wp.tree
          ? html`<dregg-merkle-tree data-tree=${JSON.stringify(wp.merkle_tree || wp.tree)} mode="compact"></dregg-merkle-tree>`
          : html`<div class="dregg-inspector__note">Merkle membership metadata without an inline tree/proof. Supply <code>tree</code> or <code>merkle_tree</code> to inspect the path.</div>`;
      } else if (lower.includes('pedersen')) {
        sub = html`<div class="dregg-inspector__note">Pedersen commitment predicate. This inspector displays commitments and witness handles only; it does not verify openings.</div>`;
      } else if (lower.includes('bridge')) {
        sub = html`<div class="dregg-inspector__note">Bridge predicate metadata. Bridge-specific verification remains in the runtime or bridge verifier.</div>`;
      } else {
        sub = html`<div class="dregg-inspector__note">Custom predicate${wp.vk_hash ? html` with verifier key <code>${shortHex(wp.vk_hash, 12)}</code>` : ''}. Evaluation is delegated to the supplied verifier/runtime.</div>`;
      }

      if (mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">W(${kind}) ${commitment ? html`<code>${shortHex(commitment, 8)}</code>` : html`<span class="dregg-inspector__meta">no commitment</span>`}</span>`;
      }
      return html`
        <div class="dregg-inspector dregg-inspector--cell dregg-witnessed-predicate">
          <header>
            <span class="dregg-inspector__kind">witnessed-predicate</span>
            <span class="dregg-inspector__id">${kind}</span>
            <span class="dregg-inspector__pill">${trustTier}</span>
          </header>
          <div class="dregg-inspector__panel">${sub}</div>
          <dl class="dregg-inspector__kv">
            <dt>commitment</dt><dd>${commitment ? html`<code title=${commitment}>${shortHex(commitment, 18)}</code>` : html`<span class="dregg-inspector__meta">not supplied</span>`}</dd>
            <dt>input ref</dt><dd>${inputRef ? html`<code>${compactJson(inputRef)}</code>` : html`<span class="dregg-inspector__meta">not supplied</span>`}</dd>
            <dt>witness index</dt><dd>${proofIndex ?? html`<span class="dregg-inspector__meta">not supplied</span>`}</dd>
            ${wp.vk_hash ? html`<dt>verifier key</dt><dd><code title=${wp.vk_hash}>${shortHex(wp.vk_hash, 18)}</code></dd>` : null}
          </dl>
          <details class="dregg-inspector__section">
            <summary>Supplied predicate fields</summary>
            <div class="dregg-inspector__section-body"><code>${compactJson(wp, 900)}</code></div>
          </details>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}
if (!customElements.get('dregg-witnessed-predicate')) customElements.define('dregg-witnessed-predicate', DreggWitnessedPredicate);

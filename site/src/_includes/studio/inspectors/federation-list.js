/**
 * <dregg-federation-list> — lists KnownFederations registry + sim-created federations.
 *
 * Per STARBRIDGE-PLAN §4.5 + §5.7: needs list_known_federations wasm binding.
 * Today: falls back to runtime-created federations (via listBlocks / getFederation).
 * Renders each as <dregg-federation> + block-dag affordance.
 *
 * Reuses platform vocab: <dregg-federation>, <dregg-block-dag>.
 *
 * Supports register affordance (placeholder until extension cclerk + binding).
 */

import { InspectorBase, dreggCodeLink, emptyState, shortHex } from './_base.js';

class DreggFederationList extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const root = document.createElement('div');
    this.appendChild(root);
    const knownSignal = this._runtime.listKnownFederations ? this._runtime.listKnownFederations() : null;
    const blocksSignal = this._runtime.listBlocks ? this._runtime.listBlocks() : null;

    const Component = () => {
      let feds = [];
      try {
        if (knownSignal && Array.isArray(knownSignal.value) && knownSignal.value.length) {
          feds = knownSignal.value;
        }
        const seen = new Set();
        for (const f of feds) seen.add(String(f.fed_index ?? f.registered_index ?? f.id ?? 0));
        for (const block of (blocksSignal?.value || [])) {
          const idx = block.fed_index ?? block.federation_index ?? 0;
          if (!seen.has(String(idx))) {
            seen.add(String(idx));
            feds.push({ fed_index: idx, name: `federation #${idx}`, height: block.height ?? 0 });
          }
        }
        if (this._runtime._wasm && typeof this._runtime._wasm.list_federation_blocks === 'function') {
          for (let i = 0; i < 8; i++) {
            try {
              const bl = this._runtime._wasm.list_federation_blocks(this._runtime._handle, i);
              if (bl && bl.length && !seen.has(String(i))) {
                seen.add(String(i));
                feds.push({ fed_index: i, name: `fed-${i}`, height: bl.length });
              }
            } catch {}
          }
        }
      } catch (e) { /* silent */ }

      if (mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">federations: ${feds.length}</span>`;
      }

      const totalHeight = feds.reduce((sum, f) => sum + Number(f.height || 0), 0);
      const totalNodes = feds.reduce((sum, f) => sum + Number(f.num_nodes || f.nodes || 0), 0);
      return html`
        <div class="dregg-inspector dregg-inspector--cell pfl">
          <header>
            <span class="dregg-inspector__kind">federation-list</span>
            <span class="pfl__count">${feds.length} known</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>Federations</span><strong>${String(feds.length)}</strong></div>
            <div><span>Total Height</span><strong>${String(totalHeight)}</strong></div>
            <div><span>Known Nodes</span><strong>${String(totalNodes)}</strong></div>
          </div>
          ${feds.length === 0
            ? emptyState(html, 'No federations known', 'Create a local federation, connect a remote node, or use the extension federation registry.')
            : html`<div class="dregg-inspector__rows">
                ${feds.map(f => html`
                  <div class="dregg-inspector__row">
                    <span>#${String(f.fed_index ?? f.registered_index ?? f.id ?? 0)}</span>
                    <strong>${dreggCodeLink(html, `dregg://federation/${f.fed_index ?? f.registered_index ?? f.id ?? 0}`, f.name || f.federation_id || 'federation')}</strong>
                    <code>${String(f.height ?? 0)} height · ${String(f.num_nodes ?? f.nodes ?? 0)} nodes · ${shortHex(f.latest_root || f.federation_id || '', 14)}</code>
                  </div>`)}
              </div>`}
          <div class="dregg-inspector__actions">
            ${feds.length ? dreggCodeLink(html, `dregg://block-dag/${feds[0].fed_index ?? 0}`, 'open first DAG') : null}
          </div>
          <div class="dregg-inspector__note">
            KnownFederations registry (node + extension) + sim list. Add via <code>registerFederation</code> (Task #28 / §4.3).
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-federation-list')) {
  customElements.define('dregg-federation-list', DreggFederationList);
}

(function injectStyles() {
  if (document.getElementById('dregg-federation-list-styles')) return;
  const s = document.createElement('style');
  s.id = 'dregg-federation-list-styles';
  s.textContent = `.pfl__list li { background: var(--bg-raised); } .pfl__count { font-size:0.8rem; }`;
  document.head.appendChild(s);
})();

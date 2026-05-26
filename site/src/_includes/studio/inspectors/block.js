/**
 * <dregg-block uri="dregg://block/<height>"> or
 * <dregg-block uri="dregg://block/<fed>/<height>"> — block at a given height.
 *
 * IMPORTANT: the wasm sim does NOT expose a block getter. `propose_block`
 * returns the new block_hash + height; `simulate_consensus_round` returns
 * the round summary. Neither lets us *retrieve* a previously-proposed
 * block by height or hash.
 *
 * Workaround: the JS runtime intercepts `proposeBlock(...)` and records
 * `{ height, block_hash, fed_index, events }` in a local log. This inspector
 * reads that log. Blocks proposed *outside* the JS runtime (none today, but
 * eventually a RemoteRuntime) won't show up here.
 *
 * Needed wasm getter: `get_block(handle, fed_idx, height) -> BlockInfo`,
 * with the full event list + block_hash + finalization status.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggBlock extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'compact';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'block')) return;

    const scoped = parsed.sub && parsed.sub.length > 0;
    const fedIndex = scoped ? parsed.id : 0;
    const height = scoped ? parsed.sub[0] : parsed.id;
    const sig = scoped
      ? this._runtime.getBlock({ fedIndex, height })
      : this._runtime.getBlock(height);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const b = sig.value;
      if (!b) return html`<div class="dregg-inspector dregg-inspector--empty">block at height ${height} not in JS log (no wasm getter available)</div>`;
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code>h=${String(b.height)}</code>
            · fed #${String(b.fed_index)}
            · <code title=${b.block_hash}>${shortHex(b.block_hash)}</code>
          </span>`;
      }
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">block</span>
            <code class="dregg-inspector__id">height ${String(b.height)}</code>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>height</dt><dd>${String(b.height)}</dd>
            <dt>federation</dt><dd>#${String(b.fed_index)}</dd>
            <dt>block hash</dt><dd><code>${b.block_hash}</code></dd>
            <dt>events</dt><dd>${b.events?.length
              ? html`<code>${b.events.length} event${b.events.length === 1 ? '' : 's'}</code>`
              : html`<span style="opacity:0.6">(empty)</span>`}</dd>
          </dl>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-block')) customElements.define('dregg-block', DreggBlock);

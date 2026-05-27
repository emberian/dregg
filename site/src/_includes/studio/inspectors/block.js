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
import { InspectorBase, dreggCodeLink, emptyState, renderParseError, shortHex } from './_base.js';

class DreggBlock extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

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
      if (!b) return emptyState(
        html,
        'Block not found',
        html`No block at height <code>${height}</code> is present in the local JS block log for federation <code>#${fedIndex}</code>.`,
        [dreggCodeLink(html, `dregg://federation/${fedIndex}`, 'open federation')],
      );
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code>h=${String(b.height)}</code>
            · fed #${String(b.fed_index)}
            · <code title=${b.block_hash}>${shortHex(b.block_hash)}</code>
          </span>`;
      }
      const events = Array.isArray(b.events) ? b.events : [];
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">block</span>
            <code class="dregg-inspector__id">height ${String(b.height)}</code>
            <span class="dregg-inspector__meta">fed #${String(b.fed_index)} · ${String(events.length)} events</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>Height</span><strong>${String(b.height)}</strong></div>
            <div><span>Federation</span><strong>#${String(b.fed_index)}</strong></div>
            <div><span>Events</span><strong>${String(events.length)}</strong></div>
            <div><span>Hash</span><strong title=${b.block_hash}>${shortHex(b.block_hash, 10)}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            <dt>height</dt><dd>${String(b.height)}</dd>
            <dt>federation</dt><dd>${dreggCodeLink(html, `dregg://federation/${b.fed_index}`, `#${String(b.fed_index)}`)}</dd>
            <dt>block hash</dt><dd><code>${b.block_hash}</code></dd>
            <dt>events</dt><dd>${events.length
              ? html`<div class="dregg-inspector__rows">${events.map((event, idx) => html`
                  <div class="dregg-inspector__row">
                    <span>${String(idx)}</span>
                    <strong>${typeof event === 'string' ? shortHex(event, 18) : (event.kind || event.type || 'event')}</strong>
                    <code>${typeof event === 'string' ? event : JSON.stringify(event).slice(0, 120)}</code>
                  </div>`)}</div>`
              : html`<span style="opacity:0.6">(empty)</span>`}</dd>
          </dl>
          <div class="dregg-inspector__actions">
            ${dreggCodeLink(html, `dregg://federation/${b.fed_index}`, 'open federation')}
            ${dreggCodeLink(html, `dregg://block-dag/${b.fed_index}`, 'open DAG')}
          </div>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-block')) customElements.define('dregg-block', DreggBlock);

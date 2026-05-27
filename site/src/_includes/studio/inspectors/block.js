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

function eventLabel(event) {
  if (typeof event === 'string') return shortHex(event, 18);
  return event?.kind || event?.type || event?.method || 'event';
}

function eventDetail(event) {
  if (typeof event === 'string') return event;
  try { return JSON.stringify(event); } catch { return String(event); }
}

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
      const prevHeight = Number(b.height) > 0 ? Number(b.height) - 1 : null;
      const eventSummary = events.length === 0
        ? 'no events recorded'
        : `${String(events.length)} event${events.length === 1 ? '' : 's'} captured`;
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">block</span>
            <code class="dregg-inspector__id">height ${String(b.height)}</code>
            <span class="dregg-inspector__meta">fed #${String(b.fed_index)} · ${eventSummary}</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>Height</span><strong>${String(b.height)}</strong></div>
            <div><span>Federation</span><strong>#${String(b.fed_index)}</strong></div>
            <div><span>Events</span><strong>${String(events.length)}</strong></div>
            <div><span>Hash</span><strong title=${b.block_hash}>${shortHex(b.block_hash, 10)}</strong></div>
          </div>
          <div class=${`dregg-inspector__notice ${events.length ? 'dregg-inspector__notice--ok' : ''}`}>
            ${events.length
              ? html`This block was captured from the local proposal log with ${String(events.length)} runtime event${events.length === 1 ? '' : 's'}.`
              : html`The local proposal log has this block, but no runtime events were recorded for it.`}
          </div>
          <dl class="dregg-inspector__kv">
            <dt>height</dt><dd>${String(b.height)}</dd>
            <dt>federation</dt><dd>${dreggCodeLink(html, `dregg://federation/${b.fed_index}`, `#${String(b.fed_index)}`)}</dd>
            <dt>block hash</dt><dd><code>${b.block_hash}</code></dd>
          </dl>
          <details class="dregg-inspector__section" open=${events.length > 0}>
            <summary>events (${String(events.length)})</summary>
            <div class="dregg-inspector__section-body">
              ${events.length
                ? html`<div class="dregg-inspector__rows">${events.map((event, idx) => html`
                  <div class="dregg-inspector__row">
                    <span>${String(idx)}</span>
                    <strong>${eventLabel(event)}</strong>
                    <code title=${eventDetail(event)}>${eventDetail(event).slice(0, 160)}</code>
                  </div>`)}</div>`
                : emptyState(html, 'No events in block log', html`This block entry has no attached events. The inspector is showing only runtime data that is present.`)}
            </div>
          </details>
          <div class="dregg-inspector__actions">
            ${dreggCodeLink(html, `dregg://federation/${b.fed_index}`, 'open federation')}
            ${dreggCodeLink(html, `dregg://block-dag/${b.fed_index}`, 'open DAG')}
            ${prevHeight == null ? null : dreggCodeLink(html, `dregg://block/${b.fed_index}/${prevHeight}`, 'previous block')}
          </div>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-block')) customElements.define('dregg-block', DreggBlock);

/**
 * <dregg-federation uri="dregg://federation/<fed_index>"> — federation summary.
 *
 * Reads `get_federation_state(handle, fed_idx)`. Federations are addressed
 * by numeric index in the sim (no stable handle by name yet).
 *
 * Shape: { name, height, num_nodes, num_events, num_finalized_roots,
 *          latest_root, fed_index (added in JS) }
 */

import { parseRef } from '../uri.js';
import { InspectorBase, dreggCodeLink, emptyState, renderParseError, shortHex } from './_base.js';

function countLabel(n, noun) {
  const value = Number(n || 0);
  return `${String(value)} ${noun}${value === 1 ? '' : 's'}`;
}

class DreggFederation extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'federation')) return;

    const fedIdx = parsed.id;
    const sig = this._runtime.getFederation(fedIdx);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const f = sig.value;
      if (!f) return emptyState(
        html,
        'Federation not found',
        html`Federation <code>#${fedIdx}</code> is not registered in this runtime.`,
      );
      const height = Number(f.height || 0);
      const events = Number(f.num_events || 0);
      const roots = Number(f.num_finalized_roots || 0);
      const density = height > 0 ? `${countLabel(events, 'event')} over ${countLabel(height, 'block')}` : 'genesis only';
      const rootLabel = f.latest_root ? shortHex(f.latest_root, 24) : 'not finalized';
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code>${f.name}</code>
            · h=${String(f.height)}
            · ${String(f.num_nodes)} nodes
          </span>`;
      }
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">federation</span>
            <code class="dregg-inspector__id">${f.name} (#${String(f.fed_index)})</code>
            <span class="dregg-inspector__meta">${density}</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>Height</span><strong>${String(f.height)}</strong></div>
            <div><span>Nodes</span><strong>${String(f.num_nodes)}</strong></div>
            <div><span>Events</span><strong>${String(f.num_events)}</strong></div>
            <div><span>Roots</span><strong>${String(f.num_finalized_roots)}</strong></div>
          </div>
          <div class=${`dregg-inspector__notice ${f.latest_root ? 'dregg-inspector__notice--ok' : ''}`}>
            ${height > 0
              ? html`Chain head is height <code>${String(height)}</code>; latest finalized root is <code title=${f.latest_root || ''}>${rootLabel}</code>.`
              : html`This federation is registered, but no proposed blocks are visible in the runtime yet.`}
          </div>
          <dl class="dregg-inspector__kv">
            <dt>name</dt><dd>${f.name}</dd>
            <dt>height</dt><dd>${String(height)}</dd>
            <dt>committee</dt><dd>${countLabel(f.num_nodes, 'node')}</dd>
            <dt>events</dt><dd>${countLabel(events, 'event')}</dd>
            <dt>finalized roots</dt><dd>${countLabel(roots, 'root')}</dd>
            <dt>latest root</dt><dd>${f.latest_root
              ? html`<code title=${f.latest_root}>${shortHex(f.latest_root, 24)}</code>`
              : html`<span class="dregg-inspector__meta">none recorded</span>`}</dd>
          </dl>
          ${height > 0 ? null : emptyState(
            html,
            'No blocks proposed',
            html`Use the federation actions or runtime controls to propose a block; this inspector will update when real block data arrives.`,
            [dreggCodeLink(html, `dregg://block-dag/${f.fed_index ?? fedIdx}`, 'open empty DAG')],
          )}
          <div class="dregg-inspector__actions">
            ${dreggCodeLink(html, `dregg://block-dag/${f.fed_index ?? fedIdx}`, 'open block DAG')}
            ${Number(f.height || 0) > 0 ? dreggCodeLink(html, `dregg://block/${f.fed_index ?? fedIdx}/${f.height}`, 'latest block') : null}
          </div>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-federation')) customElements.define('dregg-federation', DreggFederation);

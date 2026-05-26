/**
 * <dregg-receipt uri="dregg://receipt/<hex32>"> — single TurnReceipt.
 *
 * The wasm sim exposes only `get_receipt_chain(handle)` returning the entire
 * chain; the JS runtime caches it and we look up by turn_hash.
 *
 * Receipt shape (from wasm/src/bindings.rs::get_receipt_chain):
 *   { turn_hash, pre_state_hash, post_state_hash, timestamp,
 *     computrons_used, action_count }
 */

import { parseRef } from '../uri.js';
import { InspectorBase, dreggCodeLink, emptyState, renderParseError, shortHex } from './_base.js';

class DreggReceipt extends InspectorBase {
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

    const Component = () => {
      const r = sig.value;
      if (!r) return emptyState(
        html,
        'Receipt not found',
        html`No committed receipt with hash <code>${shortHex(parsed.id, 16)}</code> is present in this runtime.`,
        [dreggCodeLink(html, `dregg://turn/${parsed.id}`, 'check matching turn')],
      );
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code title=${parsed.id}>${shortHex(parsed.id)}</code>
            · ${String(r.action_count)} actions
            · ${String(r.computrons_used)} comp
          </span>`;
      }
      // Per-action authorization list (Refactor 3: actions: Vec<ActionView>)
      const actions = Array.isArray(r.actions) ? r.actions : [];
      const actionList = actions.length
        ? html`
          <dt>actions</dt>
          <dd>
            <ul class="dregg-inspector__action-list">
              ${actions.map((a, i) => {
                const authJson = a.authorization ? JSON.stringify(a.authorization) : null;
                const targetUri = a.target_cell ? `dregg://cell/${a.target_cell}` : null;
                return html`
                  <li class="dregg-inspector__action-row">
                    <span class="dregg-inspector__action-index">${String(i)}.</span>
                    ${targetUri
                      ? dreggCodeLink(html, targetUri, shortHex(a.target_cell, 10), a.target_cell)
                      : html`<code title=${a.target_cell || ''}>${shortHex(a.target_cell, 10)}</code>`}
                    <span class="dregg-inspector__action-method">${shortHex(a.method, 8)}</span>
                    ${authJson
                      ? html`<dregg-authorization data=${authJson} mode="compact"></dregg-authorization>`
                      : null}
                  </li>`;
              })}
            </ul>
          </dd>`
        : html`<dt>actions</dt><dd>${String(r.action_count)}</dd>`;

      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">receipt</span>
            <code class="dregg-inspector__id" title=${parsed.id}>${shortHex(parsed.id, 24)}</code>
            <span class="dregg-inspector__meta">${String(r.action_count)} actions · ${String(r.computrons_used)} computrons</span>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>turn hash</dt><dd>${dreggCodeLink(html, `dregg://turn/${r.turn_hash}`, shortHex(r.turn_hash, 24), r.turn_hash)}</dd>
            <dt>pre state</dt><dd><code>${r.pre_state_hash}</code></dd>
            <dt>post state</dt><dd><code>${r.post_state_hash}</code></dd>
            <dt>timestamp</dt><dd>${String(r.timestamp)}</dd>
            <dt>computrons</dt><dd>${String(r.computrons_used)}</dd>
            ${actionList}
          </dl>
          <details style="margin-top:var(--s3,8px);">
            <summary style="cursor:pointer;color:var(--fg-dim);font-size:0.82rem;user-select:none;">Proof</summary>
            <dregg-proof uri=${`dregg://receipt/${r.turn_hash}`} mode="default"></dregg-proof>
          </details>
          <details style="margin-top:var(--s3,8px);">
            <summary style="cursor:pointer;color:var(--fg-dim);font-size:0.82rem;user-select:none;">Witnessed (Wave 3 cross-embed)</summary>
            <dregg-witnessed-receipt uri=${`dregg://receipt/${r.turn_hash}`} mode="compact"></dregg-witnessed-receipt>
          </details>
        </div>`;
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-receipt')) customElements.define('dregg-receipt', DreggReceipt);

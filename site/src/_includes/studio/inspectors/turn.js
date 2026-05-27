/**
 * <dregg-turn uri="dregg://turn/<hex32>"> — single turn.
 *
 * In the sim runtime a "turn" is identified by its turn_hash; its observable
 * state is the matching TurnReceipt (pre/post state, computrons, actions).
 * Backed by the same `get_receipt_chain` lookup as <dregg-receipt>, but
 * presented as a turn (with an embedded receipt for the effects view).
 */

import { parseRef } from '../uri.js';
import { InspectorBase, dreggCodeLink, emptyState, renderParseError, shortHex } from './_base.js';

class DreggTurn extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'turn')) return;

    const sig = this._runtime.getTurn(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const t = sig.value;
      if (!t) return emptyState(
        html,
        'Turn not found',
        html`No receipt-backed turn is present for <code>${shortHex(parsed.id, 16)}</code> in this runtime.`,
        [dreggCodeLink(html, `dregg://receipt/${parsed.id}`, 'check matching receipt')],
      );
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code title=${parsed.id}>${shortHex(parsed.id)}</code>
            · ${String(t.action_count)} effects
          </span>`;
      }
      // Render per-action authorization badges if actions are available.
      const actions = Array.isArray(t.actions) ? t.actions : [];
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
        : html`<dt>actions</dt><dd>${String(t.action_count)}</dd>`;

      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">turn</span>
            <code class="dregg-inspector__id" title=${parsed.id}>${shortHex(parsed.id, 24)}</code>
            <span class="dregg-inspector__meta">${String(t.action_count)} effects · ${String(t.computrons_used)} computrons</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>Effects</span><strong>${String(t.action_count)}</strong></div>
            <div><span>Computrons</span><strong>${String(t.computrons_used)}</strong></div>
            <div><span>Proof</span><strong>${t.proof_view ? 'attached' : 'placeholder'}</strong></div>
            <div><span>Trace</span><strong>${this._runtime.getTurnTrace ? 'available' : 'unavailable'}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            <dt>turn hash</dt><dd>${dreggCodeLink(html, `dregg://turn/${t.turn_hash}`, shortHex(t.turn_hash, 24), t.turn_hash)}</dd>
            <dt>effects</dt><dd>${String(t.action_count)}</dd>
            <dt>computrons</dt><dd>${String(t.computrons_used)}</dd>
            <dt>timestamp</dt><dd>${String(t.timestamp)}</dd>
            <dt>state transition</dt>
            <dd>
              <code title=${t.pre_state_hash}>${shortHex(t.pre_state_hash, 12)}</code>
              → <code title=${t.post_state_hash}>${shortHex(t.post_state_hash, 12)}</code>
            </dd>
            ${actionList}
            <dt>receipt</dt>
            <dd>
              ${dreggCodeLink(html, `dregg://receipt/${t.turn_hash}`, 'open receipt')}
              <dregg-receipt uri=${`dregg://receipt/${t.turn_hash}`} mode="compact"></dregg-receipt>
            </dd>
          </dl>
          <details class="dregg-inspector__section">
            <summary>Trace</summary>
            <div class="dregg-inspector__section-body">
              <dregg-turn-debugger uri=${`dregg://turn/${t.turn_hash}`} mode="default"></dregg-turn-debugger>
            </div>
          </details>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-turn')) customElements.define('dregg-turn', DreggTurn);

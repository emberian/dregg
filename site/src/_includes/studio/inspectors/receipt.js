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

function proofTier(proofView) {
  if (!proofView) return 'scope-0';
  const bp = proofView.bilateral_pi;
  return bp &&
    bp.outgoing_transfer_root &&
    bp.incoming_transfer_root &&
    bp.outgoing_grant_root &&
    bp.incoming_grant_root &&
    bp.outgoing_introduce_root &&
    bp.incoming_introduce_root
    ? 'Golden'
    : 'Silver';
}

function timestampLabel(ts) {
  if (ts == null || ts === '') return 'unavailable';
  if (typeof ts === 'number') {
    const ms = ts > 10_000_000_000 ? ts : ts * 1000;
    const d = new Date(ms);
    return Number.isNaN(d.getTime()) ? String(ts) : d.toLocaleString();
  }
  const d = new Date(ts);
  return Number.isNaN(d.getTime()) ? String(ts) : d.toLocaleString();
}

function actionLabel(action) {
  return action?.method || action?.kind || action?.type || 'action';
}

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
            · ${proofTier(r.proof_view || null)}
          </span>`;
      }
      // Per-action authorization list (Refactor 3: actions: Vec<ActionView>)
      const actions = Array.isArray(r.actions) ? r.actions : [];
      const declaredActionCount = Number(r.action_count ?? actions.length ?? 0);
      const computrons = Number(r.computrons_used ?? 0);
      const avgComputrons = declaredActionCount > 0 ? Math.round(computrons / declaredActionCount) : 0;
      const tier = proofTier(r.proof_view || null);
      const receiptHash = r.turn_hash || parsed.id;
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
                    <span class="dregg-inspector__action-method" title=${actionLabel(a)}>${shortHex(actionLabel(a), 18)}</span>
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
            <code class="dregg-inspector__id" title=${receiptHash}>${shortHex(receiptHash, 24)}</code>
            <span class="dregg-inspector__meta">${String(declaredActionCount)} actions · ${String(computrons)} computrons · ${tier}</span>
          </header>
          <div class="dregg-receipt__summary">
            <div><span>Actions</span><strong>${String(declaredActionCount)}</strong></div>
            <div><span>Computrons</span><strong>${String(computrons)}</strong></div>
            <div><span>Avg / action</span><strong>${declaredActionCount > 0 ? String(avgComputrons) : 'n/a'}</strong></div>
            <div><span>Proof</span><strong>${tier}</strong></div>
          </div>
          <div class="dregg-inspector__actions">
            ${dreggCodeLink(html, `dregg://turn/${receiptHash}`, 'open turn', receiptHash)}
            ${dreggCodeLink(html, `dregg://receipt/${receiptHash}`, 'open proof', receiptHash)}
          </div>
          <dl class="dregg-inspector__kv">
            <dt>turn hash</dt><dd>${dreggCodeLink(html, `dregg://turn/${receiptHash}`, shortHex(receiptHash, 24), receiptHash)}</dd>
            <dt>pre state</dt><dd><code>${r.pre_state_hash}</code></dd>
            <dt>post state</dt><dd><code>${r.post_state_hash}</code></dd>
            <dt>timestamp</dt><dd title=${String(r.timestamp || '')}>${timestampLabel(r.timestamp)}</dd>
            <dt>computrons</dt><dd>${String(computrons)}</dd>
            ${actionList}
          </dl>
          <details class="dregg-inspector__section">
            <summary>Proof detail</summary>
            <div class="dregg-inspector__section-body">
              <dregg-proof uri=${`dregg://receipt/${receiptHash}`} mode="default"></dregg-proof>
            </div>
          </details>
          <details class="dregg-inspector__section">
            <summary>Witnessed receipt scope</summary>
            <div class="dregg-inspector__section-body">
              <dregg-witnessed-receipt uri=${`dregg://receipt/${receiptHash}`} mode="compact"></dregg-witnessed-receipt>
            </div>
          </details>
        </div>`;
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-receipt')) customElements.define('dregg-receipt', DreggReceipt);

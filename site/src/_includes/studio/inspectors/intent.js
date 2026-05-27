/**
 * <dregg-intent uri="dregg://intent/<id_or_index>"> — single intent.
 *
 * The wasm sim does NOT expose a getter to recover an intent's full spec by
 * id or index after creation. As a workaround, the JS runtime keeps a
 * `intentLedger` of every intent created through `runtime.createIntent(...)`
 * including its input spec; this inspector reads that.
 *
 * URI: the id segment may be either the hex intent_id (preferred) or a
 * numeric intent_index.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, emptyState, renderParseError, shortHex } from './_base.js';

function expiryState(expiry) {
  const n = Number(expiry || 0);
  if (!n) return { label: 'open', detail: 'no expiry', tone: '' };
  const ms = n > 10_000_000_000 ? n : n * 1000;
  const delta = ms - Date.now();
  if (delta < 0) return { label: 'expired', detail: new Date(ms).toLocaleString(), tone: 'warn' };
  const mins = Math.max(0, Math.round(delta / 60000));
  return { label: mins < 90 ? `${mins}m` : new Date(ms).toLocaleDateString(), detail: new Date(ms).toLocaleString(), tone: 'ok' };
}

class DreggIntent extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'intent')) return;

    const sig = this._runtime.getIntent(parsed.id);
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const i = sig.value;
      if (!i) return emptyState(
        html,
        'Intent not found',
        html`No intent with id/index <code>${shortHex(parsed.id, 16)}</code> is present in this runtime's intent ledger.`,
      );
      const actions = Array.isArray(i.actions) ? i.actions : [];
      const constraints = Array.isArray(i.constraints) ? i.constraints : [];
      const expiry = expiryState(i.expiry);
      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code title=${i.intent_id}>${shortHex(i.intent_id)}</code>
            · ${i.kind}
            · ${actions.length} action${actions.length === 1 ? '' : 's'}
          </span>`;
      }
      const actionsRender = actions.length
        ? html`<div class="dregg-inspector__rows">${actions.map((a, idx) => html`
            <div class="dregg-inspector__row">
              <span>${String(idx)}</span>
              <strong>${a.action || a.kind || 'action'}</strong>
              <code>${a.resource || a.target || i.resource_pattern || '*'}</code>
            </div>`)}</div>`
        : html`<span style="opacity:0.6">(none)</span>`;
      const constraintsRender = constraints.length
        ? html`<div class="dregg-inspector__rows">${constraints.map((c) => {
            const kind = c.Service || c.service || c.kind || Object.keys(c)[0] || 'constraint';
            return html`<div class="dregg-inspector__row">
              <span>${kind}</span>
              <strong>${c.value || c.name || c.Service || c.kind || 'required'}</strong>
              <code>${JSON.stringify(c).slice(0, 96)}</code>
            </div>`;
          })}</div>`
        : html`<span style="opacity:0.6">(none)</span>`;
      return html`
        <div class="dregg-inspector dregg-inspector--cell">
          <header>
            <span class="dregg-inspector__kind">intent</span>
            <code class="dregg-inspector__id" title=${i.intent_id}>${shortHex(i.intent_id, 24)}</code>
            <span class="dregg-inspector__meta">${i.kind} · ${expiry.detail}</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>Actions</span><strong>${String(actions.length)}</strong></div>
            <div><span>Constraints</span><strong>${String(constraints.length)}</strong></div>
            <div><span>Creator</span><strong>#${String(i.agent_index ?? 'n/a')}</strong></div>
            <div><span>Expiry</span><strong>${expiry.label}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            <dt>kind</dt><dd>${i.kind}</dd>
            <dt>intent id</dt><dd><code>${i.intent_id}</code></dd>
            <dt>index</dt><dd>${String(i.intent_index)}</dd>
            <dt>creator agent</dt><dd>#${String(i.agent_index)}</dd>
            <dt>actions</dt><dd>${actionsRender}</dd>
            <dt>constraints</dt><dd>${constraintsRender}</dd>
            <dt>resource pattern</dt><dd>${i.resource_pattern || html`<span style="opacity:0.6">(any)</span>`}</dd>
            <dt>expiry</dt><dd>${i.expiry ? String(i.expiry) : html`<span style="opacity:0.6">(none)</span>`}</dd>
          </dl>
        </div>`;
    };
    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}
if (!customElements.get('dregg-intent')) customElements.define('dregg-intent', DreggIntent);

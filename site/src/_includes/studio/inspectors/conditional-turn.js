/**
 * <dregg-conditional-turn uri="dregg://conditional-turn/<id>">
 *
 * Pending conditional turns + ProofCondition view.
 * Uses runtime.listPendingConditionals(). Lab submit affordance only appears
 * with mode="lab" and mutate runtime.
 *
 * Compact: id + kind + timeout
 * Default: full + condition details.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class DreggConditionalTurn extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;
    const handle = this._runtime?._handle;
    const caps = this._runtime?.caps || { mutate: false };

    let parsed = null;
    let inline = null;
    if (dataAttr) {
      try { inline = JSON.parse(dataAttr); } catch {}
    }
    if (!inline && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'conditional-turn')) return;
    }

    const listSignal = this._runtime?.listPendingConditionals ? this._runtime.listPendingConditionals() : null;

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      let cond = inline;
      if (!cond && parsed) {
        const list = (listSignal && listSignal.value) || [];
        cond = list.find(c => c.id === parsed.id) || null;
      }
      if (!cond && mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">conditional-turn</span>`;
      }
      if (!cond) {
        return html`
          <div class="dregg-inspector dregg-inspector--condturn">
            <header><span class="dregg-inspector__kind">conditional-turn</span></header>
            <div style="font-size:0.8rem;color:var(--fg-dim);">
              ${parsed
                ? html`conditional turn not found in this runtime: <code>${shortHex(parsed.id, 16)}</code>`
                : html`no pending conditional data; provide <code>uri=</code> or <code>data=</code>.`}
            </div>
            ${mode === 'lab' && caps.mutate && wasm ? html`<button data-act="submit-demo" style="margin-top:6px;font-size:0.75rem;">Submit HashPreimage via wasm</button>` : null}
          </div>`;
      }

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code>${shortHex(cond.id)}</code> · ${cond.condition_kind} · timeout@${cond.timeout_height}
          </span>`;
      }

      return html`
        <div class="dregg-inspector dregg-inspector--condturn">
          <header>
            <span class="dregg-inspector__kind">conditional-turn</span>
            <code class="dregg-inspector__id" title=${cond.id}>${shortHex(cond.id, 20)}</code>
          </header>
          <dl class="dregg-inspector__kv">
            <dt>id</dt><dd><code>${cond.id}</code></dd>
            <dt>condition</dt><dd>${cond.condition_kind}</dd>
            <dt>submitted at</dt><dd>height ${String(cond.submitted_height)}</dd>
            <dt>timeout</dt><dd>height ${String(cond.timeout_height)}</dd>
          </dl>
          <div style="font-size:0.75rem;color:var(--fg-dim);">
            ProofCondition variants: HashPreimage, TurnExecuted, RemoteProof, And/Or/Not compositions.
            Use advance_height to simulate timeouts. Real execution on condition proof is via turn executor.
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm || !handle || mode !== 'lab') return;
      if (btn.dataset.act === 'submit-demo') {
        try {
          const condJson = JSON.stringify({ kind: 'HashPreimage', hash: '00'.repeat(32) });
          const actionsJson = JSON.stringify([]);
          const res = wasm.submit_conditional(handle, 0, actionsJson, 0, condJson, 10);
          console.log('[dregg-conditional-turn] submitted demo', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn('[dregg-conditional-turn] submit failed (demo may need effects)', err); }
      }
    });
  }
}
if (!customElements.get('dregg-conditional-turn')) customElements.define('dregg-conditional-turn', DreggConditionalTurn);

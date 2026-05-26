/**
 * <pyana-conditional-turn uri="pyana://conditional-turn/<id>">
 *
 * Pending conditional turns + ProofCondition view.
 * Uses get_pending_conditionals (real vec) + submit_conditional.
 *
 * Compact: id + kind + timeout
 * Default: full + condition details + timeout simulation note.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaConditionalTurn extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;
    const handle = this._runtime?._handle;
    const caps = this._runtime?.caps || { mutate: true };

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
        cond = list.find(c => c.id === parsed.id) || { id: parsed.id, timeout_height: 0, submitted_height: 0, condition_kind: 'Unknown' };
      }
      if (!cond && mode === 'compact') {
        return html`<span class="pyana-inspector pyana-inspector--compact">conditional-turn</span>`;
      }
      if (!cond) {
        return html`
          <div class="pyana-inspector pyana-inspector--condturn">
            <header><span class="pyana-inspector__kind">conditional-turn</span></header>
            <div style="font-size:0.8rem;color:var(--fg-dim);">No pending conditionals (or list stub). Submit via demo or data=.</div>
            ${caps.mutate && wasm ? html`<button data-act="submit-demo" style="margin-top:6px;font-size:0.75rem;">Submit demo conditional (HashPreimage)</button>` : null}
          </div>`;
      }

      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <code>${shortHex(cond.id)}</code> · ${cond.condition_kind} · timeout@${cond.timeout_height}
          </span>`;
      }

      return html`
        <div class="pyana-inspector pyana-inspector--condturn">
          <header>
            <span class="pyana-inspector__kind">conditional-turn</span>
            <code class="pyana-inspector__id" title=${cond.id}>${shortHex(cond.id, 20)}</code>
          </header>
          <dl class="pyana-inspector__kv">
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
      if (!btn || !wasm || !handle) return;
      if (btn.dataset.act === 'submit-demo') {
        try {
          // Minimal demo submit: empty effects, simple condition, short timeout
          const condJson = JSON.stringify({ kind: 'HashPreimage', hash: '00'.repeat(32) });
          const actionsJson = JSON.stringify([]);
          const res = wasm.submit_conditional(handle, 0, actionsJson, 0, condJson, 10);
          console.log('[pyana-conditional-turn] submitted demo', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn('[pyana-conditional-turn] submit failed (demo may need effects)', err); }
      }
    });
  }
}
if (!customElements.get('pyana-conditional-turn')) customElements.define('pyana-conditional-turn', PyanaConditionalTurn);

/**
 * <pyana-turn-debugger uri="pyana://turn/<hex32>"> — step-by-step Effect VM
 * trace inspector for a committed turn.
 *
 * Data source: wasm `get_turn_trace(handle, turn_hash_hex)` returns:
 *   { turn_hash: string, computrons_total: number, trace_gap_note: string,
 *     steps: Array<{
 *       action_path: number[],  // call-forest path, e.g. [0, 2, 1]
 *       target_cell: string,    // hex64
 *       method: string,         // hex64 (BLAKE3 of method name)
 *       effects: string[],      // Debug-printed effect strings (v0)
 *       result: string,         // "committed" in sim
 *       computrons_used: number // receipt total (allocated uniformly for now)
 *     }>
 *   }
 *
 * Called via the runtime escape hatch so we do NOT modify runtime-in-memory.js:
 *   runtime._wasm.get_turn_trace(runtime._handle, turnHash)
 *
 * Modes:
 *   default   — full table with row selection + expansion panel + breadcrumb
 *   compact   — single-line: "N steps, K computrons"
 *
 * The selected-row expansion panel shows the full effects[] strings (raw Debug
 * output). This is intentional — the sim does not yet produce structured effect
 * records; a future refactor will add rich effect views when WitnessedReceipt
 * scope-2 bundles are wired through.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

// ── helpers ──────────────────────────────────────────────────────────────────

/** Format action_path array as dotted string, e.g. [0,2,1] → "0.2.1". */
function fmtPath(path) {
  if (!Array.isArray(path) || path.length === 0) return '—';
  return path.join('.');
}

/** Depth from path length (root = 0). */
function pathDepth(path) {
  return Array.isArray(path) ? Math.max(0, path.length - 1) : 0;
}

/** Inline styles to avoid polluting global CSS for a single component. */
const CSS = `
  .ptd { font-family: var(--font-mono, ui-monospace, monospace); font-size: 0.82rem; }
  .ptd__header { display: flex; align-items: center; justify-content: space-between;
    padding: var(--s2, 4px) var(--s3, 8px);
    border-bottom: 1px solid var(--line, #333);
    background: var(--bg-raised, #1a1a1a); }
  .ptd__kind { color: var(--fg-dim, #888); font-size: 0.7rem; text-transform: uppercase;
    letter-spacing: 0.07em; }
  .ptd__id { color: var(--fg, #eee); }
  .ptd__breadcrumb { color: var(--fg-dim, #888); font-size: 0.75rem; }
  .ptd__note { color: var(--fg-dim, #888); font-size: 0.72rem; padding: 2px var(--s3, 8px);
    border-bottom: 1px solid var(--line, #333); font-style: italic; }
  .ptd__table-wrap { overflow-x: auto; }
  .ptd__table { width: 100%; border-collapse: collapse; }
  .ptd__table th { padding: 4px 8px; text-align: left; font-size: 0.72rem;
    text-transform: uppercase; letter-spacing: 0.06em;
    color: var(--fg-dim, #888); border-bottom: 1px solid var(--line, #333);
    white-space: nowrap; background: var(--bg-raised, #1a1a1a); }
  .ptd__table td { padding: 4px 8px; border-bottom: 1px solid var(--line-faint, #222);
    white-space: nowrap; color: var(--fg, #eee); }
  .ptd__table tr.ptd__row:hover { background: var(--bg-hover, rgba(255,255,255,0.04)); cursor: pointer; }
  .ptd__table tr.ptd__row--selected { background: var(--accent-soft, rgba(100,200,255,0.08)); }
  .ptd__step-num { color: var(--fg-dim, #888); width: 2.5em; text-align: right; }
  .ptd__path { color: var(--fg-dim, #aaa); font-size: 0.78rem; }
  .ptd__path-indent { display: inline-block; }
  .ptd__target { color: var(--accent, #64c8ff); }
  .ptd__method { color: var(--fg, #eee); font-size: 0.78rem; }
  .ptd__effects-badge { display: inline-block; padding: 1px 6px; border-radius: 3px;
    background: var(--bg-raised, #2a2a2a); color: var(--fg-dim, #aaa);
    font-size: 0.75rem; }
  .ptd__result-ok { color: var(--success, #4db85a); }
  .ptd__computrons { color: var(--fg-dim, #888); }
  .ptd__expansion { padding: var(--s3, 8px) var(--s4, 16px);
    background: var(--bg-raised, #1a1a1a);
    border-bottom: 1px solid var(--line, #333); }
  .ptd__expansion-title { font-size: 0.72rem; text-transform: uppercase;
    letter-spacing: 0.07em; color: var(--fg-dim, #888); margin-bottom: 4px; }
  .ptd__effect-str { display: block; padding: 2px 0; font-size: 0.78rem;
    color: var(--fg, #eee); word-break: break-all; }
  .ptd__effect-str--empty { color: var(--fg-dim, #888); font-style: italic; }
  .ptd__empty { padding: var(--s4, 16px); color: var(--fg-dim, #888);
    font-style: italic; }
  .ptd__compact { font-size: 0.82rem; color: var(--fg-dim, #aaa); }
  .ptd__compact code { color: var(--accent, #64c8ff); }
`;

// ── component ─────────────────────────────────────────────────────────────────

class PyanaTurnDebugger extends InspectorBase {
  constructor() {
    super();
    this._selectedStep = null;
    this._traceCache = new Map(); // turnHash → signal
  }

  /** Fetch turn trace via wasm escape hatch, return a signal. */
  _getTurnTrace(turnHash) {
    if (this._traceCache.has(turnHash)) return this._traceCache.get(turnHash);
    const { signal } = this._api;

    // Initial fetch; we don't have a live subscription (the trace is immutable
    // once a turn is committed) so a one-shot signal is correct.
    const sig = signal(null);
    try {
      const raw = this._runtime._wasm.get_turn_trace(this._runtime._handle, turnHash);
      sig.value = raw && raw !== null ? raw : { steps: [], computrons_total: 0, trace_gap_note: '' };
    } catch (e) {
      sig.value = { steps: [], computrons_total: 0, trace_gap_note: String(e?.message || e), _error: true };
    }

    this._traceCache.set(turnHash, sig);
    return sig;
  }

  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();
    this._selectedStep = null;

    let parsed = null;
    try { parsed = parseRef(refAttr); } catch {}
    if (renderParseError(this, refAttr, parsed, 'turn')) return;

    // Inject component styles once per document.
    if (!document.getElementById('pyana-turn-debugger-style')) {
      const styleEl = document.createElement('style');
      styleEl.id = 'pyana-turn-debugger-style';
      styleEl.textContent = CSS;
      document.head.appendChild(styleEl);
    }

    const traceSig = this._getTurnTrace(parsed.id);
    const selectedSig = this._api.signal(null); // selected step index
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const trace = traceSig.value;
      const selected = selectedSig.value;

      if (!trace) {
        return html`<div class="pyana-inspector pyana-inspector--empty ptd ptd__empty">loading trace…</div>`;
      }

      if (mode === 'compact') {
        const n = trace.steps ? trace.steps.length : 0;
        return html`
          <span class="pyana-inspector pyana-inspector--compact ptd ptd__compact">
            <code title=${parsed.id}>${shortHex(parsed.id)}</code>
            · ${String(n)} step${n === 1 ? '' : 's'}
            · ${String(trace.computrons_total)} computrons
          </span>`;
      }

      const steps = trace.steps || [];
      if (!steps.length) {
        return html`
          <div class="pyana-inspector pyana-inspector--cell ptd">
            <header class="ptd__header">
              <span class="ptd__kind">turn debugger</span>
              <code class="ptd__id" title=${parsed.id}>${shortHex(parsed.id, 24)}</code>
            </header>
            <div class="ptd__empty">no trace steps found (turn not in receipt chain)</div>
          </div>`;
      }

      const stepCount = steps.length;
      const breadcrumb = selected != null
        ? `step ${selected + 1} of ${stepCount}`
        : `${stepCount} step${stepCount === 1 ? '' : 's'} · ${trace.computrons_total} computrons`;

      return html`
        <div class="pyana-inspector pyana-inspector--cell ptd">
          <header class="ptd__header">
            <span>
              <span class="ptd__kind">turn debugger</span>
              <code class="ptd__id" title=${parsed.id}> ${shortHex(parsed.id, 20)}</code>
            </span>
            <span class="ptd__breadcrumb">${breadcrumb}</span>
          </header>
          ${trace.trace_gap_note ? html`<div class="ptd__note">${trace.trace_gap_note}</div>` : null}
          <div class="ptd__table-wrap">
            <table class="ptd__table">
              <thead>
                <tr>
                  <th>#</th>
                  <th>path</th>
                  <th>target cell</th>
                  <th>method</th>
                  <th>effects</th>
                  <th>result</th>
                  <th>computrons</th>
                </tr>
              </thead>
              <tbody>
                ${steps.map((step, idx) => {
                  const isSelected = selected === idx;
                  const depth = pathDepth(step.action_path);
                  const indent = ' '.repeat(depth * 2); // nbsp indent for nesting
                  const effectCount = Array.isArray(step.effects) ? step.effects.length : 0;
                  return html`
                    <tr
                      class=${'ptd__row' + (isSelected ? ' ptd__row--selected' : '')}
                      onClick=${() => { selectedSig.value = isSelected ? null : idx; }}
                    >
                      <td class="ptd__step-num">${String(idx)}</td>
                      <td class="ptd__path"><span class="ptd__path-indent">${indent}</span>${fmtPath(step.action_path)}</td>
                      <td class="ptd__target"><code title=${step.target_cell}>${shortHex(step.target_cell, 12)}</code></td>
                      <td class="ptd__method"><code title=${step.method}>${shortHex(step.method, 10)}</code></td>
                      <td><span class="ptd__effects-badge">${String(effectCount)} effect${effectCount === 1 ? '' : 's'}</span></td>
                      <td class="ptd__result-ok">${step.result || '—'}</td>
                      <td class="ptd__computrons">${String(step.computrons_used)}</td>
                    </tr>
                    ${isSelected ? html`
                      <tr>
                        <td colspan="7" style="padding:0">
                          <div class="ptd__expansion">
                            <div class="ptd__expansion-title">
                              step ${idx} — effects (${String(effectCount)})
                              · target: <code title=${step.target_cell}>${step.target_cell}</code>
                              · method: <code title=${step.method}>${step.method}</code>
                            </div>
                            ${effectCount === 0
                              ? html`<span class="ptd__effect-str ptd__effect-str--empty">no effects</span>`
                              : step.effects.map((e, ei) => html`<code key=${String(ei)} class="ptd__effect-str">${e}</code>`)
                            }
                          </div>
                        </td>
                      </tr>` : null}
                  `;
                })}
              </tbody>
            </table>
          </div>
        </div>`;
    };

    this._dispose = effect(() => { render(h(Component, {}), root); });
  }
}

if (!customElements.get('pyana-turn-debugger')) {
  customElements.define('pyana-turn-debugger', PyanaTurnDebugger);
}

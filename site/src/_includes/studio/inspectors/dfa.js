/**
 * <pyana-dfa uri="pyana://dfa/<service>" | data-dfa="...">
 *
 * Inspector for pyana_dfa::Dfa / RouteTable / GovernedRouter.
 * SVG node-and-edge visualization of the compiled DFA (states + transitions).
 * Reuses platform vocabulary for filters and routes.
 *
 * Per STARBRIDGE-PLAN §4.5 + Refactor 10 in pickup: port of playground/sections/datalog
 * but for DFA routing (used by RelayOperator, PubSubTopic filters, CapTP pre-filters).
 *
 * Aligns with DFA-RATIONALIZATION-DESIGN.md and storage cell-programs (RelayOperator
 * uses DFA caveats for dispatch per Phase 5).
 *
 * Supports compact + default. Editor mode for compile test (uses runtime escape if
 * evaluate/compile binding present; else client-side note).
 */

import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaDfa extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const mode = this.getAttribute('mode') || 'default';
    const dataAttr = this.getAttribute('data-dfa');

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    let parsed = null;
    let dfaData = null;
    if (dataAttr) {
      try { dfaData = JSON.parse(dataAttr); } catch (e) {
        this.innerHTML = `<div class="pyana-inspector pyana-inspector--err">bad data-dfa: ${e.message}</div>`;
        return;
      }
    } else if (refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'dfa')) return;
      dfaData = null;
    }

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      if (!dfaData) {
        return html`
          <div class="pyana-inspector pyana-inspector--dfa pdfa">
            <div class="pdfa__header"><span class="pyana-inspector__kind">dfa</span> ${parsed ? shortHex(parsed.id, 12) : ''}</div>
            <div style="color:var(--fg-dim);font-size:0.8rem;">awaiting DFA data (data-dfa JSON or wasm get_dfa / compile_to_air binding). See dfa crate + DFA-RATIONALIZATION-DESIGN.md.</div>
          </div>`;
      }

      const states = dfaData.states || dfaData.nodes || [];
      const trans = dfaData.transitions || dfaData.edges || [];

      if (mode === 'compact') {
        return html`<span class="pyana-inspector pyana-inspector--compact">DFA ${states.length} states · ${trans.length} trans</span>`;
      }

      // Simple SVG visualization (reuses playground spirit but canonical)
      const svgNodes = states.map((s, i) => {
        const x = 40 + (i % 6) * 70;
        const y = 30 + Math.floor(i / 6) * 55;
        return h('g', {},
          h('circle', { cx: x, cy: y, r: 14, fill: s.dead ? '#f87171' : '#4ade80', stroke: 'var(--line)' }),
          h('text', { x, y: y+4, 'text-anchor': 'middle', 'font-size': '9px', fill: '#0a0f0d' }, String(s.id || i))
        );
      });

      return html`
        <div class="pyana-inspector pyana-inspector--cell pdfa">
          <header><span class="pyana-inspector__kind">dfa</span> ${dfaData.name || shortHex(dfaData.hash || '', 8)}</header>
          <svg width="460" height="140" style="border:1px solid var(--line);background:var(--bg);border-radius:4px;">
            ${svgNodes}
            ${trans.slice(0, 20).map((t, idx) => {
              // crude edges
              const from = (t.from || 0) % 6;
              const to = (t.to || 1) % 6;
              return h('line', {
                x1: 40 + from*70, y1: 30 + Math.floor((t.from||0)/6)*55,
                x2: 40 + to*70, y2: 30 + Math.floor((t.to||0)/6)*55,
                stroke: 'var(--accent)', 'stroke-width': 1, opacity: 0.6
              });
            })}
          </svg>
          <div style="font-size:0.75rem;margin-top:4px;color:var(--fg-dim);">
            ${states.length} states · ${trans.length} transitions. Use for RelayOperator dispatch, topic filters (PubSub), CapTP routing.
          </div>
          ${dfaData.air_fingerprint ? html`<div style="font-size:0.7rem;">AIR fp: ${shortHex(dfaData.air_fingerprint, 8)}</div>` : ''}
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('pyana-dfa')) {
  customElements.define('pyana-dfa', PyanaDfa);
}

/**
 * <dregg-dfa uri="dregg://dfa/<service>" | data-dfa="...">
 *
 * Inspector for dregg_dfa::Dfa / RouteTable / GovernedRouter.
 * SVG node-and-edge visualization of the compiled DFA (states + transitions).
 * Reuses platform vocabulary for filters and routes.
 *
 * Per STARBRIDGE-PLAN §4.5 + Refactor 10 in pickup: port of playground/sections/datalog
 * but for DFA routing (used by RelayOperator, PubSubTopic filters, CapTP pre-filters).
 *
 * Aligns with DFA-RATIONALIZATION-DESIGN.md and storage cell-programs (RelayOperator
 * uses DFA caveats for dispatch per Phase 5).
 *
 * Supports compact + default. It renders only caller-provided DFA data or future
 * runtime/wasm DFA bindings; it does not fabricate sample automata.
 */

import { InspectorBase, renderParseError, shortHex } from './_base.js';
import { parseRef } from '../uri.js';

class DreggDfa extends InspectorBase {
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
        this.innerHTML = `<div class="dregg-inspector dregg-inspector--err">bad data-dfa: ${e.message}</div>`;
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
          <div class="dregg-inspector dregg-inspector--dfa pdfa">
            <div class="pdfa__header"><span class="dregg-inspector__kind">dfa</span> ${parsed ? shortHex(parsed.id, 12) : ''}</div>
            <div style="color:var(--fg-dim);font-size:0.8rem;margin:4px 0;">
              awaiting DFA data (data-dfa JSON or wasm compile_dfa / get_dfa binding from dregg_dfa crate).
            </div>
            <div style="font-size:0.7rem;color:var(--fg-dim);">
              Ties to blocklace Constitution.routes_commitment (BLAKE3 of RouteTable). See dfa/{compiler,router}.rs + DFA-RATIONALIZATION-DESIGN.md + blocklace/src/constitution.rs:54.
            </div>
          </div>`;
      }

      const states = dfaData.states || dfaData.nodes || [];
      const trans = dfaData.transitions || dfaData.edges || [];

      if (mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">DFA ${states.length} states · ${trans.length} trans</span>`;
      }

      // Improved SVG visualization (layered layout + proper edges, following delegation-graph/merkle patterns; no JS reimpl of DFA semantics)
      const stateCount = states.length || 4;
      const cols = Math.min(5, Math.max(1, Math.ceil(Math.sqrt(stateCount))));
      const boxW = 520, boxH = 160;
      const nodeR = 12;
      const nodeW = 58, nodeH = 24;

      const svgNodes = states.map((s, i) => {
        const col = i % cols;
        const row = Math.floor(i / cols);
        const x = 30 + col * (nodeW + 24);
        const y = 28 + row * 42;
        const isDead = s.dead || s.id === 0 /* convention from DEAD_STATE in dfa::compiler */;
        return h('g', {},
          h('rect', {
            x: x - nodeW/2, y: y - nodeH/2, width: nodeW, height: nodeH, rx: 4,
            fill: isDead ? '#3a1a1a' : '#1a2e1a', stroke: isDead ? '#f87171' : '#4ade80', 'stroke-width': 1.5
          }),
          h('text', { x, y: y + 4, 'text-anchor': 'middle', 'font-size': '8px', fill: '#e4ddd0', 'font-family': 'ui-monospace,monospace' }, String(s.id ?? i))
        );
      });

      const svgEdges = trans.slice(0, 30).map((t) => {
        const fi = (t.from ?? 0);
        const ti = (t.to ?? 1);
        const fcol = fi % cols, frow = Math.floor(fi / cols);
        const tcol = ti % cols, trow = Math.floor(ti / cols);
        const fx = 30 + fcol * (nodeW + 24), fy = 28 + frow * 42;
        const tx = 30 + tcol * (nodeW + 24), ty = 28 + trow * 42;
        // simple line + label (first byte or '*')
        const label = t.byte != null ? String(t.byte) : (t.pattern ? '*' : '?');
        return h('g', {},
          h('line', { x1: fx + 8, y1: fy, x2: tx - 8, y2: ty, stroke: '#60a5fa', 'stroke-width': 1, opacity: 0.7 }),
          h('text', { x: (fx+tx)/2, y: (fy+ty)/2 - 2, 'font-size': '6px', fill: '#94a3b8' }, label)
        );
      });

      return html`
        <div class="dregg-inspector dregg-inspector--cell pdfa">
          <header><span class="dregg-inspector__kind">dfa</span> ${dfaData.name || shortHex(dfaData.hash || dfaData.routes_commitment || '', 8)}</header>
          <svg width="${boxW}" height="${boxH}" style="border:1px solid var(--line);background:var(--bg);border-radius:4px;">
            ${svgEdges}
            ${svgNodes}
          </svg>
          <div style="font-size:0.75rem;margin-top:4px;color:var(--fg-dim);">
            ${states.length} states · ${trans.length} transitions (from dregg_dfa::compiler / RouteTable). Use for RelayOperator, PubSubTopicFilter, CapTP pre-filters, governed routing.
          </div>
          ${dfaData.air_fingerprint || dfaData.routes_commitment ? html`<div style="font-size:0.65rem;">commit / AIR: ${shortHex(dfaData.air_fingerprint || dfaData.routes_commitment || '', 10)}</div>` : ''}
          <div style="font-size:0.65rem;margin-top:2px;color:#6a8070;">data-dfa should come from the dregg_dfa crate or a runtime route table binding; compile_dfa is a wasm substrate gap.</div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-dfa')) {
  customElements.define('dregg-dfa', DreggDfa);
}

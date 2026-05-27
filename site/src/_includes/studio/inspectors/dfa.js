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

import { InspectorBase, renderParseError, shortHex, emptyState } from './_base.js';
import { parseRef } from '../uri.js';

function asArray(value) {
  return Array.isArray(value) ? value : [];
}

function transitionLabel(t) {
  if (t == null) return '?';
  if (t.byte != null) return String(t.byte);
  if (t.symbol != null) return String(t.symbol);
  if (t.pattern != null) return String(t.pattern);
  if (t.guard != null) return String(t.guard);
  return '*';
}

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
          ${emptyState(
            html,
            'DFA unavailable',
            parsed
              ? html`The URI parsed as <code>${shortHex(parsed.id, 12)}</code>, but this runtime has no DFA lookup. Provide <code>data-dfa</code> from a route table, relay operator, or predicate witness to render states and transitions.`
              : html`Provide <code>data-dfa</code> from a route table, relay operator, or predicate witness to render states and transitions.`
          )}`;
      }

      const trans = asArray(dfaData.transitions || dfaData.edges);
      let states = asArray(dfaData.states || dfaData.nodes);
      if (!states.length && trans.length) {
        const ids = new Set();
        trans.forEach(t => {
          ids.add(String(t.from ?? t.source ?? 0));
          ids.add(String(t.to ?? t.target ?? 0));
        });
        states = Array.from(ids).map(id => ({ id }));
      }
      const start = dfaData.start_state ?? dfaData.start ?? dfaData.initial;
      const accepting = new Set(asArray(dfaData.accepting_states || dfaData.accepting || dfaData.final_states).map(String));
      const dead = new Set(asArray(dfaData.dead_states || dfaData.dead).map(String));
      const commitment = dfaData.air_fingerprint || dfaData.routes_commitment || dfaData.hash || '';

      if (mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">DFA ${states.length} states · ${trans.length} transitions${commitment ? html` · <code>${shortHex(commitment, 8)}</code>` : ''}</span>`;
      }

      // Improved SVG visualization (layered layout + proper edges, following delegation-graph/merkle patterns; no JS reimpl of DFA semantics)
      const stateCount = Math.max(states.length, 1);
      const cols = Math.min(5, Math.max(1, Math.ceil(Math.sqrt(stateCount))));
      const boxW = 520, boxH = 160;
      const nodeW = 58, nodeH = 24;
      const stateIndex = new Map(states.map((s, i) => [String(s.id ?? s.name ?? i), i]));

      const svgNodes = states.map((s, i) => {
        const col = i % cols;
        const row = Math.floor(i / cols);
        const x = 30 + col * (nodeW + 24);
        const y = 28 + row * 42;
        const id = String(s.id ?? s.name ?? i);
        const isDead = s.dead || dead.has(id);
        const isAccepting = s.accepting || accepting.has(id);
        const isStart = start != null && String(start) === id;
        return h('g', {},
          h('rect', {
            x: x - nodeW/2, y: y - nodeH/2, width: nodeW, height: nodeH, rx: 4,
            fill: isDead ? '#3a1a1a' : isAccepting ? '#16351f' : '#182233',
            stroke: isDead ? '#f87171' : isAccepting ? '#4ade80' : '#60a5fa',
            'stroke-width': isStart ? 2 : 1.5
          }),
          h('text', { x, y: y + 4, 'text-anchor': 'middle', 'font-size': '8px', fill: '#e4ddd0', 'font-family': 'ui-monospace,monospace' }, id)
        );
      });

      const svgEdges = trans.slice(0, 30).map((t) => {
        const fi = stateIndex.get(String(t.from ?? t.source ?? 0)) ?? 0;
        const ti = stateIndex.get(String(t.to ?? t.target ?? 0)) ?? 0;
        const fcol = fi % cols, frow = Math.floor(fi / cols);
        const tcol = ti % cols, trow = Math.floor(ti / cols);
        const fx = 30 + fcol * (nodeW + 24), fy = 28 + frow * 42;
        const tx = 30 + tcol * (nodeW + 24), ty = 28 + trow * 42;
        const label = transitionLabel(t);
        return h('g', {},
          h('line', { x1: fx + 8, y1: fy, x2: tx - 8, y2: ty, stroke: '#60a5fa', 'stroke-width': 1, opacity: 0.7 }),
          h('text', { x: (fx+tx)/2, y: (fy+ty)/2 - 2, 'font-size': '6px', fill: '#94a3b8' }, String(label).slice(0, 18))
        );
      });

      return html`
        <div class="dregg-inspector dregg-inspector--cell pdfa">
          <header><span class="dregg-inspector__kind">dfa</span> ${dfaData.name || shortHex(dfaData.hash || dfaData.routes_commitment || '', 8)}</header>
          <svg width="${boxW}" height="${boxH}" style="border:1px solid var(--line);background:var(--bg);border-radius:4px;">
            ${svgEdges}
            ${svgNodes}
          </svg>
          <dl class="dregg-inspector__kv">
            <dt>states</dt><dd>${states.length}${start != null ? html` · start <code>${start}</code>` : ''}${accepting.size ? html` · accepting ${accepting.size}` : ''}</dd>
            <dt>transitions</dt><dd>${trans.length}${trans.length > 30 ? html` · showing first 30` : ''}</dd>
            ${commitment ? html`<dt>commitment</dt><dd><code title=${commitment}>${shortHex(commitment, 18)}</code></dd>` : null}
          </dl>
          <details class="dregg-inspector__section">
            <summary>Transition table</summary>
            <div class="dregg-inspector__section-body">
              <table class="dregg-inspector__table">
                <tr><th>from</th><th>label</th><th>to</th></tr>
                ${trans.length
                  ? trans.slice(0, 40).map(t => html`<tr><td><code>${t.from ?? t.source ?? '?'}</code></td><td>${transitionLabel(t)}</td><td><code>${t.to ?? t.target ?? '?'}</code></td></tr>`)
                  : html`<tr><td colspan="3" class="dregg-inspector__meta">no transitions supplied</td></tr>`}
              </table>
            </div>
          </details>
          <div class="dregg-inspector__note">Rendered from caller-supplied DFA or route-table data. This view does not compile route rules or evaluate input strings.</div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));
  }
}

if (!customElements.get('dregg-dfa')) {
  customElements.define('dregg-dfa', DreggDfa);
}

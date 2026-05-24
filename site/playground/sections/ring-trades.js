// Ring Trades — intent graph editor + cycle search + atomic settle.

import { mountSection } from './_newworld.js';
import { renderRingTradeSvg } from '../visualizers/ring-trade.js';

// Greedy cycle search: find any cycle reachable from `start` via DFS.
function findCycle(nodes, edges) {
  const adj = new Map(nodes.map(n => [n.id, []]));
  for (const e of edges) adj.get(e.from)?.push(e.to);
  for (const start of nodes.map(n => n.id)) {
    const stack = [{ id: start, path: [start] }];
    const seen = new Set();
    while (stack.length) {
      const { id, path } = stack.pop();
      for (const next of adj.get(id) || []) {
        if (next === start && path.length >= 2) {
          return [...path, next];
        }
        const key = `${id}->${next}|${path.join(',')}`;
        if (seen.has(key)) continue;
        seen.add(key);
        if (!path.includes(next)) {
          stack.push({ id: next, path: [...path, next] });
        }
      }
    }
  }
  return null;
}

export function initRingTrades(_wasm) {
  mountSection('ring-trades', (api) => {
    const { html, signal } = api;

    const nodes = signal([
      { id: 'A', label: 'A wants apples', has: 'pears' },
      { id: 'B', label: 'B wants pears',  has: 'oranges' },
      { id: 'C', label: 'C wants oranges',has: 'apples' },
    ]);
    const edges = signal([
      { from: 'A', to: 'B' },
      { from: 'B', to: 'C' },
      { from: 'C', to: 'A' },
    ]);
    const cycle = signal([]);
    const settled = signal(null);   // null | 'committed' | 'rolled-back'
    const log = signal([]);

    function pushLog(msg, kind = 'info') {
      log.value = [...log.value, { t: Date.now(), msg, kind }].slice(-30);
    }

    function addNode() {
      const idChar = String.fromCharCode(65 + nodes.value.length);
      nodes.value = [...nodes.value, { id: idChar, label: idChar, has: '?' }];
      pushLog(`added party ${idChar}`);
    }
    function removeNode(id) {
      nodes.value = nodes.value.filter(n => n.id !== id);
      edges.value = edges.value.filter(e => e.from !== id && e.to !== id);
      pushLog(`removed party ${id}`, 'warn');
      cycle.value = []; settled.value = null;
    }
    function addEdge(from, to) {
      if (!from || !to || from === to) return;
      edges.value = [...edges.value, { from, to }];
      pushLog(`leg: ${from} → ${to}`);
      cycle.value = []; settled.value = null;
    }
    function search() {
      const c = findCycle(nodes.value, edges.value);
      if (c) {
        cycle.value = c.slice(0, -1);  // drop the closing dup
        pushLog(`cycle found: ${c.join(' → ')}`, 'ok');
        settled.value = null;
      } else {
        cycle.value = [];
        pushLog('no cycle in graph', 'warn');
      }
    }
    function commit() {
      if (!cycle.value.length) { pushLog('no cycle to settle', 'err'); return; }
      settled.value = 'committed';
      pushLog(`atomically settled cycle ${cycle.value.join(' → ')}`, 'ok');
    }
    function rollback() {
      settled.value = 'rolled-back';
      pushLog('one leg failed → atomic rollback, nothing settles', 'err');
    }
    function reset() {
      cycle.value = []; settled.value = null;
      pushLog('reset settlement state');
    }

    // Local UI state for the edge picker
    const newFrom = signal('A');
    const newTo = signal('B');

    const App = api.reactive(() => html`
      <section class="vizzer" aria-label="Ring trade demo">
        <header class="vizzer__head">
          <h3 class="vizzer__title">Ring-trade solver</h3>
          <p class="vizzer__sub">${cycle.value.length ? `cycle: ${cycle.value.join(' → ')}` : 'no cycle yet'}</p>
          <div class="vizzer__controls">
            <button class="inline" onClick=${search}>find cycle</button>
            <button class="inline" onClick=${commit} disabled=${!cycle.value.length}>commit</button>
            <button class="inline" data-tone="warm" onClick=${rollback} disabled=${!cycle.value.length}>rollback</button>
            <button class="inline" onClick=${reset}>reset</button>
          </div>
        </header>
        <div class="vizzer__body" style="display:flex;flex-direction:column;gap:12px;">

          ${renderRingTradeSvg(html, nodes.value, edges.value, cycle.value, settled.value)}

          <div class="grid-2">
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">parties</h3>
              <div style="display:flex;flex-direction:column;gap:4px;">
                ${nodes.value.map(n => html`
                  <div key=${n.id} style="display:flex;gap:6px;align-items:center;font-family:var(--font-mono);font-size:11px;">
                    <span class="chip">${n.id}</span>
                    <span style="color:var(--fg-dim);flex:1;">${n.label}</span>
                    <button class="inline" data-tone="danger" onClick=${() => removeNode(n.id)}>×</button>
                  </div>
                `)}
              </div>
              <button class="inline" style="margin-top:6px;" onClick=${addNode}>+ party</button>
            </div>
            <div>
              <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">add leg</h3>
              <div style="display:flex;gap:6px;align-items:center;">
                <select value=${newFrom.value} onChange=${e => newFrom.value = e.target.value}
                        style="background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:4px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;">
                  ${nodes.value.map(n => html`<option key=${n.id} value=${n.id}>${n.id}</option>`)}
                </select>
                <span style="color:var(--fg-dim);font-family:var(--font-mono);">→</span>
                <select value=${newTo.value} onChange=${e => newTo.value = e.target.value}
                        style="background:var(--bg-inset);border:1px solid var(--line);color:var(--fg);padding:4px 8px;border-radius:var(--r2);font-family:var(--font-mono);font-size:11px;">
                  ${nodes.value.map(n => html`<option key=${n.id} value=${n.id}>${n.id}</option>`)}
                </select>
                <button class="inline" onClick=${() => addEdge(newFrom.value, newTo.value)}>add</button>
              </div>
              <div style="margin-top:10px;font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);">
                ${edges.value.length} leg(s)
              </div>
            </div>
          </div>

          <div>
            <h3 style="font-family:var(--font-mono);font-size:11px;color:var(--fg-dim);text-transform:uppercase;margin-bottom:6px;">log</h3>
            <div class="log" role="log" aria-live="polite">
              ${log.value.length === 0
                ? html`<div style="color:var(--fg-muted);">no events.</div>`
                : log.value.slice().reverse().map((e, i) => html`<div key=${i} class="log__entry" data-kind=${e.kind}>${e.msg}</div>`)}
            </div>
          </div>
        </div>
      </section>
    `);
    return html`<${App} />`;
  }, {
    title: 'Ring trades',
    lede: 'When N parties each want what the next has, the intent solver finds the cycle and settles all N legs atomically (or rolls back if any fails).',
    fallback: 'Interactive ring-trade graph editor + cycle solver.',
  });
}

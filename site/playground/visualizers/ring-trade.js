// Visualizer: ring-trade
// Renders intent graph (nodes = assets, edges = "I'll give X, want Y") and
// highlights a cycle when one is found.

import { defineVisualizer } from '/_includes/visualizer-base.js';

export function renderRingTradeSvg(html, nodes, edges, cycle, settle) {
  // Layout nodes on a circle.
  const W = 480, H = 280;
  const CX = W / 2, CY = H / 2 + 10;
  const R = Math.min(W, H) * 0.36;
  const positions = nodes.map((n, i) => {
    const a = (i / nodes.length) * Math.PI * 2 - Math.PI / 2;
    return { id: n.id, label: n.label, x: CX + R * Math.cos(a), y: CY + R * Math.sin(a) };
  });
  const posMap = Object.fromEntries(positions.map(p => [p.id, p]));
  const inCycle = new Set(cycle || []);
  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${W} ${H}`} role="img"
         aria-label=${`Ring-trade intent graph: ${nodes.length} parties, ${edges.length} legs`}>
      <text class="label" x="8" y="14">parties (assets) · legs · ${cycle && cycle.length ? `cycle of ${cycle.length}` : 'no cycle'}</text>
      ${edges.map((e, i) => {
        const a = posMap[e.from], b = posMap[e.to];
        if (!a || !b) return null;
        const active = inCycle.has(e.from) && inCycle.has(e.to);
        // Curved arrow
        const dx = b.x - a.x, dy = b.y - a.y;
        const mx = (a.x + b.x) / 2, my = (a.y + b.y) / 2;
        const nx = -dy, ny = dx;
        const len = Math.hypot(nx, ny) || 1;
        const cx = mx + (nx / len) * 18;
        const cy = my + (ny / len) * 18;
        const d = `M ${a.x.toFixed(1)} ${a.y.toFixed(1)} Q ${cx.toFixed(1)} ${cy.toFixed(1)} ${b.x.toFixed(1)} ${b.y.toFixed(1)}`;
        return html`<path key=${i} class="edge" data-state=${active ? 'active' : ''}
                          d=${d} marker-end=${active ? 'url(#rt-arrow-active)' : 'url(#rt-arrow)'} />`;
      })}
      <defs>
        <marker id="rt-arrow" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto">
          <path d="M 0 0 L 10 5 L 0 10 z" fill="var(--line-strong)" />
        </marker>
        <marker id="rt-arrow-active" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="6" markerHeight="6" orient="auto">
          <path d="M 0 0 L 10 5 L 0 10 z" fill="var(--accent-bright)" />
        </marker>
      </defs>
      ${positions.map(p => html`
        <g key=${p.id}>
          <circle class="node" data-state=${inCycle.has(p.id) ? (settle === 'committed' ? 'active' : 'warm') : ''}
                  cx=${p.x} cy=${p.y} r="22" />
          <text class="label" x=${p.x} y=${p.y + 4} text-anchor="middle"
                style=${`fill:${inCycle.has(p.id) ? 'var(--fg)' : 'var(--fg-dim)'};font-weight:600;`}>${p.label}</text>
        </g>
      `)}
      ${settle === 'committed' ? html`<text class="label" x="8" y=${H - 8} style="fill:var(--success);">settled atomically</text>` :
        settle === 'rolled-back' ? html`<text class="label" x="8" y=${H - 8} style="fill:var(--danger);">rolled back</text>` : null}
    </svg>
  `;
}

defineVisualizer('ring-trade', ({ dataset, api }) => {
  const { html } = api;
  // Demo state when used statically (no live data wiring).
  const nodes = [
    { id: 'A', label: 'A' },
    { id: 'B', label: 'B' },
    { id: 'C', label: 'C' },
  ];
  const edges = [
    { from: 'A', to: 'B' },
    { from: 'B', to: 'C' },
    { from: 'C', to: 'A' },
  ];
  const cycle = dataset.cycle === 'true' ? ['A', 'B', 'C'] : [];
  return renderRingTradeSvg(html, nodes, edges, cycle, dataset.settled || null);
});

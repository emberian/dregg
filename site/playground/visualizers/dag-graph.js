/**
 * DAG Graph Visualizer.
 *
 * Two entry points:
 *   - `render(container, data, opts)` — legacy direct-render helper used
 *     by the playground blocklace simulator.
 *   - `defineVisualizer('dag-graph', ...)` — `<pyana-vizzer>` registration.
 *
 * Dataset (JSON in data-dataset):
 *   {
 *     "nodes": [{ "id": "a1", "height": 0, "creator": 0, "isFinal": true }, ...],
 *     "edges": [{ "from": "a2", "to": "a1" }, ...]
 *   }
 *
 * Height grows upward; edges should point from child to parent (causal past).
 */

import { defineVisualizer } from '/_includes/visualizer-base.js';

export const name = 'dag-graph';

const COLORS = [
  'var(--p-tide, #6ba3c7)',
  'var(--p-amber, #d99a3f)',
  'var(--p-sage, #9bb87a)',
  'var(--p-ember, #d4685c)',
  'var(--p-fern, #7aab6f)',
];

function layout(nodes, width) {
  const layers = {};
  nodes.forEach(n => {
    const layer = n.height || 0;
    if (!layers[layer]) layers[layer] = [];
    layers[layer].push(n);
  });
  const keys = Object.keys(layers).map(Number).sort((a, b) => a - b);
  const height = Math.max(220, keys.length * 55 + 60);
  const positions = {};
  keys.forEach((k, idx) => {
    const layerNodes = layers[k];
    const spacing = width / (layerNodes.length + 1);
    const y = height - 36 - idx * 50;
    layerNodes.forEach((node, nIdx) => {
      positions[node.id] = { x: spacing * (nIdx + 1), y };
    });
  });
  return { positions, height };
}

export function renderDagSvg(html, nodes, edges) {
  const W = 480;
  if (!nodes.length) {
    return html`<div class="viz-empty">Empty DAG</div>`;
  }
  const { positions, height: H } = layout(nodes, W);
  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${W} ${H}`} role="img"
         aria-label=${`DAG with ${nodes.length} blocks and ${edges.length} edges`}>
      <text class="label" x="8" y="14">blocklace · ${nodes.length} blocks · ${edges.length} edges</text>
      ${edges.map((e, i) => {
        const from = positions[e.from];
        const to = positions[e.to];
        if (!from || !to) return null;
        const opacity = e.type === 'reference' ? 0.15 : 0.35;
        return html`<line key=${i} x1=${from.x} y1=${from.y} x2=${to.x} y2=${to.y}
          stroke="var(--line-strong)" stroke-opacity=${opacity} stroke-width="1.5"/>`;
      })}
      ${nodes.map(node => {
        const pos = positions[node.id];
        if (!pos) return null;
        const color = node.isEquivocator
          ? 'var(--danger, #d4685c)'
          : COLORS[(node.creator || 0) % COLORS.length];
        const r = node.isFinal ? 8 : 5;
        return html`
          <g key=${node.id}>
            ${node.isFinal ? html`
              <circle cx=${pos.x} cy=${pos.y} r=${r + 4} fill="none"
                stroke=${color} stroke-width="1" opacity="0.45"/>
            ` : null}
            <circle cx=${pos.x} cy=${pos.y} r=${r} fill=${color}
              opacity=${node.isFinal ? 1 : 0.7}>
              <title>${node.id} · creator ${node.creator ?? 0} · height ${node.height ?? 0}${node.isFinal ? ' · final' : ''}${node.isEquivocator ? ' · equivocator' : ''}</title>
            </circle>
            ${node.label ? html`
              <text x=${pos.x} y=${pos.y + r + 12} text-anchor="middle"
                font-size="9" fill="var(--fg-muted)">${node.label}</text>
            ` : null}
          </g>
        `;
      })}
    </svg>
  `;
}

/**
 * Legacy direct-render API used by playground/sections/blocklace-sim.js.
 */
export function render(container, data, opts = {}) {
  const { nodes, edges } = data;
  const colors = opts.nodeColors || ['#6ba3c7', '#d99a3f', '#9bb87a', '#c77ab8', '#7ac7b8'];
  const width = container.clientWidth || 600;

  if (!nodes.length) {
    container.innerHTML = '<div style="padding:20px; text-align:center; font-family: var(--font-mono, monospace); font-size:10px; color: var(--fg-muted, var(--text-muted));">Empty DAG</div>';
    return;
  }

  const { positions, height } = layout(nodes, width);
  let svg = `<svg width="${width}" height="${height}" xmlns="http://www.w3.org/2000/svg">`;

  edges.forEach(edge => {
    const from = positions[edge.from];
    const to = positions[edge.to];
    if (!from || !to) return;
    const opacity = edge.type === 'reference' ? 0.15 : 0.3;
    svg += `<line x1="${from.x}" y1="${from.y}" x2="${to.x}" y2="${to.y}" stroke="rgba(232,224,208,${opacity})" stroke-width="1.5"/>`;
  });

  nodes.forEach(node => {
    const pos = positions[node.id];
    if (!pos) return;
    const color = node.isEquivocator ? '#d4685c' : colors[(node.creator || 0) % colors.length];
    const r = node.isFinal ? 8 : 5;
    if (node.isFinal && opts.showFinality !== false) {
      svg += `<circle cx="${pos.x}" cy="${pos.y}" r="${r + 4}" fill="none" stroke="${color}" stroke-width="1" opacity="0.4"/>`;
    }
    svg += `<circle cx="${pos.x}" cy="${pos.y}" r="${r}" fill="${color}" class="dag-node" data-id="${node.id}" style="cursor:pointer;" opacity="${node.isFinal ? 1 : 0.6}"/>`;
  });

  svg += `</svg>`;
  container.innerHTML = svg;

  if (opts.onNodeClick) {
    container.querySelectorAll('.dag-node').forEach(el => {
      el.addEventListener('click', () => {
        const node = nodes.find(n => n.id === el.dataset.id);
        if (node) opts.onNodeClick(node);
      });
    });
  }
}

defineVisualizer('dag-graph', ({ dataset, api }) => {
  const { html } = api;
  let nodes, edges;
  try {
    if (dataset.dataset) {
      const parsed = JSON.parse(dataset.dataset);
      nodes = parsed.nodes;
      edges = parsed.edges;
    }
  } catch (_) { /* fall through */ }
  if (!nodes) {
    // Default: a tiny 3-node-per-layer blocklace with one final tip.
    nodes = [
      { id: 'a1', height: 0, creator: 0 },
      { id: 'b1', height: 0, creator: 1 },
      { id: 'c1', height: 0, creator: 2 },
      { id: 'a2', height: 1, creator: 0 },
      { id: 'b2', height: 1, creator: 1, isFinal: true },
    ];
    edges = [
      { from: 'a2', to: 'a1' },
      { from: 'a2', to: 'b1' },
      { from: 'b2', to: 'a1' },
      { from: 'b2', to: 'b1' },
      { from: 'b2', to: 'c1' },
    ];
  }
  return renderDagSvg(html, nodes, edges);
});

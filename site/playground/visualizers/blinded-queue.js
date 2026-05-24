// Visualizer: blinded-queue
// Two entry points:
//   - `renderBlindedQueueSvg(html, commits, nullifiers)` — direct render
//     helper for the playground section (data is reactive there).
//   - `defineVisualizer('blinded-queue', ...)` — static registration for
//     `<pyana-vizzer>` use in Learn pages (renders the rest state).

import { defineVisualizer } from '/_includes/visualizer-base.js';

const COLS = 8;
const CELL = 22;
const PAD = 8;

export function renderBlindedQueueSvg(html, commits, nullifiers) {
  const commitCount = commits.length;
  const nullCount = nullifiers ? nullifiers.size : 0;
  const cells = [];
  const total = Math.max(commitCount, 8);
  for (let i = 0; i < total; i++) {
    const c = commits[i];
    const consumed = c && c.consumed;
    cells.push({ i, active: !!c, consumed });
  }
  const rows = Math.ceil(cells.length / COLS);
  const w = COLS * CELL + PAD * 2;
  const h = rows * CELL + PAD * 2 + 28;
  return html`
    <svg class="viz-svg" viewBox="0 0 ${w} ${h}" role="img"
         aria-label=${`Blinded queue: ${commitCount} commitments, ${nullCount} nullifiers`}>
      <text class="label" x=${PAD} y="14">queue · ${commitCount} commits · ${nullCount} nullifiers</text>
      ${cells.map(c => {
        const x = PAD + (c.i % COLS) * CELL;
        const y = 24 + PAD + Math.floor(c.i / COLS) * CELL;
        const state = c.consumed ? 'warm' : (c.active ? 'active' : '');
        return html`
          <g key=${c.i} transform=${`translate(${x},${y})`}>
            <rect class="node" data-state=${state} width=${CELL - 4} height=${CELL - 4} rx="3" />
            ${c.consumed ? html`<line x1="2" y1="2" x2=${CELL - 6} y2=${CELL - 6}
              stroke="var(--warm)" stroke-width="1.5" />` : null}
          </g>
        `;
      })}
    </svg>
  `;
}

defineVisualizer('blinded-queue', ({ dataset, api }) => {
  const { html } = api;
  const commitCount = parseInt(dataset.commitCount || '0', 10);
  const nullCount = parseInt(dataset.nullifierCount || '0', 10);
  const commits = Array.from({ length: commitCount }, (_, i) => ({ consumed: i < nullCount }));
  const nullifiers = new Set(Array.from({ length: nullCount }, (_, i) => `n${i}`));
  return renderBlindedQueueSvg(html, commits, nullifiers);
});

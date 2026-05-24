// Visualizer: programmable-queue
// Renders the constraint set as a stack of pill rows + an accept/reject
// timeline. `vk_hash` is derived from a digest of the constraint list.

import { defineVisualizer } from '/_includes/visualizer-base.js';

export function renderProgrammableQueueSvg(html, constraints, decisions) {
  const W = 480;
  const ROW_H = 22;
  const PAD = 8;
  const headerH = 22;
  const totalRows = Math.max(constraints.length, 1);
  const h1 = headerH + totalRows * ROW_H + PAD * 2;

  const tlH = 60;
  const tlY = h1 + PAD;
  const w = W;
  const h = h1 + tlH + PAD;

  const cellW = decisions.length ? Math.max(8, Math.min(20, (W - PAD * 2) / decisions.length)) : 0;

  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${w} ${h}`} role="img"
         aria-label=${`Programmable queue: ${constraints.length} constraints, ${decisions.length} decisions`}>
      <text class="label" x=${PAD} y="14">constraint program</text>
      ${constraints.length === 0
        ? html`<text class="label" x=${PAD} y=${headerH + 16} style="fill:var(--fg-muted);">no constraints — every enqueue accepted</text>`
        : constraints.map((c, i) => html`
            <g key=${i} transform=${`translate(${PAD},${headerH + i * ROW_H})`}>
              <rect class="node" data-state="active" width=${W - PAD * 2} height=${ROW_H - 4} rx="3" />
              <text class="label" x="8" y="14" style="fill:var(--fg);">${`${i + 1}. ${c.label}`}</text>
            </g>
          `)}
      <text class="label" x=${PAD} y=${tlY + 12}>try_enqueue timeline</text>
      ${decisions.map((d, i) => html`
        <rect key=${i}
              class="node"
              data-state=${d.accept ? 'active' : 'danger'}
              x=${PAD + i * cellW}
              y=${tlY + 18}
              width=${Math.max(2, cellW - 2)}
              height="28"
              rx="2">
          <title>${d.accept ? `accepted: ${d.label}` : `rejected: ${d.reason}`}</title>
        </rect>
      `)}
    </svg>
  `;
}

defineVisualizer('programmable-queue', ({ dataset, api }) => {
  const { html } = api;
  const n = parseInt(dataset.constraints || '3', 10);
  const constraints = Array.from({ length: n }, (_, i) => ({ label: `c${i + 1}` }));
  return renderProgrammableQueueSvg(html, constraints, []);
});

// Visualizer: batch-executor
// Collect → execute → proof. Lanes per client; per-lane failure markers.

import { defineVisualizer } from '/_includes/visualizer-base.js';

export function renderBatchExecutorSvg(html, clients, stage) {
  const W = 480, H = 220, PAD = 12;
  const colW = (W - PAD * 2) / 3;
  const rowH = 24;

  const stages = ['collect', 'execute', 'proof'];
  const stageIdx = stages.indexOf(stage);
  const headerY = 18;

  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${W} ${H}`} role="img"
         aria-label=${`Batch executor: ${clients.length} clients, stage ${stage}`}>
      ${stages.map((s, i) => html`
        <g key=${s} transform=${`translate(${PAD + i * colW},${headerY})`}>
          <text class="label" style=${`fill:${i <= stageIdx ? 'var(--accent-bright)' : 'var(--fg-muted)'};font-weight:600;`}>${i + 1}. ${s}</text>
        </g>
      `)}
      ${clients.map((c, i) => {
        const y = headerY + 22 + i * rowH;
        return html`
          <g key=${c.id}>
            <text class="label" x=${PAD} y=${y + 14}>client ${c.id}</text>
            ${stages.map((s, si) => {
              const x = PAD + 60 + si * (colW - 20);
              const reached = si <= stageIdx;
              const failed = c.failAt && stages.indexOf(c.failAt) === si;
              return html`
                <rect key=${s}
                      class="node"
                      data-state=${failed ? 'danger' : reached ? 'active' : ''}
                      x=${x} y=${y} width="56" height="18" rx="3" />
              `;
            })}
          </g>
        `;
      })}
    </svg>
  `;
}

defineVisualizer('batch-executor', ({ dataset, api }) => {
  const { html } = api;
  const clients = Array.from({ length: parseInt(dataset.clients || '4', 10) }, (_, i) => ({ id: i + 1 }));
  return renderBatchExecutorSvg(html, clients, dataset.stage || 'collect');
});

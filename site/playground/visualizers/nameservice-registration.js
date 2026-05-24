// Visualizer: nameservice-registration
// register → resolve → reverse, with the admin gate explicit.

import { defineVisualizer } from '/_includes/visualizer-base.js';

export function renderNameserviceSvg(html, names) {
  const W = 480, ROW_H = 26, PAD = 10;
  const rows = Math.max(names.length, 1);
  const H = PAD * 2 + 22 + rows * ROW_H;
  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${W} ${H}`} role="img"
         aria-label=${`Nameservice: ${names.length} registrations`}>
      <text class="label" x=${PAD} y="14">name → service id</text>
      ${names.length === 0
        ? html`<text class="label" x=${PAD} y="42" style="fill:var(--fg-muted);">no registrations.</text>`
        : names.map((n, i) => {
            const y = 22 + i * ROW_H + PAD;
            return html`
              <g key=${n.name} transform=${`translate(${PAD},${y})`}>
                <rect class="node" data-state="active" width=${W - PAD * 2} height=${ROW_H - 6} rx="3" />
                <text class="label" x="10" y="14" style="fill:var(--fg);">
                  ${`${n.name}  →  ${n.serviceId.slice(0, 16)}…`}
                </text>
              </g>
            `;
          })}
    </svg>
  `;
}

defineVisualizer('nameservice-registration', ({ dataset, api }) => {
  const { html } = api;
  const n = parseInt(dataset.count || '2', 10);
  const names = Array.from({ length: n }, (_, i) => ({
    name: `name-${i + 1}.pyana`,
    serviceId: 'service-id-placeholder-' + i,
  }));
  return renderNameserviceSvg(html, names);
});

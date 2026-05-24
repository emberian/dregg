// Visualizer: inbox-lifecycle
// Shows a recipient inbox: push → drain → gc, with TTL/anti-spam markers.

import { defineVisualizer } from '/_includes/visualizer-base.js';

export function renderInboxLifecycleSvg(html, messages) {
  const W = 480, ROW_H = 28, PAD = 8;
  const rows = Math.max(messages.length, 1);
  const H = PAD * 2 + 18 + rows * ROW_H;
  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${W} ${H}`} role="img"
         aria-label=${`Inbox: ${messages.length} messages`}>
      <text class="label" x=${PAD} y="14">recipient inbox · ${messages.length} message(s)</text>
      ${messages.length === 0
        ? html`<text class="label" x=${PAD} y="38" style="fill:var(--fg-muted);">empty.</text>`
        : messages.map((m, i) => {
            const y = 18 + i * ROW_H + PAD;
            const state =
              m.state === 'decrypted' ? 'active' :
              m.state === 'failed'    ? 'danger' :
              m.state === 'pending'   ? 'warm' : '';
            return html`
              <g key=${i} transform=${`translate(${PAD},${y})`}>
                <rect class="node" data-state=${state}
                      width=${W - PAD * 2} height=${ROW_H - 6} rx="3" />
                <text class="label" x="10" y="16" style="fill:var(--fg);font-size:11px;">
                  ${`#${i + 1} · ${m.state} · ${m.preview || '(ciphertext)'}`}
                </text>
              </g>
            `;
          })}
    </svg>
  `;
}

defineVisualizer('inbox-lifecycle', ({ dataset, api }) => {
  const { html } = api;
  const n = parseInt(dataset.count || '3', 10);
  const messages = Array.from({ length: n }, (_, i) => ({ state: 'pending', preview: '(ciphertext)' }));
  return renderInboxLifecycleSvg(html, messages);
});

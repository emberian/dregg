// Visualizer: delegation-envelope-v2
// Renders the signed payload tree: header → authority policy → caveats →
// signature, and a "re-verify check" badge column showing what each step
// validates on every authorize call.

import { defineVisualizer } from '/_includes/visualizer-base.js';

export function renderDelegationEnvelopeSvg(html, envelope) {
  const W = 480, ROW_H = 32, PAD = 10;
  const rows = envelope.rows;
  const H = PAD * 2 + 22 + rows.length * ROW_H;

  return html`
    <svg class="viz-svg" viewBox=${`0 0 ${W} ${H}`} role="img"
         aria-label=${`Delegation envelope v2 (${rows.length} fields)`}>
      <text class="label" x=${PAD} y="14">DelegatedToken v2 (signed)</text>
      ${rows.map((r, i) => {
        const y = 22 + i * ROW_H + PAD;
        return html`
          <g key=${r.label} transform=${`translate(${PAD},${y})`}>
            <rect class="node" data-state=${r.tone || 'active'} width=${W - PAD * 2} height=${ROW_H - 8} rx="3" />
            <text class="label" x="10" y="13" style="fill:var(--fg);font-weight:600;">${r.label}</text>
            <text class="label" x="10" y="22" style="fill:var(--fg-dim);font-size:10px;">${r.value}</text>
            <text class="label" x=${W - PAD * 2 - 8} y="13" text-anchor="end"
                  style=${`fill:${r.checks ? 'var(--success)' : 'var(--fg-muted)'};font-size:9px;`}>
              ${r.checks ? '✓ checked' : ''}
            </text>
          </g>
        `;
      })}
    </svg>
  `;
}

defineVisualizer('delegation-envelope-v2', ({ dataset, api }) => {
  const { html } = api;
  const envelope = {
    rows: [
      { label: 'issuer_pub', value: 'fa90…1be3', checks: true },
      { label: 'subject_pub', value: '9c12…77df', checks: true },
      { label: 'authority_policy', value: 'read,write @ alice/notes', checks: true, tone: 'warm' },
      { label: 'caveats', value: 'expires=2026-12-31, ttl<=10m', checks: true },
      { label: 'nonce', value: '0x' + (dataset.nonce || 'aa55…'), checks: false },
      { label: 'signature', value: 'Ed25519(64B)', checks: true },
    ],
  };
  return renderDelegationEnvelopeSvg(html, envelope);
});

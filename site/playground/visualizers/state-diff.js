/**
 * State Diff Visualizer.
 *
 * Two entry points:
 *   - `render(container, data)` — legacy direct-render helper.
 *   - `defineVisualizer('state-diff', ...)` — `<pyana-vizzer>` registration.
 *
 * Dataset (JSON in data-dataset):
 *   {
 *     "before": { "balance": 100, "nonce": 5, "notes": 2 },
 *     "after":  { "balance":  88, "nonce": 6, "notes": 3 }
 *   }
 */

import { defineVisualizer } from '/_includes/visualizer-base.js';

export const name = 'state-diff';

function delta(b, a) {
  if (typeof b === 'number' && typeof a === 'number') {
    const d = a - b;
    if (d === 0) return { text: '=', tone: 'muted' };
    return { text: (d > 0 ? '+' : '') + d, tone: d > 0 ? 'success' : 'danger' };
  }
  if (b === a) return { text: '=', tone: 'muted' };
  if (b === undefined) return { text: 'new', tone: 'success' };
  if (a === undefined) return { text: 'removed', tone: 'danger' };
  return { text: '≠', tone: 'warm' };
}

export function renderStateDiff(html, before, after) {
  const keys = [...new Set([...Object.keys(before), ...Object.keys(after)])];
  const tone = {
    success: 'var(--success, var(--accent-bright))',
    danger:  'var(--danger, #d4685c)',
    warm:    'var(--warm)',
    muted:   'var(--fg-muted)',
  };
  return html`
    <div class="state-diff" role="table" aria-label="State before and after">
      <div class="state-diff__row state-diff__row--head" role="row">
        <span role="columnheader">Field</span>
        <span role="columnheader">Before</span>
        <span role="columnheader">After</span>
        <span role="columnheader">Δ</span>
      </div>
      ${keys.map(k => {
        const b = before[k];
        const a = after[k];
        const d = delta(b, a);
        return html`
          <div class="state-diff__row" role="row" key=${k}>
            <span role="cell" class="state-diff__field">${k}</span>
            <span role="cell" class="state-diff__before">${b === undefined ? '—' : String(b)}</span>
            <span role="cell" class="state-diff__after">${a === undefined ? '—' : String(a)}</span>
            <span role="cell" class="state-diff__delta" style=${`color:${tone[d.tone]};`}>${d.text}</span>
          </div>
        `;
      })}
    </div>
  `;
}

/**
 * Legacy direct-render API.
 */
export function render(container, data) {
  const { before = {}, after = {} } = data;
  const keys = [...new Set([...Object.keys(before), ...Object.keys(after)])];
  let html = `<div style="font-family: var(--font-mono, monospace); font-size: 12px;">
    <div style="display: grid; grid-template-columns: 1fr 80px 80px 60px; gap: 4px; padding: 6px 8px; background: var(--bg-inset, var(--surface-2)); border-radius: 4px 4px 0 0; color: var(--fg-muted, var(--text-muted)); font-weight: 600; text-transform: uppercase; letter-spacing: 0.04em;">
      <span>Field</span><span>Before</span><span>After</span><span>Δ</span>
    </div>`;
  keys.forEach(k => {
    const b = before[k];
    const a = after[k];
    let dText = '—', cls = '';
    if (typeof b === 'number' && typeof a === 'number') {
      const d = a - b;
      dText = d > 0 ? `+${d}` : d < 0 ? `${d}` : '=';
      cls = d > 0 ? 'color: var(--success, var(--accent-bright));' : d < 0 ? 'color: var(--danger);' : '';
    }
    html += `<div style="display:grid; grid-template-columns: 1fr 80px 80px 60px; gap:4px; padding:4px 8px; border-bottom: 1px solid var(--line);">
      <span style="color: var(--fg-dim, var(--text-dim));">${k}</span>
      <span style="opacity:0.6;">${b !== undefined ? b : '—'}</span>
      <span>${a !== undefined ? a : '—'}</span>
      <span style="${cls}">${dText}</span>
    </div>`;
  });
  html += `</div>`;
  container.innerHTML = html;
}

defineVisualizer('state-diff', ({ dataset, api }) => {
  const { html } = api;
  let before, after;
  try {
    if (dataset.dataset) {
      const parsed = JSON.parse(dataset.dataset);
      before = parsed.before || {};
      after = parsed.after || {};
    }
  } catch (_) { /* fall through */ }
  if (!before) {
    before = { balance: 100, nonce: 5, notes: 2 };
    after = { balance: 88, nonce: 6, notes: 3 };
  }
  return renderStateDiff(html, before, after);
});

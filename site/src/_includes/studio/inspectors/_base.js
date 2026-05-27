/**
 * Shared InspectorBase for all <dregg-*> inspector custom elements.
 *
 * Each subclass implements `_render()` which:
 *   - Reads `uri` attribute (a dregg:// URI). NEVER `ref` (Preact-reserved).
 *   - Reads `mode` (default | compact | inspector | raw).
 *   - Uses `this._api` (Preact + signals + htm) and `this._runtime`.
 *   - Tears down previous render via `this._dispose`.
 *   - Mounts new render into a fresh child via `effect(() => render(...))`.
 */

import { findRuntime } from '../context.js';

function ensureInspectorChrome() {
  if (document.getElementById('dregg-inspector-chrome')) return;
  const style = document.createElement('style');
  style.id = 'dregg-inspector-chrome';
  style.textContent = `
.dregg-inspector__empty-title { font-weight: 650; color: var(--fg, #e8f0e8); }
.dregg-inspector__empty-body { margin-top: 4px; color: var(--fg-dim, #9aa0a6); font-size: 0.82rem; line-height: 1.4; }
.dregg-inspector__empty-actions { display: flex; flex-wrap: wrap; gap: 6px; margin-top: 8px; }
.dregg-inspector__link { color: var(--accent, #64c8ff); text-decoration: none; border-bottom: 1px dotted currentColor; cursor: pointer; }
.dregg-inspector__link:hover { border-bottom-style: solid; }
.dregg-inspector__meta { color: var(--fg-dim, #9aa0a6); font-size: 0.78rem; }
.dregg-inspector__summary { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 6px; margin: 8px 0 10px; }
.dregg-inspector__summary div { border: 1px solid var(--line, #30363d); border-radius: 4px; background: var(--bg-raised, #161b22); padding: 7px; min-width: 0; }
.dregg-inspector__summary span { display: block; color: var(--fg-dim, #9aa0a6); font-size: 0.66rem; text-transform: uppercase; }
.dregg-inspector__summary strong { display: block; margin-top: 3px; color: var(--fg, #e8f0e8); font-size: 0.86rem; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.dregg-inspector__notice { border: 1px solid var(--line, #30363d); border-radius: 4px; background: var(--bg-raised, #161b22); padding: 7px 8px; color: var(--fg-dim, #9aa0a6); font-size: 0.76rem; line-height: 1.4; margin: 6px 0; }
.dregg-inspector__notice--ok { border-color: #62c47a; color: #8ee6a2; }
.dregg-inspector__notice--warn { border-color: #c9a84c; color: #f2d06b; }
.dregg-inspector__controls { display: flex; flex-wrap: wrap; align-items: center; gap: 6px; border-top: 1px solid var(--line, #30363d); margin-top: 8px; padding-top: 8px; }
.dregg-inspector__input,
.dregg-inspector__select,
.dregg-inspector__button { border: 1px solid var(--line, #30363d); border-radius: 4px; background: var(--bg, #0d1117); color: var(--fg, #e8f0e8); font: inherit; font-size: 0.74rem; padding: 5px 7px; }
.dregg-inspector__input { font-family: var(--mono, ui-monospace, SFMono-Regular, Menlo, monospace); min-width: 10rem; }
.dregg-inspector__button { cursor: pointer; }
.dregg-inspector__button:hover { border-color: var(--accent, #64c8ff); color: var(--accent-bright, #8fddff); background: var(--accent-soft, rgba(100,200,255,0.12)); }
.dregg-inspector__button:disabled { opacity: 0.45; cursor: not-allowed; }
.dregg-inspector__action-list { list-style: none; padding: 0; margin: 0; display: flex; flex-direction: column; gap: 4px; }
.dregg-inspector__action-row { display: flex; align-items: center; gap: 6px; min-width: 0; }
.dregg-inspector__action-index { color: var(--fg-dim, #9aa0a6); font-size: 0.75rem; min-width: 1.4em; }
.dregg-inspector__action-method { color: var(--fg-dim, #9aa0a6); font-size: 0.78rem; }
.dregg-inspector__kv { display: grid; grid-template-columns: max-content minmax(0, 1fr); gap: 3px 10px; margin: 8px 0; }
.dregg-inspector__kv dt { color: var(--fg-dim, #9aa0a6); }
.dregg-inspector__kv dd { margin: 0; min-width: 0; overflow-wrap: anywhere; }
.dregg-inspector__panel { border: 1px solid var(--line, #30363d); border-radius: 5px; background: var(--bg-raised, #161b22); padding: 8px; }
.dregg-inspector__section { border: 1px solid var(--line, #30363d); border-radius: 5px; margin-top: 8px; overflow: hidden; }
.dregg-inspector__section > summary { cursor: pointer; padding: 6px 8px; color: var(--fg-dim, #9aa0a6); font-size: 0.8rem; user-select: none; }
.dregg-inspector__section-body { border-top: 1px solid var(--line, #30363d); padding: 8px; background: var(--bg, #0d1117); }
.dregg-inspector__pill { display: inline-flex; align-items: center; gap: 4px; border: 1px solid var(--line, #30363d); border-radius: 999px; padding: 2px 7px; color: var(--fg-dim, #9aa0a6); font-size: 0.68rem; text-transform: uppercase; }
.dregg-inspector__list { margin: 0; padding-left: 18px; display: grid; gap: 4px; }
.dregg-inspector__table { width: 100%; border-collapse: collapse; font-size: 0.76rem; }
.dregg-inspector__table th { color: var(--fg-dim, #9aa0a6); font-weight: 600; text-align: left; border-bottom: 1px solid var(--line, #30363d); padding: 4px 6px; }
.dregg-inspector__table td { border-bottom: 1px solid rgba(127,127,127,0.16); padding: 5px 6px; vertical-align: top; overflow-wrap: anywhere; }
.dregg-inspector__progress { display: inline-block; width: 120px; max-width: 100%; height: 8px; border: 1px solid var(--line, #30363d); border-radius: 999px; background: var(--bg, #0d1117); overflow: hidden; vertical-align: middle; }
.dregg-inspector__progress-fill { display: block; height: 100%; background: var(--accent, #64c8ff); }
.dregg-inspector__note { color: var(--fg-dim, #9aa0a6); font-size: 0.72rem; line-height: 1.4; }
.dregg-inspector__rows { display: grid; gap: 5px; min-width: 0; }
.dregg-inspector__row { display: grid; grid-template-columns: 48px minmax(120px, 0.45fr) minmax(0, 1fr); gap: 8px; align-items: center; border: 1px solid var(--line, #30363d); border-radius: 4px; background: var(--bg-raised, #161b22); padding: 5px 7px; min-width: 0; }
.dregg-inspector__row span { color: var(--fg-muted, #777); font-size: 0.68rem; text-transform: uppercase; overflow: hidden; text-overflow: ellipsis; }
.dregg-inspector__row strong { min-width: 0; overflow: hidden; text-overflow: ellipsis; color: var(--fg, #e8f0e8); font-size: 0.78rem; }
.dregg-inspector__row code { min-width: 0; overflow: hidden; text-overflow: ellipsis; color: var(--fg-dim, #9aa0a6); font-size: 0.68rem; white-space: nowrap; }
.dregg-inspector__actions { display: flex; flex-wrap: wrap; gap: 8px; margin-top: 10px; }
.dregg-storage-pattern { display: grid; gap: 10px; }
.dregg-storage-pattern__head { display: flex; align-items: flex-start; justify-content: space-between; gap: 10px; border-bottom: 1px solid var(--line, #30363d); padding-bottom: 8px; }
.dregg-storage-pattern__title { display: flex; align-items: center; gap: 7px; flex-wrap: wrap; min-width: 0; }
.dregg-storage-pattern__subtitle { color: var(--fg-dim, #9aa0a6); font-size: 0.76rem; margin-top: 3px; line-height: 1.35; }
.dregg-storage-pattern__badges { display: flex; flex-wrap: wrap; gap: 6px; }
.dregg-storage-pattern__badge { border: 1px solid var(--line, #30363d); border-radius: 999px; padding: 2px 7px; color: var(--fg-dim, #9aa0a6); font-size: 0.67rem; text-transform: uppercase; white-space: nowrap; }
.dregg-storage-pattern__badge--ok { border-color: #62c47a; color: #8ee6a2; }
.dregg-storage-pattern__badge--warn { border-color: #c9a84c; color: #f2d06b; }
.dregg-storage-pattern__summary { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 6px; }
.dregg-storage-pattern__summary div { border: 1px solid var(--line, #30363d); border-radius: 4px; background: var(--bg-raised, #161b22); padding: 7px; min-width: 0; }
.dregg-storage-pattern__summary span { display: block; color: var(--fg-dim, #9aa0a6); font-size: 0.66rem; text-transform: uppercase; }
.dregg-storage-pattern__summary strong { display: block; margin-top: 3px; color: var(--fg, #e8f0e8); font-size: 0.86rem; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
.dregg-storage-pattern__section { border: 1px solid var(--line, #30363d); border-radius: 5px; background: var(--bg-raised, #161b22); padding: 9px; }
.dregg-storage-pattern__section h4 { margin: 0 0 6px; color: var(--fg, #e8f0e8); font-size: 0.78rem; text-transform: uppercase; letter-spacing: 0.04em; }
.dregg-storage-pattern__caveats { list-style: none; padding: 0; margin: 0; display: flex; flex-direction: column; gap: 4px; }
.dregg-storage-pattern__caveats li { display: flex; align-items: baseline; gap: 6px; min-width: 0; color: var(--fg-dim, #9aa0a6); font-size: 0.78rem; }
.dregg-storage-pattern__caveats code { color: var(--fg, #e8f0e8); }
.dregg-storage-pattern__unavailable { color: var(--fg-dim, #9aa0a6); font-size: 0.78rem; line-height: 1.4; }
.dregg-storage-pattern details summary { cursor: pointer; color: var(--fg-dim, #9aa0a6); font-size: 0.8rem; user-select: none; }
.dregg-outbox { display: grid; gap: 10px; }
.dregg-outbox__head { display: flex; align-items: flex-start; justify-content: space-between; gap: 12px; border-bottom: 1px solid var(--line, #30363d); padding-bottom: 8px; }
.dregg-outbox__summary { display: grid; grid-template-columns: repeat(3, minmax(0, 1fr)); gap: 6px; width: 100%; }
.dregg-outbox__summary span { border: 1px solid var(--line, #30363d); border-radius: 4px; padding: 6px; color: var(--fg-dim, #9aa0a6); font-size: 0.74rem; }
.dregg-outbox__summary strong { display: block; color: var(--fg, #e8f0e8); font-size: 1rem; }
.dregg-outbox__btn,
.dregg-outbox__drop { border: 1px solid var(--line, #30363d); border-radius: 4px; background: var(--bg, #0d1117); color: var(--fg, #e8f0e8); font: inherit; font-size: 0.72rem; padding: 5px 8px; cursor: pointer; }
.dregg-outbox__btn:hover,
.dregg-outbox__drop:hover { border-color: var(--accent, #64c8ff); color: var(--accent-bright, #8fddff); background: var(--accent-soft, rgba(100,200,255,0.12)); }
.dregg-outbox__btn:disabled,
.dregg-outbox__drop:disabled { opacity: 0.45; cursor: not-allowed; }
.dregg-outbox__cards { display: grid; gap: 8px; }
.dregg-outbox__entry { border: 1px solid var(--line, #30363d); border-radius: 5px; background: var(--bg-raised, #161b22); padding: 10px; }
.dregg-outbox__entry-head { display: flex; align-items: center; justify-content: space-between; gap: 8px; margin-bottom: 8px; }
.dregg-outbox__entry-head strong { margin-left: 6px; font-size: 0.84rem; }
.dregg-outbox__status { border: 1px solid var(--line, #30363d); border-radius: 999px; padding: 2px 7px; color: var(--fg-dim, #9aa0a6); font-size: 0.66rem; text-transform: uppercase; }
.dregg-outbox__status--pending { border-color: #c9a84c; color: #f2d06b; }
.dregg-outbox__status--submitting { border-color: var(--accent, #64c8ff); color: var(--accent-bright, #8fddff); }
.dregg-outbox__status--failed { border-color: #d4685c; color: #f18b7d; }
.dregg-outbox__status--submitted { border-color: #62c47a; color: #8ee6a2; }
.dregg-outbox__kv dd { overflow-wrap: anywhere; }
.dregg-cell__summary,
.dregg-receipt__summary { display: grid; grid-template-columns: repeat(4, minmax(0, 1fr)); gap: 6px; margin: 8px 0 10px; }
.dregg-receipt__summary { grid-template-columns: repeat(3, minmax(0, 1fr)); }
.dregg-cell__summary div,
.dregg-receipt__summary div { border: 1px solid var(--line, #30363d); border-radius: 4px; background: var(--bg-raised, #161b22); padding: 7px; min-width: 0; }
.dregg-cell__summary span,
.dregg-receipt__summary span { display: block; color: var(--fg-dim, #9aa0a6); font-size: 0.66rem; text-transform: uppercase; }
.dregg-cell__summary strong,
.dregg-receipt__summary strong { display: block; margin-top: 3px; color: var(--fg, #e8f0e8); font-size: 0.86rem; overflow: hidden; text-overflow: ellipsis; white-space: nowrap; }
@media (max-width: 640px) {
  .dregg-cell__summary,
  .dregg-receipt__summary,
  .dregg-inspector__summary,
  .dregg-storage-pattern__summary { grid-template-columns: repeat(2, minmax(0, 1fr)); }
  .dregg-storage-pattern__head { flex-direction: column; }
  .dregg-inspector__row { grid-template-columns: 36px minmax(0, 1fr); }
  .dregg-inspector__row code { grid-column: 1 / -1; }
}
`;
  document.head.appendChild(style);
}

export function ready() {
  return new Promise(resolve => {
    if (window.dreggUi) return resolve(window.dreggUi);
    window.addEventListener('dreggUi:ready', e => resolve(e.detail), { once: true });
  });
}

export class InspectorBase extends HTMLElement {
  static get observedAttributes() { return ['uri', 'mode']; }
  constructor() {
    super();
    this._unmount = null;
    this._dispose = null;
    this._connectToken = 0;
  }
  async connectedCallback() {
    const token = ++this._connectToken;
    const [api, runtime] = await Promise.all([ready(), findRuntime(this)]);
    if (!this.isConnected || token !== this._connectToken) return;
    ensureInspectorChrome();
    this._runtime = runtime;
    this._api = api;
    this.addEventListener('click', this._onNavigateClick);
    this._render();
  }
  attributeChangedCallback() {
    if (this._api) this._render();
  }
  disconnectedCallback() {
    this._connectToken++;
    this.removeEventListener('click', this._onNavigateClick);
    if (this._dispose) this._dispose();
    if (this._unmount) this._unmount();
  }
  _onNavigateClick(e) {
    const link = e.target?.closest?.('[data-dregg-uri]');
    if (!link || !this.contains(link)) return;
    const uri = link.getAttribute('data-dregg-uri');
    if (!uri) return;
    const handled = !this.dispatchEvent(new CustomEvent('dregg:navigate', {
      bubbles: true,
      cancelable: true,
      detail: { uri },
    }));
    if (handled) e.preventDefault();
  }
  _render() { /* subclass override */ }
}

/** Render a parse error in-place; returns true if errored. */
export function renderParseError(el, refAttr, parsed, expectedKind) {
  if (!parsed) {
    renderErrorText(el, `bad ref: ${refAttr}`);
    return true;
  }
  if (expectedKind && parsed.kind !== expectedKind) {
    renderErrorText(el, `wrong kind: ${parsed.kind} (expected ${expectedKind})`);
    return true;
  }
  return false;
}

function renderErrorText(el, message) {
  el.replaceChildren();
  const div = document.createElement('div');
  div.className = 'dregg-inspector dregg-inspector--err';
  div.textContent = message;
  el.appendChild(div);
}

/** Short hex display: first 8 chars + ellipsis (with full hex as title attr). */
export function shortHex(s, len = 8) {
  if (!s) return '';
  if (s.length <= len) return s;
  return s.slice(0, len) + '…';
}

export function dreggHref(uri) {
  return `?at=${encodeURIComponent(uri)}`;
}

export function dreggCodeLink(html, uri, label, title = uri) {
  return html`<a class="dregg-inspector__link" href=${dreggHref(uri)} data-dregg-uri=${uri} title=${title}><code>${label}</code></a>`;
}

export function emptyState(html, title, body, actions = []) {
  return html`
    <div class="dregg-inspector dregg-inspector--empty">
      <div class="dregg-inspector__empty-title">${title}</div>
      ${body ? html`<div class="dregg-inspector__empty-body">${body}</div>` : null}
      ${actions.length ? html`<div class="dregg-inspector__empty-actions">${actions}</div>` : null}
    </div>`;
}

export function cellIdFrom(cell, parsed) {
  return cell?.cell_id || parsed?.id || null;
}

export function fieldHex(fields, index, len = 12) {
  const v = fields?.[index];
  return v ? shortHex(String(v), len) : 'unavailable';
}

export function fieldU64(fields, index) {
  const v = fields?.[index];
  if (v == null || v === '') return null;
  if (typeof v === 'number') return Number.isFinite(v) ? v : null;
  const s = String(v);
  const n = s.startsWith('0x') ? Number.parseInt(s.slice(2), 16) : Number.parseInt(s, 16);
  return Number.isFinite(n) ? n : null;
}

export function programConstraints(program) {
  if (!program || program.kind === 'None') return [];
  if (program.kind === 'Predicate') return program.constraints || [];
  if (program.kind === 'Cases') return (program.cases || []).flatMap(c => c.constraints || []);
  return [];
}

export function programBadge(program, constraints = programConstraints(program)) {
  if (!program || program.kind === 'None') return 'no program';
  if (program.kind === 'Circuit') return `Circuit ${shortHex(program.circuit_hash, 8)}`;
  if (program.kind === 'Cases') return `${program.cases?.length || 0} cases / ${constraints.length} caveats`;
  return `${program.kind} / ${constraints.length} caveats`;
}

export function hasConstraint(constraints, matcher) {
  return constraints.some(c => matcher(c) || (c.kind === 'AnyOf' && (c.variants || []).some(matcher)));
}

export function caveatSummaries(constraints, wanted = []) {
  const flat = [];
  for (const c of constraints) {
    flat.push(c);
    if (c.kind === 'AnyOf') flat.push(...(c.variants || []));
  }
  return flat
    .filter(c => !wanted.length || wanted.includes(c.kind) || wanted.some(w => String(c.predicate_kind || '').includes(w)))
    .map(c => {
      switch (c.kind) {
        case 'SenderAuthorized': return `SenderAuthorized ${c.set_kind || 'set'} ${shortHex(c.commitment, 10)}`;
        case 'MonotonicSequence': return `MonotonicSequence seq_slot[${c.seq_index}]`;
        case 'Monotonic': return `Monotonic slot[${c.index}]`;
        case 'StrictMonotonic': return `StrictMonotonic slot[${c.index}]`;
        case 'WriteOnce': return `WriteOnce slot[${c.index}]`;
        case 'Immutable': return `Immutable slot[${c.index}]`;
        case 'FieldLte': return `FieldLte slot[${c.index}] <= ${shortHex(c.value, 10)}`;
        case 'FieldGte': return `FieldGte slot[${c.index}] >= ${shortHex(c.value, 10)}`;
        case 'RateLimit': return `RateLimit ${c.max_per_epoch}/epoch (${c.epoch_duration})`;
        case 'RateLimitBySum': return `RateLimitBySum slot[${c.slot_index}] <= ${c.max_sum_per_epoch}/epoch`;
        case 'BoundedBy': return `BoundedBy slot[${c.index}] <= witness[${c.witness_index}]`;
        case 'Witnessed': return `Witnessed ${c.predicate_kind || 'predicate'} ${shortHex(c.commitment, 10)}`;
        case 'PreimageGate': return `PreimageGate slot[${c.commitment_index}] ${c.hash_kind || ''}`.trim();
        case 'TemporalGate': return `TemporalGate ${c.not_before ?? '*'}..${c.not_after ?? '*'}`;
        default: return c.kind;
      }
    });
}

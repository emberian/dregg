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
.dregg-inspector__action-list { list-style: none; padding: 0; margin: 0; display: flex; flex-direction: column; gap: 4px; }
.dregg-inspector__action-row { display: flex; align-items: center; gap: 6px; min-width: 0; }
.dregg-inspector__action-index { color: var(--fg-dim, #9aa0a6); font-size: 0.75rem; min-width: 1.4em; }
.dregg-inspector__action-method { color: var(--fg-dim, #9aa0a6); font-size: 0.78rem; }
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
  .dregg-receipt__summary { grid-template-columns: repeat(2, minmax(0, 1fr)); }
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

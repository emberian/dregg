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
  }
  async connectedCallback() {
    const [api, runtime] = await Promise.all([ready(), findRuntime(this)]);
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
    el.innerHTML = `<div class="dregg-inspector dregg-inspector--err">bad ref: ${refAttr}</div>`;
    return true;
  }
  if (expectedKind && parsed.kind !== expectedKind) {
    el.innerHTML = `<div class="dregg-inspector dregg-inspector--err">wrong kind: ${parsed.kind} (expected ${expectedKind})</div>`;
    return true;
  }
  return false;
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

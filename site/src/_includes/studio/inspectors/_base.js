/**
 * Shared InspectorBase for all <pyana-*> inspector custom elements.
 *
 * Each subclass implements `_render()` which:
 *   - Reads `uri` attribute (a pyana:// URI). NEVER `ref` (Preact-reserved).
 *   - Reads `mode` (default | compact | inspector | raw).
 *   - Uses `this._api` (Preact + signals + htm) and `this._runtime`.
 *   - Tears down previous render via `this._dispose`.
 *   - Mounts new render into a fresh child via `effect(() => render(...))`.
 */

import { findRuntime } from '../context.js';

export function ready() {
  return new Promise(resolve => {
    if (window.pyanaUi) return resolve(window.pyanaUi);
    window.addEventListener('pyanaUi:ready', e => resolve(e.detail), { once: true });
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
    this._runtime = runtime;
    this._api = api;
    this._render();
  }
  attributeChangedCallback() {
    if (this._api) this._render();
  }
  disconnectedCallback() {
    if (this._dispose) this._dispose();
    if (this._unmount) this._unmount();
  }
  _render() { /* subclass override */ }
}

/** Render a parse error in-place; returns true if errored. */
export function renderParseError(el, refAttr, parsed, expectedKind) {
  if (!parsed) {
    el.innerHTML = `<div class="pyana-inspector pyana-inspector--err">bad ref: ${refAttr}</div>`;
    return true;
  }
  if (expectedKind && parsed.kind !== expectedKind) {
    el.innerHTML = `<div class="pyana-inspector pyana-inspector--err">wrong kind: ${parsed.kind} (expected ${expectedKind})</div>`;
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

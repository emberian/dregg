/**
 * <pyana-revocation-channel uri="pyana://revocation-channel/<id-hex>">
 *
 * Per-channel state + list (via list_revocation_channels stub + is_channel_active).
 * Create/trip affordances when mutate.
 *
 * Replaces tiered-revocation playground bits (retired).
 * Canonical: create_revocation_channel, trip_revocation_channel, is_channel_active.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, renderParseError, shortHex } from './_base.js';

class PyanaRevocationChannel extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;
    const handle = this._runtime?._handle;
    const caps = this._runtime?.caps || { mutate: true };

    let parsed = null;
    let inline = null;
    if (dataAttr) {
      try { inline = JSON.parse(dataAttr); } catch {}
    }
    if (!inline && refAttr) {
      try { parsed = parseRef(refAttr); } catch {}
      if (renderParseError(this, refAttr, parsed, 'revocation-channel')) return;
    }

    const listSignal = this._runtime?.listRevocationChannels ? this._runtime.listRevocationChannels() : null;

    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      let ch = inline;
      if (!ch && parsed) {
        const list = (listSignal && listSignal.value) || [];
        ch = list.find(c => c.channel_id === parsed.id) || { channel_id: parsed.id, active: true };
      }
      if (!ch && mode === 'compact') {
        return html`<span class="pyana-inspector pyana-inspector--compact">revocation-channel</span>`;
      }
      if (!ch) {
        return html`
          <div class="pyana-inspector pyana-inspector--revchan">
            <header><span class="pyana-inspector__kind">revocation-channel</span></header>
            <div style="font-size:0.8rem;color:var(--fg-dim);">No channel data. Use create affordance or data=.</div>
            ${caps.mutate && wasm ? html`<button data-act="create" style="margin-top:6px;font-size:0.75rem;">Create Channel (agent 0)</button>` : null}
          </div>`;
      }

      const status = ch.active ? html`<span style="color:#166534;">ACTIVE</span>` : html`<span style="color:#b91c1c;">TRIPPED</span>`;

      if (mode === 'compact') {
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            <code>${shortHex(ch.channel_id)}</code> ${ch.active ? 'active' : 'tripped'}
          </span>`;
      }

      const tripBtn = (caps.mutate && wasm && ch.active) ? html`
        <button data-act="trip" style="font-size:0.75rem;padding:2px 6px;">Trip Channel</button>
      ` : null;

      return html`
        <div class="pyana-inspector pyana-inspector--revchan">
          <header>
            <span class="pyana-inspector__kind">revocation-channel</span>
            <code class="pyana-inspector__id" title=${ch.channel_id}>${shortHex(ch.channel_id, 20)}</code>
          </header>
          <dl class="pyana-inspector__kv">
            <dt>channel id</dt><dd><code>${ch.channel_id}</code></dd>
            <dt>state</dt><dd>${status}</dd>
          </dl>
          ${tripBtn}
          <div style="font-size:0.7rem;color:var(--fg-dim);margin-top:6px;">
            Revocation channels are sovereign-cell primitives (pyana_cell::RevocationChannel). Trip emits to federation for consensus.
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm || !handle) return;
      const act = btn.dataset.act;
      if (act === 'create') {
        try {
          const res = wasm.create_revocation_channel(handle, 0);
          console.log('[pyana-revocation-channel] created', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn(err); }
      } else if (act === 'trip') {
        const id = (inline || (parsed ? {channel_id: parsed.id} : {})).channel_id;
        if (id) {
          try {
            const res = wasm.trip_revocation_channel(handle, 0, id);
            console.log('[pyana-revocation-channel] tripped', res);
            if (this._runtime?.version) this._runtime.version.value++;
          } catch (err) { console.warn(err); }
        }
      }
    });
  }
}
if (!customElements.get('pyana-revocation-channel')) customElements.define('pyana-revocation-channel', PyanaRevocationChannel);

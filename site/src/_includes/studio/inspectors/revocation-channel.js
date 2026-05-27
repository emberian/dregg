/**
 * <dregg-revocation-channel uri="dregg://revocation-channel/<id-hex>">
 *
 * Per-channel state + list via runtime.listRevocationChannels().
 * Lab create/trip affordances only appear with mode="lab" and mutate runtime.
 *
 * Replaces tiered-revocation playground bits (retired).
 * Canonical: create_revocation_channel, trip_revocation_channel, is_channel_active.
 */

import { parseRef } from '../uri.js';
import { InspectorBase, emptyState, renderParseError, shortHex } from './_base.js';

class DreggRevocationChannel extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const refAttr = this.getAttribute('uri');
    const dataAttr = this.getAttribute('data');
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    const wasm = this._runtime?._wasm || null;
    const handle = this._runtime?._handle;
    const caps = this._runtime?.caps || { mutate: false };

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
        ch = list.find(c => c.channel_id === parsed.id) || null;
      }
      if (!ch && mode === 'compact') {
        return html`<span class="dregg-inspector dregg-inspector--compact">revocation-channel</span>`;
      }
      if (!ch) {
        return html`<div class="dregg-inspector dregg-inspector--revchan">
          ${emptyState(html, 'Revocation channel not found', parsed
            ? html`No channel <code>${shortHex(parsed.id, 16)}</code> is present in this runtime.`
            : html`No channel data; provide <code>uri=</code> or <code>data=</code>.`)}
          ${mode === 'lab' && caps.mutate && wasm ? html`<div class="dregg-inspector__controls"><button class="dregg-inspector__button" data-act="create">Create channel via wasm</button></div>` : null}
        </div>`;
      }

      const stateLabel = ch.active === true ? 'active' : ch.active === false ? 'tripped' : 'unknown';
      const status = ch.active === true
        ? html`<span class="dregg-inspector__notice dregg-inspector__notice--ok">ACTIVE</span>`
        : ch.active === false
          ? html`<span class="dregg-inspector__notice dregg-inspector__notice--warn">TRIPPED</span>`
          : html`<span class="dregg-inspector__notice">unknown; awaiting channel state</span>`;

      if (mode === 'compact') {
        return html`
          <span class="dregg-inspector dregg-inspector--compact">
            <code>${shortHex(ch.channel_id)}</code> ${stateLabel}
          </span>`;
      }

      const tripBtn = mode === 'lab' && caps.mutate && wasm ? html`
        <div class="dregg-inspector__controls">
          <button class="dregg-inspector__button" data-act="trip" disabled=${!ch.active}>Trip via wasm</button>
        </div>
      ` : null;

      return html`
        <div class="dregg-inspector dregg-inspector--revchan">
          <header>
            <span class="dregg-inspector__kind">revocation-channel</span>
            <code class="dregg-inspector__id" title=${ch.channel_id}>${shortHex(ch.channel_id, 20)}</code>
            <span class="dregg-inspector__meta">${stateLabel}</span>
          </header>
          <div class="dregg-inspector__summary">
            <div><span>State</span><strong>${stateLabel}</strong></div>
            <div><span>Trip height</span><strong>${ch.trip_height ?? ch.tripped_at ?? 'n/a'}</strong></div>
            <div><span>Owner</span><strong>${ch.owner ? shortHex(ch.owner, 10) : 'unknown'}</strong></div>
          </div>
          <dl class="dregg-inspector__kv">
            <dt>channel id</dt><dd><code>${ch.channel_id}</code></dd>
            <dt>state</dt><dd>${status}</dd>
          </dl>
          ${tripBtn}
          <div class="dregg-inspector__note">
            Revocation channels are sovereign-cell primitives (dregg_cell::RevocationChannel). Trip emits to federation for consensus.
          </div>
        </div>`;
    };

    this._dispose = effect(() => render(h(Component, {}), root));

    root.addEventListener('click', (e) => {
      const btn = e.target.closest('button[data-act]');
      if (!btn || !wasm || !handle || mode !== 'lab') return;
      const act = btn.dataset.act;
      if (act === 'create') {
        try {
          const res = wasm.create_revocation_channel(handle, 0);
          console.log('[dregg-revocation-channel] created', res);
          if (this._runtime?.version) this._runtime.version.value++;
        } catch (err) { console.warn(err); }
      } else if (act === 'trip') {
        const id = (inline || (parsed ? {channel_id: parsed.id} : {})).channel_id;
        if (id) {
          try {
            const res = wasm.trip_revocation_channel(handle, 0, id);
            console.log('[dregg-revocation-channel] tripped', res);
            if (this._runtime?.version) this._runtime.version.value++;
          } catch (err) { console.warn(err); }
        }
      }
    });
  }
}
if (!customElements.get('dregg-revocation-channel')) customElements.define('dregg-revocation-channel', DreggRevocationChannel);

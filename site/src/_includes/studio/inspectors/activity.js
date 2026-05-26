/**
 * <pyana-activity> — live observability event feed inspector (Task #30).
 *
 * Subscribes to the runtime's signal-cached getTraceEvents() (which calls
 * the canonical wasm get_trace_events_json backed by pyana-observability
 * EventLog + Emitter). Pure rendering of Rust types — no JS reimplementation
 * of pyana (substrate rule).
 *
 * Renders all 7 TraceEvent variants using platform vocabulary:
 *   turn_lifecycle, authorization, sovereign_witness_verified,
 *   state_constraint_evaluated, bilateral_receipt, bilateral_rollup, federation.
 *
 * Sim runtime: events are Placeholder-tier (honest about scope-0).
 * Remote: will reflect the node's trust tier once node emits real events.
 *
 * Modes:
 *   compact — "N events • last: Turn Committed"
 *   default — scrollable timeline list with kind badges, envelope context,
 *             and variant-specific payload summary (KV or short desc).
 *
 * Usage (no uri needed; global to the runtime):
 *   <pyana-activity mode="default"></pyana-activity>
 */

import { InspectorBase, shortHex } from './_base.js';

// Kind labels + platform vocabulary (not raw Rust tags).
const KIND_LABELS = {
  turn_lifecycle: 'Turn Lifecycle',
  authorization: 'Authorization',
  sovereign_witness_verified: 'Sovereign Witness Verified',
  state_constraint_evaluated: 'State Constraint Evaluated',
  bilateral_receipt: 'Bilateral Receipt (γ.2)',
  bilateral_rollup: 'Bilateral Rollup',
  federation: 'Federation Event',
};

// Simple color badges (trust-tier aware: sim is always placeholder style).
const KIND_COLORS = {
  turn_lifecycle: { bg: '#ecfdf5', fg: '#065f46', border: '#10b981' },
  authorization: { bg: '#eff6ff', fg: '#1e40af', border: '#3b82f6' },
  sovereign_witness_verified: { bg: '#fef3c7', fg: '#92400e', border: '#f59e0b' },
  state_constraint_evaluated: { bg: '#f3e8ff', fg: '#6b21a8', border: '#a855f7' },
  bilateral_receipt: { bg: '#e0f2fe', fg: '#075985', border: '#0ea5e9' },
  bilateral_rollup: { bg: '#f0fdfa', fg: '#134e4a', border: '#14b8a6' },
  federation: { bg: '#fce7f3', fg: '#9d174d', border: '#ec4899' },
};

function kindBadge(kind, html) {
  const label = KIND_LABELS[kind] || kind;
  const c = KIND_COLORS[kind] || KIND_COLORS.turn_lifecycle;
  const style = `background:${c.bg};color:${c.fg};border:1px solid ${c.border};` +
    `padding:1px 6px;border-radius:3px;font-size:0.7rem;font-weight:600;letter-spacing:0.02em;`;
  return html`<span style=${style}>${label}</span>`;
}

// Trust tier badge (sim = Placeholder; remote can be Silver/Golden later).
function tierBadge(html) {
  return html`<span style="background:#f3f4f6;color:#374151;border:1px solid #d1d5db;padding:0 4px;border-radius:2px;font-size:0.65rem;margin-left:4px;">Placeholder (sim)</span>`;
}

// Render payload summary for each of the 7 variants (using platform vocab).
function renderPayload(kind, payload, html) {
  if (!payload) return html`<span style="color:var(--fg-dim)">no payload</span>`;

  if (kind === 'turn_lifecycle') {
    const p = payload;
    const phase = p.phase || 'unknown';
    if (phase === 'committed' || phase === 'Committed') {
      return html`
        <div>Committed • actions: ${String(p.action_count || 0)} • computrons: ${String(p.computrons_used || 0)}</div>
        <div style="font-size:0.7rem;color:var(--fg-dim)">receipt ${shortHex(p.receipt_hash, 12)} → post ${shortHex(p.post_state_hash, 8)}</div>
      `;
    }
    if (phase === 'rejected' || phase === 'Rejected') {
      return html`<div>Rejected: ${String(p.reason || 'unknown')} @ ${JSON.stringify(p.at_action || [])}</div>`;
    }
    if (phase === 'expired' || phase === 'Expired') {
      return html`<div>Expired (valid_until passed)</div>`;
    }
    return html`<div>${phase}</div>`;
  }

  if (kind === 'authorization') {
    const a = payload;
    const authKind = a.auth_kind || a.kind || 'unknown';
    return html`<div>Auth: ${authKind} ${a.token_hash ? shortHex(a.token_hash, 8) : ''}</div>`;
  }

  if (kind === 'sovereign_witness_verified') {
    const s = payload;
    return html`
      <div>Cell ${shortHex(s.cell_id, 8)} seq ${String(s.sequence)} • ${s.has_stark_proof ? 'STARK' : 're-exec'}</div>
      <div style="font-size:0.7rem">commit ${shortHex(s.new_commitment, 8)}</div>
    `;
  }

  if (kind === 'state_constraint_evaluated') {
    const c = payload;
    const status = c.accepted ? 'accepted' : 'rejected';
    return html`<div>${c.constraint_kind || '?'} @ slot ${String(c.slot_index)} → ${status}</div>`;
  }

  if (kind === 'bilateral_receipt') {
    const b = payload;
    return html`<div>${b.direction || '?'} • peer ${shortHex(b.peer_cell_id, 8)} amt ${b.amount != null ? b.amount : '—'}</div>`;
  }

  if (kind === 'bilateral_rollup') {
    const r = payload;
    const counts = r.counts || {};
    return html`<div>Rollup: ${Object.values(counts).reduce((a, v) => a + (v || 0), 0)} entries</div>`;
  }

  if (kind === 'federation') {
    const f = payload;
    const ev = f.event || f.kind || 'event';
    return html`<div>Fed ${ev} • epoch ${String(f.epoch_after || f.epoch || 0)}</div>`;
  }

  // Fallback for unknown/additive
  return html`<pre style="font-size:0.65rem;margin:0">${JSON.stringify(payload).slice(0, 200)}</pre>`;
}

class PyanaActivity extends InspectorBase {
  _render() {
    const { h, render, html, effect } = this._api;
    const mode = this.getAttribute('mode') || 'default';

    if (this._dispose) { this._dispose(); this._dispose = null; }
    this.replaceChildren();

    // Activity feed is runtime-global (no uri parse needed).
    const eventsSignal = this._runtime.getTraceEvents ? this._runtime.getTraceEvents() : null;
    const root = document.createElement('div');
    this.appendChild(root);

    const Component = () => {
      const data = eventsSignal ? eventsSignal.value : null;
      const evs = (data && data.events) || [];
      const count = data ? (data.event_count || evs.length) : 0;

      if (mode === 'compact') {
        const last = evs.length ? evs[evs.length - 1] : null;
        const lastKind = last ? (last.kind || '—') : '—';
        return html`
          <span class="pyana-inspector pyana-inspector--compact">
            ${count} events${tierBadge(html)} • last: ${lastKind}
          </span>`;
      }

      // Default: live scrolling feed
      if (!evs.length) {
        return html`
          <div class="pyana-inspector pyana-inspector--empty">
            No observability events yet. Execute turns to populate the live feed.
            ${tierBadge(html)}
          </div>`;
      }

      const items = evs.slice().reverse().map((e, i) => {  // newest first
        const k = e.kind || 'unknown';
        const env = e.envelope || {};
        const pl = e.payload || {};
        const ts = env.timestamp || '';
        const actor = env.actor ? shortHex(env.actor, 8) : '';
        return html`
          <div style="border-bottom:1px solid var(--line-faint,#222);padding:4px 0;display:flex;gap:8px;align-items:flex-start">
            <div style="flex:0 0 auto">${kindBadge(k, html)}</div>
            <div style="flex:1 1 auto;min-width:0">
              <div style="font-size:0.7rem;color:var(--fg-dim)">
                ${ts} ${actor ? `• actor ${actor}` : ''} ${env.seq != null ? `#${env.seq}` : ''}
              </div>
              <div style="margin-top:2px">
                ${renderPayload(k, pl, html)}
              </div>
            </div>
          </div>`;
      });

      return html`
        <div class="pyana-inspector pyana-inspector--activity" style="max-height:320px;overflow:auto;border:1px solid var(--line,#333);border-radius:4px;padding:4px;background:var(--bg-raised,#111)">
          <div style="display:flex;align-items:center;justify-content:space-between;padding:2px 6px 4px;font-size:0.75rem;color:var(--fg-dim)">
            <span>Live Activity Feed ${tierBadge(html)}</span>
            <span>${count} events</span>
          </div>
          ${items}
        </div>`;
    };

    this._dispose = effect(() => {
      render(h(Component, {}), root);
    });
  }
}
if (!customElements.get('pyana-activity')) customElements.define('pyana-activity', PyanaActivity);

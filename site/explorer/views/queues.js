/**
 * Queues view — programmable / blinded / inbox.
 *
 * Anonymous reads: summary rows only (name, depth, root, vk_hash).
 * Admin reads: full entries (gated by api.runWithAuth → auth-dialog).
 *
 * Visualizer reuse: the detail panel embeds a `<dregg-vizzer>` element per
 * family (`programmable-queue`, `blinded-queue`, `inbox-lifecycle`); the
 * matching modules are loaded as <script type="module"> from explorer
 * index.html and self-register via runtime-bootstrap's `dreggUi:ready` event.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';
import { runWithAuth } from '../components/auth-dialog.js';

export const name = 'queues';

let container = null;
let activeTab = 'programmable';
let cachedSummaries = { programmable: null, blinded: null, inbox: null };
let loadError = '';

export function init(el) {
  container = el;
  const tabs = el.querySelectorAll('.ex-subtab');
  tabs.forEach(btn => {
    btn.addEventListener('click', () => switchTab(btn.dataset.subtab));
    btn.addEventListener('keydown', (e) => {
      const order = ['programmable', 'blinded', 'inbox'];
      const i = order.indexOf(activeTab);
      if (e.key === 'ArrowRight') switchTab(order[(i + 1) % order.length]);
      else if (e.key === 'ArrowLeft') switchTab(order[(i - 1 + order.length) % order.length]);
      else if (e.key === 'Home') switchTab(order[0]);
      else if (e.key === 'End') switchTab(order[order.length - 1]);
    });
  });

  const closeBtn = document.getElementById('queue-detail-close');
  closeBtn?.addEventListener('click', closeDetail);

  // Initial render
  load();
}

export function update() {
  if (state.currentPage === 'queues') load();
}

export function destroy() {}

function switchTab(tab) {
  if (!['programmable', 'blinded', 'inbox'].includes(tab)) return;
  activeTab = tab;
  container.querySelectorAll('.ex-subtab').forEach(b => {
    const sel = b.dataset.subtab === tab;
    b.classList.toggle('active', sel);
    b.setAttribute('aria-selected', sel ? 'true' : 'false');
  });
  render();
}

async function load() {
  let services = [];
  loadError = '';
  try {
    services = await api.listServices();
  } catch (e) {
    cachedSummaries = { programmable: [], blinded: [], inbox: [] };
    loadError = e?.message || 'Service registry endpoint is unavailable.';
    render();
    return;
  }

  // Pull summaries for each family in parallel — fail-soft per service.
  cachedSummaries.programmable = await Promise.all(services.map(s =>
    api.getProgrammableQueue(svcName(s)).catch(() => null).then(d => withServiceName(d, s, 'programmable'))
  ));
  cachedSummaries.blinded = await Promise.all(services.map(s =>
    api.getBlindedQueue(svcName(s)).catch(() => null).then(d => withServiceName(d, s, 'blinded'))
  ));
  cachedSummaries.inbox = await Promise.all(services.map(s =>
    api.getInboxQueue(svcName(s)).catch(() => null).then(d => withServiceName(d, s, 'inbox'))
  ));

  for (const k of Object.keys(cachedSummaries)) {
    cachedSummaries[k] = (cachedSummaries[k] || []).filter(Boolean);
  }
  render();
}

function svcName(s) { return typeof s === 'string' ? s : (s.name || s.id || ''); }
function withServiceName(data, s, family) {
  if (!data) return null;
  return { service: svcName(s), family, ...data };
}

function render() {
  const root = document.getElementById('queues-content');
  if (!root) return;
  if (loadError) {
    root.innerHTML = `<div class="empty-state">No live queue data from this node.<br><span class="ex-hint">${escapeHtml(loadError)}</span></div>`;
    return;
  }
  const rows = cachedSummaries[activeTab] || [];
  if (!rows.length) {
    root.innerHTML = '<div class="empty-state">No queues reported for this family.</div>';
    return;
  }
  root.innerHTML = `
    <div class="ex-table-container">
      <table class="ex-table">
        <thead>
          <tr>
            <th>Service</th>
            <th>Name</th>
            <th>Depth</th>
            <th>Root</th>
            <th>${activeTab === 'inbox' ? 'TTL / Deposit' : 'vk_hash'}</th>
            <th></th>
          </tr>
        </thead>
        <tbody>
          ${rows.map((r, i) => `
            <tr class="ex-table__row" data-row="${i}">
              <td>${escapeHtml(r.service || '--')}</td>
              <td>${escapeHtml(r.name || '--')}</td>
              <td>${api.formatNumber(r.depth ?? r.leaves_count ?? 0)}</td>
              <td class="mono">${api.shortHash(r.root, 10, 6)}</td>
              <td class="mono">${activeTab === 'inbox'
                ? `${r.ttl_secs ?? '--'}s / ${r.deposit_min ?? '--'}`
                : api.shortHash(r.vk_hash, 10, 6)}</td>
              <td><button class="btn btn-secondary btn-sm" data-action="drill" data-row="${i}">Inspect</button></td>
            </tr>
          `).join('')}
        </tbody>
      </table>
    </div>
  `;
  root.querySelectorAll('[data-action="drill"]').forEach(btn => {
    btn.addEventListener('click', () => openDetail(rows[parseInt(btn.dataset.row, 10)]));
  });
}

function openDetail(row) {
  if (!row) return;
  const panel = document.getElementById('queue-detail');
  const body = document.getElementById('queue-detail-content');
  if (!panel || !body) return;
  panel.hidden = false;

  const vizName = row.family === 'blinded' ? 'blinded-queue'
                : row.family === 'inbox'   ? 'inbox-lifecycle'
                : 'programmable-queue';

  body.innerHTML = `
    <h3>${escapeHtml(row.service)} / ${escapeHtml(row.name || '')}</h3>
    <dl class="dregg-kv">
      <dt>Family</dt><dd>${row.family}</dd>
      <dt>Depth</dt><dd>${api.formatNumber(row.depth ?? row.leaves_count ?? 0)}</dd>
      <dt>Root</dt><dd class="mono">${row.root || '--'}</dd>
      ${row.vk_hash ? `<dt>vk_hash</dt><dd class="mono">${row.vk_hash}</dd>` : ''}
      ${row.nullifier_count !== undefined ? `<dt>Nullifiers</dt><dd>${api.formatNumber(row.nullifier_count)}</dd>` : ''}
      ${row.deposit_min ? `<dt>Anti-spam deposit</dt><dd>${row.deposit_min}</dd>` : ''}
      ${row.ttl_secs ? `<dt>TTL</dt><dd>${row.ttl_secs}s</dd>` : ''}
    </dl>

    <h4>Visualization</h4>
    <dregg-vizzer data-vizzer="${vizName}"
                  data-service="${escapeAttr(row.service)}"
                  data-name="${escapeAttr(row.name || '')}"
                  data-root="${escapeAttr(row.root || '')}">
      <div class="vizzer-fallback">
        Static summary: depth ${row.depth ?? row.leaves_count ?? 0},
        root ${api.shortHash(row.root)}.
      </div>
    </dregg-vizzer>

    <h4>Entries</h4>
    <div id="queue-entries-host">
      <button class="btn btn-primary" id="queue-load-entries">Load entries (admin)</button>
      <p class="ex-hint">Anonymous endpoint only exposes counts. Loading entries requires an admin bearer token.</p>
    </div>
  `;

  // Re-mount visualizers in this newly-injected subtree.
  if (window.dreggUi?.mount) {
    try { window.dreggUi.mount(body); } catch (e) { console.warn('[queues] mount failed', e); }
  }

  document.getElementById('queue-load-entries')?.addEventListener('click', () => loadEntries(row));
}

async function loadEntries(row) {
  const host = document.getElementById('queue-entries-host');
  if (!host) return;
  host.innerHTML = '<div class="loading-placeholder">Requesting entries...</div>';
  const fn = row.family === 'blinded' ? api.getBlindedQueueEntries
           : row.family === 'inbox'   ? api.getInboxQueueEntries
           :                            api.getProgrammableQueueEntries;
  try {
    const entries = await runWithAuth(() => fn(row.service));
    if (!entries || !entries.length) {
      host.innerHTML = '<div class="dregg-empty">Queue is empty.</div>';
      return;
    }
    host.innerHTML = `
      <table class="ex-table">
        <thead><tr><th>#</th><th>Commitment / payload</th><th>Status</th></tr></thead>
        <tbody>
          ${entries.slice(0, 100).map((e, i) => `
            <tr>
              <td>${i}</td>
              <td class="mono">${api.shortHash(e.commitment || e.payload_hash || '', 14, 6)}</td>
              <td><span class="dregg-pill" data-state="${pillStateFor(e)}">${escapeHtml(e.status || 'live')}</span></td>
            </tr>
          `).join('')}
        </tbody>
      </table>
      ${entries.length > 100 ? `<p class="ex-hint">Showing first 100 of ${entries.length}.</p>` : ''}
    `;
  } catch (e) {
    if (e.message === 'auth cancelled') {
      host.innerHTML = '<div class="dregg-empty">Auth cancelled — counts only.</div>';
    } else {
      host.innerHTML = `<div class="dregg-empty">Failed to load entries: ${escapeHtml(e.message || String(e))}</div>`;
    }
  }
}

function pillStateFor(e) {
  if (e.consumed) return 'muted';
  if (e.status === 'rejected' || e.status === 'expired') return 'err';
  if (e.status === 'pending') return 'warn';
  return undefined;
}

function closeDetail() {
  const panel = document.getElementById('queue-detail');
  if (panel) panel.hidden = true;
}

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, c => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
  }[c]));
}
function escapeAttr(s) { return escapeHtml(s); }

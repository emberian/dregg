/**
 * Names view — nameservice browser.
 *
 * Anonymous: list/search/sort by prefix, tag, expiry.
 * Click a row → resolve to dregg:// URI + status pill.
 * Embeds <dregg-vizzer data-vizzer="nameservice-registration"> in the detail
 * panel; the module is loaded by explorer/index.html and self-registers.
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'names';

let container = null;
let cached = null;
let searchEl, sortEl, filterEl;
let loadError = '';

export function init(el) {
  container = el;
  searchEl = document.getElementById('names-search');
  sortEl   = document.getElementById('names-sort');
  filterEl = document.getElementById('names-filter');

  const onChange = () => load();
  searchEl?.addEventListener('input', debounce(onChange, 200));
  sortEl?.addEventListener('change', render);
  filterEl?.addEventListener('change', onChange);

  document.getElementById('name-detail-close')?.addEventListener('click', () => {
    const p = document.getElementById('name-detail');
    if (p) p.hidden = true;
  });

  load();
}

export function update() {
  if (state.currentPage === 'names') load();
}
export function destroy() {}

async function load() {
  const prefix = searchEl?.value?.trim() || '';
  const tag    = filterEl?.value || '';
  loadError = '';
  try {
    cached = await api.listNames({ prefix, tag });
  } catch {
    cached = [];
    loadError = 'Nameservice endpoint is unavailable on this node.';
  }
  render();
}

function render() {
  const root = document.getElementById('names-content');
  if (!root) return;
  if (loadError) {
    root.innerHTML = `<div class="empty-state">No live nameservice data from this node.<br><span class="ex-hint">${escapeHtml(loadError)}</span></div>`;
    return;
  }
  let rows = (cached || []).slice();
  const sort = sortEl?.value || 'name';
  rows.sort((a, b) => {
    if (sort === 'expiry')    return (a.expires_at || 0) - (b.expires_at || 0);
    if (sort === 'recent')    return (b.registered_at || 0) - (a.registered_at || 0);
    return a.name.localeCompare(b.name);
  });
  if (!rows.length) {
    root.innerHTML = '<div class="dregg-empty">No names match the current filter.</div>';
    return;
  }
  root.innerHTML = `
    <div class="ex-table-container">
      <table class="ex-table">
        <thead>
          <tr><th>Name</th><th>Status</th><th>Owner</th><th>Expires</th><th>Tags</th><th></th></tr>
        </thead>
        <tbody>
          ${rows.map((n, i) => {
            const st = statusOf(n);
            return `
              <tr class="ex-table__row" data-row="${i}">
                <td class="mono">${escapeHtml(n.name)}</td>
                <td><span class="dregg-pill" data-state="${pillFor(st)}">${st}</span></td>
                <td class="mono">${api.shortHash(n.owner)}</td>
                <td>${n.expires_at ? api.relativeTime(n.expires_at) : '--'}</td>
                <td>${(n.tags || []).map(t => `<span class="dregg-pill" data-state="muted">${escapeHtml(t)}</span>`).join(' ')}</td>
                <td><button class="btn btn-secondary btn-sm" data-action="resolve" data-row="${i}">Resolve</button></td>
              </tr>
            `;
          }).join('')}
        </tbody>
      </table>
    </div>
  `;
  root.querySelectorAll('[data-action="resolve"]').forEach(btn => {
    btn.addEventListener('click', () => openDetail(rows[parseInt(btn.dataset.row, 10)]));
  });
}

async function openDetail(row) {
  if (!row) return;
  const panel = document.getElementById('name-detail');
  const body  = document.getElementById('name-detail-content');
  if (!panel || !body) return;
  panel.hidden = false;
  body.innerHTML = '<div class="loading-placeholder">Resolving...</div>';

  let resolved = null;
  try { resolved = await api.resolveName(row.name); }
  catch { resolved = { uri: row.uri, ...row, status: statusOf(row) }; }

  const st = resolved.status || statusOf(row);

  body.innerHTML = `
    <h3>${escapeHtml(row.name)}</h3>
    <dl class="dregg-kv">
      <dt>URI</dt><dd class="mono">${escapeHtml(resolved.uri || '--')}</dd>
      <dt>Status</dt><dd><span class="dregg-pill" data-state="${pillFor(st)}">${escapeHtml(st)}</span></dd>
      <dt>Owner</dt><dd class="mono">${escapeHtml(resolved.owner || '--')}</dd>
      <dt>Registered</dt><dd>${resolved.registered_at ? api.formatTime(resolved.registered_at) : '--'}</dd>
      <dt>Expires</dt><dd>${resolved.expires_at ? api.formatTime(resolved.expires_at) : '--'}</dd>
      ${(resolved.tags && resolved.tags.length) ? `<dt>Tags</dt><dd>${resolved.tags.map(escapeHtml).join(', ')}</dd>` : ''}
    </dl>

    <h4>Registration lifecycle</h4>
    <dregg-vizzer data-vizzer="nameservice-registration"
                  data-name="${escapeAttr(row.name)}"
                  data-status="${escapeAttr(st)}">
      <div class="vizzer-fallback">
        register → resolve → renew → expire timeline for "${escapeHtml(row.name)}".
      </div>
    </dregg-vizzer>
  `;
  if (window.dreggUi?.mount) {
    try { window.dreggUi.mount(body); } catch (e) { console.warn('[names] mount failed', e); }
  }
}

function statusOf(n) {
  if (n.status) return n.status;
  const now = Math.floor(Date.now() / 1000);
  if (n.disputed) return 'disputed';
  if (!n.expires_at) return 'active';
  if (now > n.expires_at) return 'expired';
  if (now > n.expires_at - 86400 * 7) return 'grace';
  return 'active';
}

function pillFor(status) {
  return ({ active: undefined, grace: 'warn', expired: 'err', disputed: 'err' })[status] ?? 'muted';
}

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, c => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;'
  }[c]));
}
function escapeAttr(s) { return escapeHtml(s); }

function debounce(fn, ms) {
  let t = null;
  return (...args) => { clearTimeout(t); t = setTimeout(() => fn(...args), ms); };
}

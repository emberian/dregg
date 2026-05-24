/**
 * Names view — nameservice browser.
 *
 * Anonymous: list/search/sort by prefix, tag, expiry.
 * Click a row → resolve to pyana:// URI + status pill.
 * Embeds <pyana-vizzer data-vizzer="nameservice-registration"> in the detail
 * panel (Builder A wires the visualizer; until then the fallback content
 * renders).
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'names';

let container = null;
let cached = null;
let searchEl, sortEl, filterEl;

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
  try {
    cached = await api.listNames({ prefix, tag });
  } catch {
    cached = null;
  }
  if (!cached || !cached.length) {
    cached = mockNames();
    if (prefix) cached = cached.filter(n => n.name.startsWith(prefix));
    if (tag) cached = cached.filter(n => statusOf(n) === tag);
  }
  render();
}

function render() {
  const root = document.getElementById('names-content');
  if (!root) return;
  let rows = (cached || []).slice();
  const sort = sortEl?.value || 'name';
  rows.sort((a, b) => {
    if (sort === 'expiry')    return (a.expires_at || 0) - (b.expires_at || 0);
    if (sort === 'recent')    return (b.registered_at || 0) - (a.registered_at || 0);
    return a.name.localeCompare(b.name);
  });
  if (!rows.length) {
    root.innerHTML = '<div class="pyana-empty">No names match the current filter.</div>';
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
                <td><span class="pyana-pill" data-state="${pillFor(st)}">${st}</span></td>
                <td class="mono">${api.shortHash(n.owner)}</td>
                <td>${n.expires_at ? api.relativeTime(n.expires_at) : '--'}</td>
                <td>${(n.tags || []).map(t => `<span class="pyana-pill" data-state="muted">${escapeHtml(t)}</span>`).join(' ')}</td>
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
    <dl class="pyana-kv">
      <dt>URI</dt><dd class="mono">${escapeHtml(resolved.uri || '--')}</dd>
      <dt>Status</dt><dd><span class="pyana-pill" data-state="${pillFor(st)}">${escapeHtml(st)}</span></dd>
      <dt>Owner</dt><dd class="mono">${escapeHtml(resolved.owner || '--')}</dd>
      <dt>Registered</dt><dd>${resolved.registered_at ? api.formatTime(resolved.registered_at) : '--'}</dd>
      <dt>Expires</dt><dd>${resolved.expires_at ? api.formatTime(resolved.expires_at) : '--'}</dd>
      ${(resolved.tags && resolved.tags.length) ? `<dt>Tags</dt><dd>${resolved.tags.map(escapeHtml).join(', ')}</dd>` : ''}
    </dl>

    <h4>Registration lifecycle</h4>
    <!-- VIZZER_TODO: nameservice-registration — playground registers this. -->
    <pyana-vizzer data-vizzer="nameservice-registration"
                  data-name="${escapeAttr(row.name)}"
                  data-status="${escapeAttr(st)}">
      <div class="vizzer-fallback">
        nameservice-registration visualizer pending — would animate
        register → resolve → renew → expire for "${escapeHtml(row.name)}".
      </div>
    </pyana-vizzer>
  `;
  if (window.pyana?.mount) {
    try { window.pyana.mount(body); } catch (e) { console.warn('[names] mount failed', e); }
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

// =============================================================================
// Mock data
// =============================================================================
function mockNames() {
  const now = Math.floor(Date.now() / 1000);
  return [
    { name: 'alice.pyana',      owner: 'aa11bb22cc33dd44ee55ff6677889900', uri: 'pyana://alice', registered_at: now - 86400 * 30, expires_at: now + 86400 * 30,  tags: ['user'] },
    { name: 'gallery.app',      owner: 'bbcc11223344556677889900aabbccdd', uri: 'pyana://gallery', registered_at: now - 86400 * 90, expires_at: now + 86400 * 100, tags: ['app', 'production'] },
    { name: 'devnet.federation',owner: '11223344556677889900aabbccddeeff', uri: 'pyana://federation/devnet', registered_at: now - 86400 * 365, expires_at: now + 86400 * 365, tags: ['federation'] },
    { name: 'old.example',      owner: '99887766554433221100ffeeddccbbaa', uri: 'pyana://example/old',       registered_at: now - 86400 * 400, expires_at: now - 86400 * 5,   tags: ['user'] },
    { name: 'dispute.test',     owner: 'ddeeff001122334455667788aabbccdd', uri: 'pyana://test/dispute',      registered_at: now - 86400 * 10,  expires_at: now + 86400 * 100, tags: ['user'], disputed: true },
    { name: 'renewal.example',  owner: 'cafe1234deadbeef0011223344556677', uri: 'pyana://example/renewal',   registered_at: now - 86400 * 60,  expires_at: now + 86400 * 3,   tags: ['user'] },
  ];
}

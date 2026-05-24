/**
 * Delegations view — known signed-delegation chains.
 *
 * Row: delegator → delegatee + restrictions + envelope-hash + authority policy.
 * Click → signed payload tree (vizzer: delegation-envelope-v2).
 */

import { bus, state } from '../app.js';
import * as api from '../api.js';

export const name = 'delegations';

let container = null;
let cached = null;
let searchEl;

export function init(el) {
  container = el;
  searchEl = document.getElementById('delegations-search');
  searchEl?.addEventListener('input', debounce(() => load(), 200));

  document.getElementById('delegation-detail-close')?.addEventListener('click', () => {
    const p = document.getElementById('delegation-detail');
    if (p) p.hidden = true;
  });

  load();
}

export function update() {
  if (state.currentPage === 'delegations') load();
}
export function destroy() {}

async function load() {
  const q = searchEl?.value?.trim() || '';
  try { cached = await api.listDelegations({ q }); }
  catch { cached = null; }
  if (!cached || !cached.length) {
    cached = mockDelegations();
    if (q) cached = cached.filter(d =>
      d.delegator.includes(q) || d.delegatee.includes(q) || (d.cap_id || '').includes(q)
    );
  }
  render();
}

function render() {
  const root = document.getElementById('delegations-content');
  if (!root) return;
  if (!cached || !cached.length) {
    root.innerHTML = '<div class="pyana-empty">No delegations found.</div>';
    return;
  }
  root.innerHTML = `
    <div class="ex-table-container">
      <table class="ex-table">
        <thead>
          <tr>
            <th>Chain</th>
            <th>Caveats</th>
            <th>Authority</th>
            <th>Envelope</th>
            <th></th>
          </tr>
        </thead>
        <tbody>
          ${cached.map((d, i) => `
            <tr class="ex-table__row" data-row="${i}">
              <td class="mono">
                <span class="pyana-hash-badge" style="--hash-color:${swatchFor(d.delegator)}">${api.shortHash(d.delegator)}</span>
                <span aria-hidden="true">&nbsp;→&nbsp;</span>
                <span class="pyana-hash-badge" style="--hash-color:${swatchFor(d.delegatee)}">${api.shortHash(d.delegatee)}</span>
              </td>
              <td>${(d.caveats || []).map(c => `<span class="pyana-pill" data-state="muted">${escapeHtml(c)}</span>`).join(' ') || '<span class="ex-hint">none</span>'}</td>
              <td><span class="pyana-pill" data-state="${policyPill(d.authority_policy)}">${escapeHtml(d.authority_policy || 'unsigned')}</span></td>
              <td class="mono">${api.shortHash(d.envelope_hash, 10, 6)}</td>
              <td><button class="btn btn-secondary btn-sm" data-action="detail" data-row="${i}">Open</button></td>
            </tr>
          `).join('')}
        </tbody>
      </table>
    </div>
  `;
  root.querySelectorAll('[data-action="detail"]').forEach(btn => {
    btn.addEventListener('click', () => openDetail(cached[parseInt(btn.dataset.row, 10)]));
  });
}

async function openDetail(row) {
  if (!row) return;
  const panel = document.getElementById('delegation-detail');
  const body  = document.getElementById('delegation-detail-content');
  if (!panel || !body) return;
  panel.hidden = false;
  body.innerHTML = '<div class="loading-placeholder">Loading envelope...</div>';

  let env = null;
  try { env = await api.getDelegation(row.id || row.envelope_hash); } catch { env = row; }

  body.innerHTML = `
    <h3>Delegation envelope</h3>
    <dl class="pyana-kv">
      <dt>Delegator</dt><dd class="mono">${escapeHtml(env.delegator || '--')}</dd>
      <dt>Delegatee</dt><dd class="mono">${escapeHtml(env.delegatee || '--')}</dd>
      <dt>Capability</dt><dd class="mono">${escapeHtml(env.cap_id || '--')}</dd>
      <dt>Authority policy</dt><dd><span class="pyana-pill" data-state="${policyPill(env.authority_policy)}">${escapeHtml(env.authority_policy || 'unsigned')}</span></dd>
      <dt>Envelope hash</dt><dd class="mono">${escapeHtml(env.envelope_hash || '--')}</dd>
      <dt>Signed at</dt><dd>${env.signed_at ? api.formatTime(env.signed_at) : '--'}</dd>
      ${env.revoked_at ? `<dt>Revoked at</dt><dd>${api.formatTime(env.revoked_at)}</dd>` : ''}
    </dl>

    <h4>Restrictions / caveats</h4>
    ${(env.caveats && env.caveats.length)
      ? `<ul class="ex-list">${env.caveats.map(c => `<li class="mono">${escapeHtml(typeof c === 'string' ? c : JSON.stringify(c))}</li>`).join('')}</ul>`
      : '<p class="ex-hint">No caveats — delegation passes the full authority through.</p>'}

    <h4>Signed payload tree</h4>
    <!-- VIZZER_TODO: delegation-envelope-v2 — Builder A registers this. -->
    <pyana-vizzer data-vizzer="delegation-envelope-v2"
                  data-envelope-hash="${escapeAttr(env.envelope_hash || '')}"
                  data-cap-id="${escapeAttr(env.cap_id || '')}">
      <div class="vizzer-fallback">
        delegation-envelope-v2 visualizer pending — would render the signed
        payload tree, show which fields are signature-bound, and overlay
        the v2 authority-policy decision graph.
      </div>
    </pyana-vizzer>
  `;
  if (window.pyana?.mount) {
    try { window.pyana.mount(body); } catch (e) { console.warn('[delegations] mount failed', e); }
  }
}

function policyPill(p) {
  if (!p || p === 'unsigned') return 'err';
  if (p === 'attenuated') return 'warn';
  if (p === 'restricted') return 'warn';
  return undefined;
}

function swatchFor(hex) {
  if (!hex) return 'var(--fg-muted)';
  const n = parseInt(hex.slice(0, 6), 16) || 0;
  return ['#5b8a5a', '#c49245', '#6ba3c7', '#d4685c', '#9cc08a'][n % 5];
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
function mockDelegations() {
  const now = Math.floor(Date.now() / 1000);
  return [
    {
      id: 'd-001',
      delegator: 'aa11bb22cc33dd44ee55ff66',
      delegatee: 'bb22cc33dd44ee55ff667788',
      cap_id:    'cap-gallery-bid',
      caveats:   ['amount<=100', 'until=2026-12-31'],
      authority_policy: 'attenuated',
      envelope_hash: '5b8a5a4f7c0d8b1e2f3a4b5c6d7e8f90deadbeefcafe0011',
      signed_at: now - 86400 * 3,
    },
    {
      id: 'd-002',
      delegator: 'ccddeeff00112233445566778899aabb',
      delegatee: 'ddee0011223344556677889900aabbcc',
      cap_id:    'cap-vault-withdraw',
      caveats:   ['multisig_required'],
      authority_policy: 'restricted',
      envelope_hash: '9bb87a5e6a7c8d9e0f1234567890abcdfeedfacecafebabe',
      signed_at: now - 86400 * 14,
    },
    {
      id: 'd-003',
      delegator: 'feedfacecafebabe0123456789abcdef',
      delegatee: '0123456789abcdef0123456789abcdef',
      cap_id:    'cap-nameservice-register',
      caveats:   [],
      authority_policy: 'full',
      envelope_hash: 'd4685c11223344556677889900112233aabbccddeeff0011',
      signed_at: now - 86400 * 60,
    },
  ];
}

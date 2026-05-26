// starbridge-apps/governed-namespace/pages/inspectors.js
//
// Web components for the starbridge-governed-namespace app:
//
//   <dregg-namespace uri="...">             — live cell summary
//   <dregg-namespace-route-table uri="..."> — DFA route table viewer +
//                                             editor (add/remove rows)
//   <dregg-namespace-proposal uri="...">    — propose / vote / commit /
//                                             register UI with status,
//                                             vote-tally visualization,
//                                             and per-step receipts
//   <dregg-namespace-dispatch uri="...">    — path → target lookup form
//
// All policy lives in Rust (starbridge-apps/governed-namespace/src/lib.rs);
// JS is the thinnest UX layer. Mutations route through
// `window.dreggTurnBuilders['governed-namespace']` (the cipherclerk-
// named builder presets) which terminate in window.dregg.signTurn.
//
// Slot indices mirror constants in src/lib.rs:
//   ROUTE_TABLE_ROOT_SLOT          = 0
//   VERSION_SLOT                   = 1
//   GOVERNANCE_COMMITTEE_ROOT_SLOT = 2
//   THRESHOLD_SLOT                 = 3
//   DISPUTE_WINDOW_HEIGHT_SLOT     = 4
//   PENDING_PROPOSAL_ROOT_SLOT     = 5

const ROUTE_TABLE_ROOT_SLOT = 0;
const VERSION_SLOT = 1;
const GOVERNANCE_COMMITTEE_ROOT_SLOT = 2;
const THRESHOLD_SLOT = 3;
const DISPUTE_WINDOW_HEIGHT_SLOT = 4;
const PENDING_PROPOSAL_ROOT_SLOT = 5;

// Method names — must match the Rust `symbol(...)` arguments.
const METHOD_PROPOSE  = 'propose_table_update';
const METHOD_VOTE     = 'vote_on_proposal';
const METHOD_COMMIT   = 'commit_table_update';
const METHOD_REGISTER = 'register_service';

// Vote-kind tag bytes — matches `VoteKind::tag_field()` in src/lib.rs.
const VOTE_TAG_APPROVE = 1;
const VOTE_TAG_REJECT  = 2;

const POLL_INTERVAL_MS = 6_000;

// ─── helpers ─────────────────────────────────────────────────────────────

function escapeHtml(s) {
  return String(s ?? '').replace(/[&<>"']/g, (c) => ({
    '&': '&amp;', '<': '&lt;', '>': '&gt;', '"': '&quot;', "'": '&#39;',
  })[c]);
}

function u64BE(n) {
  const out = new Uint8Array(32);
  let v = BigInt(n);
  for (let i = 31; i >= 24 && v > 0n; i--) {
    out[i] = Number(v & 0xffn);
    v >>= 8n;
  }
  return out;
}

function fieldToU64BE(bytes) {
  let v = 0n;
  for (let i = 24; i < 32; i++) {
    v = (v << 8n) | BigInt(bytes?.[i] ?? 0);
  }
  return Number(v);
}

function hex(bytes) {
  return Array.from(bytes ?? [], (b) => b.toString(16).padStart(2, '0')).join('');
}

function fieldShort(bytes, head = 8, tail = 4) {
  const h = hex(bytes);
  if (h.length <= head + tail + 1) return h;
  return `${h.slice(0, head)}…${h.slice(-tail)}`;
}

function isZero(bytes) {
  return Array.from(bytes ?? []).every((b) => b === 0);
}

async function blake3Field(input) {
  if (typeof window !== 'undefined' && window.dregg?.blake3) {
    return window.dregg.blake3(input);
  }
  const enc = typeof input === 'string' ? new TextEncoder().encode(input) : input;
  const buf = await crypto.subtle.digest('SHA-256', enc);
  return new Uint8Array(buf);
}

function describeTarget(target) {
  if (!target) return '—';
  if (target.Handler !== undefined) return `Handler(${escapeHtml(target.Handler)})`;
  if (target.Drop !== undefined) return 'Drop';
  if (target.Federation !== undefined) {
    const id = target.Federation.group_id || target.Federation;
    return `Federation(${escapeHtml(fieldShort(id))})`;
  }
  if (target.Userspace !== undefined) {
    return `Userspace(${escapeHtml(target.Userspace.kind)}, ${target.Userspace.payload?.length ?? 0}b)`;
  }
  return escapeHtml(JSON.stringify(target));
}

// =========================================================================
// <dregg-namespace> — browse view
// =========================================================================

class NamespaceInspector extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._state = null;
    this._error = null;
    this._loading = true;
    this._poll = null;
  }

  connectedCallback() {
    this.refresh();
    this._poll = setInterval(() => this.refresh(), POLL_INTERVAL_MS);
  }
  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
  }
  attributeChangedCallback() { this.refresh(); }

  async refresh() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.dregg?.readCell) {
      this._loading = false;
      this.render();
      return;
    }
    try {
      const cell = await window.dregg.readCell(uri);
      this._state = cell?.state ?? null;
      this._error = null;
    } catch (e) {
      this._error = String(e);
    }
    this._loading = false;
    this.render();
  }

  render() {
    const f = this._state?.fields;
    const tableRoot = f ? fieldShort(f[ROUTE_TABLE_ROOT_SLOT]) : '—';
    const version = f ? fieldToU64BE(f[VERSION_SLOT]) : '—';
    const committee = f ? fieldShort(f[GOVERNANCE_COMMITTEE_ROOT_SLOT]) : '—';
    const threshold = f ? fieldToU64BE(f[THRESHOLD_SLOT]) : '—';
    const windowH = f ? fieldToU64BE(f[DISPUTE_WINDOW_HEIGHT_SLOT]) : '—';
    const pending = f
      ? isZero(f[PENDING_PROPOSAL_ROOT_SLOT])
        ? '(none)'
        : fieldShort(f[PENDING_PROPOSAL_ROOT_SLOT])
      : '—';
    const hasPending = f && !isZero(f[PENDING_PROPOSAL_ROOT_SLOT]);

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: monospace; padding: 1em; }
        .dregg-namespace-summary {
          display: grid;
          grid-template-columns: max-content 1fr;
          gap: 0.4em 1em;
          max-width: 720px;
        }
        .dregg-namespace-summary dt { font-weight: bold; color: #335; }
        .dregg-namespace-summary dd { margin: 0; }
        .dregg-namespace-error { color: #b00; }
        .dregg-namespace-badge {
          display: inline-block;
          padding: 0.1em 0.5em;
          border-radius: 3px;
          font-size: 0.85em;
          font-weight: 700;
        }
        .dregg-namespace-badge-pending {
          background: #ffe7ab;
          color: #6b4500;
        }
        .dregg-namespace-badge-quiet {
          background: #e5e7eb;
          color: #444;
        }
      </style>
      <h2>Governed Namespace</h2>
      ${this._loading ? `<dregg-status-bar state="loading" message="loading cell…"></dregg-status-bar>` : ''}
      ${this._error ? `<div class="dregg-namespace-error">${escapeHtml(this._error)}</div>` : ''}
      <dl class="dregg-namespace-summary">
        <dt>state</dt><dd>
          <span class="dregg-namespace-badge ${hasPending ? 'dregg-namespace-badge-pending' : 'dregg-namespace-badge-quiet'}">
            ${hasPending ? 'PROPOSAL PENDING' : 'STABLE'}
          </span>
        </dd>
        <dt>route_table_root</dt><dd>${escapeHtml(tableRoot)}</dd>
        <dt>version</dt><dd>${escapeHtml(String(version))}</dd>
        <dt>governance_committee_root</dt><dd>${escapeHtml(committee)}</dd>
        <dt>threshold</dt><dd>${escapeHtml(String(threshold))}</dd>
        <dt>dispute_window_height</dt><dd>${escapeHtml(String(windowH))}</dd>
        <dt>pending_proposal_root</dt><dd>${escapeHtml(pending)}</dd>
      </dl>
    `;
  }
}

// =========================================================================
// <dregg-namespace-route-table> — DFA route table viewer + editor
// =========================================================================

class RouteTableInspector extends HTMLElement {
  static get observedAttributes() { return ['uri', 'editable']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._table = null;
    this._error = null;
    this._loading = true;
    this._poll = null;
    this._draftRoutes = null;   // user-edited working copy
  }

  connectedCallback() {
    this.refresh();
    this._poll = setInterval(() => this.refresh(), POLL_INTERVAL_MS);
  }
  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
  }
  attributeChangedCallback() { this.refresh(); }

  async refresh() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.dregg?.readCell) {
      this._loading = false;
      this.render();
      return;
    }
    try {
      const cell = await window.dregg.readCell(uri);
      const root = cell?.state?.fields?.[ROUTE_TABLE_ROOT_SLOT];
      if (!root || isZero(root)) {
        this._table = { routes: [] };
      } else if (window.dregg.resolveRouteTable) {
        this._table = await window.dregg.resolveRouteTable(root);
      } else {
        this._table = { root_hex: hex(root), routes: null };
      }
      this._error = null;
    } catch (e) {
      this._error = String(e);
    }
    this._loading = false;
    this.render();
  }

  render() {
    const editable = this.getAttribute('editable') === 'true';
    const routes = this._draftRoutes ?? this._table?.routes ?? [];
    const rows = routes.length > 0
      ? routes.map((r, i) => `
          <tr>
            <td><code>${escapeHtml(r.path ?? r[0] ?? '')}</code></td>
            <td>${describeTarget(r.target ?? r[1])}</td>
            ${editable ? `<td><button data-action="remove" data-i="${i}">×</button></td>` : ''}
          </tr>`).join('')
      : `<tr><td colspan="${editable ? 3 : 2}"><em>
          ${this._table?.root_hex
            ? `root=${escapeHtml(fieldShort(this._table.root_hex))} (no resolver wired)`
            : 'empty route table'}
        </em></td></tr>`;

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: monospace; padding: 1em; }
        .dregg-namespace-routes-table {
          width: 100%;
          border-collapse: collapse;
          max-width: 720px;
        }
        .dregg-namespace-routes-table th,
        .dregg-namespace-routes-table td {
          text-align: left;
          padding: 0.3em 0.6em;
          border-bottom: 1px solid #ddd;
        }
        .dregg-namespace-routes-table th {
          background: #f3f5fb;
          font-weight: 600;
        }
        .dregg-namespace-routes-error { color: #b00; }
        .dregg-namespace-routes-editor {
          margin-top: 0.6em;
          display: grid;
          grid-template-columns: 1fr 1fr auto;
          gap: 0.4em;
          max-width: 720px;
        }
        .dregg-namespace-routes-editor input {
          padding: 0.3em;
          font: inherit;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        button {
          padding: 0.3em 0.7em;
          font: inherit;
          background: #eef;
          border: 1px solid #ccd;
          border-radius: 3px;
          cursor: pointer;
        }
        .dregg-namespace-routes-actions {
          margin-top: 0.5em;
          display: flex;
          gap: 0.4em;
        }
      </style>
      <h2>Route Table</h2>
      ${this._loading ? `<dregg-status-bar state="loading" message="resolving route table…"></dregg-status-bar>` : ''}
      ${this._error ? `<div class="dregg-namespace-routes-error">${escapeHtml(this._error)}</div>` : ''}
      <table class="dregg-namespace-routes-table">
        <thead>
          <tr>
            <th>path</th>
            <th>target</th>
            ${editable ? '<th></th>' : ''}
          </tr>
        </thead>
        <tbody>${rows}</tbody>
      </table>
      ${editable ? `
        <div class="dregg-namespace-routes-editor">
          <input id="new-path" placeholder="/public/*" />
          <input id="new-target" placeholder='{"Handler": "public"}' />
          <button data-action="add">+ Add</button>
        </div>
        <div class="dregg-namespace-routes-actions">
          <button data-action="reset" ${this._draftRoutes ? '' : 'disabled'}>Reset draft</button>
          <button data-action="emit-draft" ${this._draftRoutes ? '' : 'disabled'}>Emit draft JSON…</button>
        </div>
      ` : ''}
    `;

    if (editable) {
      this.shadowRoot.querySelectorAll('button[data-action=remove]').forEach((btn) => {
        btn.addEventListener('click', () => {
          const i = Number(btn.dataset.i);
          const draft = [...(this._draftRoutes ?? this._table?.routes ?? [])];
          draft.splice(i, 1);
          this._draftRoutes = draft;
          this.render();
        });
      });
      this.shadowRoot.querySelector('button[data-action=add]')?.addEventListener('click', () => {
        const path = this.shadowRoot.getElementById('new-path').value.trim();
        const tgtStr = this.shadowRoot.getElementById('new-target').value.trim();
        if (!path) return;
        let target;
        try { target = JSON.parse(tgtStr); } catch { target = { Handler: tgtStr }; }
        this._draftRoutes = [...(this._draftRoutes ?? this._table?.routes ?? []), { path, target }];
        this.render();
      });
      this.shadowRoot.querySelector('button[data-action=reset]')?.addEventListener('click', () => {
        this._draftRoutes = null;
        this.render();
      });
      this.shadowRoot.querySelector('button[data-action=emit-draft]')?.addEventListener('click', () => {
        this.dispatchEvent(new CustomEvent('route-draft', {
          bubbles: true, composed: true,
          detail: { routes: this._draftRoutes },
        }));
      });
    }
  }
}

// =========================================================================
// <dregg-namespace-proposal> — propose / vote / commit / register UI
// =========================================================================

class ProposalInspector extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._activeTab = 'propose';
    this._busy = null;
    this._error = null;
    this._receipt = null;
    this._lastMethod = null;
    this._voteTally = { approve: 0, reject: 0, threshold: 0 };
    this._cellState = null;
    this._poll = null;
  }

  connectedCallback() {
    this.refreshCell();
    this._poll = setInterval(() => this.refreshCell(), POLL_INTERVAL_MS);
    this.render();
  }
  disconnectedCallback() {
    if (this._poll) clearInterval(this._poll);
  }
  attributeChangedCallback() {
    this.refreshCell();
    this.render();
  }

  async refreshCell() {
    const uri = this.getAttribute('uri');
    if (!uri || !window.dregg?.readCell) return;
    try {
      const cell = await window.dregg.readCell(uri);
      this._cellState = cell?.state ?? null;
      if (this._cellState?.fields) {
        this._voteTally.threshold = fieldToU64BE(this._cellState.fields[THRESHOLD_SLOT]);
      }
      this.render();
    } catch { /* ignore — polling */ }
  }

  render() {
    const uri = this.getAttribute('uri') ?? '';
    const f = this._cellState?.fields;
    const hasPending = !!(f && !isZero(f[PENDING_PROPOSAL_ROOT_SLOT]));
    const pendingRoot = hasPending ? fieldShort(f[PENDING_PROPOSAL_ROOT_SLOT]) : '';
    const threshold = f ? fieldToU64BE(f[THRESHOLD_SLOT]) : 0;
    const approve = this._voteTally.approve;
    const reject = this._voteTally.reject;
    const approvePct = threshold > 0 ? Math.min(100, Math.round((approve / threshold) * 100)) : 0;
    const rejectPct  = threshold > 0 ? Math.min(100, Math.round((reject / threshold) * 100)) : 0;

    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: monospace; padding: 1em; }
        .dregg-namespace-proposal-tabs {
          display: flex;
          gap: 0.3em;
          border-bottom: 1px solid #ccc;
          margin-bottom: 0.6em;
        }
        .dregg-namespace-proposal-tab {
          padding: 0.4em 0.8em;
          background: #f3f5fb;
          border: 1px solid #ccc;
          border-bottom: 0;
          border-radius: 3px 3px 0 0;
          cursor: pointer;
          font: inherit;
        }
        .dregg-namespace-proposal-tab[aria-selected=true] {
          background: #fff;
          font-weight: 600;
          color: #3956c8;
        }
        .dregg-namespace-proposal-panel {
          display: grid;
          gap: 0.6em;
        }
        .dregg-namespace-proposal-panel label {
          display: grid;
          gap: 0.2em;
        }
        textarea, input, select {
          width: 100%;
          box-sizing: border-box;
          font: inherit;
          font-family: ui-monospace, monospace;
          padding: 0.4em;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        .dregg-namespace-proposal-panel button[type=submit] {
          padding: 0.5em 1em;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          font-weight: 600;
          cursor: pointer;
        }
        .dregg-namespace-proposal-panel button[disabled] {
          opacity: 0.5; cursor: wait;
        }
        .dregg-namespace-proposal-tally {
          display: grid;
          gap: 0.4em;
          margin-bottom: 0.6em;
          padding: 0.6em;
          background: #fafbff;
          border: 1px solid #d8dcee;
          border-radius: 4px;
        }
        .dregg-namespace-proposal-bar {
          height: 1.1em;
          background: #eee;
          border-radius: 3px;
          overflow: hidden;
          position: relative;
        }
        .dregg-namespace-proposal-bar-fill {
          height: 100%;
          transition: width 0.3s ease;
        }
        .dregg-namespace-proposal-bar-approve .dregg-namespace-proposal-bar-fill {
          background: linear-gradient(90deg, #66bb6a, #2e7d32);
        }
        .dregg-namespace-proposal-bar-reject .dregg-namespace-proposal-bar-fill {
          background: linear-gradient(90deg, #ef5350, #b71c1c);
        }
        .dregg-namespace-proposal-bar-label {
          position: absolute;
          inset: 0;
          display: grid;
          place-items: center;
          color: #fff;
          font-size: 0.78rem;
          font-weight: 700;
          mix-blend-mode: difference;
        }
      </style>
      <h2>Governance</h2>
      <p>Target: <code>${escapeHtml(uri || '(no uri attribute set)')}</code></p>

      <div class="dregg-namespace-proposal-tally">
        <strong>${hasPending ? `Pending proposal: ${escapeHtml(pendingRoot)}` : 'No pending proposal'}</strong>
        <div>
          <div>Approve weight: ${approve} / ${threshold}</div>
          <div class="dregg-namespace-proposal-bar dregg-namespace-proposal-bar-approve">
            <div class="dregg-namespace-proposal-bar-fill" style="width:${approvePct}%"></div>
            <div class="dregg-namespace-proposal-bar-label">${approvePct}%</div>
          </div>
        </div>
        <div>
          <div>Reject weight: ${reject} / ${threshold}</div>
          <div class="dregg-namespace-proposal-bar dregg-namespace-proposal-bar-reject">
            <div class="dregg-namespace-proposal-bar-fill" style="width:${rejectPct}%"></div>
            <div class="dregg-namespace-proposal-bar-label">${rejectPct}%</div>
          </div>
        </div>
      </div>

      <div class="dregg-namespace-proposal-tabs" role="tablist">
        ${['propose','vote','commit','register'].map((t) => `
          <button class="dregg-namespace-proposal-tab" role="tab" data-tab="${t}"
                  aria-selected="${this._activeTab === t}">${t}</button>
        `).join('')}
      </div>

      ${this.#renderPanel()}

      <dregg-status-bar
        state="${this._busy ? 'loading' : (this._error ? 'error' : (this._receipt ? 'success' : 'idle'))}"
        message="${escapeHtml(this._busy?.message ?? this._error ?? (this._receipt ? `${this._lastMethod} submitted` : ''))}"
        receipt="${escapeHtml(this._receipt ?? '')}"
      ></dregg-status-bar>
      ${this._receipt ? `
        <dregg-token-cap
          kind="receipt"
          label="${escapeHtml(this._lastMethod)}"
          target="${escapeHtml(uri)}"
          action="${escapeHtml(this._lastMethod)}"
          tag="${escapeHtml(this._receipt)}"
        ></dregg-token-cap>
      ` : ''}
    `;

    this.shadowRoot.querySelectorAll('.dregg-namespace-proposal-tab').forEach((b) => {
      b.addEventListener('click', () => {
        this._activeTab = b.dataset.tab;
        this.render();
      });
    });
    this.shadowRoot.querySelector('#propose-form')?.addEventListener('submit', (e) => {
      e.preventDefault();
      this.#onPropose(e.target);
    });
    this.shadowRoot.querySelector('#vote-form')?.addEventListener('submit', (e) => {
      e.preventDefault();
      this.#onVote(e.target);
    });
    this.shadowRoot.querySelector('#commit-form')?.addEventListener('submit', (e) => {
      e.preventDefault();
      this.#onCommit(e.target);
    });
    this.shadowRoot.querySelector('#register-form')?.addEventListener('submit', (e) => {
      e.preventDefault();
      this.#onRegister(e.target);
    });
  }

  #renderPanel() {
    switch (this._activeTab) {
      case 'propose':
        return `
          <form id="propose-form" class="dregg-namespace-proposal-panel">
            <label>Proposed routes (JSON)
              <textarea name="routes" rows="5">[
  {"path": "/public/*", "target": {"Handler": "public"}},
  {"path": "/treasury/*", "target": {"Handler": "treasury"}}
]</textarea>
            </label>
            <label>Description
              <input name="description" value="Add /public + /treasury routes"/>
            </label>
            <label>Dispute window (blocks)
              <input name="window" type="number" value="1000"/>
            </label>
            <button type="submit" ${this._busy ? 'disabled' : ''}>
              ${this._busy?.mode === 'propose' ? 'proposing…' : 'Submit proposal'}
            </button>
          </form>`;
      case 'vote':
        return `
          <form id="vote-form" class="dregg-namespace-proposal-panel">
            <label>Prior pending proposal root (hex)
              <input name="prior" placeholder="(auto from cell)" />
            </label>
            <label>Vote kind
              <select name="kind">
                <option value="approve">Approve</option>
                <option value="reject">Reject</option>
              </select>
            </label>
            <label>Weight
              <input name="weight" type="number" value="1" min="1"/>
            </label>
            <button type="submit" ${this._busy ? 'disabled' : ''}>
              ${this._busy?.mode === 'vote' ? 'voting…' : 'Submit vote'}
            </button>
          </form>`;
      case 'commit':
        return `
          <form id="commit-form" class="dregg-namespace-proposal-panel">
            <label>Committed route table (JSON — must match the proposal)
              <textarea name="routes" rows="5">[
  {"path": "/public/*", "target": {"Handler": "public"}},
  {"path": "/treasury/*", "target": {"Handler": "treasury"}}
]</textarea>
            </label>
            <label>New version
              <input name="version" type="number" value="1" min="1"/>
            </label>
            <label>Governance committee root (hex)
              <input name="committee" />
            </label>
            <label>Threshold-signature bytes (hex)
              <textarea name="sig" rows="3"></textarea>
            </label>
            <button type="submit" ${this._busy ? 'disabled' : ''}>
              ${this._busy?.mode === 'commit' ? 'committing…' : 'Commit (Custom auth)'}
            </button>
          </form>`;
      case 'register':
        return `
          <form id="register-form" class="dregg-namespace-proposal-panel">
            <label>Path
              <input name="path" value="/treasury/main"/>
            </label>
            <label>Target cell URI
              <input name="target" value="dregg://cell/..."/>
            </label>
            <button type="submit" ${this._busy ? 'disabled' : ''}>
              ${this._busy?.mode === 'register' ? 'registering…' : 'Register service'}
            </button>
          </form>`;
      default:
        return '';
    }
  }

  async _send(method, args) {
    const uri = this.getAttribute('uri');
    if (!uri) {
      this._error = 'No uri attribute set';
      this.render();
      return;
    }
    this._busy = { mode: this._tabForMethod(method), message: `submitting ${method}…` };
    this._error = null;
    this._receipt = null;
    this._lastMethod = method;
    this.render();
    try {
      const builders = window.dreggTurnBuilders?.['governed-namespace'];
      if (!builders) throw new Error('namespace turn-builders not loaded');
      const turn = await builders[method]({ target: uri, ...args });
      const signed = await window.dregg.signTurn(turn);
      const receipt = await window.dregg.submitTurn?.(signed) ?? signed;
      const hashHex = receipt?.hash_hex
        ?? receipt?.id
        ?? receipt?.turnId
        ?? JSON.stringify(receipt).slice(0, 40);
      this._busy = null;
      this._receipt = String(hashHex);
      // Update local vote tally tracker so the UI feels responsive
      // before the cell-read poll lands.
      if (method === METHOD_VOTE) {
        const w = Number(args.vote_weight) || 1;
        if (args.vote_kind === 'approve') this._voteTally.approve += w;
        else this._voteTally.reject += w;
      } else if (method === METHOD_COMMIT) {
        this._voteTally = { approve: 0, reject: 0, threshold: this._voteTally.threshold };
      }
    } catch (e) {
      this._busy = null;
      this._error = `${method} failed: ${String(e)}`;
    }
    this.render();
  }

  _tabForMethod(method) {
    return ({
      [METHOD_PROPOSE]: 'propose',
      [METHOD_VOTE]: 'vote',
      [METHOD_COMMIT]: 'commit',
      [METHOD_REGISTER]: 'register',
    })[method] ?? this._activeTab;
  }

  #onPropose(form) {
    const fd = new FormData(form);
    let routes;
    try { routes = JSON.parse(fd.get('routes')); }
    catch (e) { this._error = `bad routes JSON: ${e}`; this.render(); return; }
    return this._send(METHOD_PROPOSE, {
      routes,
      description: fd.get('description'),
      dispute_window_height: Number(fd.get('window')),
    });
  }
  #onVote(form) {
    const fd = new FormData(form);
    const prior = fd.get('prior')
      || (this._cellState?.fields ? hex(this._cellState.fields[PENDING_PROPOSAL_ROOT_SLOT]) : '');
    return this._send(METHOD_VOTE, {
      prior_proposal_root_hex: prior,
      vote_kind: fd.get('kind'),
      vote_weight: Number(fd.get('weight')),
    });
  }
  #onCommit(form) {
    const fd = new FormData(form);
    let routes;
    try { routes = JSON.parse(fd.get('routes')); }
    catch (e) { this._error = `bad routes JSON: ${e}`; this.render(); return; }
    return this._send(METHOD_COMMIT, {
      routes,
      new_version: Number(fd.get('version')),
      governance_committee_root_hex: fd.get('committee'),
      threshold_sig_hex: fd.get('sig'),
    });
  }
  #onRegister(form) {
    const fd = new FormData(form);
    return this._send(METHOD_REGISTER, {
      path: fd.get('path'),
      target_uri: fd.get('target'),
    });
  }
}

// =========================================================================
// <dregg-namespace-dispatch>
// =========================================================================

class DispatchInspector extends HTMLElement {
  static get observedAttributes() { return ['uri']; }

  constructor() {
    super();
    this.attachShadow({ mode: 'open' });
    this._result = null;
    this._error = null;
    this._busy = null;
  }

  connectedCallback() { this.render(); }
  attributeChangedCallback() { this.render(); }

  render() {
    this.shadowRoot.innerHTML = `
      <style>
        :host { display: block; font-family: monospace; padding: 1em; }
        .dregg-namespace-dispatch-form {
          display: grid;
          gap: 0.6em;
          max-width: 540px;
        }
        .dregg-namespace-dispatch-form input {
          padding: 0.4em;
          font: inherit;
          font-family: ui-monospace, monospace;
          border: 1px solid #ccc;
          border-radius: 3px;
        }
        button {
          padding: 0.4em 1em;
          font: inherit;
          background: #3956c8;
          color: #fff;
          border: 0;
          border-radius: 3px;
          cursor: pointer;
        }
        button[disabled] { opacity: 0.5; cursor: wait; }
        .dregg-namespace-dispatch-error { color: #b00; }
        .dregg-namespace-dispatch-result {
          margin-top: 0.6em;
          padding: 0.6em;
          background: #fafbff;
          border: 1px solid #d8dcee;
          border-radius: 4px;
        }
      </style>
      <h2>Dispatch lookup</h2>
      <p>Classify an input path against the live route table.</p>
      <form class="dregg-namespace-dispatch-form">
        <label>Path
          <input id="path" name="path" value="/treasury/transfer" />
        </label>
        <button id="go" type="submit" ${this._busy ? 'disabled' : ''}>
          ${this._busy ? 'classifying…' : 'Classify'}
        </button>
      </form>
      ${this._error ? `<div class="dregg-namespace-dispatch-error">${escapeHtml(this._error)}</div>` : ''}
      ${this._result ? `
        <div class="dregg-namespace-dispatch-result">
          <h3 style="margin-top: 0;">Result</h3>
          <p>target: <strong>${describeTarget(this._result.target)}</strong></p>
          <p>matched_prefix: <code>${escapeHtml(this._result.matched_prefix ?? '(empty)')}</code></p>
          <p>remainder: <code>${escapeHtml(this._result.remainder ?? '(empty)')}</code></p>
        </div>
      ` : ''}
    `;
    this.shadowRoot.querySelector('form').addEventListener('submit', (e) => {
      e.preventDefault();
      this.onLookup();
    });
  }

  async onLookup() {
    const uri = this.getAttribute('uri');
    const path = this.shadowRoot.getElementById('path').value;
    if (!uri) {
      this._error = 'No uri attribute set';
      this.render();
      return;
    }
    this._busy = true;
    this._error = null;
    this._result = null;
    this.render();
    try {
      if (!window.dregg?.classifyNamespacePath) {
        throw new Error(
          'classifyNamespacePath helper not exposed by runtime; ' +
          'see starbridge-governed-namespace::dispatch for the server-side equivalent',
        );
      }
      this._result = await window.dregg.classifyNamespacePath(uri, path);
    } catch (e) {
      this._error = String(e);
    }
    this._busy = false;
    this.render();
  }
}

// =========================================================================
// Element registration
// =========================================================================

const COMPONENTS = {
  'dregg-namespace':             NamespaceInspector,
  'dregg-namespace-route-table': RouteTableInspector,
  'dregg-namespace-proposal':    ProposalInspector,
  'dregg-namespace-dispatch':    DispatchInspector,
};

if (typeof customElements !== 'undefined') {
  for (const [tag, ctor] of Object.entries(COMPONENTS)) {
    if (!customElements.get(tag)) customElements.define(tag, ctor);
    if (typeof window !== 'undefined' && window.dreggUi?.register) {
      window.dreggUi.register(tag, ctor);
    }
  }
}

export {
  NamespaceInspector,
  RouteTableInspector,
  ProposalInspector,
  DispatchInspector,
  ROUTE_TABLE_ROOT_SLOT,
  VERSION_SLOT,
  GOVERNANCE_COMMITTEE_ROOT_SLOT,
  THRESHOLD_SLOT,
  DISPUTE_WINDOW_HEIGHT_SLOT,
  PENDING_PROPOSAL_ROOT_SLOT,
  METHOD_PROPOSE,
  METHOD_VOTE,
  METHOD_COMMIT,
  METHOD_REGISTER,
  VOTE_TAG_APPROVE,
  VOTE_TAG_REJECT,
  u64BE,
  fieldToU64BE,
  hex,
  blake3Field,
};

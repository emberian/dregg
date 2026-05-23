/**
 * app.js — Governed Namespace frontend.
 *
 * Connects to the governed-namespace backend for file storage, registry,
 * route governance, and DFA-routed namespace operations.
 */

const App = (() => {
    const API = '';

    let currentView = 'files';

    // =========================================================================
    // Initialization
    // =========================================================================

    function init() {
        setupNavigation();
        setupForms();
        checkConnection();
        setInterval(checkConnection, 10000);
    }

    // =========================================================================
    // Navigation
    // =========================================================================

    function setupNavigation() {
        document.querySelectorAll('.nav-link').forEach(link => {
            link.addEventListener('click', (e) => {
                e.preventDefault();
                switchView(link.dataset.view);
            });
        });
    }

    function switchView(view) {
        currentView = view;
        document.querySelectorAll('.view').forEach(el => el.classList.remove('active'));
        document.querySelectorAll('.nav-link').forEach(el => el.classList.remove('active'));
        const viewEl = document.getElementById('view-' + view);
        if (viewEl) viewEl.classList.add('active');
        const navEl = document.querySelector(`[data-view="${view}"]`);
        if (navEl) navEl.classList.add('active');

        // Load data for the view
        if (view === 'routes') loadRoutes();
        if (view === 'governance') loadGovernance();
        if (view === 'namespace') loadNamespaceTree();
    }

    // =========================================================================
    // Connection
    // =========================================================================

    async function checkConnection() {
        try {
            const resp = await fetch(API + '/routes');
            if (resp.ok) {
                updateConnectionUI(true);
                return;
            }
        } catch (e) {}
        updateConnectionUI(false);
    }

    function updateConnectionUI(ok) {
        const dot = document.getElementById('conn-dot');
        const label = document.getElementById('conn-label');
        const status = document.getElementById('api-status');

        if (ok) {
            dot.className = 'dot connected';
            label.textContent = 'connected';
            if (status) { status.textContent = 'API: connected'; status.style.color = 'var(--success)'; }
        } else {
            dot.className = 'dot disconnected';
            label.textContent = 'disconnected';
            if (status) { status.textContent = 'API: disconnected'; status.style.color = 'var(--error)'; }
        }
    }

    // =========================================================================
    // Forms Setup
    // =========================================================================

    function setupForms() {
        // Files
        bind('upload-form', handleUpload);
        bind('read-form', handleRead);
        bind('splice-form', handleSplice);
        bind('delete-form', handleDelete);
        // Registry
        bind('mount-form', handleMount);
        bind('discover-form', handleDiscover);
        bind('resolve-form', handleResolve);
        // Routes
        bind('propose-form', handlePropose);
        bind('vote-form', handleVote);
        // Namespace
        bind('ns-write-form', handleNsWrite);
        bind('ns-read-form', handleNsRead);
    }

    function bind(formId, handler) {
        const el = document.getElementById(formId);
        if (el) el.addEventListener('submit', (e) => { e.preventDefault(); handler(); });
    }

    // =========================================================================
    // File Handlers
    // =========================================================================

    async function handleUpload() {
        const content = document.getElementById('upload-content').value;
        if (!content) { showToast('Enter content to upload', 'error'); return; }

        try {
            const resp = await fetch(API + '/files', {
                method: 'POST',
                body: content,
            });
            const data = await resp.json();
            if (resp.ok) {
                show('upload-result');
                document.getElementById('upload-hash').textContent = data.hash;
                showToast(`Uploaded! Size: ${data.size} bytes`, 'success');
            } else {
                showToast(data.error || 'Upload failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function handleRead() {
        const hash = document.getElementById('read-hash').value.trim();
        if (!hash) { showToast('Enter a hash', 'error'); return; }

        try {
            const resp = await fetch(API + '/files/' + hash);
            if (resp.ok) {
                const text = await resp.text();
                show('read-result');
                document.getElementById('read-content').textContent = text;
            } else {
                const data = await resp.json().catch(() => ({}));
                showToast(data.error || `Not found (${resp.status})`, 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function handleSplice() {
        const hash = document.getElementById('splice-hash').value.trim();
        const content = document.getElementById('splice-content').value;
        if (!hash || !content) { showToast('Fill in both fields', 'error'); return; }

        try {
            const resp = await fetch(API + '/files/' + hash, {
                method: 'PUT',
                body: content,
            });
            const data = await resp.json();
            if (resp.ok) {
                show('splice-result');
                document.getElementById('splice-new-hash').textContent = data.new_hash;
                document.getElementById('splice-nullified').textContent =
                    data.old_nullified ? 'old nullified' : '';
                showToast('Spliced successfully', 'success');
            } else {
                showToast(data.error || 'Splice failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function handleDelete() {
        const hash = document.getElementById('delete-hash').value.trim();
        if (!hash) { showToast('Enter a hash', 'error'); return; }

        try {
            const resp = await fetch(API + '/files/' + hash, { method: 'DELETE' });
            const data = await resp.json();
            if (resp.ok) {
                show('delete-result');
                document.getElementById('delete-nullifier').textContent = data.nullifier;
                showToast('Deleted', 'success');
            } else {
                showToast(data.error || 'Delete failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    // =========================================================================
    // Registry Handlers
    // =========================================================================

    async function handleMount() {
        const path = document.getElementById('mount-path').value.trim();
        const name = document.getElementById('mount-name').value.trim();
        const kind = document.getElementById('mount-kind').value;
        const sturdyRef = document.getElementById('mount-ref').value.trim();
        const tagsRaw = document.getElementById('mount-tags').value.trim();
        const description = document.getElementById('mount-desc').value.trim();

        if (!path || !name || !sturdyRef) {
            showToast('Path, name, and sturdy ref are required', 'error');
            return;
        }

        const tags = tagsRaw ? tagsRaw.split(',').map(t => t.trim()).filter(Boolean) : [];

        try {
            const resp = await fetch(API + '/registry/mount', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({
                    path, name, kind, sturdy_ref: sturdyRef,
                    tags, description, expected_version: 0,
                }),
            });
            const data = await resp.json();
            if (resp.ok) {
                show('mount-result');
                document.getElementById('mount-response').textContent =
                    `${data.name} @ ${data.path} (v${data.version})`;
                showToast('Service mounted', 'success');
            } else {
                showToast(data.error || 'Mount failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function handleDiscover() {
        const tagsRaw = document.getElementById('discover-tags').value.trim();
        const tags = tagsRaw ? tagsRaw.split(',').map(t => t.trim()).filter(Boolean) : [];
        const params = tags.map(t => 'tag=' + encodeURIComponent(t)).join('&');

        try {
            const resp = await fetch(API + '/registry/discover?' + params);
            const data = await resp.json();
            show('discover-result');

            const list = document.getElementById('discover-list');
            if (!data.services || data.services.length === 0) {
                list.innerHTML = '<div class="empty-state">No services found</div>';
            } else {
                list.innerHTML = data.services.map(svc => `
                    <div class="service-card">
                        <div class="service-name">${esc(svc.name || svc.entry?.name || '--')}</div>
                        <div class="service-path">${esc(svc.path || '--')}</div>
                        <div class="service-tags">
                            ${(svc.tags || svc.entry?.tags || []).map(t => `<span class="tag">${esc(t)}</span>`).join('')}
                        </div>
                    </div>
                `).join('');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function handleResolve() {
        const path = document.getElementById('resolve-path').value.trim();
        if (!path) { showToast('Enter a path', 'error'); return; }

        const urlPath = path.startsWith('/') ? path.substring(1) : path;

        try {
            const resp = await fetch(API + '/registry/resolve/' + urlPath);
            const data = await resp.json();
            show('resolve-result');

            const detail = document.getElementById('resolve-detail');
            if (resp.ok) {
                detail.innerHTML = `
                    <div><strong>${esc(data.name)}</strong> (${esc(data.kind)})</div>
                    <div class="mono" style="margin-top:0.5rem;color:var(--accent);">${esc(data.sturdy_ref)}</div>
                    <div style="margin-top:0.5rem;color:var(--text-secondary);">${esc(data.description || '')}</div>
                    <div style="margin-top:0.5rem;">
                        Health: <span class="status-badge ${data.health === 'healthy' ? 'status-healthy' : 'status-down'}">${esc(data.health || 'unknown')}</span>
                    </div>
                `;
            } else {
                detail.innerHTML = `<div class="empty-state">${esc(data.error || 'Not found')}</div>`;
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    // =========================================================================
    // Route Handlers
    // =========================================================================

    async function loadRoutes() {
        try {
            const resp = await fetch(API + '/routes');
            const data = await resp.json();

            document.getElementById('route-commitment').textContent =
                data.commitment || '--';
            document.getElementById('route-version').textContent =
                data.version != null ? data.version : '--';

            const tbody = document.getElementById('route-table-body');
            if (!data.routes || data.routes.length === 0) {
                tbody.innerHTML = '<tr><td colspan="3" class="empty-state">No routes defined</td></tr>';
            } else {
                tbody.innerHTML = data.routes.map(r => `
                    <tr>
                        <td class="mono">${esc(r.prefix)}</td>
                        <td><span class="status-badge status-${classColor(r.class)}">${esc(r.class)}</span></td>
                        <td>${esc(r.description || '')}</td>
                    </tr>
                `).join('');
            }

            // Also update namespace tree
            renderNamespaceTree(data.routes || []);
        } catch (e) {
            console.warn('Failed to load routes:', e);
        }
    }

    async function handlePropose() {
        const proposer = document.getElementById('propose-proposer').value;
        const description = document.getElementById('propose-description').value.trim();
        const routesRaw = document.getElementById('propose-routes').value.trim();

        if (!description || !routesRaw) {
            showToast('Fill in description and routes', 'error');
            return;
        }

        let routes;
        try {
            routes = JSON.parse(routesRaw);
        } catch (e) {
            showToast('Invalid JSON in routes field', 'error');
            return;
        }

        try {
            const resp = await fetch(API + '/routes/propose', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ proposer, routes, description }),
            });
            const data = await resp.json();
            if (resp.ok) {
                show('propose-result');
                document.getElementById('propose-id').textContent = data.proposal_id;
                showToast('Proposal submitted', 'success');
                loadGovernance();
            } else {
                showToast(data.error || 'Proposal failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function handleVote() {
        const voter = document.getElementById('vote-voter').value;
        const proposalId = document.getElementById('vote-proposal').value.trim();
        const approve = document.querySelector('input[name="vote-approve"]:checked').value === 'true';

        if (!proposalId) { showToast('Enter a proposal ID', 'error'); return; }

        try {
            const resp = await fetch(API + '/routes/vote', {
                method: 'POST',
                headers: { 'Content-Type': 'application/json' },
                body: JSON.stringify({ voter, proposal_id: proposalId, approve }),
            });
            const data = await resp.json();
            if (resp.ok) {
                show('vote-result');
                document.getElementById('vote-status').textContent =
                    `Status: ${data.proposal_status || 'voted'}`;
                showToast('Vote cast', 'success');
                loadRoutes();
                loadGovernance();
            } else {
                showToast(data.error || 'Vote failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    // =========================================================================
    // Governance
    // =========================================================================

    async function loadGovernance() {
        // Constitution
        try {
            const resp = await fetch(API + '/governance/constitution');
            const data = await resp.json();
            const el = document.getElementById('constitution-info');

            el.innerHTML = `
                <div style="margin-bottom:1rem;">
                    <span class="info-label">Threshold</span>
                    <span class="info-value">${data.threshold} (${esc(data.threshold_formula || '2n/3+1')})</span>
                </div>
                <div style="margin-bottom:0.5rem;">
                    <span class="info-label">Routes Commitment</span>
                    <code class="mono">${esc(data.routes_commitment || '--')}</code>
                </div>
                <div class="constitution-grid">
                    ${(data.participants || []).map(p => `
                        <div class="participant-card">
                            <div class="participant-name">${esc(p.name || p.id)}</div>
                            <div class="participant-weight">weight: ${p.weight}</div>
                        </div>
                    `).join('')}
                </div>
            `;
        } catch (e) {
            document.getElementById('constitution-info').innerHTML =
                '<div class="empty-state">Failed to load constitution</div>';
        }

        // Proposals
        try {
            const resp = await fetch(API + '/governance/proposals');
            const data = await resp.json();
            const el = document.getElementById('proposals-list');
            const all = data.all || data.pending || [];

            if (all.length === 0) {
                el.innerHTML = '<div class="empty-state">No proposals yet</div>';
            } else {
                el.innerHTML = all.map(p => `
                    <div class="proposal-card">
                        <div class="proposal-header">
                            <span class="proposal-id">${esc(p.id || '--')}</span>
                            <span class="status-badge status-${p.status === 'pending' ? 'pending' : p.status === 'enacted' ? 'healthy' : 'down'}">${esc(p.status || 'unknown')}</span>
                        </div>
                        <div class="proposal-desc">${esc(p.description || '')}</div>
                        <div class="proposal-votes">
                            Proposer: ${esc(p.proposer || '--')} |
                            Votes: ${(p.votes || []).length}
                        </div>
                    </div>
                `).join('');
            }

            // Amendments
            const amendments = data.amendments || [];
            const aEl = document.getElementById('amendments-list');
            if (amendments.length === 0) {
                aEl.innerHTML = '<div class="empty-state">No amendments enacted yet</div>';
            } else {
                aEl.innerHTML = amendments.map(a => `
                    <div class="proposal-card">
                        <div class="proposal-desc">${esc(a.description || 'Route table updated')}</div>
                        <div class="proposal-votes">Version: ${a.version || '--'}</div>
                    </div>
                `).join('');
            }
        } catch (e) {
            document.getElementById('proposals-list').innerHTML =
                '<div class="empty-state">Failed to load proposals</div>';
        }
    }

    // =========================================================================
    // Namespace Handlers
    // =========================================================================

    async function loadNamespaceTree() {
        await loadRoutes();
    }

    function renderNamespaceTree(routes) {
        const el = document.getElementById('namespace-tree');
        if (!routes || routes.length === 0) {
            el.innerHTML = '<div class="empty-state">No routes in namespace</div>';
            return;
        }

        let html = '<div class="tree-node"><span class="tree-prefix">/</span> <span class="tree-class">root</span></div>';
        routes.forEach(r => {
            const cls = r.class || 'unknown';
            html += `<div class="tree-node">
                <span class="tree-prefix">${esc(r.prefix)}</span>
                <span class="tree-class ${cls}">[${esc(cls)}]</span>
                ${r.description ? `<span style="color:var(--text-muted);margin-left:0.5rem;">${esc(r.description)}</span>` : ''}
            </div>`;
        });
        el.innerHTML = html;
    }

    async function handleNsWrite() {
        const path = document.getElementById('ns-write-path').value.trim();
        const auth = document.getElementById('ns-write-auth').value;
        const content = document.getElementById('ns-write-content').value;

        if (!path || !content) { showToast('Enter path and content', 'error'); return; }

        const urlPath = path.startsWith('/') ? path.substring(1) : path;
        const headers = {};
        if (auth) headers['X-Auth-Level'] = auth;

        try {
            const resp = await fetch(API + '/namespace/' + urlPath, {
                method: 'POST',
                headers,
                body: content,
            });
            const data = await resp.json();
            show('ns-write-result');

            const detail = document.getElementById('ns-write-detail');
            if (resp.ok) {
                detail.innerHTML = `
                    <div><strong>Written</strong></div>
                    <div>Hash: <code class="mono">${esc(data.hash)}</code></div>
                    <div>Route: <span class="status-badge status-${classColor(data.route_class)}">${esc(data.route_class)}</span> (${esc(data.route_prefix)})</div>
                    <div>Size: ${data.size} bytes</div>
                `;
                showToast('Written to namespace', 'success');
            } else {
                detail.innerHTML = `<div style="color:var(--error);">${esc(data.error)}</div>`;
                showToast(data.error || 'Write failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function handleNsRead() {
        const path = document.getElementById('ns-read-path').value.trim();
        const hash = document.getElementById('ns-read-hash').value.trim();
        const auth = document.getElementById('ns-read-auth').value;

        if (!path) { showToast('Enter a path', 'error'); return; }

        const urlPath = path.startsWith('/') ? path.substring(1) : path;
        const headers = {};
        if (auth) headers['X-Auth-Level'] = auth;
        if (hash) headers['X-Content-Hash'] = hash;

        try {
            const resp = await fetch(API + '/namespace/' + urlPath, { headers });
            show('ns-read-result');
            const detail = document.getElementById('ns-read-detail');

            if (hash && resp.ok) {
                // Got file content back
                const text = await resp.text();
                detail.innerHTML = `<pre style="white-space:pre-wrap;">${esc(text)}</pre>`;
            } else {
                const data = await resp.json().catch(() => ({}));
                if (resp.ok) {
                    detail.innerHTML = `
                        <div>Classification: <span class="status-badge status-${classColor(data.classification)}">${esc(data.classification || '--')}</span></div>
                        <div style="margin-top:0.5rem;color:var(--text-secondary);">${esc(data.message || '')}</div>
                    `;
                } else {
                    detail.innerHTML = `<div style="color:var(--error);">${esc(data.error || 'Failed')}</div>`;
                }
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    // =========================================================================
    // Utilities
    // =========================================================================

    function show(id) {
        const el = document.getElementById(id);
        if (el) el.classList.remove('hidden');
    }

    function classColor(cls) {
        if (!cls) return 'pending';
        if (cls === 'public') return 'healthy';
        if (cls === 'members_only') return 'pending';
        if (cls === 'admin_only' || cls === 'admin') return 'down';
        return 'pending';
    }

    function esc(str) {
        if (!str) return '';
        const div = document.createElement('div');
        div.textContent = str;
        return div.innerHTML;
    }

    function showToast(msg, type) {
        const toast = document.createElement('div');
        toast.className = 'toast ' + type;
        toast.textContent = msg;
        document.body.appendChild(toast);
        setTimeout(() => toast.remove(), 4000);
    }

    return { init };
})();

document.addEventListener('DOMContentLoaded', () => { App.init(); });

/**
 * app.js — Identity Credentials frontend.
 *
 * Connects to the identity backend for credential management,
 * selective-disclosure presentations, verification, and revocation.
 */

let DEVNET_KEY = '';

async function loadConfig() {
    try {
        const resp = await fetch('/config.json');
        if (resp.ok) {
            const config = await resp.json();
            DEVNET_KEY = config.devnet_api_key || '';
        }
    } catch (e) {
        console.warn('Could not load config, mutations may fail:', e);
    }
}

function apiHeaders(extra = {}) {
    const headers = { 'Content-Type': 'application/json', ...extra };
    if (DEVNET_KEY) headers['X-Devnet-Key'] = DEVNET_KEY;
    return headers;
}

const App = (() => {
    const API = '';

    let currentView = 'cclerk';
    let credentials = [];
    let cclerkConnected = false;

    // Schema -> default attributes
    const SCHEMA_ATTRS = {
        'identity.basic': ['name', 'date_of_birth', 'nationality'],
        'identity.age': ['age', 'over_18', 'over_21'],
        'membership.org': ['organization', 'role', 'member_since'],
        'finance.kyc': ['level', 'verified_at', 'jurisdiction'],
        'custom': [],
    };

    // =========================================================================
    // Initialization
    // =========================================================================

    function init() {
        setupNavigation();
        setupWallet();
        setupForms();
        loadCredentials();
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

        if (view === 'present') populateCredentialSelect();
    }

    // =========================================================================
    // Cipherclerk
    // =========================================================================

    function setupWallet() {
        const el = document.getElementById('cclerk-status');
        if (el) el.addEventListener('click', toggleWallet);
        if (window.pyana) connectWalletBridge();
    }

    async function toggleWallet() {
        if (cclerkConnected) {
            cclerkConnected = false;
            updateWalletUI();
        } else {
            await connectWalletBridge();
        }
    }

    async function connectWalletBridge() {
        try {
            if (window.pyana) await window.pyana.connect();
            cclerkConnected = true;
            updateWalletUI();
        } catch (e) { console.warn('Cipherclerk failed:', e); }
    }

    function updateWalletUI() {
        const dot = document.getElementById('cclerk-dot');
        const label = document.getElementById('cclerk-label');
        dot.className = cclerkConnected ? 'dot connected' : 'dot disconnected';
        label.textContent = cclerkConnected ? 'Connected' : 'Connect Cipherclerk';
    }

    // =========================================================================
    // Data
    // =========================================================================

    async function loadCredentials() {
        try {
            const data = await apiGet('/credentials/list');
            credentials = data.credentials || [];
            renderCredentials();
            updateConnectionStatus(true);
        } catch (e) {
            console.warn('Credential fetch failed:', e);
            updateConnectionStatus(false);
        }
    }

    function refreshCredentials() { loadCredentials(); }

    // =========================================================================
    // Rendering
    // =========================================================================

    function renderCredentials() {
        const grid = document.getElementById('credential-grid');
        if (!grid) return;

        if (credentials.length === 0) {
            grid.innerHTML = '<div class="empty-state">No credentials in cclerk. Issue or receive credentials to get started.</div>';
            return;
        }

        grid.innerHTML = credentials.map(cred => {
            const attrs = cred.attributes || {};
            const attrHtml = Object.entries(attrs).map(([k, v]) => `
                <div class="cred-attr">
                    <span class="attr-key">${escapeHtml(k)}</span>
                    <span class="attr-value">${escapeHtml(String(v))}</span>
                </div>
            `).join('');

            const statusClass = cred.revoked ? 'revoked' : (cred.expired ? 'expired' : 'valid');
            const statusText = cred.revoked ? 'Revoked' : (cred.expired ? 'Expired' : 'Valid');

            return `
                <div class="credential-card">
                    <div class="cred-header">
                        <span class="cred-schema">${escapeHtml(cred.schema || 'unknown')}</span>
                        <span class="cred-status ${statusClass}">${statusText}</span>
                    </div>
                    <div class="cred-issuer">
                        <span class="label">Issuer: </span>
                        <span class="value">${(cred.issuer || '').slice(0, 20)}...</span>
                    </div>
                    <div class="cred-attributes">
                        ${attrHtml}
                    </div>
                    <div class="cred-footer">
                        <span>ID: ${(cred.id || '').slice(0, 12)}...</span>
                        <span>${cred.issued_at || ''}</span>
                    </div>
                </div>
            `;
        }).join('');
    }

    // =========================================================================
    // Issue
    // =========================================================================

    function setupForms() {
        const issueForm = document.getElementById('issue-form');
        if (issueForm) issueForm.addEventListener('submit', handleIssue);

        const schemaSelect = document.getElementById('issue-schema');
        if (schemaSelect) {
            schemaSelect.addEventListener('change', () => {
                const schema = schemaSelect.value;
                document.getElementById('custom-schema-group').style.display = schema === 'custom' ? '' : 'none';
                populateSchemaAttributes(schema);
            });
            // Initialize
            populateSchemaAttributes(schemaSelect.value);
        }

        // Present credential select
        const presentCred = document.getElementById('present-cred');
        if (presentCred) {
            presentCred.addEventListener('change', () => {
                const credId = presentCred.value;
                populateAttributeSelection(credId);
            });
        }

        // File upload for verify
        const verifyFile = document.getElementById('verify-file');
        if (verifyFile) {
            verifyFile.addEventListener('change', async (e) => {
                const file = e.target.files[0];
                if (file) {
                    const text = await file.text();
                    document.getElementById('verify-input').value = text;
                }
            });
        }
    }

    function populateSchemaAttributes(schema) {
        const container = document.getElementById('attribute-fields');
        if (!container) return;

        const attrs = SCHEMA_ATTRS[schema] || [];
        if (attrs.length === 0) {
            container.innerHTML = '';
            return;
        }

        container.innerHTML = attrs.map(attr => `
            <div class="attr-input-row">
                <input type="text" value="${escapeHtml(attr)}" readonly placeholder="Key">
                <input type="text" placeholder="Value for ${escapeHtml(attr)}">
                <button type="button" class="remove-attr" onclick="this.parentElement.remove()">&times;</button>
            </div>
        `).join('');
    }

    function addAttribute() {
        const container = document.getElementById('attribute-fields');
        if (!container) return;
        const row = document.createElement('div');
        row.className = 'attr-input-row';
        row.innerHTML = `
            <input type="text" placeholder="Attribute key">
            <input type="text" placeholder="Attribute value">
            <button type="button" class="remove-attr" onclick="this.parentElement.remove()">&times;</button>
        `;
        container.appendChild(row);
    }

    async function handleIssue(e) {
        e.preventDefault();
        const subject = document.getElementById('issue-subject').value;
        let schema = document.getElementById('issue-schema').value;
        if (schema === 'custom') {
            schema = document.getElementById('issue-custom-schema').value;
        }
        const expiry = document.getElementById('issue-expiry').value || null;

        // Collect attributes
        const rows = document.querySelectorAll('#attribute-fields .attr-input-row');
        const attributes = {};
        rows.forEach(row => {
            const inputs = row.querySelectorAll('input');
            const key = inputs[0].value.trim();
            const val = inputs[1].value.trim();
            if (key && val) attributes[key] = val;
        });

        if (!subject || !schema) {
            showToast('Subject and schema are required', 'error');
            return;
        }

        try {
            const body = { subject, schema, attributes, expiry };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/credentials/issue', body);
            if (result.id) {
                showToast('Credential issued: ' + result.id.slice(0, 12), 'success');
                e.target.reset();
                loadCredentials();
            } else {
                showToast(result.error || 'Issue failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    // =========================================================================
    // Present
    // =========================================================================

    function populateCredentialSelect() {
        const select = document.getElementById('present-cred');
        if (!select) return;
        select.innerHTML = '<option value="">Choose a credential...</option>' +
            credentials.filter(c => !c.revoked && !c.expired).map(c =>
                `<option value="${c.id}">${c.schema} (${(c.id || '').slice(0, 8)}...)</option>`
            ).join('');
    }

    function populateAttributeSelection(credId) {
        const container = document.getElementById('present-attributes');
        const predicateSection = document.getElementById('predicate-section');
        if (!container) return;

        const cred = credentials.find(c => c.id === credId);
        if (!cred) {
            container.innerHTML = '';
            if (predicateSection) predicateSection.classList.add('hidden');
            return;
        }

        const attrs = Object.keys(cred.attributes || {});
        container.innerHTML = `
            <h3 style="margin: 1rem 0 0.5rem; font-size: 0.95rem; font-weight: 500;">Select Attributes to Reveal</h3>
            <div class="attr-select-list">
                ${attrs.map(attr => `
                    <div class="attr-select-item">
                        <input type="checkbox" id="reveal-${attr}" data-attr="${attr}" checked>
                        <span class="attr-name">${escapeHtml(attr)}</span>
                        <select data-attr="${attr}" class="disclosure-type">
                            <option value="reveal">Reveal</option>
                            <option value="predicate">Prove Predicate</option>
                        </select>
                    </div>
                `).join('')}
            </div>
        `;

        if (predicateSection) predicateSection.classList.remove('hidden');
    }

    function addPredicate() {
        const container = document.getElementById('predicate-fields');
        if (!container) return;
        const row = document.createElement('div');
        row.className = 'predicate-row';
        row.innerHTML = `
            <input type="text" placeholder="attribute">
            <select>
                <option value="gt">></option>
                <option value="gte">>=</option>
                <option value="lt"><</option>
                <option value="lte"><=</option>
                <option value="eq">=</option>
            </select>
            <input type="text" placeholder="value">
            <button type="button" class="remove-pred" onclick="this.parentElement.remove()">&times;</button>
        `;
        container.appendChild(row);
    }

    async function createPresentation() {
        const credId = document.getElementById('present-cred').value;
        if (!credId) {
            showToast('Select a credential', 'error');
            return;
        }

        // Gather revealed attributes
        const revealed = [];
        const predicates = [];

        document.querySelectorAll('.attr-select-item').forEach(item => {
            const checkbox = item.querySelector('input[type="checkbox"]');
            const typeSelect = item.querySelector('.disclosure-type');
            const attr = checkbox.dataset.attr;
            if (checkbox.checked) {
                if (typeSelect.value === 'reveal') {
                    revealed.push(attr);
                }
            }
        });

        // Gather custom predicates
        document.querySelectorAll('#predicate-fields .predicate-row').forEach(row => {
            const inputs = row.querySelectorAll('input');
            const select = row.querySelector('select');
            const attr = inputs[0].value.trim();
            const op = select.value;
            const val = inputs[1].value.trim();
            if (attr && val) predicates.push({ attribute: attr, operator: op, value: val });
        });

        try {
            const body = { credential_id: credId, revealed_attributes: revealed, predicates };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/presentations/create', body);

            const output = document.getElementById('presentation-json');
            if (result.presentation) {
                output.textContent = JSON.stringify(result.presentation, null, 2);
                showToast('Presentation created', 'success');
            } else {
                output.textContent = JSON.stringify(result, null, 2);
                showToast(result.error || 'Creation failed', 'error');
            }
        } catch (err) {
            showToast(err.message, 'error');
        }
    }

    // =========================================================================
    // Verify
    // =========================================================================

    async function verifyPresentation() {
        const input = document.getElementById('verify-input').value.trim();
        if (!input) {
            showToast('Paste or upload a presentation', 'error');
            return;
        }

        let presentation;
        try {
            presentation = JSON.parse(input);
        } catch (e) {
            showToast('Invalid JSON', 'error');
            return;
        }

        try {
            const result = await apiPost('/presentations/verify', { presentation });
            const resultEl = document.getElementById('verify-result');
            resultEl.classList.remove('hidden', 'valid', 'invalid');

            if (result.valid) {
                resultEl.classList.add('valid');
                resultEl.innerHTML = `
                    <h4>Presentation Valid</h4>
                    <p>Issuer: ${escapeHtml(result.issuer || '--')}</p>
                    <p>Schema: ${escapeHtml(result.schema || '--')}</p>
                    <p>Revealed attributes: ${(result.revealed || []).join(', ') || 'none'}</p>
                    <p>Predicates satisfied: ${(result.predicates_satisfied || []).length}</p>
                `;
            } else {
                resultEl.classList.add('invalid');
                resultEl.innerHTML = `
                    <h4>Verification Failed</h4>
                    <p>${escapeHtml(result.reason || 'Unknown reason')}</p>
                `;
            }
        } catch (err) {
            showToast('Verification request failed: ' + err.message, 'error');
        }
    }

    // =========================================================================
    // Revocation
    // =========================================================================

    async function revokeCredential() {
        const id = document.getElementById('revoke-id').value.trim();
        const reason = document.getElementById('revoke-reason').value;

        if (!id) {
            showToast('Enter a credential ID', 'error');
            return;
        }

        if (!confirm('Revoke this credential? This cannot be undone.')) return;

        try {
            const body = { credential_id: id, reason };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/revocations/revoke', body);
            if (result.success) {
                showToast('Credential revoked', 'success');
                loadCredentials();
            } else {
                showToast(result.error || 'Revocation failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    async function checkRevocation() {
        const id = document.getElementById('check-revoke-id').value.trim();
        if (!id) {
            showToast('Enter a credential ID', 'error');
            return;
        }

        try {
            const result = await apiGet('/revocations/status/' + encodeURIComponent(id));
            const el = document.getElementById('revocation-result');
            el.classList.remove('hidden', 'active', 'revoked');

            if (result.revoked) {
                el.classList.add('revoked');
                el.innerHTML = `Revoked | Reason: ${escapeHtml(result.reason || '--')} | At: ${result.revoked_at || '--'}`;
            } else {
                el.classList.add('active');
                el.innerHTML = 'Active (not revoked)';
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    // =========================================================================
    // Utilities
    // =========================================================================

    function escapeHtml(str) {
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

    function updateConnectionStatus(ok) {
        const el = document.getElementById('connection-status');
        if (el) {
            el.textContent = ok ? 'API: connected' : 'API: disconnected';
            el.style.color = ok ? 'var(--success)' : 'var(--error)';
        }
    }

    async function apiGet(path) {
        const resp = await fetch(API + path);
        if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
        return resp.json();
    }

    async function apiPost(path, body) {
        const resp = await fetch(API + path, {
            method: 'POST',
            headers: apiHeaders(),
            body: JSON.stringify(body),
        });
        if (!resp.ok) throw new Error(`HTTP ${resp.status}`);
        return resp.json();
    }

    // =========================================================================
    // Public API
    // =========================================================================

    return {
        init,
        refreshCredentials,
        addAttribute,
        addPredicate,
        createPresentation,
        verifyPresentation,
        revokeCredential,
        checkRevocation,
    };
})();

document.addEventListener('DOMContentLoaded', async () => {
    await loadConfig();
    App.init();
});

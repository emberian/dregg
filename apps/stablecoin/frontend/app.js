/**
 * app.js — Stablecoin CDP frontend.
 *
 * Connects to the stablecoin backend API for CDP management,
 * oracle price feeds, and liquidation monitoring.
 */

const App = (() => {
    const API = '';  // Same origin

    let currentView = 'dashboard';
    let cdps = [];
    let oraclePrice = null;
    let priceHistory = [];
    let walletConnected = false;

    // =========================================================================
    // Initialization
    // =========================================================================

    function init() {
        setupNavigation();
        setupWallet();
        setupForms();
        loadData();
        // Poll for updates every 10s
        setInterval(loadData, 10000);
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
    }

    // =========================================================================
    // Wallet
    // =========================================================================

    function setupWallet() {
        const el = document.getElementById('wallet-status');
        if (el) {
            el.addEventListener('click', toggleWallet);
        }
        // Auto-connect
        if (window.pyana) {
            connectWallet();
        }
    }

    async function toggleWallet() {
        if (walletConnected) {
            walletConnected = false;
            updateWalletUI();
        } else {
            await connectWallet();
        }
    }

    async function connectWallet() {
        try {
            if (window.pyana) {
                await window.pyana.connect();
            }
            walletConnected = true;
            updateWalletUI();
        } catch (e) {
            console.warn('Wallet connection failed:', e);
        }
    }

    function updateWalletUI() {
        const dot = document.getElementById('wallet-dot');
        const label = document.getElementById('wallet-label');
        if (walletConnected) {
            dot.className = 'dot connected';
            label.textContent = 'Connected';
        } else {
            dot.className = 'dot disconnected';
            label.textContent = 'Connect Wallet';
        }
    }

    // =========================================================================
    // Data Loading
    // =========================================================================

    async function loadData() {
        await Promise.all([
            loadOracle(),
            loadCDPs(),
            loadLiquidations(),
        ]);
        updateConnectionStatus(true);
    }

    async function loadOracle() {
        try {
            const data = await apiGet('/oracle/price');
            oraclePrice = data.price;
            priceHistory = data.history || [];
            document.getElementById('current-price').textContent = '$' + formatNum(oraclePrice);
            document.getElementById('oracle-price').textContent = '$' + formatNum(oraclePrice);
            document.getElementById('oracle-updated').textContent = data.updated_at || '--';
            document.getElementById('oracle-source').textContent = data.source || 'aggregated';
            renderPriceHistory();
        } catch (e) {
            console.warn('Oracle fetch failed:', e);
            updateConnectionStatus(false);
        }
    }

    async function loadCDPs() {
        try {
            const data = await apiGet('/cdp/list');
            cdps = data.cdps || [];
            renderCDPs();
        } catch (e) {
            console.warn('CDP fetch failed:', e);
        }
    }

    async function loadLiquidations() {
        try {
            const data = await apiGet('/cdp/undercollateralized');
            renderLiquidations(data.cdps || []);
        } catch (e) {
            console.warn('Liquidation fetch failed:', e);
        }
    }

    // =========================================================================
    // Rendering
    // =========================================================================

    function renderCDPs() {
        const grid = document.getElementById('cdp-grid');
        if (!grid) return;

        if (cdps.length === 0) {
            grid.innerHTML = '<div class="empty-state">No CDPs found. Open one to get started.</div>';
            return;
        }

        grid.innerHTML = cdps.map(cdp => {
            const health = computeHealth(cdp);
            const badgeClass = health > 1.5 ? 'safe' : health > 1.2 ? 'warning' : 'danger';
            const badgeText = health > 1.5 ? 'SAFE' : health > 1.2 ? 'CAUTION' : 'DANGER';

            return `
                <div class="cdp-card" onclick="App.manageCDP('${cdp.id}')">
                    <div class="cdp-header">
                        <span class="cdp-id">CDP #${cdp.id.slice(0, 8)}</span>
                        <span class="health-badge ${badgeClass}">${badgeText}</span>
                    </div>
                    <div class="cdp-stats">
                        <div class="cdp-stat">
                            <span class="label">Collateral</span>
                            <span class="value mono">${formatNum(cdp.collateral)}</span>
                        </div>
                        <div class="cdp-stat">
                            <span class="label">Debt</span>
                            <span class="value mono">${formatNum(cdp.debt)}</span>
                        </div>
                        <div class="cdp-stat">
                            <span class="label">Health Factor</span>
                            <span class="value mono">${health.toFixed(2)}</span>
                        </div>
                        <div class="cdp-stat">
                            <span class="label">Status</span>
                            <span class="value">${cdp.status || 'active'}</span>
                        </div>
                    </div>
                </div>
            `;
        }).join('');
    }

    function renderLiquidations(liquidatable) {
        const list = document.getElementById('liquidation-list');
        if (!list) return;

        if (liquidatable.length === 0) {
            list.innerHTML = '<div class="empty-state">No undercollateralized CDPs</div>';
            return;
        }

        list.innerHTML = liquidatable.map(cdp => {
            const health = computeHealth(cdp);
            return `
                <div class="liquidation-item">
                    <div class="liq-info">
                        <div class="liq-stat">
                            <span class="label">CDP</span>
                            <span class="value">#${cdp.id.slice(0, 8)}</span>
                        </div>
                        <div class="liq-stat">
                            <span class="label">Collateral</span>
                            <span class="value">${formatNum(cdp.collateral)}</span>
                        </div>
                        <div class="liq-stat">
                            <span class="label">Debt</span>
                            <span class="value">${formatNum(cdp.debt)}</span>
                        </div>
                        <div class="liq-stat">
                            <span class="label">Health</span>
                            <span class="value" style="color: var(--error)">${health.toFixed(2)}</span>
                        </div>
                    </div>
                    <button class="btn btn-danger" onclick="event.stopPropagation(); App.liquidate('${cdp.id}')">
                        Liquidate
                    </button>
                </div>
            `;
        }).join('');
    }

    function renderPriceHistory() {
        const container = document.getElementById('price-history');
        if (!container) return;

        if (priceHistory.length === 0) {
            container.innerHTML = '<div class="empty-state">No price history available</div>';
            return;
        }

        container.innerHTML = priceHistory.slice(0, 20).map(entry => `
            <div class="price-entry">
                <span class="price">$${formatNum(entry.price)}</span>
                <span class="time">${entry.timestamp || '--'}</span>
            </div>
        `).join('');
    }

    // =========================================================================
    // Forms
    // =========================================================================

    function setupForms() {
        const form = document.getElementById('open-cdp-form');
        if (form) {
            form.addEventListener('submit', handleOpenCDP);
            // Live ratio calculation
            const collInput = document.getElementById('collateral-amount');
            const debtInput = document.getElementById('debt-amount');
            const updateRatio = () => {
                const coll = parseFloat(collInput.value) || 0;
                const debt = parseFloat(debtInput.value) || 0;
                const price = oraclePrice || 0;
                const ratio = debt > 0 ? (coll * price) / debt : 0;
                const ratioEl = document.getElementById('open-ratio');
                if (ratioEl) {
                    ratioEl.textContent = ratio > 0 ? (ratio * 100).toFixed(0) + '%' : '--';
                    ratioEl.style.color = ratio >= 1.5 ? 'var(--success)' : ratio >= 1.2 ? 'var(--warning)' : 'var(--error)';
                }
            };
            collInput.addEventListener('input', updateRatio);
            debtInput.addEventListener('input', updateRatio);
        }
    }

    async function handleOpenCDP(e) {
        e.preventDefault();
        const collateral = parseFloat(document.getElementById('collateral-amount').value);
        const debt = parseFloat(document.getElementById('debt-amount').value);

        if (!collateral || !debt) {
            showToast('Please fill in both fields', 'error');
            return;
        }

        const ratio = oraclePrice ? (collateral * oraclePrice) / debt : 0;
        if (ratio < 1.5) {
            showToast('Collateralization ratio must be at least 150%', 'error');
            return;
        }

        try {
            const body = { collateral, debt };
            if (window.pyana) {
                body.signature = await window.pyana.signTurn(body);
            }
            const result = await apiPost('/cdp/open', body);
            if (result.id) {
                showToast('CDP opened: #' + result.id.slice(0, 8), 'success');
                e.target.reset();
                loadCDPs();
                switchView('dashboard');
            } else {
                showToast('Failed: ' + (result.error || 'unknown'), 'error');
            }
        } catch (err) {
            showToast('Failed: ' + err.message, 'error');
        }
    }

    // =========================================================================
    // Manage CDP
    // =========================================================================

    function manageCDP(id) {
        const cdp = cdps.find(c => c.id === id);
        if (!cdp) return;

        const health = computeHealth(cdp);
        const modal = document.getElementById('manage-modal');
        const detail = document.getElementById('manage-detail');

        detail.innerHTML = `
            <h2>Manage CDP #${cdp.id.slice(0, 8)}</h2>
            <div class="manage-section">
                <div class="ratio-display">
                    <div class="ratio-row">
                        <span class="ratio-label">Collateral</span>
                        <span class="ratio-value">${formatNum(cdp.collateral)}</span>
                    </div>
                    <div class="ratio-row">
                        <span class="ratio-label">Debt</span>
                        <span class="ratio-value">${formatNum(cdp.debt)}</span>
                    </div>
                    <div class="ratio-row">
                        <span class="ratio-label">Health Factor</span>
                        <span class="ratio-value" style="color: ${health > 1.5 ? 'var(--success)' : health > 1.2 ? 'var(--warning)' : 'var(--error)'}">${health.toFixed(3)}</span>
                    </div>
                </div>
            </div>
            <div class="manage-section">
                <h3>Actions</h3>
                <div class="manage-actions">
                    <div class="manage-action">
                        <label>Mint More Stablecoin</label>
                        <input type="number" id="mint-amount" step="0.01" min="0" placeholder="Amount">
                        <button class="btn btn-primary" onclick="App.mintMore('${cdp.id}')">Mint</button>
                    </div>
                    <div class="manage-action">
                        <label>Repay Debt</label>
                        <input type="number" id="repay-amount" step="0.01" min="0" placeholder="Amount">
                        <button class="btn btn-primary" onclick="App.repayDebt('${cdp.id}')">Repay</button>
                    </div>
                </div>
            </div>
            <div class="manage-section" style="margin-top: 1.5rem;">
                <button class="btn btn-danger btn-large" onclick="App.closeCDP('${cdp.id}')">Close CDP (Repay All)</button>
            </div>
        `;

        modal.classList.remove('hidden');
        modal.querySelector('.modal-backdrop').onclick = () => modal.classList.add('hidden');
        modal.querySelector('.modal-close').onclick = () => modal.classList.add('hidden');
    }

    async function mintMore(id) {
        const amount = parseFloat(document.getElementById('mint-amount').value);
        if (!amount) return showToast('Enter an amount', 'error');

        try {
            const body = { cdp_id: id, amount };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/cdp/mint', body);
            if (result.success) {
                showToast('Minted ' + formatNum(amount), 'success');
                closeModal();
                loadCDPs();
            } else {
                showToast(result.error || 'Mint failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function repayDebt(id) {
        const amount = parseFloat(document.getElementById('repay-amount').value);
        if (!amount) return showToast('Enter an amount', 'error');

        try {
            const body = { cdp_id: id, amount };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/cdp/repay', body);
            if (result.success) {
                showToast('Repaid ' + formatNum(amount), 'success');
                closeModal();
                loadCDPs();
            } else {
                showToast(result.error || 'Repay failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function closeCDP(id) {
        if (!confirm('Close this CDP and repay all debt?')) return;

        try {
            const body = { cdp_id: id };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/cdp/close', body);
            if (result.success) {
                showToast('CDP closed', 'success');
                closeModal();
                loadCDPs();
            } else {
                showToast(result.error || 'Close failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    async function liquidate(id) {
        if (!confirm('Liquidate this CDP?')) return;

        try {
            const body = { cdp_id: id };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/cdp/liquidate', body);
            if (result.success) {
                showToast('CDP liquidated', 'success');
                loadData();
            } else {
                showToast(result.error || 'Liquidation failed', 'error');
            }
        } catch (e) { showToast(e.message, 'error'); }
    }

    // =========================================================================
    // Utilities
    // =========================================================================

    function computeHealth(cdp) {
        if (!cdp.debt || cdp.debt === 0) return 999;
        const price = oraclePrice || 1;
        return (cdp.collateral * price) / cdp.debt;
    }

    function formatNum(n) {
        if (n == null) return '--';
        return Number(n).toLocaleString(undefined, { maximumFractionDigits: 4 });
    }

    function closeModal() {
        document.getElementById('manage-modal').classList.add('hidden');
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
            headers: { 'Content-Type': 'application/json' },
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
        manageCDP,
        mintMore,
        repayDebt,
        closeCDP,
        liquidate,
    };
})();

document.addEventListener('DOMContentLoaded', App.init);

/**
 * app.js — AMM DEX frontend.
 *
 * Connects to the AMM backend for pool info, swaps, and liquidity management.
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

    let currentView = 'pools';
    let pools = [];
    let walletConnected = false;

    // =========================================================================
    // Initialization
    // =========================================================================

    function init() {
        setupNavigation();
        setupWallet();
        setupForms();
        setupLiveQuote();
        loadPools();
        setInterval(loadPools, 10000);
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
        if (el) el.addEventListener('click', toggleWallet);
        if (window.pyana) connectWallet();
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
            if (window.pyana) await window.pyana.connect();
            walletConnected = true;
            updateWalletUI();
        } catch (e) { console.warn('Wallet connect failed:', e); }
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
    // Data
    // =========================================================================

    async function loadPools() {
        try {
            const data = await apiGet('/pools/list');
            pools = data.pools || [];
            renderPools();
            populatePoolSelects();
            updateConnectionStatus(true);
        } catch (e) {
            console.warn('Pool fetch failed:', e);
            updateConnectionStatus(false);
        }
    }

    // =========================================================================
    // Rendering
    // =========================================================================

    function renderPools() {
        const list = document.getElementById('pool-list');
        if (!list) return;

        if (pools.length === 0) {
            list.innerHTML = '<div class="empty-state">No liquidity pools found</div>';
            return;
        }

        list.innerHTML = pools.map(pool => `
            <div class="pool-card" onclick="App.viewPool('${pool.id}')">
                <div class="pool-header">
                    <span class="pool-pair">${pool.token_a} / ${pool.token_b}</span>
                    <span class="pool-fee-badge">${(pool.fee_rate * 100).toFixed(2)}% fee</span>
                </div>
                <div class="pool-stats">
                    <div class="pool-stat">
                        <span class="label">Reserve A</span>
                        <span class="value">${formatNum(pool.reserve_a)}</span>
                    </div>
                    <div class="pool-stat">
                        <span class="label">Reserve B</span>
                        <span class="value">${formatNum(pool.reserve_b)}</span>
                    </div>
                    <div class="pool-stat">
                        <span class="label">K Value</span>
                        <span class="value">${formatNum(pool.k)}</span>
                    </div>
                    <div class="pool-stat">
                        <span class="label">Total Fees</span>
                        <span class="value">${formatNum(pool.accumulated_fees)}</span>
                    </div>
                </div>
            </div>
        `).join('');
    }

    function populatePoolSelects() {
        const selects = ['swap-pool', 'add-pool', 'remove-pool'];
        selects.forEach(id => {
            const el = document.getElementById(id);
            if (!el) return;
            const current = el.value;
            el.innerHTML = '<option value="">Select a pool...</option>' +
                pools.map(p => `<option value="${p.id}" ${p.id === current ? 'selected' : ''}>${p.token_a} / ${p.token_b}</option>`).join('');
        });
    }

    // =========================================================================
    // Pool Detail
    // =========================================================================

    async function viewPool(id) {
        try {
            const data = await apiGet('/pools/' + id);
            showPoolModal(data);
        } catch (e) {
            showToast('Failed to load pool', 'error');
        }
    }

    function showPoolModal(data) {
        const pool = data.pool || data;
        const modal = document.getElementById('pool-modal');
        const detail = document.getElementById('pool-detail');

        const history = (data.history || []).slice(0, 15);

        detail.innerHTML = `
            <h2>${pool.token_a} / ${pool.token_b}</h2>
            <div class="pool-detail-stats">
                <div class="stat">
                    <span class="stat-label">Reserve A</span>
                    <span class="stat-value">${formatNum(pool.reserve_a)}</span>
                </div>
                <div class="stat">
                    <span class="stat-label">Reserve B</span>
                    <span class="stat-value">${formatNum(pool.reserve_b)}</span>
                </div>
                <div class="stat">
                    <span class="stat-label">Price (A/B)</span>
                    <span class="stat-value">${pool.reserve_b > 0 ? (pool.reserve_a / pool.reserve_b).toFixed(4) : '--'}</span>
                </div>
            </div>
            <h3 style="margin-bottom: 0.5rem;">Reserve Ratio History</h3>
            <canvas id="ratio-chart" class="pool-chart"></canvas>
            <div style="margin-top: 0.5rem; font-size: 0.8rem; color: var(--text-muted);">
                K = ${formatNum(pool.k)} | Fee Rate = ${(pool.fee_rate * 100).toFixed(2)}% | Total LP = ${formatNum(pool.total_lp)}
            </div>
        `;

        modal.classList.remove('hidden');
        modal.querySelector('.modal-backdrop').onclick = () => modal.classList.add('hidden');
        modal.querySelector('.modal-close').onclick = () => modal.classList.add('hidden');

        // Draw simple chart
        setTimeout(() => drawRatioChart(history, pool), 50);
    }

    function drawRatioChart(history, pool) {
        const canvas = document.getElementById('ratio-chart');
        if (!canvas || !canvas.getContext) return;

        const ctx = canvas.getContext('2d');
        canvas.width = canvas.offsetWidth;
        canvas.height = canvas.offsetHeight;

        const w = canvas.width;
        const h = canvas.height;

        // If no history, draw current state as a flat line
        const points = history.length > 0
            ? history.map(entry => entry.reserve_a / (entry.reserve_b || 1))
            : [pool.reserve_a / (pool.reserve_b || 1)];

        if (points.length < 2) {
            points.push(points[0]);
        }

        const min = Math.min(...points) * 0.9;
        const max = Math.max(...points) * 1.1 || 1;
        const range = max - min || 1;

        ctx.fillStyle = '#1a1a26';
        ctx.fillRect(0, 0, w, h);

        ctx.strokeStyle = '#8b7cf7';
        ctx.lineWidth = 2;
        ctx.beginPath();

        for (let i = 0; i < points.length; i++) {
            const x = (i / (points.length - 1)) * w;
            const y = h - ((points[i] - min) / range) * (h - 20) - 10;
            if (i === 0) ctx.moveTo(x, y);
            else ctx.lineTo(x, y);
        }
        ctx.stroke();

        // Draw dots
        ctx.fillStyle = '#a094f7';
        for (let i = 0; i < points.length; i++) {
            const x = (i / (points.length - 1)) * w;
            const y = h - ((points[i] - min) / range) * (h - 20) - 10;
            ctx.beginPath();
            ctx.arc(x, y, 3, 0, Math.PI * 2);
            ctx.fill();
        }
    }

    // =========================================================================
    // Swap
    // =========================================================================

    function setupLiveQuote() {
        const input = document.getElementById('swap-input');
        const poolSelect = document.getElementById('swap-pool');
        const dirSelect = document.getElementById('swap-direction');

        const update = () => fetchQuote();
        if (input) input.addEventListener('input', update);
        if (poolSelect) poolSelect.addEventListener('change', update);
        if (dirSelect) dirSelect.addEventListener('change', update);
    }

    async function fetchQuote() {
        const poolId = document.getElementById('swap-pool').value;
        const amount = parseFloat(document.getElementById('swap-input').value);
        const direction = document.getElementById('swap-direction').value;

        if (!poolId || !amount) {
            setQuote('--', '--', '--', '--');
            return;
        }

        try {
            const data = await apiGet(`/pools/${poolId}/quote?amount=${amount}&direction=${direction}`);
            setQuote(
                formatNum(data.output),
                (data.price_impact * 100).toFixed(2) + '%',
                formatNum(data.fee),
                data.rate ? data.rate.toFixed(6) : '--'
            );
        } catch (e) {
            // Compute locally as fallback
            const pool = pools.find(p => p.id === poolId);
            if (pool) {
                const [inR, outR] = direction === 'a_to_b'
                    ? [pool.reserve_a, pool.reserve_b]
                    : [pool.reserve_b, pool.reserve_a];
                const fee = amount * (pool.fee_rate || 0.003);
                const amountAfterFee = amount - fee;
                const output = (outR * amountAfterFee) / (inR + amountAfterFee);
                const impact = amount / (inR + amount);
                setQuote(formatNum(output), (impact * 100).toFixed(2) + '%', formatNum(fee), (output / amount).toFixed(6));
            }
        }
    }

    function setQuote(output, impact, fee, rate) {
        document.getElementById('quote-output').textContent = output;
        document.getElementById('quote-impact').textContent = impact;
        document.getElementById('quote-fee').textContent = fee;
        document.getElementById('quote-rate').textContent = rate;
    }

    // =========================================================================
    // Forms
    // =========================================================================

    function setupForms() {
        const swapForm = document.getElementById('swap-form');
        if (swapForm) swapForm.addEventListener('submit', handleSwap);

        const addForm = document.getElementById('add-liq-form');
        if (addForm) addForm.addEventListener('submit', handleAddLiquidity);

        const removeForm = document.getElementById('remove-liq-form');
        if (removeForm) removeForm.addEventListener('submit', handleRemoveLiquidity);

        // Live proportional calc for add liquidity
        const addAmountA = document.getElementById('add-amount-a');
        const addPool = document.getElementById('add-pool');
        const updateProp = () => {
            const poolId = addPool ? addPool.value : '';
            const amtA = parseFloat(addAmountA ? addAmountA.value : 0);
            const pool = pools.find(p => p.id === poolId);
            const amtBInput = document.getElementById('add-amount-b');
            if (pool && amtA && amtBInput) {
                const ratio = pool.reserve_b / (pool.reserve_a || 1);
                amtBInput.value = (amtA * ratio).toFixed(4);
            }
        };
        if (addAmountA) addAmountA.addEventListener('input', updateProp);
        if (addPool) addPool.addEventListener('change', updateProp);

        // Live calc for remove liquidity
        const removeLp = document.getElementById('remove-lp');
        const removePool = document.getElementById('remove-pool');
        const updateReceive = () => {
            const poolId = removePool ? removePool.value : '';
            const lp = parseFloat(removeLp ? removeLp.value : 0);
            const pool = pools.find(p => p.id === poolId);
            if (pool && lp) {
                const share = lp / (pool.total_lp || 1);
                document.getElementById('receive-a').textContent = formatNum(pool.reserve_a * share);
                document.getElementById('receive-b').textContent = formatNum(pool.reserve_b * share);
            } else {
                document.getElementById('receive-a').textContent = '--';
                document.getElementById('receive-b').textContent = '--';
            }
        };
        if (removeLp) removeLp.addEventListener('input', updateReceive);
        if (removePool) removePool.addEventListener('change', updateReceive);
    }

    async function handleSwap(e) {
        e.preventDefault();
        const poolId = document.getElementById('swap-pool').value;
        const amount = parseFloat(document.getElementById('swap-input').value);
        const direction = document.getElementById('swap-direction').value;

        if (!poolId || !amount) {
            showToast('Select a pool and enter an amount', 'error');
            return;
        }

        try {
            const body = { pool_id: poolId, amount, direction };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/pools/swap', body);
            if (result.output != null) {
                showToast(`Swapped! Received ${formatNum(result.output)}`, 'success');
                document.getElementById('swap-input').value = '';
                setQuote('--', '--', '--', '--');
                loadPools();
            } else {
                showToast(result.error || 'Swap failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    async function handleAddLiquidity(e) {
        e.preventDefault();
        const poolId = document.getElementById('add-pool').value;
        const amountA = parseFloat(document.getElementById('add-amount-a').value);
        const amountB = parseFloat(document.getElementById('add-amount-b').value);

        if (!poolId || !amountA || !amountB) {
            showToast('Fill in all fields', 'error');
            return;
        }

        try {
            const body = { pool_id: poolId, amount_a: amountA, amount_b: amountB };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/pools/add_liquidity', body);
            if (result.lp_tokens != null) {
                showToast(`Added! Received ${formatNum(result.lp_tokens)} LP tokens`, 'success');
                document.getElementById('add-amount-a').value = '';
                document.getElementById('add-amount-b').value = '';
                loadPools();
            } else {
                showToast(result.error || 'Add liquidity failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    async function handleRemoveLiquidity(e) {
        e.preventDefault();
        const poolId = document.getElementById('remove-pool').value;
        const lpAmount = parseFloat(document.getElementById('remove-lp').value);

        if (!poolId || !lpAmount) {
            showToast('Fill in all fields', 'error');
            return;
        }

        try {
            const body = { pool_id: poolId, lp_amount: lpAmount };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/pools/remove_liquidity', body);
            if (result.amount_a != null) {
                showToast(`Removed! Got ${formatNum(result.amount_a)} A + ${formatNum(result.amount_b)} B`, 'success');
                document.getElementById('remove-lp').value = '';
                loadPools();
            } else {
                showToast(result.error || 'Remove liquidity failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    // =========================================================================
    // Utilities
    // =========================================================================

    function formatNum(n) {
        if (n == null) return '--';
        return Number(n).toLocaleString(undefined, { maximumFractionDigits: 4 });
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

    return { init, viewPool };
})();

document.addEventListener('DOMContentLoaded', async () => {
    await loadConfig();
    App.init();
});

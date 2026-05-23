/**
 * app.js — Orderbook frontend.
 *
 * Connects to the orderbook backend for order placement, book display,
 * trade history, and optional WebSocket live updates.
 */

const App = (() => {
    const API = '';

    let currentView = 'book';
    let ws = null;
    let darkPoolMode = false;
    let walletConnected = false;
    let book = { bids: [], asks: [] };
    let myOrders = [];
    let trades = [];

    // =========================================================================
    // Initialization
    // =========================================================================

    function init() {
        setupNavigation();
        setupWallet();
        setupForms();
        setupDarkPoolToggle();
        connectWebSocket();
        loadAll();
        setInterval(loadAll, 8000);
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
        if (window.pyana) connectWalletBridge();
    }

    async function toggleWallet() {
        if (walletConnected) {
            walletConnected = false;
            updateWalletUI();
        } else {
            await connectWalletBridge();
        }
    }

    async function connectWalletBridge() {
        try {
            if (window.pyana) await window.pyana.connect();
            walletConnected = true;
            updateWalletUI();
        } catch (e) { console.warn('Wallet failed:', e); }
    }

    function updateWalletUI() {
        const dot = document.getElementById('wallet-dot');
        const label = document.getElementById('wallet-label');
        dot.className = walletConnected ? 'dot connected' : 'dot disconnected';
        label.textContent = walletConnected ? 'Connected' : 'Connect Wallet';
    }

    // =========================================================================
    // Dark Pool
    // =========================================================================

    function setupDarkPoolToggle() {
        const toggle = document.getElementById('dark-pool-toggle');
        if (toggle) {
            toggle.addEventListener('change', () => {
                darkPoolMode = toggle.checked;
                loadAll();
            });
        }
    }

    // =========================================================================
    // WebSocket
    // =========================================================================

    function connectWebSocket() {
        const wsUrl = (window.location.origin).replace(/^http/, 'ws') + '/ws';
        const statusEl = document.getElementById('ws-status');

        try {
            ws = new WebSocket(wsUrl);
            ws.onopen = () => {
                statusEl.textContent = 'WS: connected';
                statusEl.className = 'ws-status connected';
            };
            ws.onmessage = (event) => {
                try {
                    const data = JSON.parse(event.data);
                    handleWsEvent(data);
                } catch (e) {}
            };
            ws.onclose = () => {
                statusEl.textContent = 'WS: disconnected';
                statusEl.className = 'ws-status disconnected';
                setTimeout(connectWebSocket, 3000);
            };
            ws.onerror = () => {
                statusEl.textContent = 'WS: error';
                statusEl.className = 'ws-status disconnected';
            };
        } catch (e) {
            console.warn('WebSocket failed:', e);
        }
    }

    function handleWsEvent(event) {
        switch (event.type) {
            case 'BookUpdate':
                book = event.book || book;
                renderBook();
                break;
            case 'Trade':
                trades.unshift(event.trade);
                trades = trades.slice(0, 100);
                renderTrades();
                break;
            case 'OrderUpdate':
                loadMyOrders();
                break;
        }
    }

    // =========================================================================
    // Data
    // =========================================================================

    async function loadAll() {
        await Promise.all([loadBook(), loadMyOrders(), loadTrades()]);
    }

    async function loadBook() {
        try {
            const endpoint = darkPoolMode ? '/book/dark' : '/book/levels';
            const data = await apiGet(endpoint);
            book = { bids: data.bids || [], asks: data.asks || [] };
            renderBook();
        } catch (e) { console.warn('Book fetch failed:', e); }
    }

    async function loadMyOrders() {
        try {
            const data = await apiGet('/orders/mine');
            myOrders = data.orders || [];
            renderMyOrders();
        } catch (e) { console.warn('Orders fetch failed:', e); }
    }

    async function loadTrades() {
        try {
            const data = await apiGet('/trades');
            trades = data.trades || [];
            renderTrades();
        } catch (e) { console.warn('Trades fetch failed:', e); }
    }

    // =========================================================================
    // Rendering
    // =========================================================================

    function renderBook() {
        renderBookSide('asks-list', book.asks, 'asks');
        renderBookSide('bids-list', book.bids, 'bids');
        updateSpread();
    }

    function renderBookSide(containerId, entries, side) {
        const container = document.getElementById(containerId);
        if (!container) return;

        if (entries.length === 0) {
            container.innerHTML = '<div class="empty-state">No orders</div>';
            return;
        }

        const maxTotal = Math.max(...entries.map(e => e.total || e.amount));

        // Asks show reversed (highest at top, lowest near spread)
        const sorted = side === 'asks' ? [...entries].reverse() : entries;

        container.innerHTML = sorted.map(entry => {
            const depthWidth = ((entry.total || entry.amount) / maxTotal * 100).toFixed(0);
            return `
                <div class="book-entry">
                    <span class="price">${formatPrice(entry.price)}</span>
                    <span>${formatNum(entry.amount)}</span>
                    <span>${formatNum(entry.total || entry.amount)}</span>
                    <div class="depth-bar" style="width: ${depthWidth}%"></div>
                </div>
            `;
        }).join('');
    }

    function updateSpread() {
        const el = document.getElementById('spread-value');
        if (!el) return;
        const bestAsk = book.asks.length > 0 ? book.asks[0].price : null;
        const bestBid = book.bids.length > 0 ? book.bids[0].price : null;
        if (bestAsk != null && bestBid != null) {
            el.textContent = formatPrice(bestAsk - bestBid);
        } else {
            el.textContent = '--';
        }
    }

    function renderMyOrders() {
        const container = document.getElementById('my-orders');
        if (!container) return;

        if (myOrders.length === 0) {
            container.innerHTML = '<div class="empty-state">No active orders</div>';
            return;
        }

        container.innerHTML = myOrders.map(order => `
            <div class="order-item">
                <span class="side-badge ${order.side}">${order.side.toUpperCase()}</span>
                <div class="order-field">
                    <span class="label">Type</span>
                    <span class="value">${order.order_type || order.type}</span>
                </div>
                <div class="order-field">
                    <span class="label">Price</span>
                    <span class="value">${order.price ? formatPrice(order.price) : 'MKT'}</span>
                </div>
                <div class="order-field">
                    <span class="label">Amount</span>
                    <span class="value">${formatNum(order.amount)}</span>
                </div>
                <div class="order-field">
                    <span class="label">Filled</span>
                    <span class="value">${formatNum(order.filled || 0)}</span>
                </div>
                <button class="btn-cancel" onclick="App.cancelOrder('${order.id}')">Cancel</button>
            </div>
        `).join('');
    }

    function renderTrades() {
        const container = document.getElementById('trades-list');
        if (!container) return;

        if (trades.length === 0) {
            container.innerHTML = '<div class="empty-state">No recent trades</div>';
            return;
        }

        container.innerHTML = trades.slice(0, 50).map(trade => `
            <div class="trade-item">
                <span class="trade-side ${trade.side || 'buy'}">${(trade.side || 'buy').toUpperCase()}</span>
                <span>${formatPrice(trade.price)}</span>
                <span>${formatNum(trade.amount)}</span>
                <span class="trade-time">${trade.timestamp || '--'}</span>
            </div>
        `).join('');
    }

    // =========================================================================
    // Forms
    // =========================================================================

    function setupForms() {
        const form = document.getElementById('order-form');
        if (form) form.addEventListener('submit', handlePlaceOrder);

        // Show/hide price fields based on type
        const typeSelect = document.getElementById('order-type');
        if (typeSelect) {
            typeSelect.addEventListener('change', () => {
                const type = typeSelect.value;
                document.getElementById('price-group').style.display = type === 'market' ? 'none' : '';
                document.getElementById('stop-group').style.display = type === 'stop' ? '' : 'none';
            });
        }

        // Live total calc
        const priceInput = document.getElementById('order-price');
        const amountInput = document.getElementById('order-amount');
        const updateTotal = () => {
            const price = parseFloat(priceInput.value) || 0;
            const amount = parseFloat(amountInput.value) || 0;
            document.getElementById('order-total').textContent = price && amount ? formatNum(price * amount) : '--';
        };
        if (priceInput) priceInput.addEventListener('input', updateTotal);
        if (amountInput) amountInput.addEventListener('input', updateTotal);
    }

    async function handlePlaceOrder(e) {
        e.preventDefault();
        const side = document.getElementById('order-side').value;
        const type = document.getElementById('order-type').value;
        const price = parseFloat(document.getElementById('order-price').value);
        const stopPrice = parseFloat(document.getElementById('order-stop-price').value);
        const amount = parseFloat(document.getElementById('order-amount').value);

        if (!amount) {
            showToast('Enter an amount', 'error');
            return;
        }

        if (type === 'limit' && !price) {
            showToast('Enter a price for limit order', 'error');
            return;
        }

        const body = {
            side,
            order_type: type,
            amount,
            dark_pool: darkPoolMode,
        };

        if (type !== 'market') body.price = price;
        if (type === 'stop') body.stop_price = stopPrice;

        try {
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/orders/place', body);
            if (result.id) {
                showToast('Order placed: ' + result.id.slice(0, 8), 'success');
                e.target.reset();
                loadMyOrders();
                loadBook();
            } else {
                showToast(result.error || 'Order failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    async function cancelOrder(id) {
        try {
            const body = { order_id: id };
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/orders/cancel', body);
            if (result.success) {
                showToast('Order cancelled', 'success');
                loadMyOrders();
                loadBook();
            } else {
                showToast(result.error || 'Cancel failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    async function cancelAll() {
        if (!confirm('Cancel all active orders?')) return;
        try {
            const body = {};
            if (window.pyana) body.signature = await window.pyana.signTurn(body);
            const result = await apiPost('/orders/cancel_all', body);
            if (result.success) {
                showToast('All orders cancelled', 'success');
                loadMyOrders();
                loadBook();
            } else {
                showToast(result.error || 'Cancel all failed', 'error');
            }
        } catch (err) { showToast(err.message, 'error'); }
    }

    // =========================================================================
    // Utilities
    // =========================================================================

    function formatPrice(n) {
        if (n == null) return '--';
        return Number(n).toFixed(4);
    }

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

    return { init, cancelOrder, cancelAll };
})();

document.addEventListener('DOMContentLoaded', App.init);

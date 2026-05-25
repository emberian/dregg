/**
 * app.js — Main gallery application.
 *
 * Connects to the gallery backend API and WebSocket for live updates.
 * Manages the UI state: gallery grid, auction listings, bidding flow.
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
    // API base URL (configurable; defaults to same origin).
    const API_BASE = window.GALLERY_API || window.location.origin;

    let ws = null;
    let currentView = 'gallery';
    let artworks = [];
    let auctions = [];

    // =========================================================================
    // Initialization
    // =========================================================================

    function init() {
        setupNavigation();
        setupWalletButton();
        setupForms();
        connectWebSocket();
        loadArtworks();
        loadAuctions();

        // Auto-connect cclerk.
        Cipherclerk.connect();
    }

    // =========================================================================
    // Navigation
    // =========================================================================

    function setupNavigation() {
        document.querySelectorAll('.nav-link').forEach(link => {
            link.addEventListener('click', (e) => {
                e.preventDefault();
                const view = link.dataset.view;
                switchView(view);
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
    // Cipherclerk
    // =========================================================================

    function setupWalletButton() {
        const statusEl = document.getElementById('cclerk-status');
        if (statusEl) {
            statusEl.addEventListener('click', async () => {
                if (Cipherclerk.isConnected()) {
                    Cipherclerk.disconnect();
                } else {
                    await Cipherclerk.connect();
                }
            });
        }
    }

    // =========================================================================
    // WebSocket
    // =========================================================================

    function connectWebSocket() {
        const wsUrl = API_BASE.replace(/^http/, 'ws') + '/ws';
        const statusEl = document.getElementById('ws-status');

        try {
            ws = new WebSocket(wsUrl);

            ws.onopen = () => {
                if (statusEl) {
                    statusEl.textContent = 'WS: connected';
                    statusEl.className = 'ws-status connected';
                }
            };

            ws.onmessage = (event) => {
                try {
                    const data = JSON.parse(event.data);
                    handleWsEvent(data);
                } catch (e) {
                    console.warn('Invalid WS message:', event.data);
                }
            };

            ws.onclose = () => {
                if (statusEl) {
                    statusEl.textContent = 'WS: disconnected';
                    statusEl.className = 'ws-status disconnected';
                }
                // Reconnect after delay.
                setTimeout(connectWebSocket, 3000);
            };

            ws.onerror = () => {
                if (statusEl) {
                    statusEl.textContent = 'WS: error';
                    statusEl.className = 'ws-status disconnected';
                }
            };
        } catch (e) {
            console.warn('WebSocket connection failed:', e);
        }
    }

    function handleWsEvent(event) {
        switch (event.type) {
            case 'NewBid':
                console.log('New bid:', event);
                // Refresh auction if viewing it.
                loadAuctions();
                break;

            case 'BidRevealed':
                console.log('Bid revealed:', event);
                loadAuctions();
                break;

            case 'PhaseChange':
                console.log('Phase change:', event);
                loadAuctions();
                break;

            case 'AuctionSettled':
                console.log('Auction settled:', event);
                loadAuctions();
                loadArtworks();
                break;

            case 'NewArtwork':
                console.log('New artwork:', event);
                loadArtworks();
                break;

            default:
                console.log('Unknown WS event:', event);
        }
    }

    // =========================================================================
    // API Calls
    // =========================================================================

    async function apiGet(path) {
        const resp = await fetch(API_BASE + path);
        return resp.json();
    }

    async function apiPost(path, body) {
        const resp = await fetch(API_BASE + path, {
            method: 'POST',
            headers: apiHeaders(),
            body: JSON.stringify(body),
        });
        return resp.json();
    }

    // =========================================================================
    // Load Data
    // =========================================================================

    async function loadArtworks() {
        try {
            const data = await apiGet('/artworks');
            artworks = data.artworks || [];
            renderArtworkGrid();
        } catch (e) {
            console.error('Failed to load artworks:', e);
        }
    }

    async function loadAuctions() {
        try {
            const data = await apiGet('/auctions');
            auctions = data.auctions || [];
            renderAuctionList();
        } catch (e) {
            console.error('Failed to load auctions:', e);
        }
    }

    // =========================================================================
    // Render Functions
    // =========================================================================

    function renderArtworkGrid() {
        const grid = document.getElementById('artwork-grid');
        if (!grid) return;

        if (artworks.length === 0) {
            grid.innerHTML = '<div class="empty-state">No artworks registered yet</div>';
            return;
        }

        grid.innerHTML = artworks.map(artwork => `
            <div class="artwork-card" data-id="${artwork.id}" onclick="App.viewArtwork('${artwork.id}')">
                <div class="card-image">
                    <div class="placeholder-art" style="background: ${generateGradient(artwork.image_hash)}"></div>
                </div>
                <div class="card-body">
                    <div class="card-title">${escapeHtml(artwork.title)}</div>
                    <div class="card-artist">${artwork.artist.slice(0, 12)}...</div>
                    <div class="card-price">Reserve: ${artwork.reserve_price} units</div>
                    <div class="card-tags">
                        ${artwork.tags.map(t => `<span class="tag">${escapeHtml(t)}</span>`).join('')}
                    </div>
                </div>
            </div>
        `).join('');
    }

    function renderAuctionList() {
        const list = document.getElementById('auction-list');
        if (!list) return;

        if (auctions.length === 0) {
            list.innerHTML = '<div class="empty-state">No active auctions</div>';
            return;
        }

        list.innerHTML = auctions.map(auction => `
            <div class="auction-item" onclick="App.viewAuction('${auction.id}')">
                <div class="auction-info">
                    <h3>Auction: ${auction.artwork_id.slice(0, 12)}...</h3>
                    <div class="auction-meta">
                        <span>Bids: ${auction.commitment_count}</span>
                        <span>Revealed: ${auction.revealed_count}</span>
                        <span>Reserve: ${auction.reserve_price}</span>
                        ${auction.highest_revealed_bid ? `<span>High: ${auction.highest_revealed_bid}</span>` : ''}
                    </div>
                </div>
                <div class="auction-badge">
                    <div class="phase-badge ${auction.phase}">${auction.phase.toUpperCase()}</div>
                </div>
            </div>
        `).join('');
    }

    // =========================================================================
    // Artwork Detail
    // =========================================================================

    async function viewArtwork(artworkId) {
        try {
            const data = await apiGet('/artworks/' + artworkId);
            showArtworkModal(data);
        } catch (e) {
            console.error('Failed to load artwork:', e);
        }
    }

    function showArtworkModal(artwork) {
        const modal = document.getElementById('auction-modal');
        const detail = document.getElementById('auction-detail');
        if (!modal || !detail) return;

        const provenance = (artwork.provenance || []).map(p => `
            <div class="provenance-entry">
                <span class="address">${p.from.slice(0, 8)}...</span>
                <span class="arrow">-></span>
                <span class="address">${p.to.slice(0, 8)}...</span>
                <span class="price">${p.price > 0 ? p.price + ' units' : 'registered'}</span>
            </div>
        `).join('');

        detail.innerHTML = `
            <h2>${escapeHtml(artwork.title)}</h2>
            <p>${escapeHtml(artwork.description || '')}</p>
            <div class="artwork-meta">
                <span class="meta-label">Artist</span>
                <span class="meta-value mono">${artwork.artist}</span>
            </div>
            <div class="artwork-meta">
                <span class="meta-label">Current Owner</span>
                <span class="meta-value mono">${artwork.current_owner}</span>
            </div>
            <div class="artwork-meta">
                <span class="meta-label">Image Hash</span>
                <span class="meta-value mono">${artwork.image_hash}</span>
            </div>
            <div class="artwork-meta">
                <span class="meta-label">Reserve Price</span>
                <span class="meta-value">${artwork.reserve_price} units</span>
            </div>
            <h3 style="margin-top: 1.5rem;">Provenance</h3>
            <div class="provenance-chain">
                ${provenance || '<div class="empty-state">No history</div>'}
            </div>
        `;

        modal.classList.remove('hidden');

        // Close handlers.
        modal.querySelector('.modal-backdrop').onclick = () => modal.classList.add('hidden');
        modal.querySelector('.modal-close').onclick = () => modal.classList.add('hidden');
    }

    // =========================================================================
    // Auction Detail
    // =========================================================================

    async function viewAuction(auctionId) {
        // For simplicity, redirect to auction.html with query param.
        // In a real SPA this would be a route change.
        window.location.href = `auction.html?id=${auctionId}`;
    }

    // =========================================================================
    // Forms
    // =========================================================================

    function setupForms() {
        const registerForm = document.getElementById('register-form');
        if (registerForm) {
            registerForm.addEventListener('submit', handleRegister);
        }

        const bidForm = document.getElementById('bid-form');
        if (bidForm) {
            bidForm.addEventListener('submit', handleBid);
        }

        const revealBtn = document.getElementById('reveal-btn');
        if (revealBtn) {
            revealBtn.addEventListener('click', handleReveal);
        }
    }

    async function handleRegister(e) {
        e.preventDefault();

        if (!Cipherclerk.isConnected()) {
            alert('Please connect your cclerk first.');
            return;
        }

        const identity = Cipherclerk.getIdentity();
        const title = document.getElementById('reg-title').value;
        const description = document.getElementById('reg-description').value;
        const reserve = parseInt(document.getElementById('reg-reserve').value, 10);
        const tags = document.getElementById('reg-tags').value
            .split(',')
            .map(t => t.trim())
            .filter(t => t.length > 0);

        // Hash the image file (or use a placeholder).
        const imageInput = document.getElementById('reg-image');
        let imageHash;
        if (imageInput && imageInput.files.length > 0) {
            const buffer = await imageInput.files[0].arrayBuffer();
            const hashBytes = new Uint8Array(32);
            // Simple hash of file content for demo.
            const view = new Uint8Array(buffer);
            for (let i = 0; i < view.length; i++) {
                hashBytes[i % 32] ^= view[i];
            }
            imageHash = Array.from(hashBytes).map(b => b.toString(16).padStart(2, '0')).join('');
        } else {
            // Generate a placeholder hash.
            imageHash = Array.from(new Uint8Array(32)).map(() =>
                Math.floor(Math.random() * 256).toString(16).padStart(2, '0')
            ).join('');
        }

        try {
            const result = await apiPost('/artworks', {
                title,
                description,
                image_hash: imageHash,
                artist_cell: identity.cellId,
                reserve_price: reserve,
                tags,
            });

            if (result.id) {
                alert('Artwork registered! ID: ' + result.id.slice(0, 16) + '...');
                e.target.reset();
                loadArtworks();
                switchView('gallery');
            } else {
                alert('Registration failed: ' + (result.error || 'unknown error'));
            }
        } catch (err) {
            alert('Registration failed: ' + err.message);
        }
    }

    async function handleBid(e) {
        e.preventDefault();

        if (!Cipherclerk.isConnected()) {
            alert('Please connect your cclerk first.');
            return;
        }

        const identity = Cipherclerk.getIdentity();
        const amount = parseInt(document.getElementById('bid-amount').value, 10);
        const auctionId = getAuctionIdFromUrl();

        if (!auctionId) {
            alert('No auction selected.');
            return;
        }

        // Create bid (generates nonce, computes commitment, stores locally).
        const bid = Bidding.createBid(auctionId, identity.cellId, amount);

        try {
            const result = await apiPost(`/auctions/${auctionId}/bid`, {
                commitment: bid.commitment,
                bidder_cell: identity.cellId,
                escrow_amount: amount,
            });

            if (result.status === 'committed') {
                alert('Bid committed! Your bid amount is hidden.\nRemember to reveal during the reveal phase.');
                document.getElementById('bid-amount').value = '';
            } else {
                alert('Bid failed: ' + (result.error || 'unknown error'));
            }
        } catch (err) {
            alert('Bid failed: ' + err.message);
        }
    }

    async function handleReveal() {
        if (!Cipherclerk.isConnected()) {
            alert('Please connect your cclerk first.');
            return;
        }

        const identity = Cipherclerk.getIdentity();
        const auctionId = getAuctionIdFromUrl();

        if (!auctionId) {
            alert('No auction selected.');
            return;
        }

        // Retrieve stored bid data.
        const bidData = Bidding.getStoredBid(auctionId, identity.cellId);
        if (!bidData) {
            alert('No stored bid found for this auction. Did you bid from this browser?');
            return;
        }

        try {
            const result = await apiPost(`/auctions/${auctionId}/reveal`, {
                commitment: bidData.commitment,
                bidder_cell: identity.cellId,
                amount: bidData.amount,
                nonce: bidData.nonce,
            });

            if (result.status === 'revealed') {
                alert(`Bid revealed: ${bidData.amount} units`);
                Bidding.clearBid(auctionId, identity.cellId);
            } else {
                alert('Reveal failed: ' + (result.error || 'unknown error'));
            }
        } catch (err) {
            alert('Reveal failed: ' + err.message);
        }
    }

    // =========================================================================
    // Auction Page Logic (auction.html)
    // =========================================================================

    async function loadAuctionPage() {
        const auctionId = getAuctionIdFromUrl();
        if (!auctionId) return;

        try {
            const data = await apiGet('/auctions/' + auctionId);
            renderAuctionDetail(data);
        } catch (e) {
            console.error('Failed to load auction:', e);
        }
    }

    function renderAuctionDetail(data) {
        const auction = data.auction;
        if (!auction) return;

        // Update phase badge.
        const badge = document.getElementById('phase-badge');
        if (badge) {
            badge.textContent = auction.phase.toUpperCase();
            badge.className = 'phase-badge ' + auction.phase;
        }

        // Update stats.
        setTextContent('reserve-price', auction.reserve_price + ' units');
        setTextContent('total-bids', auction.commitment_count);
        setTextContent('highest-bid', auction.highest_revealed_bid ? auction.highest_revealed_bid + ' units' : '--');

        // Show appropriate section based on phase.
        const bidSection = document.getElementById('bid-section');
        const revealSection = document.getElementById('reveal-section');
        const settledSection = document.getElementById('settled-section');

        if (bidSection) bidSection.classList.toggle('hidden', auction.phase !== 'bidding');
        if (revealSection) revealSection.classList.toggle('hidden', auction.phase !== 'reveal');
        if (settledSection) settledSection.classList.toggle('hidden', auction.phase !== 'settled');

        if (auction.phase === 'settled' && auction.winner) {
            setTextContent('winner-address', auction.winner);
            setTextContent('winning-amount', auction.winning_bid + ' units');
        }

        // Render bid history.
        renderBidHistory(data.commitments || [], data.revealed_bids || [], auction.phase);
    }

    function renderBidHistory(commitments, revealed, phase) {
        const list = document.getElementById('bid-list');
        if (!list) return;

        if (commitments.length === 0) {
            list.innerHTML = '<div class="empty-state">No bids yet</div>';
            return;
        }

        // During bidding phase, show only commitment hashes.
        // After reveal, show amounts.
        const entries = commitments.map(c => {
            const revealedBid = revealed.find(r => r.commitment === c.commitment);
            if (revealedBid) {
                return `
                    <div class="bid-entry">
                        <span class="bidder">${c.bidder.slice(0, 12)}...</span>
                        <span class="bid-amount">${revealedBid.amount} units</span>
                    </div>
                `;
            } else {
                return `
                    <div class="bid-entry">
                        <span class="bidder">${c.bidder.slice(0, 12)}...</span>
                        <span class="bid-hash">${c.commitment.slice(0, 16)}... (hidden)</span>
                    </div>
                `;
            }
        });

        list.innerHTML = entries.join('');
    }

    // =========================================================================
    // Utilities
    // =========================================================================

    function getAuctionIdFromUrl() {
        const params = new URLSearchParams(window.location.search);
        return params.get('id');
    }

    function setTextContent(id, text) {
        const el = document.getElementById(id);
        if (el) el.textContent = text;
    }

    function escapeHtml(str) {
        const div = document.createElement('div');
        div.textContent = str;
        return div.innerHTML;
    }

    function generateGradient(hash) {
        // Generate a deterministic gradient from the hash string.
        const h1 = parseInt(hash.slice(0, 2), 16) * 1.4;
        const h2 = parseInt(hash.slice(2, 4), 16) * 1.4;
        const s = 40 + parseInt(hash.slice(4, 6), 16) % 30;
        return `linear-gradient(${h1}deg, hsl(${h1}, ${s}%, 20%), hsl(${h2}, ${s}%, 15%))`;
    }

    // =========================================================================
    // Public API
    // =========================================================================

    return {
        init,
        viewArtwork,
        viewAuction,
        loadAuctionPage,
    };
})();

// Initialize on DOM ready.
document.addEventListener('DOMContentLoaded', async () => {
    await loadConfig();
    App.init();

    // If on auction.html, load the auction detail.
    if (window.location.pathname.includes('auction.html')) {
        App.loadAuctionPage();
    }
});

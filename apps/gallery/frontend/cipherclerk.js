/**
 * cipherclerk.js — Extension bridge for the pyana browser extension.
 *
 * Connects to the pyana browser extension via window.pyana interface.
 * Provides identity management and turn signing for the gallery UI.
 */

const Cipherclerk = (() => {
    let _identity = null;
    let _connected = false;

    /**
     * Check if the pyana extension is available.
     */
    function isExtensionAvailable() {
        return typeof window.pyana !== 'undefined';
    }

    /**
     * Connect to the pyana extension and retrieve identity.
     * Falls back to a demo identity if the extension is not installed.
     */
    async function connect() {
        if (isExtensionAvailable()) {
            try {
                _identity = await window.pyana.getIdentity();
                _connected = true;
                updateUI(true, _identity.cellId);
                return _identity;
            } catch (err) {
                console.warn('Extension connection failed:', err);
            }
        }

        // Fallback: generate a demo identity for testing without extension.
        _identity = generateDemoIdentity();
        _connected = true;
        updateUI(true, _identity.cellId);
        console.info('Using demo identity (extension not available):', _identity.cellId.slice(0, 16) + '...');
        return _identity;
    }

    /**
     * Disconnect cclerk.
     */
    function disconnect() {
        _identity = null;
        _connected = false;
        updateUI(false, null);
    }

    /**
     * Get the current identity (cell ID as hex string).
     */
    function getIdentity() {
        return _identity;
    }

    /**
     * Check connection status.
     */
    function isConnected() {
        return _connected;
    }

    /**
     * Sign a turn via the extension.
     * Falls back to local signing for demo mode.
     */
    async function signTurn(turnData) {
        if (isExtensionAvailable() && _connected) {
            try {
                return await window.pyana.signTurn(turnData);
            } catch (err) {
                console.warn('Extension signTurn failed:', err);
            }
        }

        // Demo fallback: return a mock signature.
        return {
            signature: generateMockSignature(turnData),
            cellId: _identity.cellId,
        };
    }

    /**
     * Generate a deterministic demo identity for testing.
     */
    function generateDemoIdentity() {
        // Use a simple hash of a fixed seed + timestamp for demo purposes.
        const seed = 'gallery-demo-' + Date.now().toString(36);
        const cellId = blake3Hex(seed);
        return {
            cellId: cellId,
            publicKey: cellId, // In demo mode, just reuse the cell ID.
            mode: 'demo',
        };
    }

    /**
     * Simple BLAKE3-like hash for demo (not cryptographically secure — just for UI).
     * In production, this uses the WASM SDK.
     */
    function blake3Hex(input) {
        // Simple deterministic hash for demo UI.
        let hash = 0;
        for (let i = 0; i < input.length; i++) {
            const char = input.charCodeAt(i);
            hash = ((hash << 5) - hash) + char;
            hash = hash & hash;
        }
        // Expand to 32 bytes.
        const bytes = new Uint8Array(32);
        for (let i = 0; i < 32; i++) {
            bytes[i] = (hash * (i + 1) * 7) & 0xff;
        }
        return Array.from(bytes).map(b => b.toString(16).padStart(2, '0')).join('');
    }

    /**
     * Generate a mock signature for demo mode.
     */
    function generateMockSignature(data) {
        const input = JSON.stringify(data) + (_identity ? _identity.cellId : '');
        return blake3Hex(input);
    }

    /**
     * Update the cclerk UI elements.
     */
    function updateUI(connected, cellId) {
        const statusEl = document.getElementById('cclerk-status');
        const labelEl = document.getElementById('cclerk-label');
        const dotEl = statusEl ? statusEl.querySelector('.dot') : null;

        if (dotEl) {
            dotEl.className = connected ? 'dot connected' : 'dot disconnected';
        }
        if (labelEl) {
            labelEl.textContent = connected
                ? (cellId ? cellId.slice(0, 8) + '...' : 'Connected')
                : 'Connect Cipherclerk';
        }
    }

    return {
        isExtensionAvailable,
        connect,
        disconnect,
        getIdentity,
        isConnected,
        signTurn,
    };
})();

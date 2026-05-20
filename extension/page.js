// Injected into page context. Defines window.pyana API.
// Security: uses nonce-based event channels to prevent spoofing (Bug 7 fix).

// Retrieve the session nonce from the script tag's data attribute.
const currentScript = document.currentScript || document.querySelector('script[data-pyana-nonce]');
const SESSION_NONCE = currentScript?.dataset?.pyanaNonce;

if (!SESSION_NONCE) {
  console.error('[pyana] Failed to initialize: missing session nonce.');
  throw new Error('pyana: injection integrity check failed');
}

const pending = new Map();
let idCounter = 0;

function sendMessage(type, payload) {
  return new Promise((resolve, reject) => {
    const id = `pyana_${Date.now()}_${idCounter++}`;
    pending.set(id, { resolve, reject });
    window.dispatchEvent(new CustomEvent(`pyana:request:${SESSION_NONCE}`, {
      detail: { type, id, ...payload },
    }));
    setTimeout(() => {
      if (pending.has(id)) {
        pending.delete(id);
        reject(new Error('Pyana: request timed out'));
      }
    }, 30000);
  });
}

window.addEventListener(`pyana:response:${SESSION_NONCE}`, (event) => {
  const detail = event.detail;
  if (!detail) return;
  const resolver = pending.get(detail.id);
  if (!resolver) return;
  pending.delete(detail.id);
  if (detail.error) {
    resolver.reject(new Error(detail.error));
  } else {
    resolver.resolve(detail.result);
  }
});

// ---------------------------------------------------------------------------
// Event system
// ---------------------------------------------------------------------------

const eventListeners = new Map(); // event -> Set<callback>

function addListener(event, callback) {
  if (typeof callback !== 'function') {
    throw new TypeError('pyana.on: callback must be a function');
  }
  // Only expose non-sensitive event types to pages.
  const validEvents = ['ready', 'authorization', 'revoked'];
  if (!validEvents.includes(event)) {
    throw new Error(`pyana.on: unknown event "${event}". Valid: ${validEvents.join(', ')}`);
  }
  if (!eventListeners.has(event)) {
    eventListeners.set(event, new Set());
    // Subscribe to this event type in the background.
    sendMessage('pyana:subscribe', { event }).catch(() => {});
  }
  eventListeners.get(event).add(callback);
}

function removeListener(event, callback) {
  const listeners = eventListeners.get(event);
  if (listeners) {
    listeners.delete(callback);
  }
}

// Listen for event notifications forwarded from content script (nonce-secured channel).
window.addEventListener(`pyana:event:${SESSION_NONCE}`, (event) => {
  const { eventName, payload } = event.detail || {};
  const listeners = eventListeners.get(eventName);
  if (listeners) {
    for (const cb of listeners) {
      try { cb(payload); } catch (e) { console.error('[pyana] event handler error:', e); }
    }
  }
});

// ---------------------------------------------------------------------------
// Public API (minimal, security-hardened surface)
// ---------------------------------------------------------------------------

const pyana = {
  /**
   * Request authorization for an action on a resource.
   * The wallet evaluates internally and produces a ZK proof if allowed.
   *
   * @param {{action: string, resource: string, mode?: 'trusted'|'private'|'selective'}} request
   * @returns {Promise<{allowed: boolean, proof?: number[], facts?: string[], error?: string}>}
   */
  authorize(request) {
    return sendMessage('pyana:authorize', { request });
  },

  /**
   * Check if the pyana wallet extension is connected and available.
   * @returns {Promise<boolean>}
   */
  isConnected() {
    return sendMessage('pyana:isConnected').then(() => true).catch(() => false);
  },

  /**
   * Check whether the wallet CAN authorize a given action/resource, without
   * producing a proof. Returns only a boolean — does NOT reveal what capabilities
   * the wallet holds or how many tokens match.
   *
   * @param {{action: string, resource: string}} request
   * @returns {Promise<boolean>}
   */
  canAuthorize(request) {
    return sendMessage('pyana:canAuthorize', { request });
  },

  /**
   * Provision a capability token into the wallet.
   * The extension will show a confirmation dialog to the user.
   * Requires origin to be in the user-approved allowlist (prompted on first use).
   *
   * @param {Uint8Array|object} tokenBytes - Token data.
   * @returns {Promise<{accepted: boolean, tokenId?: string}>}
   */
  provision(tokenBytes) {
    let tokenData;
    if (tokenBytes instanceof Uint8Array) {
      try {
        tokenData = JSON.parse(new TextDecoder().decode(tokenBytes));
      } catch (e) {
        return Promise.reject(new Error('pyana.provision: invalid token bytes'));
      }
    } else if (tokenBytes && typeof tokenBytes === 'object') {
      tokenData = tokenBytes;
    } else {
      return Promise.reject(new Error('pyana.provision: tokenBytes must be Uint8Array or object'));
    }
    return sendMessage('pyana:provision', { tokenData });
  },

  /**
   * Broadcast an intent: "I need a capability matching this spec".
   * Requires user confirmation popup AND origin allowlist approval.
   *
   * @param {object} matchSpec - What capabilities are needed.
   * @param {object} [options] - Options for the intent.
   * @returns {Promise<{intentId: string, expiry: number}>}
   */
  postIntent(matchSpec, options) {
    return sendMessage('pyana:postIntent', { matchSpec, options });
  },

  /**
   * Register an event listener for non-sensitive wallet events.
   *
   * @param {'ready'|'authorization'|'revoked'} event
   * @param {function} callback
   */
  on(event, callback) {
    addListener(event, callback);
  },

  /**
   * Remove an event listener.
   *
   * @param {'ready'|'authorization'|'revoked'} event
   * @param {function} callback
   */
  off(event, callback) {
    removeListener(event, callback);
  },
};

Object.defineProperty(window, 'pyana', {
  value: Object.freeze(pyana),
  writable: false,
  configurable: false,
});

window.dispatchEvent(new Event('pyana:ready'));

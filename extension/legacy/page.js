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
  const validEvents = ['ready', 'authorization', 'revoked', 'stealthNoteReceived', 'privateTransfer', 'intentFulfilled', 'privacyModeChanged'];
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

// ---------------------------------------------------------------------------
// Utility: ArrayBuffer to base64 and back
// ---------------------------------------------------------------------------

function arrayBufferToBase64(buffer) {
  const bytes = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer);
  let binary = '';
  for (let i = 0; i < bytes.length; i++) {
    binary += String.fromCharCode(bytes[i]);
  }
  return btoa(binary);
}

function base64ToArrayBuffer(base64) {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes.buffer;
}

const pyana = {
  /**
   * Request authorization for an action on a resource.
   * The cipherclerk evaluates internally and produces a ZK proof if allowed.
   *
   * The user will be shown a disclosure picker to choose their privacy level:
   * - "full" (trusted): The verifier sees the full token.
   * - "selective": The user chooses which facts to reveal.
   * - "private" (zero-knowledge): Only allow/deny is shared.
   *
   * The site CANNOT force a disclosure level — the user always has the final choice.
   *
   * @param {{action: string, resource: string, requestedDisclosure?: Array<{key: string}>}} request
   *   - requestedDisclosure: Optional hint for which facts the site needs. The user can decline.
   * @returns {Promise<{allowed: boolean, proof?: number[], facts?: string[], mode?: string, disclosedFacts?: string[], error?: string}>}
   */
  authorize(request) {
    return sendMessage('pyana:authorize', { request });
  },

  /**
   * Check if the pyana cipherclerk extension is connected and available.
   * @returns {Promise<boolean>}
   */
  isConnected() {
    return sendMessage('pyana:isConnected').then(() => true).catch(() => false);
  },

  /**
   * Check whether the cipherclerk CAN authorize a given action/resource, without
   * producing a proof. Returns only a boolean — does NOT reveal what capabilities
   * the cipherclerk holds or how many tokens match.
   *
   * @param {{action: string, resource: string}} request
   * @returns {Promise<boolean>}
   */
  canAuthorize(request) {
    return sendMessage('pyana:canAuthorize', { request });
  },

  /**
   * Provision a capability token into the cipherclerk.
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
   * Get this cipherclerk's stealth meta-address for receiving private notes.
   * Returns { spendPubkey: number[], viewPubkey: number[] } or error if unavailable.
   * @returns {Promise<{spendPubkey: number[], viewPubkey: number[]}>}
   */
  getStealthAddress() {
    return sendMessage('pyana:getStealthAddress', {});
  },

  /**
   * Post an encrypted intent with searchable encryption (SSE) tokens.
   * The intent body is sealed so only matching fulfillers can decrypt.
   *
   * @param {object} matchSpec - The intent match specification.
   * @param {object} [options] - { expiry, keywords, recipientPubkey }
   * @returns {Promise<{intentId: string, expiry: number, encrypted: boolean}>}
   */
  postEncryptedIntent(matchSpec, options) {
    return sendMessage('pyana:postEncryptedIntent', { matchSpec, options });
  },

  /**
   * Send a private transfer to a recipient's stealth meta-address.
   * Amount is hidden via Pedersen commitments; recipient via stealth address.
   *
   * @param {number} amount - Amount to transfer (hidden from network).
   * @param {string} assetType - Asset type identifier.
   * @param {{spendPubkey: number[], viewPubkey: number[]}} recipientStealthMeta
   * @returns {Promise<{success: boolean, turnId?: string, commitment?: number[]}>}
   */
  privateTransfer(amount, assetType, recipientStealthMeta) {
    return sendMessage('pyana:privateTransfer', { amount, assetType, recipientStealthMeta });
  },

  /**
   * Create a bearer capability token.
   * Bearer caps are proof-carrying: whoever holds the token can exercise the capability.
   *
   * @param {string} targetCellHex - 64-char hex ID of the target cell.
   * @param {string} action - The action to authorize.
   * @param {number} [expiry] - Unix timestamp expiry (0 = no expiry).
   * @returns {Promise<{bearerTokenHex: string, targetCell: string, action: string}>}
   */
  createBearerCap(targetCellHex, action, expiry) {
    return sendMessage('pyana:createBearerCap', { targetCellHex, action, expiry: expiry || 0 });
  },

  /**
   * Verify a bearer capability token.
   *
   * @param {string} bearerTokenHex - The token to verify.
   * @param {string} delegatorKeyHex - The delegator's key.
   * @param {string} targetCellHex - The target cell.
   * @param {string} action - The action claimed.
   * @param {number} expiry - The claimed expiry.
   * @returns {Promise<{valid: boolean, expired: boolean}>}
   */
  verifyBearerCap(bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry) {
    return sendMessage('pyana:verifyBearerCap', {
      bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry,
    });
  },

  /**
   * Create a cell from a deployed factory.
   * Factory-created cells have verifiable provenance.
   *
   * @param {string} factoryVkHex - 64-char hex of the factory verification key.
   * @param {string} ownerPubkeyHex - 64-char hex of the new cell owner.
   * @param {number} initialBalance - Starting balance.
   * @returns {Promise<{childVk: string, paramHash: string, factoryVk: string}>}
   */
  createFromFactory(factoryVkHex, ownerPubkeyHex, initialBalance) {
    return sendMessage('pyana:createFromFactory', {
      factoryVkHex, ownerPubkeyHex, initialBalance,
    });
  },

  /**
   * Verify the provenance (factory origin) of a cell.
   *
   * @param {string} cellVkHex - The cell's verification key hash.
   * @param {string[]} knownFactoryVks - Array of known factory VK hex strings.
   * @returns {Promise<{fromFactory: boolean, factoryVk: string|null}>}
   */
  verifyProvenance(cellVkHex, knownFactoryVks) {
    return sendMessage('pyana:verifyProvenance', { cellVkHex, knownFactoryVks });
  },

  /**
   * Toggle sovereign mode for a cell.
   * In sovereign mode, the federation stores only a commitment; the agent
   * maintains the full state locally.
   *
   * @param {string} cellIdHex - 64-char hex of the cell ID.
   * @returns {Promise<{cellId: string, stateCommitment: string, mode: string}>}
   */
  makeCellSovereign(cellIdHex) {
    return sendMessage('pyana:makeCellSovereign', { cellIdHex });
  },

  /**
   * Execute a peer exchange with STARK proof between sovereign cells.
   *
   * @param {string} receiverCellHex - The receiver cell ID.
   * @param {number} amount - Amount to exchange.
   * @returns {Promise<{exchangeId: string, proofCommitment: string}>}
   */
  peerExchange(receiverCellHex, amount) {
    return sendMessage('pyana:peerExchange', { receiverCellHex, amount });
  },

  /**
   * Compose multiple proofs into a single aggregate proof.
   *
   * @param {Array<{proofJson: string, publicInputs?: number[]}>} proofs
   * @param {'and'|'or'|'chain'|'aggregate'} mode - Composition strategy.
   * @returns {Promise<{composedProof: string, mode: string, inputCount: number, valid: boolean}>}
   */
  composeProofs(proofs, mode) {
    return sendMessage('pyana:composeProofs', { proofs, mode });
  },

  /**
   * Build, sign, and submit a turn to the pyana node.
   * The turn is constructed locally (via WASM), signed with the cipherclerk's key,
   * and then POSTed to the configured node endpoint.
   *
   * @param {{action: string, resource?: string, amount?: number, recipient?: string, metadata?: object}} turnSpec
   * @returns {Promise<{turnId?: string, submitted: boolean, error?: string, nodeResult?: object}>}
   */
  signTurn(turnSpec) {
    return sendMessage('pyana:signTurn', { turnSpec });
  },

  /**
   * Query the cipherclerk's balance from the pyana node.
   *
   * @returns {Promise<{balance?: number, error?: string}>}
   */
  queryBalance() {
    return sendMessage('pyana:queryBalance', {});
  },

  /**
   * Read the current node URL configuration.
   * Returns { nodeUrl, wssUrl, wsUrl } (devnetKey is redacted).
   *
   * @returns {Promise<{nodeUrl: string, wssUrl: string, wsUrl: string, devnetKey: string}>}
   */
  getNodeConfig() {
    return sendMessage('pyana:getNodeConfig', {});
  },

  /**
   * Update the node URL configuration.
   * Only available from extension popup context; page-context calls will be rejected.
   *
   * @param {{nodeUrl?: string, wssUrl?: string, wsUrl?: string, devnetKey?: string}} config
   * @returns {Promise<{success: boolean, nodeUrl: string}>}
   */
  setNodeConfig(config) {
    return sendMessage('pyana:setNodeConfig', { config });
  },

  // =========================================================================
  // CapTP operations
  // =========================================================================

  /**
   * Share a cell as a pyana:// URI (export sturdy ref).
   * @param {string} cellId - 64-char hex cell ID.
   * @returns {Promise<{uri: string, cellId: string, nodeId: string}>}
   */
  shareCapability(cellId) {
    return sendMessage('pyana:shareCapability', { cellId });
  },

  /**
   * Accept (enliven) a pyana:// URI, returning live ref info.
   * @param {string} uri - A pyana:// URI.
   * @returns {Promise<{refId: string, cellId: string, nodeId: string, permissions: string}>}
   */
  acceptCapability(uri) {
    return sendMessage('pyana:acceptCapability', { uri });
  },

  /**
   * Create a handoff certificate for offline capability delegation.
   * @param {string} cellId - Cell to delegate.
   * @param {string} recipientPk - Recipient's public key (hex).
   * @returns {Promise<{certificateHash: string, cellId: string, recipientPk: string}>}
   */
  createHandoff(cellId, recipientPk) {
    return sendMessage('pyana:createHandoff', { cellId, recipientPk });
  },

  // =========================================================================
  // Directory / Namespace
  // =========================================================================

  /**
   * Mount a service in the governed directory.
   * @param {string} path - Full path (e.g., "/services/oracle").
   * @param {{sturdyRef: string, kind?: string, tags?: string[]}} opts
   * @returns {Promise<{path: string, version: number, kind: string}>}
   */
  mountService(path, opts) {
    return sendMessage('pyana:mountService', { path, ...opts });
  },

  /**
   * Discover services by tags.
   * @param {string[]} tags - Tags to search.
   * @returns {Promise<{results: Array}>}
   */
  discoverServices(tags) {
    return sendMessage('pyana:discoverServices', { tags });
  },

  /**
   * Resolve a path to its sturdy ref and metadata.
   * @param {string} path - Directory path.
   * @returns {Promise<object>}
   */
  resolvePath(path) {
    return sendMessage('pyana:resolvePath', { path });
  },

  // =========================================================================
  // Storage
  // =========================================================================

  /**
   * Write data to content-addressed storage.
   * @param {ArrayBuffer|Uint8Array} data - Data to store.
   * @returns {Promise<{hash: string, size: number}>}
   */
  storageWrite(data) {
    return sendMessage('pyana:storageWrite', { data: arrayBufferToBase64(data) });
  },

  /**
   * Read data from storage by content hash.
   * @param {string} hash - Content hash.
   * @returns {Promise<{hash: string, data: ArrayBuffer, size: number}>}
   */
  storageRead(hash) {
    return sendMessage('pyana:storageRead', { hash }).then(result => {
      if (result && result.data) {
        result.data = base64ToArrayBuffer(result.data);
      }
      return result;
    });
  },

  /**
   * Check storage quota usage.
   * @returns {Promise<{bytesStored: number, bytesLimit: number, computronsUsed: number, computronsRemaining: number, objectCount: number}>}
   */
  storageQuota() {
    return sendMessage('pyana:storageQuota', {});
  },

  // =========================================================================
  // Federation
  // =========================================================================

  /**
   * Get federation status.
   * @returns {Promise<{mode: string, height: number, peerCount: number, merkleRoot: string}>}
   */
  federationStatus() {
    return sendMessage('pyana:federationStatus', {});
  },

  /**
   * Propose route updates to the federation.
   * @param {Array} routes - Route entries to propose.
   * @returns {Promise<{proposalId: string, submitted: boolean}>}
   */
  proposeRoutes(routes) {
    return sendMessage('pyana:proposeRoutes', { routes });
  },

  /**
   * Vote on a governance proposal.
   * @param {string} proposalId - Proposal ID.
   * @param {boolean} approve - Whether to approve.
   * @returns {Promise<{accepted: boolean, proposalId: string}>}
   */
  voteOnProposal(proposalId, approve) {
    return sendMessage('pyana:voteOnProposal', { proposalId, approve });
  },

  /**
   * Register an event listener for non-sensitive cipherclerk events.
   *
   * @param {'ready'|'authorization'|'revoked'|'stealthNoteReceived'|'privateTransfer'|'intentFulfilled'} event
   * @param {function} callback
   */
  on(event, callback) {
    addListener(event, callback);
  },

  /**
   * Remove an event listener.
   *
   * @param {'ready'|'authorization'|'revoked'|'stealthNoteReceived'|'privateTransfer'} event
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

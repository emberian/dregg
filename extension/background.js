// Pyana wallet background service worker.
// Manages wallet state, evaluates authorization, generates proofs via WASM.

const STORAGE_KEY = 'pyana_wallet';
const ALLOWED_ORIGINS_KEY = 'pyana_allowed_origins';
const NODE_WSS_URL = 'wss://localhost:8420/ws';
const NODE_WS_URL = 'ws://localhost:8420/ws'; // Fallback for localhost only.
const DISCOVERY_URL = 'https://emberian.github.io/pyana/discovery.json';
const DISCOVERY_POLL_INTERVAL = 5 * 60 * 1000; // 5 minutes

// ---------------------------------------------------------------------------
// WASM module loading
// ---------------------------------------------------------------------------

let wasm = null;

const wasmReady = (async () => {
  try {
    wasm = await import('./pyana_wasm.js');
    await wasm.default();
    console.log('[pyana] WASM module loaded');
  } catch (e) {
    console.warn('[pyana] WASM module unavailable, falling back to stubs:', e.message);
    wasm = null;
  }
})();

// Queue for authorize calls that arrive before WASM is ready.
const pendingQueue = [];
let ready = false;
wasmReady.then(() => {
  ready = true;
  for (const { msg, sender, resolve } of pendingQueue) {
    resolve(handleMessage(msg, sender));
  }
  pendingQueue.length = 0;
});

// ---------------------------------------------------------------------------
// Event bus (authorization, revoked notifications)
// ---------------------------------------------------------------------------

const subscribers = new Map(); // tabId -> Set of event names

function notifySubscribers(event, payload) {
  for (const [tabId, events] of subscribers) {
    if (events.has(event)) {
      chrome.tabs.sendMessage(tabId, { type: 'pyana:event', event, payload }).catch(() => {
        subscribers.delete(tabId);
      });
    }
  }
}

// ---------------------------------------------------------------------------
// Wallet state
// ---------------------------------------------------------------------------

let state = null;

async function loadState() {
  if (state) return state;
  const stored = await chrome.storage.local.get(STORAGE_KEY);
  if (stored[STORAGE_KEY]) {
    state = stored[STORAGE_KEY];
  } else {
    const publicKey = new Uint8Array(32);
    const secretKey = new Uint8Array(64);
    crypto.getRandomValues(publicKey);
    crypto.getRandomValues(secretKey);
    state = {
      locked: false,
      publicKey: Array.from(publicKey),
      secretKey: Array.from(secretKey),
      tokens: [],
      receiptChain: [],
      log: [],
    };
    await saveState();
  }
  return state;
}

async function saveState() {
  if (!state) return;
  await chrome.storage.local.set({ [STORAGE_KEY]: state });
}

// ---------------------------------------------------------------------------
// Origin allowlist management
// ---------------------------------------------------------------------------

async function getOriginAllowlist() {
  const stored = await chrome.storage.local.get(ALLOWED_ORIGINS_KEY);
  return stored[ALLOWED_ORIGINS_KEY] || [];
}

async function addOriginToAllowlist(origin) {
  const allowlist = await getOriginAllowlist();
  if (!allowlist.includes(origin)) {
    allowlist.push(origin);
    await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
  }
}

// ---------------------------------------------------------------------------
// Authorization logic — delegates to WASM when available
// ---------------------------------------------------------------------------

function evaluateDatalog(token, request) {
  if (wasm) {
    try {
      const facts = token.actions.map(a => ({
        predicate: 'grant',
        terms: [a, token.resource || '*'],
      }));
      const reqJson = JSON.stringify({
        action: request.action,
        service: request.resource,
      });
      const result = wasm.evaluate_datalog(JSON.stringify(facts), reqJson);
      return {
        allowed: result.conclusion === 'allow',
        trace: result.steps.map(s => `rule(${s.rule_id}) derived ${s.derived_predicate_hex}`),
      };
    } catch (e) {
      console.warn('[pyana] WASM evaluate_datalog failed, using stub:', e.message);
    }
  }

  // Stub fallback: checks action membership.
  const allowed = token.actions.includes(request.action);
  const trace = allowed
    ? [`token(${token.id}) grants action(${request.action}) on resource(${request.resource})`]
    : [`no matching grant for action(${request.action})`];
  return { allowed, trace };
}

function generateProof(witness, mode) {
  if (wasm) {
    try {
      const hash = witness.reduce((acc, b, i) => acc ^ (b << ((i % 4) * 8)), 0) >>> 0;
      const depth = mode === 'private' ? 8 : mode === 'selective' ? 4 : 2;
      const result = wasm.generate_stark_proof(hash, depth);
      return new TextEncoder().encode(result.proof_json);
    } catch (e) {
      console.warn('[pyana] WASM generate_stark_proof failed, using stub:', e.message);
    }
  }

  const size = mode === 'private' ? 256 : mode === 'selective' ? 128 : 64;
  const proof = new Uint8Array(size);
  crypto.getRandomValues(proof);
  return proof;
}

function verifyToken(tokenStr, rootKey, appId, action) {
  if (wasm) {
    try {
      return wasm.verify_token(tokenStr, rootKey, appId, action);
    } catch (e) {
      console.warn('[pyana] WASM verify_token failed:', e.message);
    }
  }
  return { allowed: true, policy: null, error: null };
}

function computeMerkleRoot(leaves) {
  if (wasm) {
    try {
      return wasm.compute_merkle_root(JSON.stringify(leaves));
    } catch (e) {
      console.warn('[pyana] WASM compute_merkle_root failed:', e.message);
    }
  }
  return { root_hex: '0'.repeat(64), num_leaves: leaves.length };
}

async function authorize(request) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { allowed: false, error: 'Wallet is locked' };
  }

  const matchingToken = wallet.tokens.find(
    t => t.actions.includes(request.action) &&
         (t.resource === '*' || t.resource === request.resource) &&
         (!t.expiry || t.expiry > Date.now())
  );

  if (!matchingToken) {
    return { allowed: false, error: 'No capability token grants this action' };
  }

  const evalResult = evaluateDatalog(matchingToken, request);
  if (!evalResult.allowed) {
    return { allowed: false, facts: evalResult.trace };
  }

  const mode = request.mode || 'trusted';
  const witness = new TextEncoder().encode(
    JSON.stringify({ token: matchingToken.id, action: request.action, resource: request.resource })
  );
  const proof = generateProof(witness, mode);

  const receiptHash = Array.from(proof.slice(0, 16))
    .map(b => b.toString(16).padStart(2, '0'))
    .join('');
  wallet.receiptChain.push(receiptHash);

  wallet.log.push({
    action: request.action,
    resource: request.resource,
    allowed: true,
    timestamp: Date.now(),
  });
  await saveState();

  const result = { allowed: true, proof: Array.from(proof), facts: evalResult.trace };
  notifySubscribers('authorization', {
    action: request.action,
    resource: request.resource,
    allowed: true,
  });
  return result;
}

// ---------------------------------------------------------------------------
// canAuthorize — dry-run check, returns boolean only (Bug 2 fix)
// ---------------------------------------------------------------------------

async function canAuthorize(request) {
  const wallet = await loadState();
  if (wallet.locked) return false;

  const matchingToken = wallet.tokens.find(
    t => t.actions.includes(request.action) &&
         (t.resource === '*' || t.resource === request.resource) &&
         (!t.expiry || t.expiry > Date.now())
  );

  if (!matchingToken) return false;

  const evalResult = evaluateDatalog(matchingToken, request);
  return evalResult.allowed;
}

// ---------------------------------------------------------------------------
// Token provisioning (with user confirmation popup)
// ---------------------------------------------------------------------------

async function provisionToken(tokenData, senderTabId) {
  return new Promise((resolve) => {
    const popupUrl = chrome.runtime.getURL('provision.html') +
      '?data=' + encodeURIComponent(JSON.stringify(tokenData));

    chrome.windows.create({
      url: popupUrl,
      type: 'popup',
      width: 400,
      height: 480,
      focused: true,
    }, (win) => {
      const listener = async (message, sender, sendResponse) => {
        if (message.type !== 'pyana:provisionDecision') return;
        chrome.runtime.onMessage.removeListener(listener);

        if (message.accepted) {
          const wallet = await loadState();
          const token = {
            id: `tok_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`,
            actions: tokenData.actions || [],
            resource: tokenData.resource || '*',
            expiry: tokenData.expiry || null,
            issuer: tokenData.issuer || null,
            provisioned: Date.now(),
          };
          wallet.tokens.push(token);
          await saveState();
          resolve({ accepted: true, tokenId: token.id });
        } else {
          resolve({ accepted: false });
        }
      };
      chrome.runtime.onMessage.addListener(listener);
    });
  });
}

// ---------------------------------------------------------------------------
// Intent matching engine
// ---------------------------------------------------------------------------

const intentPool = new Map(); // intentId -> { intent, receivedAt }
const DEFAULT_INTENT_EXPIRY_MS = 5 * 60 * 1000;
const INTENT_GC_INTERVAL = 60_000;

/**
 * Post an intent (Need) — requires user confirmation popup (Bug 5 fix).
 */
async function postIntent(matchSpec, options) {
  // Show confirmation popup before broadcasting.
  const confirmed = await showIntentConfirmation('postIntent', matchSpec, options);
  if (!confirmed) {
    return { error: 'User denied intent broadcast' };
  }

  const expiry = options?.expiry || (Date.now() + DEFAULT_INTENT_EXPIRY_MS);
  const intentId = await computeIntentId('need', matchSpec, expiry);
  const intent = {
    id: intentId,
    kind: 'need',
    matcher: matchSpec,
    expiry,
    createdAt: Date.now(),
  };
  intentPool.set(intentId, { intent, receivedAt: Date.now() });

  if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
    nodeWs.send(JSON.stringify({ type: 'broadcast_intent', intent }));
  }

  return { intentId, expiry };
}

/**
 * Post an offer (Offer) — requires user confirmation popup (Bug 5 fix).
 * NOTE: offerCapability is now popup-only (removed from page API), but
 * we keep the confirmation for defense in depth.
 */
async function offerCapability(matchSpec, options) {
  const confirmed = await showIntentConfirmation('offerCapability', matchSpec, options);
  if (!confirmed) {
    return { error: 'User denied capability offer' };
  }

  const expiry = options?.expiry || (Date.now() + DEFAULT_INTENT_EXPIRY_MS);
  const intentId = await computeIntentId('offer', matchSpec, expiry);
  const intent = {
    id: intentId,
    kind: 'offer',
    matcher: matchSpec,
    expiry,
    createdAt: Date.now(),
  };
  intentPool.set(intentId, { intent, receivedAt: Date.now() });

  if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
    nodeWs.send(JSON.stringify({ type: 'broadcast_intent', intent }));
  }

  return { intentId, expiry };
}

/**
 * Show a confirmation popup for intent/offer actions (Bug 5 fix).
 */
function showIntentConfirmation(action, matchSpec, options) {
  return new Promise((resolve) => {
    const popupUrl = chrome.runtime.getURL('confirm-intent.html') +
      '?action=' + encodeURIComponent(action) +
      '&spec=' + encodeURIComponent(JSON.stringify(matchSpec)) +
      '&options=' + encodeURIComponent(JSON.stringify(options || {}));

    chrome.windows.create({
      url: popupUrl,
      type: 'popup',
      width: 400,
      height: 380,
      focused: true,
    }, (win) => {
      const listener = (message, sender, sendResponse) => {
        if (message.type !== 'pyana:intentConfirmation') return;
        chrome.runtime.onMessage.removeListener(listener);
        resolve(message.confirmed === true);
      };
      chrome.runtime.onMessage.addListener(listener);

      // If the popup is closed without responding, deny.
      if (win?.id) {
        chrome.windows.onRemoved.addListener(function onClose(closedId) {
          if (closedId === win.id) {
            chrome.windows.onRemoved.removeListener(onClose);
            chrome.runtime.onMessage.removeListener(listener);
            resolve(false);
          }
        });
      }
    });
  });
}

/**
 * List active intents in the pool (popup-only, Bug 4 fix).
 */
function listIntents(filter) {
  const now = Date.now();
  const results = [];
  for (const [, { intent }] of intentPool) {
    if (intent.expiry <= now) continue;
    if (filter?.kind && intent.kind !== filter.kind) continue;
    results.push({
      id: intent.id,
      kind: intent.kind,
      matcher: intent.matcher,
      expiry: intent.expiry,
    });
  }
  return results;
}

/**
 * Receive an intent from the gossip network and attempt local matching.
 */
async function receiveGossipIntent(intent) {
  const now = Date.now();
  if (intent.expiry <= now) return;
  if (intentPool.has(intent.id)) return;

  intentPool.set(intent.id, { intent, receivedAt: now });

  if (intent.kind !== 'need') return;

  const wallet = await loadState();
  if (wallet.locked) return;

  const matchResult = matchIntentLocally(intent, wallet.tokens, now);
  if (matchResult) {
    notifySubscribers('intentMatch', {
      intentId: intent.id,
      actions: matchResult.grantedActions,
      resource: matchResult.resource,
      mode: 'trusted',
    });
  }
}

function matchIntentLocally(intent, tokens, now) {
  const spec = intent.matcher;
  if (!spec) return null;

  for (const token of tokens) {
    if (token.expiry && token.expiry <= now) continue;

    if (spec.actions && spec.actions.length > 0) {
      const actionsSatisfied = spec.actions.every(pattern => {
        if (!pattern.action) return true;
        return token.actions.includes(pattern.action) || token.actions.includes('*');
      });
      if (!actionsSatisfied) continue;
    }

    if (spec.resourcePattern) {
      const tokenResource = token.resource || '*';
      if (tokenResource !== '*' && tokenResource !== spec.resourcePattern) {
        if (!tokenResource.endsWith('/*') ||
            !spec.resourcePattern.startsWith(tokenResource.slice(0, -2))) {
          continue;
        }
      }
    }

    if (spec.constraints && spec.constraints.length > 0) {
      let constraintsMet = true;
      for (const c of spec.constraints) {
        if (c.type === 'appId' && token.appId !== c.value) { constraintsMet = false; break; }
        if (c.type === 'service' && token.service !== c.value) { constraintsMet = false; break; }
        if (c.type === 'notExpiredAt' && token.expiry && token.expiry <= c.value) { constraintsMet = false; break; }
      }
      if (!constraintsMet) continue;
    }

    const grantedActions = spec.actions
      ? spec.actions.map(p => p.action).filter(Boolean)
      : token.actions;

    return {
      tokenId: token.id,
      grantedActions,
      resource: spec.resourcePattern || token.resource || '*',
    };
  }

  return null;
}

async function computeIntentId(kind, matchSpec, expiry) {
  const data = JSON.stringify({ kind, matchSpec, expiry, nonce: Math.random() });
  const encoded = new TextEncoder().encode(data);
  const hashBuffer = await crypto.subtle.digest('SHA-256', encoded);
  const hashArray = Array.from(new Uint8Array(hashBuffer));
  return hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
}

function gcIntentPool() {
  const now = Date.now();
  for (const [id, { intent }] of intentPool) {
    if (intent.expiry <= now) {
      intentPool.delete(id);
    }
  }
}

setInterval(gcIntentPool, INTENT_GC_INTERVAL);

// ---------------------------------------------------------------------------
// Wallet state queries
// ---------------------------------------------------------------------------

async function getWalletState() {
  const wallet = await loadState();
  return {
    locked: wallet.locked,
    tokenCount: wallet.tokens.length,
    chainLength: wallet.receiptChain.length,
  };
}

/**
 * getCapabilities — popup-only (Bug 2 fix). Pages use canAuthorize() instead.
 */
async function getCapabilities() {
  const wallet = await loadState();
  if (wallet.locked) return [];
  const actions = new Set();
  for (const token of wallet.tokens) {
    for (const action of token.actions) {
      actions.add(action);
    }
  }
  return Array.from(actions);
}

async function revokeToken(tokenId) {
  const wallet = await loadState();
  const idx = wallet.tokens.findIndex(t => t.id === tokenId);
  if (idx === -1) return { revoked: false, error: 'Token not found' };
  wallet.tokens.splice(idx, 1);
  await saveState();
  notifySubscribers('revoked', { tokenId });
  return { revoked: true };
}

// ---------------------------------------------------------------------------
// Sender validation helpers
// ---------------------------------------------------------------------------

/**
 * Check if a message sender is the extension's own popup/UI.
 */
function isExtensionPopup(sender) {
  // Extension popups have sender.url starting with the extension's own origin.
  if (!sender?.url) return false;
  return sender.url.startsWith(`chrome-extension://${chrome.runtime.id}/`);
}

/**
 * Check if a message sender is a content script (tab-based page context).
 */
function isContentScript(sender) {
  return sender?.tab != null;
}

// ---------------------------------------------------------------------------
// Origin permission request handler
// ---------------------------------------------------------------------------

function handleOriginPermissionRequest(origin, method) {
  return new Promise((resolve) => {
    const popupUrl = chrome.runtime.getURL('origin-permission.html') +
      '?origin=' + encodeURIComponent(origin) +
      '&method=' + encodeURIComponent(method);

    chrome.windows.create({
      url: popupUrl,
      type: 'popup',
      width: 420,
      height: 320,
      focused: true,
    }, (win) => {
      const listener = async (message, sender, sendResponse) => {
        if (message.type !== 'pyana:originPermissionDecision') return;
        chrome.runtime.onMessage.removeListener(listener);

        if (message.granted) {
          await addOriginToAllowlist(origin);
          resolve({ granted: true });
        } else {
          resolve({ granted: false });
        }
      };
      chrome.runtime.onMessage.addListener(listener);

      // If popup closed without decision, deny.
      if (win?.id) {
        chrome.windows.onRemoved.addListener(function onClose(closedId) {
          if (closedId === win.id) {
            chrome.windows.onRemoved.removeListener(onClose);
            chrome.runtime.onMessage.removeListener(listener);
            resolve({ granted: false });
          }
        });
      }
    });
  });
}

// ---------------------------------------------------------------------------
// Message router
// ---------------------------------------------------------------------------

// Methods accessible from page context (via content script).
const PAGE_ALLOWED_METHODS = new Set([
  'pyana:authorize',
  'pyana:isConnected',
  'pyana:canAuthorize',
  'pyana:subscribe',
  'pyana:provision',
  'pyana:postIntent',
  // Note: pyana:offerCapability, pyana:getCapabilities, pyana:listIntents are
  // NOT accessible from page context — popup-only.
]);

// Methods that ONLY the extension popup can call.
const POPUP_ONLY_METHODS = new Set([
  'pyana:unlock',
  'pyana:lock',
  'pyana:getCapabilities',
  'pyana:listIntents',
  'pyana:offerCapability',
  'pyana:revoke',
  'pyana:getState',
  'pyana:getFederation',
  'pyana:refreshDiscovery',
]);

async function handleMessage(message, sender) {
  switch (message.type) {
    case 'pyana:authorize':
      return { id: message.id, result: await authorize(message.request) };

    case 'pyana:isConnected':
      return { id: message.id, result: true };

    case 'pyana:canAuthorize':
      return { id: message.id, result: await canAuthorize(message.request) };

    case 'pyana:getCapabilities':
      return { id: message.id, result: await getCapabilities() };

    case 'pyana:getState':
      return { id: message.id, result: await getWalletState() };

    case 'pyana:lock': {
      const wallet = await loadState();
      wallet.locked = true;
      await saveState();
      return { id: message.id, result: true };
    }

    case 'pyana:unlock': {
      // Bug 1 fix: unlock ONLY from extension popup.
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Unlock is only available from the extension popup.' };
      }
      const wallet = await loadState();
      wallet.locked = false;
      await saveState();
      notifySubscribers('ready', { locked: false });
      return { id: message.id, result: true };
    }

    case 'pyana:provision': {
      const tabId = sender?.tab?.id;
      const result = await provisionToken(message.tokenData, tabId);
      return { id: message.id, result };
    }

    case 'pyana:revoke': {
      const result = await revokeToken(message.tokenId);
      return { id: message.id, result };
    }

    case 'pyana:subscribe': {
      const tabId = sender?.tab?.id;
      if (tabId != null) {
        if (!subscribers.has(tabId)) subscribers.set(tabId, new Set());
        subscribers.get(tabId).add(message.event);
      }
      return { id: message.id, result: true };
    }

    case 'pyana:provisionDecision':
      return { id: message.id, result: true };

    case 'pyana:intentConfirmation':
      return { id: message.id, result: true };

    case 'pyana:postIntent': {
      const result = await postIntent(message.matchSpec, message.options);
      return { id: message.id, result };
    }

    case 'pyana:offerCapability': {
      const result = await offerCapability(message.matchSpec, message.options);
      return { id: message.id, result };
    }

    case 'pyana:listIntents': {
      const result = listIntents(message.filter);
      return { id: message.id, result };
    }

    case 'pyana:getFederation':
      return { id: message.id, result: federationState };

    case 'pyana:refreshDiscovery':
      await fetchDiscovery();
      return { id: message.id, result: federationState };

    case 'pyana:requestOriginPermission': {
      const result = await handleOriginPermissionRequest(message.origin, message.method);
      return result;
    }

    case 'pyana:originPermissionDecision':
      return { id: message.id, result: true };

    default:
      return { id: message.id, error: 'Unknown message type' };
  }
}

chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
  const dispatch = async () => {
    // Access control: check if this sender is allowed to call this method.
    const msgType = message.type;

    // Popup-only methods: reject from content scripts (page context).
    if (POPUP_ONLY_METHODS.has(msgType) && !isExtensionPopup(sender)) {
      return { id: message.id, error: `"${msgType}" is only available from the extension popup.` };
    }

    // For page-sourced messages via content script: verify the method is page-accessible.
    if (isContentScript(sender) && !PAGE_ALLOWED_METHODS.has(msgType) && !POPUP_ONLY_METHODS.has(msgType)) {
      // Allow internal messages like requestOriginPermission from content script.
      if (msgType !== 'pyana:requestOriginPermission') {
        return { id: message.id, error: `"${msgType}" is not available from page context.` };
      }
    }

    // Defer authorize calls until WASM is ready (other calls are fine without it).
    if (message.type === 'pyana:authorize' && !ready) {
      return new Promise((resolve) => {
        pendingQueue.push({ msg: message, sender, resolve });
      });
    }
    return handleMessage(message, sender);
  };
  dispatch().then(sendResponse).catch(err => {
    sendResponse({ id: message.id, error: String(err) });
  });
  return true;
});

// ---------------------------------------------------------------------------
// WebSocket connection to pyana-node for real-time sync (Bug 6 fix: wss)
// ---------------------------------------------------------------------------

let nodeWs = null;
let wsReconnectDelay = 1000;
const WS_MAX_RECONNECT_DELAY = 60000;

function connectNodeWs() {
  if (nodeWs && (nodeWs.readyState === WebSocket.CONNECTING || nodeWs.readyState === WebSocket.OPEN)) {
    return;
  }

  // Try wss:// first. Fall back to ws:// ONLY for localhost (Bug 6 fix).
  tryConnect(NODE_WSS_URL, () => {
    console.warn('[pyana] wss:// connection failed, falling back to ws:// (localhost only)');
    const wsUrl = new URL(NODE_WS_URL);
    if (wsUrl.hostname === 'localhost' || wsUrl.hostname === '127.0.0.1' || wsUrl.hostname === '::1') {
      tryConnect(NODE_WS_URL, () => {
        scheduleReconnect();
      });
    } else {
      console.error('[pyana] Refusing ws:// fallback for non-localhost host:', wsUrl.hostname);
      scheduleReconnect();
    }
  });
}

function tryConnect(url, onFail) {
  try {
    nodeWs = new WebSocket(url);
  } catch (e) {
    console.warn('[pyana] WebSocket construction failed:', e.message);
    if (onFail) onFail();
    return;
  }

  nodeWs.onopen = () => {
    console.log('[pyana] WebSocket connected to node via', url);
    wsReconnectDelay = 1000;

    nodeWs.send(JSON.stringify({
      type: 'subscribe',
      topics: ['roots', 'revocations', 'receipts', 'intents'],
    }));
  };

  nodeWs.onmessage = async (event) => {
    let msg;
    try {
      msg = JSON.parse(event.data);
    } catch {
      return;
    }

    switch (msg.type) {
      case 'root': {
        console.log('[pyana] New root:', msg.height, msg.merkle_root);
        notifySubscribers('root', { height: msg.height, merkle_root: msg.merkle_root });
        break;
      }
      case 'revocation': {
        const wallet = await loadState();
        const idx = wallet.tokens.findIndex(t => t.id === msg.token_id);
        if (idx !== -1) {
          wallet.tokens.splice(idx, 1);
          await saveState();
          console.log('[pyana] Token revoked via WS:', msg.token_id);
        }
        notifySubscribers('revoked', { tokenId: msg.token_id });
        break;
      }
      case 'receipt': {
        const wallet = await loadState();
        wallet.receiptChain.push(msg.hash);
        await saveState();
        notifySubscribers('receipt', { hash: msg.hash });
        break;
      }
      case 'intent': {
        await receiveGossipIntent(msg.intent);
        break;
      }
      case 'subscribed':
        console.log('[pyana] Subscribed to topics:', msg.topics);
        break;
      case 'error':
        console.warn('[pyana] WS error from node:', msg.message);
        break;
    }
  };

  nodeWs.onclose = () => {
    console.log('[pyana] WebSocket disconnected from node');
    nodeWs = null;
    scheduleReconnect();
  };

  nodeWs.onerror = (err) => {
    console.warn('[pyana] WebSocket error:', err);
    nodeWs = null;
    if (onFail) onFail();
  };
}

function scheduleReconnect() {
  setTimeout(() => {
    connectNodeWs();
  }, wsReconnectDelay);
  wsReconnectDelay = Math.min(wsReconnectDelay * 2, WS_MAX_RECONNECT_DELAY);
}

// ---------------------------------------------------------------------------
// Federation Discovery
// ---------------------------------------------------------------------------

let federationState = {
  nodes: [],
  intentService: null,
  lastUpdated: null,
  fetchError: null,
};

async function fetchDiscovery() {
  try {
    const response = await fetch(DISCOVERY_URL, {
      cache: 'no-cache',
      headers: { 'Accept': 'application/json' },
    });
    if (!response.ok) {
      throw new Error(`HTTP ${response.status}: ${response.statusText}`);
    }
    const data = await response.json();

    federationState = {
      nodes: (data.federation || []).map(node => ({
        nodeId: node.node_id,
        ticket: node.ticket,
        lastSeen: node.last_seen,
        role: node.role,
      })),
      intentService: data.intent_service ? {
        nodeId: data.intent_service.node_id,
        ticket: data.intent_service.ticket,
        lastSeen: data.intent_service.last_seen,
      } : null,
      lastUpdated: data.updated_at,
      commit: data.commit,
      fetchError: null,
    };

    console.log('[pyana] Federation discovery updated:', federationState.nodes.length, 'nodes');
    notifySubscribers('federation', {
      nodes: federationState.nodes,
      intentService: federationState.intentService,
      lastUpdated: federationState.lastUpdated,
    });
  } catch (e) {
    console.warn('[pyana] Federation discovery fetch failed:', e.message);
    federationState.fetchError = e.message;
  }
}

let discoveryInterval = null;

function startDiscoveryPolling() {
  fetchDiscovery();
  discoveryInterval = setInterval(fetchDiscovery, DISCOVERY_POLL_INTERVAL);
}

function stopDiscoveryPolling() {
  if (discoveryInterval) {
    clearInterval(discoveryInterval);
    discoveryInterval = null;
  }
}

// ---------------------------------------------------------------------------
// Initialization
// ---------------------------------------------------------------------------

loadState();
connectNodeWs();
startDiscoveryPolling();

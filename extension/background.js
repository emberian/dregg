// Pyana wallet background service worker.
// Manages wallet state, evaluates authorization, generates proofs (via WASM when available).

const STORAGE_KEY = 'pyana_wallet';

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

function evaluateDatalog(token, request) {
  // Stub: checks action membership. Will call pyana WASM Datalog engine.
  const allowed = token.actions.includes(request.action);
  const trace = allowed
    ? [`token(${token.id}) grants action(${request.action}) on resource(${request.resource})`]
    : [`no matching grant for action(${request.action})`];
  return { allowed, trace };
}

function generateProof(witness, mode) {
  // Stub: returns random bytes. Will call pyana WASM circuit prover.
  const size = mode === 'private' ? 256 : mode === 'selective' ? 128 : 64;
  const proof = new Uint8Array(size);
  crypto.getRandomValues(proof);
  return proof;
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

  return { allowed: true, proof: Array.from(proof), facts: evalResult.trace };
}

async function getWalletState() {
  const wallet = await loadState();
  return {
    locked: wallet.locked,
    tokenCount: wallet.tokens.length,
    chainLength: wallet.receiptChain.length,
  };
}

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

chrome.runtime.onMessage.addListener((message, _sender, sendResponse) => {
  const handle = async () => {
    switch (message.type) {
      case 'pyana:authorize':
        return { id: message.id, result: await authorize(message.request) };
      case 'pyana:isConnected':
        return { id: message.id, result: true };
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
        const wallet = await loadState();
        wallet.locked = false;
        await saveState();
        return { id: message.id, result: true };
      }
      default:
        return { id: message.id, error: 'Unknown message type' };
    }
  };
  handle().then(sendResponse).catch(err => {
    sendResponse({ id: message.id, error: String(err) });
  });
  return true;
});

loadState();

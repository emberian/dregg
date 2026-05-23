// Pyana wallet background service worker.
// Manages wallet state, evaluates authorization, generates proofs via WASM.

const STORAGE_KEY = 'pyana_wallet';
const ENCRYPTED_STATE_KEY = 'pyana_wallet_encrypted';
const MNEMONIC_KEY = 'pyana_mnemonic_encrypted';
const STEALTH_KEYS_KEY = 'pyana_stealth_keys_encrypted';
const ALLOWED_ORIGINS_KEY = 'pyana_allowed_origins';
const NODE_CONFIG_KEY = 'pyana_node_config';
const DEFAULT_NODE_URL = 'https://devnet.pyana.fg-goose.online';
const DEFAULT_NODE_WSS_URL = 'wss://devnet.pyana.fg-goose.online/ws';
const DEFAULT_NODE_WS_URL = 'ws://localhost:8420/ws'; // Fallback for localhost only.
const DISCOVERY_URL = 'https://emberian.github.io/pyana/discovery.json';
const DISCOVERY_POLL_INTERVAL = 5 * 60 * 1000; // 5 minutes
const PBKDF2_ITERATIONS = 600000; // OWASP recommendation for PBKDF2-SHA256
const DISCLOSURE_PREFS_KEY = 'pyana_disclosure_prefs'; // Per-origin disclosure preferences
const LOCK_TIMEOUT_MS = 5 * 60 * 1000; // 5 minutes auto-lock
const ORIGIN_PERMISSION_EXPIRY_MS = 24 * 60 * 60 * 1000; // 24 hours default
const RATE_LIMIT_MAX_CALLS = 5; // Max authorize calls per origin per window
const RATE_LIMIT_WINDOW_MS = 60 * 1000; // 60-second sliding window
// Internal encryption key is now randomly generated per session (see getInternalEncryptionKey).
const PRIVACY_STATE_KEY = 'pyana_privacy_state'; // Tracks active privacy features

// ---------------------------------------------------------------------------
// Node configuration (user-configurable via settings page)
// ---------------------------------------------------------------------------

let nodeConfig = {
  nodeUrl: DEFAULT_NODE_URL,
  wssUrl: DEFAULT_NODE_WSS_URL,
  wsUrl: DEFAULT_NODE_WS_URL,
  devnetKey: '', // X-Devnet-Key header value
};

/**
 * Load node configuration from storage.
 */
async function loadNodeConfig() {
  const stored = await chrome.storage.local.get(NODE_CONFIG_KEY);
  if (stored[NODE_CONFIG_KEY]) {
    nodeConfig = { ...nodeConfig, ...stored[NODE_CONFIG_KEY] };
  }
  return nodeConfig;
}

/**
 * Save node configuration to storage.
 */
async function saveNodeConfig(config) {
  nodeConfig = { ...nodeConfig, ...config };
  await chrome.storage.local.set({ [NODE_CONFIG_KEY]: nodeConfig });
  // Reconnect WebSocket with new URL.
  if (nodeWs) {
    nodeWs.close();
    nodeWs = null;
  }
  connectNodeWs();
}

/**
 * Get HTTP headers for node API requests.
 */
function getNodeHeaders() {
  const headers = { 'Content-Type': 'application/json' };
  if (nodeConfig.devnetKey) {
    headers['X-Devnet-Key'] = nodeConfig.devnetKey;
  }
  return headers;
}

/**
 * Make an HTTP request to the node API with proper error handling.
 * @param {string} path - API path (e.g. '/turns/submit')
 * @param {object} options - fetch options override
 * @returns {Promise<{ok: boolean, data?: any, error?: string, status?: number}>}
 */
async function nodeRequest(path, options = {}) {
  const url = nodeConfig.nodeUrl.replace(/\/$/, '') + path;
  const baseHeaders = getNodeHeaders();
  const mergedHeaders = { ...baseHeaders, ...(options.headers || {}) };
  try {
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(10000),
      ...options,
      headers: mergedHeaders,
    });
    if (resp.ok) {
      const data = await resp.json().catch(() => null);
      return { ok: true, data, status: resp.status };
    } else {
      const errText = await resp.text().catch(() => '');
      return { ok: false, error: `HTTP ${resp.status}: ${errText}`, status: resp.status };
    }
  } catch (e) {
    if (e.name === 'TimeoutError' || e.name === 'AbortError') {
      return { ok: false, error: 'Node request timed out. Is the node online?' };
    }
    return { ok: false, error: `Network error: ${e.message}` };
  }
}

// Load node config on startup.
loadNodeConfig();

// ---------------------------------------------------------------------------
// WASM module loading (compatible with both Chrome and Firefox MV3 workers)
// ---------------------------------------------------------------------------

let wasm = null;
let wasmLoaded = false;
let wasmLoadError = null;

// Load WASM without ES module import() — uses fetch + WebAssembly.instantiate.
// The pyana_wasm.js glue is loaded via importScripts (no-modules build) or
// inlined initialization when built with --target web.
const wasmReady = (async () => {
  try {
    // Try importScripts for no-modules build (Firefox-compatible).
    try {
      importScripts('./pyana_wasm.js');
    } catch (_importErr) {
      // importScripts failed — pyana_wasm.js may not exist yet (dev mode).
      // Fall through to fetch-based loading below.
    }

    // If importScripts populated a global init function (wasm-bindgen no-modules),
    // use it. Otherwise, try fetch-based loading for --target web builds.
    if (typeof wasm_bindgen !== 'undefined') {
      // wasm-bindgen no-modules pattern: wasm_bindgen is a global function.
      const wasmUrl = chrome.runtime.getURL('pyana_wasm_bg.wasm');
      await wasm_bindgen(wasmUrl);
      wasm = wasm_bindgen;
      wasmLoaded = true;
      console.log('[pyana] WASM module loaded via importScripts/wasm_bindgen');
    } else if (typeof __pyana_wasm_init !== 'undefined') {
      // Alternative: custom global init if we bundled differently.
      wasm = await __pyana_wasm_init();
      wasmLoaded = true;
      console.log('[pyana] WASM module loaded via __pyana_wasm_init');
    } else {
      // Fetch-based fallback: manually instantiate the WASM module.
      const wasmUrl = chrome.runtime.getURL('pyana_wasm_bg.wasm');
      const response = await fetch(wasmUrl);
      if (!response.ok) {
        throw new Error(`Failed to fetch WASM: HTTP ${response.status}`);
      }
      const wasmBytes = await response.arrayBuffer();
      const { instance } = await WebAssembly.instantiate(wasmBytes, {});
      wasm = instance.exports;
      wasmLoaded = true;
      console.log('[pyana] WASM module loaded via fetch+instantiate');
    }
  } catch (e) {
    console.error('[pyana] WASM module failed to load:', e.message);
    wasm = null;
    wasmLoaded = false;
    wasmLoadError = e.message;
  }
})();

/**
 * Require WASM to be loaded for cryptographic operations.
 * Throws if WASM is unavailable — crypto ops MUST NOT silently degrade.
 */
function requireWasm(operation) {
  if (!wasmLoaded || !wasm) {
    throw new Error(
      `WASM cryptographic module not loaded. Cannot perform ${operation}. ` +
      (wasmLoadError ? `Load error: ${wasmLoadError}` : 'Module unavailable.')
    );
  }
}

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
// Auto-lock timer (P2-20)
// ---------------------------------------------------------------------------

let lockTimer = null;

function resetLockTimer() {
  if (lockTimer !== null) {
    clearTimeout(lockTimer);
  }
  lockTimer = setTimeout(async () => {
    console.log('[pyana] Auto-lock triggered after inactivity');
    await lockWallet();
    notifySubscribers('ready', { locked: true });
  }, LOCK_TIMEOUT_MS);
}

// ---------------------------------------------------------------------------
// Rate limiter for authorize calls (P2-11)
// Persisted to session storage so state survives service worker eviction.
// ---------------------------------------------------------------------------

async function checkRateLimit(origin) {
  const { _rateLimits } = await chrome.storage.session.get('_rateLimits') || {};
  const limits = _rateLimits || {};
  const now = Date.now();
  const entry = limits[origin] || { count: 0, windowStart: now };

  if (now - entry.windowStart > RATE_LIMIT_WINDOW_MS) {
    entry.count = 0;
    entry.windowStart = now;
  }

  if (entry.count >= RATE_LIMIT_MAX_CALLS) return false;

  entry.count++;
  limits[origin] = entry;
  await chrome.storage.session.set({ _rateLimits: limits });
  return true;
}

// ---------------------------------------------------------------------------
// Internal encryption key (for when no passphrase is set)
// ---------------------------------------------------------------------------

/**
 * Get a random internal encryption key. Generated on first use and stored in
 * session storage (cleared when browser closes, requiring passphrase on restart).
 * This protects the brief window between wallet creation and passphrase setup.
 */
async function getInternalEncryptionKey() {
  let { _internalKey } = await chrome.storage.session.get('_internalKey');
  if (!_internalKey) {
    const keyBytes = new Uint8Array(32);
    crypto.getRandomValues(keyBytes);
    _internalKey = Array.from(keyBytes).map(b => b.toString(16).padStart(2, '0')).join('');
    await chrome.storage.session.set({ _internalKey });
  }
  return _internalKey;
}

// ---------------------------------------------------------------------------
// Encryption helpers (PBKDF2 + AES-256-GCM via SubtleCrypto)
// ---------------------------------------------------------------------------

/**
 * Derive an AES-256-GCM key from a passphrase using PBKDF2.
 */
async function deriveEncryptionKey(passphrase, salt) {
  const enc = new TextEncoder();
  const keyMaterial = await crypto.subtle.importKey(
    'raw', enc.encode(passphrase), 'PBKDF2', false, ['deriveKey']
  );
  return crypto.subtle.deriveKey(
    { name: 'PBKDF2', salt, iterations: PBKDF2_ITERATIONS, hash: 'SHA-256' },
    keyMaterial,
    { name: 'AES-GCM', length: 256 },
    false,
    ['encrypt', 'decrypt']
  );
}

/**
 * Encrypt a plaintext string with a passphrase. Returns { salt, iv, ciphertext } as arrays.
 */
async function encryptWithPassphrase(plaintext, passphrase) {
  const salt = crypto.getRandomValues(new Uint8Array(16));
  const iv = crypto.getRandomValues(new Uint8Array(12));
  const key = await deriveEncryptionKey(passphrase, salt);
  const enc = new TextEncoder();
  const ciphertext = await crypto.subtle.encrypt(
    { name: 'AES-GCM', iv },
    key,
    enc.encode(plaintext)
  );
  return {
    salt: Array.from(salt),
    iv: Array.from(iv),
    ciphertext: Array.from(new Uint8Array(ciphertext)),
  };
}

/**
 * Decrypt ciphertext encrypted with encryptWithPassphrase.
 */
async function decryptWithPassphrase(encrypted, passphrase) {
  const salt = new Uint8Array(encrypted.salt);
  const iv = new Uint8Array(encrypted.iv);
  const ciphertext = new Uint8Array(encrypted.ciphertext);
  const key = await deriveEncryptionKey(passphrase, salt);
  const plainBuffer = await crypto.subtle.decrypt(
    { name: 'AES-GCM', iv },
    key,
    ciphertext
  );
  return new TextDecoder().decode(plainBuffer);
}

// ---------------------------------------------------------------------------
// BIP39 Mnemonic generation (pure JS, matches SDK's Rust implementation)
// ---------------------------------------------------------------------------

// Subset not needed: the full 2048-word list is loaded from a bundled file.
// For the extension, we use a simplified approach with the WASM module when
// available, or a JS fallback.

/**
 * Generate a 24-word mnemonic. Prefers WASM; falls back to JS implementation.
 */
async function generateMnemonic() {
  if (wasm && wasm.generate_mnemonic) {
    try {
      return wasm.generate_mnemonic();
    } catch (e) {
      console.warn('[pyana] WASM generate_mnemonic failed, using JS fallback:', e.message);
    }
  }
  // JS fallback: generate 256 bits of entropy, compute SHA-256 checksum,
  // then map to word indices. Word list is fetched from bundled resource.
  const entropy = crypto.getRandomValues(new Uint8Array(32));
  const hashBuffer = await crypto.subtle.digest('SHA-256', entropy);
  const checksum = new Uint8Array(hashBuffer)[0];

  // Build 264-bit array.
  const bits = new Array(264);
  for (let i = 0; i < 32; i++) {
    for (let bit = 0; bit < 8; bit++) {
      bits[i * 8 + bit] = (entropy[i] >> (7 - bit)) & 1;
    }
  }
  for (let bit = 0; bit < 8; bit++) {
    bits[256 + bit] = (checksum >> (7 - bit)) & 1;
  }

  // Convert to 24 word indices (11 bits each).
  const indices = [];
  for (let i = 0; i < 24; i++) {
    let index = 0;
    for (let bit = 0; bit < 11; bit++) {
      if (bits[i * 11 + bit]) {
        index |= 1 << (10 - bit);
      }
    }
    indices.push(index);
  }

  // Load word list.
  const wordlist = await getWordlist();
  return indices.map(i => wordlist[i]).join(' ');
}

/**
 * Validate a mnemonic (24 words, valid checksum).
 */
async function validateMnemonic(mnemonic) {
  if (wasm && wasm.validate_mnemonic) {
    try {
      return wasm.validate_mnemonic(mnemonic);
    } catch (e) {
      // Fall through to JS validation.
    }
  }

  const words = mnemonic.trim().split(/\s+/);
  if (words.length !== 24) return false;

  const wordlist = await getWordlist();
  const indices = [];
  for (const word of words) {
    const idx = wordlist.indexOf(word);
    if (idx === -1) return false;
    indices.push(idx);
  }

  // Reconstruct bits.
  const bits = new Array(264);
  for (let i = 0; i < 24; i++) {
    for (let bit = 0; bit < 11; bit++) {
      bits[i * 11 + bit] = (indices[i] >> (10 - bit)) & 1;
    }
  }

  // Extract entropy and checksum.
  const entropy = new Uint8Array(32);
  for (let i = 0; i < 32; i++) {
    for (let bit = 0; bit < 8; bit++) {
      if (bits[i * 8 + bit]) {
        entropy[i] |= 1 << (7 - bit);
      }
    }
  }

  let checksumByte = 0;
  for (let bit = 0; bit < 8; bit++) {
    if (bits[256 + bit]) {
      checksumByte |= 1 << (7 - bit);
    }
  }

  const hashBuffer = await crypto.subtle.digest('SHA-256', entropy);
  const expectedChecksum = new Uint8Array(hashBuffer)[0];
  return checksumByte === expectedChecksum;
}

// Cached wordlist.
let _wordlistCache = null;

async function getWordlist() {
  if (_wordlistCache) return _wordlistCache;
  try {
    const url = chrome.runtime.getURL('bip39_english.txt');
    const resp = await fetch(url);
    const text = await resp.text();
    _wordlistCache = text.trim().split('\n');
    if (_wordlistCache.length === 2048) return _wordlistCache;
  } catch (e) {
    console.warn('[pyana] Failed to load wordlist from bundle:', e.message);
  }
  // Hardcoded fallback: return null (mnemonic operations will fail gracefully).
  _wordlistCache = null;
  return null;
}

/**
 * Derive an Ed25519 keypair from a mnemonic + passphrase using BLAKE3 (via WASM).
 * Falls back to a deterministic PBKDF2-HMAC-SHA512 derivation via Web Crypto
 * (BIP39-compatible: mnemonic -> seed, then use first 32 bytes as Ed25519 seed).
 */
async function deriveKeypairFromMnemonic(mnemonic, passphrase) {
  if (wasm && wasm.derive_keypair_from_mnemonic) {
    try {
      const result = wasm.derive_keypair_from_mnemonic(mnemonic, passphrase, 'pyana/0');
      return { publicKey: result.public_key, secretKey: result.secret_key };
    } catch (e) {
      console.warn('[pyana] WASM derive_keypair_from_mnemonic failed:', e.message);
    }
  }
  // WASM is required for Ed25519 keypair derivation. The Web Crypto API does not
  // support Ed25519 point multiplication, so there is no valid JS fallback.
  // Producing a fake public key (e.g. SHA-256 of the seed) is a security risk —
  // it creates an invalid key that cannot sign or verify anything.
  throw new Error(
    'WASM cryptographic module is required for keypair derivation. ' +
    'Ed25519 key generation cannot be performed without the native module. ' +
    (wasmLoadError ? `WASM load error: ${wasmLoadError}` : 'Module unavailable.')
  );
}

// ---------------------------------------------------------------------------
// Stealth address support
// ---------------------------------------------------------------------------

/**
 * Derive stealth keys from the wallet seed (mnemonic).
 *
 * Produces a StealthMetaAddress consisting of:
 *   - spend_pubkey: Ed25519 public key for spending (derived via BLAKE3(seed, "pyana-stealth-spend"))
 *   - view_pubkey: X25519 public key for scanning (derived via BLAKE3(seed, "pyana-stealth-view"))
 *
 * The private keys are stored encrypted alongside the wallet state.
 *
 * TODO: WASM exports needed:
 *   - wasm.derive_stealth_keys(mnemonic, passphrase) -> { spend_pubkey, spend_privkey, view_pubkey, view_privkey }
 *     Must use BLAKE3(seed, "pyana-stealth-spend") for Ed25519 spend key
 *     and BLAKE3(seed, "pyana-stealth-view") for X25519 view key.
 *   - wasm.stealth_pubkey_from_privkey(privkey_bytes, key_type) -> pubkey_bytes
 *     (key_type: "ed25519" | "x25519")
 */
async function deriveStealthKeys(mnemonic, passphrase) {
  requireWasm('deriveStealthKeys');

  // TODO: wasm.derive_stealth_keys should implement:
  //   1. seed = BIP39_to_seed(mnemonic, passphrase)
  //   2. spend_seed = BLAKE3(seed, context="pyana-stealth-spend") -> 32 bytes
  //   3. view_seed = BLAKE3(seed, context="pyana-stealth-view") -> 32 bytes
  //   4. spend_keypair = Ed25519::from_seed(spend_seed)
  //   5. view_keypair = X25519::from_seed(view_seed)
  if (!wasm.derive_stealth_keys) {
    throw new Error(
      'WASM export "derive_stealth_keys" not available. ' +
      'Stealth address support requires the updated WASM module.'
    );
  }

  const result = wasm.derive_stealth_keys(mnemonic, passphrase || '');
  return {
    spendPubkey: Array.from(result.spend_pubkey),   // Ed25519 public key (32 bytes)
    spendPrivkey: Array.from(result.spend_privkey),  // Ed25519 private key (32 bytes)
    viewPubkey: Array.from(result.view_pubkey),      // X25519 public key (32 bytes)
    viewPrivkey: Array.from(result.view_privkey),    // X25519 private key (32 bytes)
  };
}

/**
 * Get or derive the stealth meta-address for the current wallet.
 * The meta-address (spend_pubkey + view_pubkey) is the public-facing identifier
 * that senders use to derive one-time stealth addresses for us.
 *
 * Returns { spendPubkey: number[], viewPubkey: number[] } or null if unavailable.
 */
async function getStealthMetaAddress() {
  const wallet = await loadState();
  if (wallet.locked) return null;

  // Check if stealth keys are already derived and stored.
  if (wallet.stealthMeta) {
    return {
      spendPubkey: wallet.stealthMeta.spendPubkey,
      viewPubkey: wallet.stealthMeta.viewPubkey,
    };
  }

  // Derive from mnemonic. Requires wallet to be unlocked and mnemonic available.
  const mnemonic = await getMnemonic();
  if (!mnemonic) return null;

  try {
    const keys = await deriveStealthKeys(mnemonic, walletPassphrase === await getInternalEncryptionKey() ? '' : walletPassphrase || '');

    // Store the full stealth key material in wallet state (encrypted at rest).
    state.stealthMeta = {
      spendPubkey: keys.spendPubkey,
      viewPubkey: keys.viewPubkey,
    };
    state.stealthPrivate = {
      spendPrivkey: keys.spendPrivkey,
      viewPrivkey: keys.viewPrivkey,
    };
    await saveState();

    return {
      spendPubkey: keys.spendPubkey,
      viewPubkey: keys.viewPubkey,
    };
  } catch (e) {
    console.warn('[pyana] Failed to derive stealth keys:', e.message);
    return null;
  }
}

/**
 * Check if a note announcement is addressed to us (stealth ownership check).
 *
 * A stealth note announcement contains:
 *   - ephemeralPubkey: X25519 public key used by the sender
 *   - oneTimePubkey: the derived one-time address the funds were sent to
 *   - encryptedMemo: optional encrypted memo (decryptable with shared secret)
 *
 * We check ownership by:
 *   1. Performing X25519 DH: sharedSecret = X25519(viewPrivkey, ephemeralPubkey)
 *   2. Deriving the expected one-time pubkey: hash(sharedSecret) * G + spendPubkey
 *   3. Comparing with the announced oneTimePubkey
 *
 * TODO: WASM exports needed:
 *   - wasm.check_stealth_ownership(view_privkey, spend_pubkey, ephemeral_pubkey, one_time_pubkey)
 *     -> { is_ours: bool, one_time_privkey: Uint8Array | null }
 *   - wasm.decrypt_stealth_memo(shared_secret, encrypted_memo) -> plaintext
 */
function checkStealthOwnership(announcement, viewPrivkey, spendPubkey) {
  requireWasm('checkStealthOwnership');

  // TODO: wasm.check_stealth_ownership should implement:
  //   1. shared_secret = x25519(view_privkey, ephemeral_pubkey)
  //   2. scalar = BLAKE3(shared_secret, context="pyana-stealth-derive")
  //   3. expected_one_time = scalar * G_ed25519 + spend_pubkey
  //   4. return expected_one_time == one_time_pubkey
  //   5. If match: one_time_privkey = scalar + spend_privkey (mod L)
  if (!wasm.check_stealth_ownership) {
    throw new Error(
      'WASM export "check_stealth_ownership" not available. ' +
      'Stealth scanning requires the updated WASM module.'
    );
  }

  const result = wasm.check_stealth_ownership(
    new Uint8Array(viewPrivkey),
    new Uint8Array(spendPubkey),
    new Uint8Array(announcement.ephemeralPubkey),
    new Uint8Array(announcement.oneTimePubkey)
  );

  return {
    isOurs: result.is_ours,
    oneTimePrivkey: result.one_time_privkey ? Array.from(result.one_time_privkey) : null,
  };
}

/**
 * Scan a batch of note announcements for notes addressed to us.
 * Returns an array of matched notes with their derived spending keys.
 */
async function scanStealthNotes(announcements) {
  const wallet = await loadState();
  if (wallet.locked || !wallet.stealthPrivate) return [];

  const viewPrivkey = wallet.stealthPrivate.viewPrivkey;
  const spendPubkey = wallet.stealthMeta.spendPubkey;
  const matched = [];

  for (const announcement of announcements) {
    try {
      const result = checkStealthOwnership(announcement, viewPrivkey, spendPubkey);
      if (result.isOurs) {
        matched.push({
          noteId: announcement.noteId,
          amount: announcement.amount, // Will be null for committed (private) transfers
          assetType: announcement.assetType,
          oneTimePrivkey: result.oneTimePrivkey,
          ephemeralPubkey: announcement.ephemeralPubkey,
          memo: announcement.encryptedMemo || null,
          receivedAt: Date.now(),
        });
      }
    } catch (e) {
      // Skip announcements that fail to check (malformed, etc.)
      console.warn('[pyana] Stealth check failed for announcement:', e.message);
    }
  }

  // Store matched notes in wallet state.
  if (matched.length > 0) {
    if (!state.stealthNotes) state.stealthNotes = [];
    state.stealthNotes.push(...matched);
    await saveState();

    notifySubscribers('stealthNoteReceived', {
      count: matched.length,
      noteIds: matched.map(n => n.noteId),
    });
  }

  return matched;
}

// ---------------------------------------------------------------------------
// Encrypted intent posting (SSE tokens + sealed body)
// ---------------------------------------------------------------------------

/**
 * Post an encrypted intent with searchable encryption (SSE) tokens.
 *
 * The intent body is sealed (encrypted) so only the fulfiller can read the
 * full match specification. SSE tokens derived from keywords allow the intent
 * service to route without seeing plaintext.
 *
 * TODO: WASM exports needed:
 *   - wasm.generate_sse_tokens(keywords: string[]) -> Uint8Array[]
 *     Derives deterministic searchable encryption tokens from keywords using
 *     BLAKE3 keyed hash with a per-intent random key.
 *   - wasm.seal_intent_body(plaintext_json: string, recipient_pubkey: Uint8Array | null)
 *     -> { ciphertext: Uint8Array, ephemeral_pubkey: Uint8Array, nonce: Uint8Array }
 *     If recipient_pubkey is null, uses a broadcast encryption scheme where any
 *     matching node can decrypt with the SSE key.
 *   - wasm.unseal_intent_body(ciphertext, ephemeral_pubkey, nonce, privkey)
 *     -> plaintext_json
 *
 * @param {object} matchSpec - The intent match specification (same as postIntent)
 * @param {object} options - { expiry, keywords, recipientPubkey }
 *   keywords: array of strings for SSE token generation (e.g. ["swap", "USDC", "ETH"])
 *   recipientPubkey: optional targeted encryption to a specific fulfiller
 */
async function postEncryptedIntent(matchSpec, options = {}) {
  requireWasm('postEncryptedIntent');

  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  // Show confirmation popup before broadcasting (same security model as postIntent).
  const confirmed = await showIntentConfirmation('postEncryptedIntent', matchSpec, options);
  if (!confirmed) {
    return { error: 'User denied encrypted intent broadcast' };
  }

  const expiry = options.expiry || (Date.now() + DEFAULT_INTENT_EXPIRY_MS);
  const keywords = options.keywords || extractKeywordsFromSpec(matchSpec);

  // Generate SSE tokens from keywords.
  // TODO: wasm.generate_sse_tokens should use BLAKE3 keyed hash for each keyword.
  if (!wasm.generate_sse_tokens) {
    throw new Error(
      'WASM export "generate_sse_tokens" not available. ' +
      'Encrypted intent posting requires the updated WASM module.'
    );
  }
  const sseTokens = wasm.generate_sse_tokens(keywords);

  // Seal the match specification body.
  if (!wasm.seal_intent_body) {
    throw new Error(
      'WASM export "seal_intent_body" not available. ' +
      'Encrypted intent posting requires the updated WASM module.'
    );
  }
  const recipientPubkey = options.recipientPubkey
    ? new Uint8Array(options.recipientPubkey)
    : null;
  const sealed = wasm.seal_intent_body(
    JSON.stringify(matchSpec),
    recipientPubkey
  );

  // Compute an intent ID for the encrypted intent.
  const intentId = await computeIntentId('need', matchSpec, expiry);

  const encryptedIntent = {
    id: intentId,
    kind: 'need',
    expiry,
    createdAt: Date.now(),
    encrypted: true,
    sseTokens: Array.from(sseTokens),
    sealedBody: {
      ciphertext: Array.from(sealed.ciphertext),
      ephemeralPubkey: Array.from(sealed.ephemeral_pubkey),
      nonce: Array.from(sealed.nonce),
    },
    creatorPubkey: wallet.publicKey,
  };

  // Store locally.
  intentPool.set(intentId, { intent: encryptedIntent, receivedAt: Date.now() });

  // Broadcast via WebSocket.
  if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
    nodeWs.send(JSON.stringify({
      type: 'broadcast_encrypted_intent',
      intent: encryptedIntent,
    }));
  }

  return { intentId, expiry, encrypted: true, sseTokenCount: keywords.length };
}

/**
 * Extract searchable keywords from a match specification for SSE token generation.
 * Heuristic: pull action names, resource patterns, constraint values.
 */
function extractKeywordsFromSpec(matchSpec) {
  const keywords = [];

  if (matchSpec.actions) {
    for (const a of matchSpec.actions) {
      if (a.action) keywords.push(a.action.toLowerCase());
      if (a.resource) keywords.push(a.resource.toLowerCase());
    }
  }
  if (matchSpec.resourcePattern) {
    // Split resource pattern into segments.
    const segments = matchSpec.resourcePattern.split('/').filter(Boolean);
    keywords.push(...segments.map(s => s.toLowerCase()));
  }
  if (matchSpec.constraints) {
    for (const c of matchSpec.constraints) {
      if (c.value && typeof c.value === 'string') {
        keywords.push(c.value.toLowerCase());
      }
    }
  }

  // Deduplicate.
  return [...new Set(keywords)];
}

// ---------------------------------------------------------------------------
// Private transfer support (committed/hidden amounts)
// ---------------------------------------------------------------------------

/**
 * Send a private transfer to a recipient's stealth meta-address.
 *
 * This creates:
 *   1. A one-time stealth address for the recipient (from their meta-address)
 *   2. A Pedersen value commitment hiding the amount
 *   3. A range proof (Bulletproof-style) proving the amount is valid
 *   4. A committed turn submitted to the network
 *
 * TODO: WASM exports needed:
 *   - wasm.derive_stealth_one_time_address(recipient_spend_pubkey, recipient_view_pubkey)
 *     -> { one_time_pubkey: Uint8Array, ephemeral_pubkey: Uint8Array, ephemeral_privkey: Uint8Array }
 *   - wasm.create_value_commitment(amount: u64, blinding: Uint8Array)
 *     -> { commitment: Uint8Array, blinding: Uint8Array }
 *     Uses Ristretto Pedersen commitment: C = amount * H + blinding * G
 *   - wasm.generate_range_proof(amount: u64, blinding: Uint8Array, commitment: Uint8Array)
 *     -> { proof: Uint8Array, proof_size_bytes: number }
 *   - wasm.build_committed_turn(params: JSON) -> { turn_bytes: Uint8Array, turn_id: string }
 *     Builds a Turn with committed value fields.
 *
 * @param {number} amount - The amount to transfer (hidden from network)
 * @param {string} assetType - Asset type identifier (e.g. "PYANA", "USDC")
 * @param {object} recipientStealthMeta - { spendPubkey: number[], viewPubkey: number[] }
 * @returns {object} { turnId, commitment, ephemeralPubkey, success }
 */
async function privateTransfer(amount, assetType, recipientStealthMeta) {
  requireWasm('privateTransfer');

  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }
  if (!wallet.secretKey) {
    return { error: 'Wallet secret key not available (locked or not derived)' };
  }
  if (!amount || amount <= 0) {
    return { error: 'Amount must be positive' };
  }
  if (!recipientStealthMeta || !recipientStealthMeta.spendPubkey || !recipientStealthMeta.viewPubkey) {
    return { error: 'Recipient stealth meta-address is required (spendPubkey + viewPubkey)' };
  }

  // Step 1: Derive a one-time stealth address for the recipient.
  // TODO: wasm.derive_stealth_one_time_address should implement:
  //   1. Generate ephemeral X25519 keypair
  //   2. shared_secret = X25519(ephemeral_privkey, recipient_view_pubkey)
  //   3. scalar = BLAKE3(shared_secret, context="pyana-stealth-derive")
  //   4. one_time_pubkey = scalar * G_ed25519 + recipient_spend_pubkey
  if (!wasm.derive_stealth_one_time_address) {
    throw new Error(
      'WASM export "derive_stealth_one_time_address" not available. ' +
      'Private transfers require the updated WASM module.'
    );
  }
  const stealthAddr = wasm.derive_stealth_one_time_address(
    new Uint8Array(recipientStealthMeta.spendPubkey),
    new Uint8Array(recipientStealthMeta.viewPubkey)
  );

  // Step 2: Create a Pedersen value commitment hiding the amount.
  // TODO: wasm.create_value_commitment should use Ristretto points:
  //   C = amount * H + blinding * G, where H is a nothing-up-my-sleeve generator.
  if (!wasm.create_value_commitment) {
    throw new Error(
      'WASM export "create_value_commitment" not available. ' +
      'Private transfers require the updated WASM module.'
    );
  }
  // Generate random blinding factor.
  const blindingBytes = new Uint8Array(32);
  crypto.getRandomValues(blindingBytes);
  const commitment = wasm.create_value_commitment(amount, blindingBytes);

  // Step 3: Generate a range proof proving amount is in valid range [0, 2^64).
  // TODO: wasm.generate_range_proof should produce a Bulletproof or similar
  //   compact range proof over the Pedersen commitment.
  if (!wasm.generate_range_proof) {
    throw new Error(
      'WASM export "generate_range_proof" not available. ' +
      'Private transfers require the updated WASM module.'
    );
  }
  const rangeProof = wasm.generate_range_proof(
    amount,
    blindingBytes,
    new Uint8Array(commitment.commitment)
  );

  // Step 4: Build the committed turn.
  // TODO: wasm.build_committed_turn constructs a Turn with:
  //   - sender: wallet.publicKey
  //   - recipient: one_time_pubkey (stealth)
  //   - value_commitment: the Pedersen commitment
  //   - range_proof: the range proof bytes
  //   - asset_type: assetType
  //   - ephemeral_pubkey: for stealth scanning by recipient
  if (!wasm.build_committed_turn) {
    throw new Error(
      'WASM export "build_committed_turn" not available. ' +
      'Private transfers require the updated WASM module.'
    );
  }
  const turnParams = {
    sender_pubkey: wallet.publicKey,
    sender_privkey: wallet.secretKey,
    recipient_one_time_pubkey: Array.from(stealthAddr.one_time_pubkey),
    value_commitment: Array.from(commitment.commitment),
    blinding_factor: Array.from(commitment.blinding),
    range_proof: Array.from(rangeProof.proof),
    asset_type: assetType,
    amount: amount, // Included in the turn for the sender's records, NOT transmitted
    ephemeral_pubkey: Array.from(stealthAddr.ephemeral_pubkey),
  };
  const turn = wasm.build_committed_turn(JSON.stringify(turnParams));

  // Step 5: Submit the committed turn via WebSocket or HTTP.
  let submitted = false;
  if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
    nodeWs.send(JSON.stringify({
      type: 'submit_committed_turn',
      turn_id: turn.turn_id,
      turn_bytes: Array.from(turn.turn_bytes),
    }));
    submitted = true;
  } else {
    // Fallback: HTTP submission via configurable node URL.
    const resp = await nodeRequest('/turns/submit', {
      method: 'POST',
      body: JSON.stringify({
        turn_id: turn.turn_id,
        turn_bytes: Array.from(turn.turn_bytes),
        committed: true,
      }),
    });
    if (resp.ok) {
      submitted = true;
    } else {
      return { error: `Node rejected committed turn: ${resp.error}` };
    }
  }

  // Log the transfer locally (we keep the plaintext amount for our own records).
  wallet.log.push({
    action: 'privateTransfer',
    resource: assetType,
    allowed: true,
    timestamp: Date.now(),
    mode: 'private',
    turnId: turn.turn_id,
    amount: amount,
    recipientStealthMeta: {
      spendPubkey: recipientStealthMeta.spendPubkey,
      viewPubkey: recipientStealthMeta.viewPubkey,
    },
  });
  await saveState();

  // Update privacy state.
  await updatePrivacyState({ lastPrivateTransfer: Date.now() });

  notifySubscribers('privateTransfer', {
    turnId: turn.turn_id,
    assetType,
    submitted,
  });

  return {
    success: true,
    turnId: turn.turn_id,
    commitment: Array.from(commitment.commitment),
    ephemeralPubkey: Array.from(stealthAddr.ephemeral_pubkey),
    rangeProofSize: rangeProof.proof_size_bytes || rangeProof.proof.length,
    submitted,
  };
}

// ---------------------------------------------------------------------------
// Privacy mode state tracking
// ---------------------------------------------------------------------------

/**
 * Get the current privacy features state.
 * Returns which privacy features are active for the session.
 */
async function getPrivacyState() {
  const wallet = await loadState();
  if (wallet.locked) {
    return { active: false, locked: true };
  }

  const stored = await chrome.storage.session.get(PRIVACY_STATE_KEY);
  const privacyState = stored[PRIVACY_STATE_KEY] || {};

  const stealthMeta = wallet.stealthMeta || null;
  const hasStealthKeys = stealthMeta !== null;
  const stealthNotesCount = (wallet.stealthNotes || []).length;

  return {
    active: true,
    features: {
      stealthAddresses: hasStealthKeys,
      committedTransfers: privacyState.committedTransfersActive || false,
      encryptedIntents: privacyState.encryptedIntentsActive || false,
    },
    stealthMeta: stealthMeta ? {
      spendPubkey: stealthMeta.spendPubkey,
      viewPubkey: stealthMeta.viewPubkey,
    } : null,
    stealthNotesReceived: stealthNotesCount,
    lastPrivateTransfer: privacyState.lastPrivateTransfer || null,
    sessionStarted: privacyState.sessionStarted || null,
  };
}

/**
 * Update the session privacy state.
 */
async function updatePrivacyState(updates) {
  const stored = await chrome.storage.session.get(PRIVACY_STATE_KEY);
  const privacyState = stored[PRIVACY_STATE_KEY] || { sessionStarted: Date.now() };
  Object.assign(privacyState, updates);
  await chrome.storage.session.set({ [PRIVACY_STATE_KEY]: privacyState });
}

/**
 * Enable or disable committed (amount-hidden) transfer mode.
 */
async function setCommittedTransferMode(enabled) {
  await updatePrivacyState({ committedTransfersActive: !!enabled });
  notifySubscribers('privacyModeChanged', {
    feature: 'committedTransfers',
    enabled: !!enabled,
  });
  return { success: true, committedTransfersActive: !!enabled };
}

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
let walletPassphrase = null; // Held in memory while unlocked; cleared on lock.

async function loadState() {
  if (state) return state;

  // Try loading legacy unencrypted state and migrate it.
  const stored = await chrome.storage.local.get(STORAGE_KEY);
  if (stored[STORAGE_KEY]) {
    // Migrate: encrypt with internal key and remove plaintext.
    state = stored[STORAGE_KEY];
    state.needsPassphraseSetup = true;
    const internalKey = await getInternalEncryptionKey();
    walletPassphrase = internalKey;
    state.locked = false;
    await saveState();
    // Also migrate any plaintext mnemonic.
    const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
    if (mnemonicStored[MNEMONIC_KEY]?.plaintext) {
      const encMnemonic = await encryptWithPassphrase(mnemonicStored[MNEMONIC_KEY].plaintext, internalKey);
      await chrome.storage.local.set({ [MNEMONIC_KEY]: encMnemonic });
    }
    // Lock after migration — user must set passphrase.
    state.locked = true;
    state.secretKey = null;
    walletPassphrase = null;
    return state;
  }

  // Try loading encrypted state.
  const encrypted = await chrome.storage.local.get(ENCRYPTED_STATE_KEY);
  if (encrypted[ENCRYPTED_STATE_KEY]) {
    // State exists but is encrypted — wallet is locked.
    state = {
      locked: true,
      publicKey: encrypted[ENCRYPTED_STATE_KEY].publicKey || [],
      tokens: [],
      receiptChain: [],
      log: [],
      hasMnemonic: encrypted[ENCRYPTED_STATE_KEY].hasMnemonic || false,
      needsPassphraseSetup: encrypted[ENCRYPTED_STATE_KEY].needsPassphraseSetup || false,
    };
    return state;
  }

  // First run: generate mnemonic and create wallet.
  // Always encrypt at rest — use internal key if no user passphrase is set.
  const mnemonic = await generateMnemonic();
  const keypair = await deriveKeypairFromMnemonic(mnemonic, '');
  state = {
    locked: true, // Start locked — require passphrase setup before use.
    publicKey: Array.from(keypair.publicKey),
    secretKey: Array.from(keypair.secretKey),
    tokens: [],
    receiptChain: [],
    log: [],
    hasMnemonic: true,
    mnemonicShown: false, // Track whether user has seen the mnemonic.
    needsPassphraseSetup: true, // Signal to popup to prompt for passphrase.
  };

  // Encrypt with internal key for at-rest protection (until user sets passphrase).
  const internalKey = await getInternalEncryptionKey();
  walletPassphrase = internalKey;
  state.locked = false;
  await saveState();

  // Encrypt mnemonic with the internal key — never store plaintext.
  const encryptedMnemonic = await encryptWithPassphrase(mnemonic, internalKey);
  await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });

  // Lock immediately so user must set a passphrase on first interaction.
  state.locked = true;
  state.secretKey = null;
  walletPassphrase = null;
  state.needsPassphraseSetup = true;

  return state;
}

async function saveState() {
  if (!state) return;

  if (!walletPassphrase && !state.locked) {
    // No passphrase available and not locked — use internal key for encryption.
    // This should not happen in normal flow, but is a safety net.
    walletPassphrase = await getInternalEncryptionKey();
  }

  if (walletPassphrase && !state.locked) {
    // Always save encrypted.
    const plaintext = JSON.stringify({
      publicKey: state.publicKey,
      secretKey: state.secretKey,
      tokens: state.tokens,
      receiptChain: state.receiptChain,
      log: state.log,
      hasMnemonic: state.hasMnemonic,
      mnemonicShown: state.mnemonicShown,
      needsPassphraseSetup: state.needsPassphraseSetup || false,
      stealthMeta: state.stealthMeta || null,
      stealthPrivate: state.stealthPrivate || null,
      stealthNotes: state.stealthNotes || [],
    });
    const encrypted = await encryptWithPassphrase(plaintext, walletPassphrase);
    encrypted.publicKey = state.publicKey; // Keep public key readable for UI.
    encrypted.hasMnemonic = state.hasMnemonic;
    encrypted.needsPassphraseSetup = state.needsPassphraseSetup || false;
    await chrome.storage.local.set({ [ENCRYPTED_STATE_KEY]: encrypted });
    // Remove any legacy unencrypted state.
    await chrome.storage.local.remove(STORAGE_KEY);
  } else if (state.locked) {
    // Wallet is locked; we cannot re-encrypt (no passphrase in memory).
    // The encrypted state on disk is already correct. Do nothing.
  }
}

/**
 * Lock the wallet: encrypt state and clear sensitive data from memory.
 */
async function lockWallet() {
  if (!state) return;

  // Ensure state is saved encrypted before clearing.
  if (walletPassphrase) {
    state.locked = false; // Temporarily unlock to save full state.
    await saveState();
  }

  // Clear sensitive fields from memory.
  state.locked = true;
  state.secretKey = null;
  walletPassphrase = null;

  // Clear the auto-lock timer.
  if (lockTimer !== null) {
    clearTimeout(lockTimer);
    lockTimer = null;
  }
}

/**
 * Unlock the wallet with a passphrase: decrypt state from storage.
 */
async function unlockWallet(passphrase) {
  const encrypted = await chrome.storage.local.get(ENCRYPTED_STATE_KEY);
  if (!encrypted[ENCRYPTED_STATE_KEY]) {
    // No encrypted state: should not happen in new flow. Mark unlocked.
    if (state) state.locked = false;
    return { success: true };
  }

  // Try user-provided passphrase first.
  const attempts = [passphrase];
  // If the wallet needs passphrase setup, also try the internal key.
  if (encrypted[ENCRYPTED_STATE_KEY].needsPassphraseSetup) {
    const internalKey = await getInternalEncryptionKey();
    attempts.push(internalKey);
  }

  for (const attempt of attempts) {
    try {
      const plaintext = await decryptWithPassphrase(encrypted[ENCRYPTED_STATE_KEY], attempt);
      const decrypted = JSON.parse(plaintext);
      state = {
        locked: false,
        publicKey: decrypted.publicKey,
        secretKey: decrypted.secretKey,
        tokens: decrypted.tokens || [],
        receiptChain: decrypted.receiptChain || [],
        log: decrypted.log || [],
        hasMnemonic: decrypted.hasMnemonic || false,
        mnemonicShown: decrypted.mnemonicShown || false,
        needsPassphraseSetup: decrypted.needsPassphraseSetup || false,
        stealthMeta: decrypted.stealthMeta || null,
        stealthPrivate: decrypted.stealthPrivate || null,
        stealthNotes: decrypted.stealthNotes || [],
      };
      walletPassphrase = attempt;
      resetLockTimer();
      return { success: true, needsPassphraseSetup: state.needsPassphraseSetup };
    } catch (e) {
      // Try next attempt.
    }
  }

  return { success: false, error: 'Invalid passphrase' };
}

/**
 * Set or change the wallet passphrase. Encrypts state and mnemonic.
 */
async function setPassphrase(newPassphrase) {
  const oldPassphrase = walletPassphrase;
  walletPassphrase = newPassphrase;

  // Clear the needsPassphraseSetup flag — user has set their own passphrase.
  if (state) {
    state.needsPassphraseSetup = false;
  }

  // Re-encrypt mnemonic with the new passphrase.
  const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
  if (mnemonicStored[MNEMONIC_KEY]) {
    let mnemonic = null;
    // Try decrypting with old passphrase (or internal key).
    const keysToTry = oldPassphrase ? [oldPassphrase] : [];
    const internalKey = await getInternalEncryptionKey();
    keysToTry.push(internalKey);

    for (const key of keysToTry) {
      try {
        mnemonic = await decryptWithPassphrase(mnemonicStored[MNEMONIC_KEY], key);
        break;
      } catch (e) {
        // Try next.
      }
    }

    if (mnemonic) {
      const encryptedMnemonic = await encryptWithPassphrase(mnemonic, newPassphrase);
      await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });
    }
  }

  await saveState();
  resetLockTimer();
}

/**
 * Get the mnemonic (requires wallet to be unlocked and passphrase known).
 */
async function getMnemonic() {
  const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
  if (!mnemonicStored[MNEMONIC_KEY]) return null;

  // Encrypted: need passphrase or internal key.
  if (!walletPassphrase) return null;
  const keysToTry = [walletPassphrase];
  const internalKey = await getInternalEncryptionKey();
  if (walletPassphrase !== internalKey) {
    keysToTry.push(internalKey);
  }

  for (const key of keysToTry) {
    try {
      return await decryptWithPassphrase(mnemonicStored[MNEMONIC_KEY], key);
    } catch (e) {
      // Try next.
    }
  }
  return null;
}

/**
 * Recover wallet from mnemonic + passphrase.
 */
async function recoverFromMnemonic(mnemonic, passphrase) {
  const valid = await validateMnemonic(mnemonic);
  if (!valid) {
    return { success: false, error: 'Invalid mnemonic (bad checksum or unknown words)' };
  }

  const keypair = await deriveKeypairFromMnemonic(mnemonic, passphrase);
  state = {
    locked: false,
    publicKey: Array.from(keypair.publicKey),
    secretKey: Array.from(keypair.secretKey),
    tokens: [],
    receiptChain: [],
    log: [],
    hasMnemonic: true,
    mnemonicShown: true,
    needsPassphraseSetup: false,
  };

  // Always encrypt — use user passphrase if provided, otherwise internal key.
  const encryptionKey = passphrase || await getInternalEncryptionKey();
  walletPassphrase = encryptionKey;
  const encryptedMnemonic = await encryptWithPassphrase(mnemonic, encryptionKey);
  await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });

  if (!passphrase) {
    state.needsPassphraseSetup = true;
  }

  await saveState();
  resetLockTimer();
  return { success: true, publicKey: state.publicKey };
}

// ---------------------------------------------------------------------------
// Origin allowlist management (per-method, with expiry)
// ---------------------------------------------------------------------------

/**
 * Get the full origin allowlist. Format:
 * { "https://example.com": { methods: ["pyana:provision"], expires: 1716300000000 }, ... }
 */
async function getOriginAllowlist() {
  const stored = await chrome.storage.local.get(ALLOWED_ORIGINS_KEY);
  const raw = stored[ALLOWED_ORIGINS_KEY] || {};
  // Migrate from legacy array format if needed.
  if (Array.isArray(raw)) {
    const migrated = {};
    for (const origin of raw) {
      migrated[origin] = { methods: ['*'], expires: Date.now() + ORIGIN_PERMISSION_EXPIRY_MS };
    }
    await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: migrated });
    return migrated;
  }
  return raw;
}

/**
 * Check if an origin is allowed for a specific method.
 */
async function isOriginAllowedForMethod(origin, method) {
  const allowlist = await getOriginAllowlist();
  const entry = allowlist[origin];
  if (!entry) return false;
  // Check expiry.
  if (entry.expires && entry.expires < Date.now()) {
    // Expired — remove entry.
    delete allowlist[origin];
    await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
    return false;
  }
  // Check method.
  return entry.methods.includes('*') || entry.methods.includes(method);
}

/**
 * Add a method permission for an origin with expiry.
 */
async function addOriginToAllowlist(origin, method) {
  const allowlist = await getOriginAllowlist();
  if (!allowlist[origin]) {
    allowlist[origin] = { methods: [], expires: Date.now() + ORIGIN_PERMISSION_EXPIRY_MS };
  }
  if (!allowlist[origin].methods.includes(method)) {
    allowlist[origin].methods.push(method);
  }
  // Refresh expiry on new grant.
  allowlist[origin].expires = Date.now() + ORIGIN_PERMISSION_EXPIRY_MS;
  await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
}

/**
 * Revoke all permissions for an origin.
 */
async function revokeOriginPermissions(origin) {
  const allowlist = await getOriginAllowlist();
  delete allowlist[origin];
  await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
}

/**
 * Get all origin permissions for display in the popup.
 */
async function getAllOriginPermissions() {
  const allowlist = await getOriginAllowlist();
  const result = [];
  const now = Date.now();
  for (const [origin, entry] of Object.entries(allowlist)) {
    if (entry.expires && entry.expires < now) continue; // Skip expired.
    result.push({
      origin,
      methods: entry.methods,
      expires: entry.expires,
      expiresIn: entry.expires ? Math.max(0, entry.expires - now) : null,
    });
  }
  return result;
}

// ---------------------------------------------------------------------------
// Authorization logic — delegates to WASM when available
// ---------------------------------------------------------------------------

function evaluateDatalog(token, request) {
  requireWasm('evaluateDatalog');

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
}

function generateProof(witness, mode) {
  requireWasm('generateProof');

  const hash = witness.reduce((acc, b, i) => acc ^ (b << ((i % 4) * 8)), 0) >>> 0;
  const depth = mode === 'private' ? 8 : mode === 'selective' ? 4 : 2;
  const result = wasm.generate_demo_stark_proof(hash, depth);
  return new TextEncoder().encode(result.proof_json);
}

function verifyToken(tokenStr, rootKey, appId, action) {
  requireWasm('verifyToken');
  return wasm.verify_token(tokenStr, rootKey, appId, action);
}

function computeMerkleRoot(leaves) {
  requireWasm('computeMerkleRoot');
  return wasm.compute_merkle_root(JSON.stringify(leaves));
}

/**
 * Resolve the private numeric value for a fact key from a token.
 * Used by predicate proofs to get the actual attribute value.
 * Returns a number or null if the key cannot be resolved.
 */
function resolvePrivateValue(token, key) {
  // Direct numeric properties on the token.
  const directMap = {
    'expires': token.expiry,
    'expiry': token.expiry,
    'issued': token.provisioned,
    'provisioned': token.provisioned,
    'balance': token.balance,
    'amount': token.amount,
    'reputation': token.reputation,
    'score': token.score,
    'level': token.level,
    'depth': token.depth,
    'delegationDepth': token.delegationDepth,
    'budget': token.budget,
  };

  if (key in directMap && directMap[key] != null) {
    const val = directMap[key];
    return typeof val === 'number' ? val : parseInt(val, 10) || null;
  }

  // Check token metadata/attributes if present.
  if (token.attributes && key in token.attributes) {
    const val = token.attributes[key];
    return typeof val === 'number' ? val : parseInt(val, 10) || null;
  }

  // Check token.meta (alternative metadata field).
  if (token.meta && key in token.meta) {
    const val = token.meta[key];
    return typeof val === 'number' ? val : parseInt(val, 10) || null;
  }

  return null;
}

async function authorize(request) {
  // SECURITY: Fail-closed if WASM cryptographic module is not loaded.
  // All proof generation and policy evaluation requires WASM.
  if (!wasmLoaded || !wasm) {
    return { allowed: false, error: 'Cryptographic module unavailable. Cannot authorize securely.' };
  }

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
    mode,
    disclosedFacts: request._disclosedFacts || null,
    predicateFacts: request._predicateFacts || null,
  });
  await saveState();

  const result = { allowed: true, proof: Array.from(proof), facts: evalResult.trace, mode };

  // For selective disclosure, filter facts to only those the user chose to disclose.
  if (mode === 'selective' && request._disclosedFacts) {
    result.facts = evalResult.trace.filter(traceEntry => {
      // Include trace entries that reference disclosed fact keys.
      return request._disclosedFacts.some(key =>
        traceEntry.toLowerCase().includes(key.toLowerCase())
      );
    });
    result.disclosedFacts = request._disclosedFacts;
  }

  // For predicate proofs, generate real ZK range/comparison proofs via WASM.
  if (mode === 'selective' && request._predicateFacts) {
    // Fetch the current ledger Merkle state root from the node ONCE for all predicates.
    // The circuit's compute_blinded_fact_commitment expects the same state_root
    // that the verifier will check against. Using the receipt chain hash was
    // incorrect — it doesn't match the circuit's expectation.
    let stateRoot = 0;
    try {
      // Fetch state root from the configured node.
      const statusResult = await nodeRequest('/status');
      if (statusResult.ok) {
        const statusData = statusResult.data;
        // Validate the response is signed by the node if a signature is present.
        if (nodePublicKey && statusData.signature && statusData.payload) {
          if (!validateNodeSignature(statusData.payload, statusData.signature, nodePublicKey)) {
            throw new Error('Invalid signature on /status response');
          }
        }
        // The node's /status endpoint returns the current Merkle state root
        // as a hex string. Convert the first 8 hex chars to a u32.
        const merkleRoot = statusData.merkle_root || statusData.state_root || '';
        if (merkleRoot) {
          stateRoot = parseInt(merkleRoot.slice(0, 8), 16) >>> 0;
        }
      }
    } catch (_e) {
      // If the node is unreachable, fall back to a BLAKE3 hash of the
      // receipt chain (degraded mode — proofs may not verify cross-system).
      const stateRootInput = wallet.receiptChain.length > 0
        ? wallet.receiptChain[wallet.receiptChain.length - 1]
        : '0';
      const stateRootHash = wasm.blake3_hash(stateRootInput);
      stateRoot = parseInt(stateRootHash.slice(0, 8), 16) >>> 0;
    }

    result.predicateProofs = request._predicateFacts.map(pf => {
      // Look up the private value for this fact from the token.
      const privateValue = resolvePrivateValue(matchingToken, pf.key);
      if (privateValue === null) {
        // Cannot prove: attribute value not found in token.
        return {
          key: pf.key,
          predicateType: pf.predicateType,
          threshold: pf.threshold,
          proof: null,
          error: `Attribute "${pf.key}" not found in token`,
        };
      }

      // Map disclosure picker predicate types to WASM predicate types.
      const predicateTypeMap = {
        'gte': 'gte', '>=': 'gte',
        'lte': 'lte', '<=': 'lte',
        'gt': 'gt', '>': 'gt',
        'lt': 'lt', '<': 'lt',
        'neq': 'neq', '!=': 'neq',
      };
      const wasmPredicateType = predicateTypeMap[pf.predicateType] || 'gte';
      const thresholdValue = typeof pf.threshold === 'number'
        ? pf.threshold
        : parseInt(pf.threshold, 10) || 0;

      try {
        const proofResult = wasm.generate_predicate_proof(
          wasmPredicateType,
          privateValue >>> 0,  // Ensure u32
          thresholdValue >>> 0,
          pf.key,
          stateRoot
        );
        return {
          key: pf.key,
          predicateType: pf.predicateType,
          threshold: pf.threshold,
          proof: proofResult.proof_json,
          factCommitment: proofResult.fact_commitment,
          verified: proofResult.verified,
          proofSizeBytes: proofResult.proof_size_bytes,
        };
      } catch (e) {
        // Proof generation failed (predicate not satisfiable or WASM error).
        return {
          key: pf.key,
          predicateType: pf.predicateType,
          threshold: pf.threshold,
          proof: null,
          error: e.message || 'Predicate proof generation failed',
        };
      }
    });
  }

  // For zero-knowledge, strip all facts from the result.
  if (mode === 'private') {
    result.facts = [];
  }

  notifySubscribers('authorization', {
    action: request.action,
    resource: request.resource,
    allowed: true,
    mode,
  });
  return result;
}

// ---------------------------------------------------------------------------
// Disclosure picker — progressive disclosure UX
// ---------------------------------------------------------------------------

/**
 * Get per-origin disclosure preferences.
 */
async function getDisclosurePrefs() {
  const stored = await chrome.storage.local.get(DISCLOSURE_PREFS_KEY);
  return stored[DISCLOSURE_PREFS_KEY] || {};
}

/**
 * Save a disclosure preference for an origin.
 */
async function saveDisclosurePref(origin, level) {
  const prefs = await getDisclosurePrefs();
  prefs[origin] = { level, savedAt: Date.now() };
  await chrome.storage.local.set({ [DISCLOSURE_PREFS_KEY]: prefs });
}

/**
 * Extract disclosable facts from a token for display in the picker.
 */
function extractTokenFacts(token, request) {
  const facts = [];

  // Permission facts.
  if (token.actions && token.actions.length > 0) {
    for (const act of token.actions) {
      facts.push({ key: 'action', value: act, category: 'permissions' });
    }
  }
  if (token.resource) {
    facts.push({ key: 'resource', value: token.resource, category: 'resource' });
  }
  if (token.service) {
    facts.push({ key: 'service', value: token.service, category: 'permissions' });
  }

  // Identity facts.
  if (token.userId || token.user) {
    facts.push({ key: 'user', value: token.userId || token.user, category: 'identity' });
  }
  if (token.org || token.organization) {
    facts.push({ key: 'organization', value: token.org || token.organization, category: 'identity' });
  }
  if (token.email) {
    facts.push({ key: 'email', value: token.email, category: 'identity' });
  }
  if (token.issuer) {
    facts.push({ key: 'issuer', value: token.issuer, category: 'identity' });
  }

  // Temporal facts.
  if (token.expiry) {
    facts.push({ key: 'expires', value: token.expiry, category: 'temporal' });
  }
  if (token.provisioned) {
    facts.push({ key: 'issued', value: token.provisioned, category: 'temporal' });
  }

  // Add the action/resource from the request as context.
  if (request.action && !facts.some(f => f.key === 'action' && f.value === request.action)) {
    facts.push({ key: 'action', value: request.action, category: 'permissions' });
  }
  if (request.resource && request.resource !== '*' && !facts.some(f => f.key === 'resource' && f.value === request.resource)) {
    facts.push({ key: 'resource', value: request.resource, category: 'resource' });
  }

  return facts;
}

/**
 * Show the disclosure picker popup for a given authorization request.
 * Returns the user's disclosure choice or null if denied.
 */
function showDisclosurePicker(origin, request, tokenFacts) {
  return new Promise((resolve) => {
    // Facts that are required for this action (action + resource always required).
    const requiredFacts = tokenFacts.filter(f =>
      f.key === 'action' || f.key === 'resource'
    );

    // Facts the site explicitly requested (from request.requestedDisclosure).
    const siteRequested = request.requestedDisclosure || [];

    const popupUrl = chrome.runtime.getURL('disclosure-picker.html') +
      '?origin=' + encodeURIComponent(origin) +
      '&action=' + encodeURIComponent(request.action) +
      '&resource=' + encodeURIComponent(request.resource) +
      '&facts=' + encodeURIComponent(JSON.stringify(tokenFacts)) +
      '&required=' + encodeURIComponent(JSON.stringify(requiredFacts)) +
      '&siteRequested=' + encodeURIComponent(JSON.stringify(siteRequested));

    chrome.windows.create({
      url: popupUrl,
      type: 'popup',
      width: 440,
      height: 620,
      focused: true,
    }, (win) => {
      const listener = (message, sender, sendResponse) => {
        if (message.type !== 'pyana:disclosureDecision') return;
        chrome.runtime.onMessage.removeListener(listener);
        resolve(message);
      };
      chrome.runtime.onMessage.addListener(listener);

      // If the popup is closed without responding, deny.
      if (win?.id) {
        chrome.windows.onRemoved.addListener(function onClose(closedId) {
          if (closedId === win.id) {
            chrome.windows.onRemoved.removeListener(onClose);
            chrome.runtime.onMessage.removeListener(listener);
            resolve({ authorized: false });
          }
        });
      }
    });
  });
}

/**
 * Authorize with disclosure — the main entry point for page-initiated authorizations.
 * Checks for saved preferences, otherwise shows the disclosure picker.
 */
async function authorizeWithDisclosure(request, origin) {
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

  // Check for saved disclosure preference for this origin.
  const prefs = await getDisclosurePrefs();
  const savedPref = prefs[origin];

  let disclosureLevel;
  let disclosedFacts = [];

  let predicateFacts = [];

  if (savedPref && !request.forceDisclosurePicker) {
    // Use saved preference.
    disclosureLevel = savedPref.level;
  } else {
    // Show the disclosure picker to the user.
    const tokenFacts = extractTokenFacts(matchingToken, request);
    const decision = await showDisclosurePicker(origin, request, tokenFacts);

    if (!decision.authorized) {
      return { allowed: false, error: 'User denied authorization' };
    }

    disclosureLevel = decision.level;
    disclosedFacts = decision.disclosedFacts || [];

    // Extract predicate proof specs from the structured facts array.
    if (decision.facts && Array.isArray(decision.facts)) {
      for (const factDecision of decision.facts) {
        if (factDecision.disclosure === 'reveal') {
          // Ensure revealed facts are in the disclosedFacts array.
          const factObj = tokenFacts[factDecision.index];
          if (factObj && !disclosedFacts.includes(factObj.key)) {
            disclosedFacts.push(factObj.key);
          }
        } else if (factDecision.disclosure === 'predicate') {
          const factObj = tokenFacts[factDecision.index];
          if (factObj) {
            predicateFacts.push({
              key: factObj.key,
              predicateType: factDecision.predicateType || 'gte',
              threshold: factDecision.threshold,
            });
          }
        }
      }
    }

    // Save preference if user checked "remember".
    if (decision.remember && origin) {
      await saveDisclosurePref(origin, disclosureLevel);
    }
  }

  // Map disclosure level to proof mode.
  const modeMap = { full: 'trusted', selective: 'selective', private: 'private' };
  const mode = modeMap[disclosureLevel] || 'trusted';

  // Perform the actual authorization with the chosen mode.
  return authorize({
    ...request,
    mode,
    _disclosedFacts: disclosedFacts.length > 0 ? disclosedFacts : null,
    _predicateFacts: predicateFacts.length > 0 ? predicateFacts : null,
  });
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
 * Fulfill an intent from the pool using a matching token from the wallet.
 * Calls POST /intents/fulfill on the local node to complete the fulfillment.
 *
 * Requires user confirmation before fulfilling.
 */
async function fulfillIntent(intentId, tokenId) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  // Find the intent in the local pool.
  const entry = intentPool.get(intentId);
  if (!entry) {
    return { error: 'Intent not found in local pool' };
  }
  const intent = entry.intent;

  // Check expiry.
  if (intent.expiry <= Date.now()) {
    intentPool.delete(intentId);
    return { error: 'Intent has expired' };
  }

  // Find the specified token (or auto-match if tokenId is null).
  let matchingToken;
  if (tokenId) {
    matchingToken = wallet.tokens.find(t => t.id === tokenId);
    if (!matchingToken) {
      return { error: `Token "${tokenId}" not found in wallet` };
    }
  } else {
    // Auto-match: find the first token that satisfies the intent.
    const matchResult = matchIntentLocally(intent, wallet.tokens, Date.now());
    if (!matchResult) {
      return { error: 'No matching token found for this intent' };
    }
    matchingToken = wallet.tokens.find(t => t.id === matchResult.tokenId);
    if (!matchingToken) {
      return { error: 'Matched token no longer available' };
    }
  }

  // Confirm with user before fulfilling.
  const confirmed = await showIntentConfirmation('fulfillIntent', intent.matcher, {
    intentId,
    tokenId: matchingToken.id,
    intentKind: intent.kind,
  });
  if (!confirmed) {
    return { error: 'User denied intent fulfillment' };
  }

  // Build the fulfillment payload for the node.
  const fulfillmentPayload = {
    intent_id: intentId,
    fulfiller_token: {
      id: matchingToken.id,
      actions: matchingToken.actions,
      resource: matchingToken.resource || '*',
      expiry: matchingToken.expiry || null,
    },
    fulfiller_public_key: wallet.publicKey,
    timestamp: Date.now(),
  };

  // Call the node's fulfillment endpoint.
  try {
    const response = await nodeRequest('/intents/fulfill', {
      method: 'POST',
      body: JSON.stringify(fulfillmentPayload),
    });

    if (!response.ok) {
      return {
        error: `Node rejected fulfillment: ${response.error}`,
      };
    }

    const result = response.data;

    // Log the fulfillment.
    wallet.log.push({
      action: 'fulfillIntent',
      resource: intent.matcher?.resourcePattern || '*',
      allowed: true,
      timestamp: Date.now(),
      mode: 'trusted',
      intentId,
      tokenId: matchingToken.id,
    });
    await saveState();

    // Remove fulfilled intent from pool.
    intentPool.delete(intentId);

    // Notify subscribers.
    notifySubscribers('intentFulfilled', {
      intentId,
      tokenId: matchingToken.id,
      result,
    });

    return {
      fulfilled: true,
      intentId,
      tokenId: matchingToken.id,
      nodeResult: result,
    };
  } catch (e) {
    return {
      error: `Failed to contact node: ${e.message}`,
    };
  }
}

/**
 * Get intents that can be fulfilled by the current wallet's tokens.
 * Returns a list of { intent, matchedToken } pairs.
 */
async function getFulfillableIntents() {
  const wallet = await loadState();
  if (wallet.locked) return [];

  const now = Date.now();
  const fulfillable = [];

  for (const [, { intent }] of intentPool) {
    if (intent.expiry <= now) continue;
    if (intent.kind !== 'need') continue; // Can only fulfill "need" intents.

    const matchResult = matchIntentLocally(intent, wallet.tokens, now);
    if (matchResult) {
      fulfillable.push({
        intentId: intent.id,
        kind: intent.kind,
        matcher: intent.matcher,
        expiry: intent.expiry,
        matchedTokenId: matchResult.tokenId,
        grantedActions: matchResult.grantedActions,
        resource: matchResult.resource,
      });
    }
  }

  return fulfillable;
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

/**
 * Compute a deterministic intent ID aligned with the Rust intent engine.
 *
 * When WASM is available, delegates to `compute_intent_id` which uses the
 * exact same postcard + BLAKE3 computation as `Intent::compute_id()` in Rust.
 *
 * When WASM is unavailable, falls back to deterministic SHA-256 over canonical
 * JSON (no random nonce). The returned ID is prefixed with "js:" so the node
 * knows to recompute the canonical BLAKE3 ID on receipt.
 */
async function computeIntentId(kind, matchSpec, expiry) {
  // Build the canonical input matching the Rust Intent structure.
  const intentInput = {
    kind: kind === 'need' ? 'Need' : kind === 'offer' ? 'Offer' : 'Query',
    actions: (matchSpec?.actions || []).map(a => ({
      action: a.action || null,
      resource: a.resource || null,
    })),
    constraints: (matchSpec?.constraints || []).map(c => {
      if (c.type === 'appId') return { AppId: c.value };
      if (c.type === 'service') return { Service: c.value };
      if (c.type === 'userId') return { UserId: c.value };
      if (c.type === 'notExpiredAt') return { NotExpiredAt: c.value };
      if (c.type === 'feature') return { Feature: c.value };
      if (c.type === 'oauthProvider') return { OAuthProvider: c.value };
      return { predicate: c.type || '', value: c.value || '' };
    }),
    min_budget: matchSpec?.minBudget || null,
    resource_pattern: matchSpec?.resourcePattern || null,
    expiry: expiry,
    creator: matchSpec?.creator || null,
    proof_of_stake: matchSpec?.proofOfStake || null,
  };

  // Prefer WASM: produces the exact same ID as the Rust node.
  if (wasm && wasm.compute_intent_id) {
    try {
      return wasm.compute_intent_id(JSON.stringify(intentInput));
    } catch (e) {
      console.warn('[pyana] WASM compute_intent_id failed, using SHA-256 fallback:', e.message);
    }
  }

  // Fallback: deterministic SHA-256 (no random nonce). Prefix with "js:" so
  // the receiving node knows this is not a canonical BLAKE3 ID and will
  // recompute on receipt.
  const canonical = JSON.stringify({
    kind: intentInput.kind,
    actions: intentInput.actions,
    constraints: intentInput.constraints,
    min_budget: intentInput.min_budget,
    resource_pattern: intentInput.resource_pattern,
    expiry: intentInput.expiry,
  });
  const encoded = new TextEncoder().encode(canonical);
  const hashBuffer = await crypto.subtle.digest('SHA-256', encoded);
  const hashArray = Array.from(new Uint8Array(hashBuffer));
  return 'js:' + hashArray.map(b => b.toString(16).padStart(2, '0')).join('');
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
// CapTP operations (share, accept, handoff)
// ---------------------------------------------------------------------------

const LIVE_REFS_KEY = 'pyana_live_refs';
const CAPTP_STORAGE_KEY = 'pyana_captp_state';

// In-memory live ref tracking: refId -> { cellId, uri, permissions, tabId, createdAt }
const liveRefs = new Map();

/**
 * Share a cell as a pyana:// URI (export sturdy ref).
 * @param {string} cellId - 64-char hex cell ID.
 * @returns {Promise<{uri: string, cellId: string}>}
 */
async function shareCapability(cellId) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  // Call node to generate the sturdy ref
  const body = { cell_id: cellId };
  const resp = await nodeRequest('/turns/bearer-auth', {
    method: 'POST',
    body: JSON.stringify(body),
  });

  if (!resp.ok) {
    return { error: `Failed to export sturdy ref: ${resp.error}` };
  }

  const nodeId = resp.data?.node_id || 'local';
  const secret = resp.data?.secret || '';
  const uri = `pyana://${nodeId}/${cellId}/${secret}`;

  // Log the export
  wallet.log.push({
    action: 'shareCapability',
    resource: cellId,
    allowed: true,
    timestamp: Date.now(),
    mode: 'captp',
  });
  await saveState();

  return { uri, cellId, nodeId };
}

/**
 * Accept (enliven) a pyana:// URI, returning live ref info.
 * @param {string} uri - A pyana:// URI.
 * @returns {Promise<{refId: string, cellId: string, nodeId: string}>}
 */
async function acceptCapability(uri, tabId) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  if (!uri.startsWith('pyana://')) {
    return { error: 'Invalid URI: must start with pyana://' };
  }

  const parts = uri.replace('pyana://', '').split('/');
  if (parts.length < 3) {
    return { error: 'Invalid URI format. Expected: pyana://<node>/<cell>/<secret>' };
  }

  const [nodeId, cellId, secret] = parts;

  const body = { node_id: nodeId, cell_id: cellId, secret };
  const resp = await nodeRequest('/turns/peer-exchange', {
    method: 'POST',
    body: JSON.stringify(body),
  });

  if (!resp.ok) {
    return { error: `Failed to enliven capability: ${resp.error}` };
  }

  const refId = `ref_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
  const liveRef = {
    cellId,
    uri,
    nodeId,
    permissions: resp.data?.permissions || 'full',
    tabId: tabId || null,
    createdAt: Date.now(),
    capId: resp.data?.cap_id || null,
  };
  liveRefs.set(refId, liveRef);

  // Persist live refs summary to session storage for popup display
  await persistLiveRefs();

  wallet.log.push({
    action: 'acceptCapability',
    resource: cellId,
    allowed: true,
    timestamp: Date.now(),
    mode: 'captp',
  });
  await saveState();

  return { refId, cellId, nodeId, permissions: liveRef.permissions };
}

/**
 * Create a handoff certificate for offline delegation.
 * @param {string} cellId - Cell to delegate.
 * @param {string} recipientPk - Recipient's public key (hex).
 * @returns {Promise<{certificateHash: string, cellId: string, recipientPk: string}>}
 */
async function createHandoff(cellId, recipientPk) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  const body = { cell_id: cellId, recipient_pk: recipientPk };
  const resp = await nodeRequest('/turns/peer-exchange', {
    method: 'POST',
    body: JSON.stringify(body),
  });

  if (!resp.ok) {
    return { error: `Failed to create handoff: ${resp.error}` };
  }

  return {
    certificateHash: resp.data?.certificate_hash || '',
    cellId,
    recipientPk,
  };
}

/**
 * Get all currently held live refs.
 */
function getLiveRefs() {
  const result = [];
  for (const [refId, ref] of liveRefs) {
    result.push({ refId, ...ref });
  }
  return result;
}

/**
 * Drop a specific live ref.
 */
async function dropLiveRef(refId) {
  if (!liveRefs.has(refId)) {
    return { error: 'Live ref not found' };
  }
  liveRefs.delete(refId);
  await persistLiveRefs();
  return { dropped: true, refId };
}

/**
 * Persist live refs to session storage for popup access.
 */
async function persistLiveRefs() {
  const summary = [];
  for (const [refId, ref] of liveRefs) {
    summary.push({ refId, cellId: ref.cellId, nodeId: ref.nodeId, createdAt: ref.createdAt });
  }
  await chrome.storage.session.set({ [LIVE_REFS_KEY]: summary });
}

/**
 * Clean up live refs associated with a specific tab.
 */
function cleanupTabRefs(tabId) {
  for (const [refId, ref] of liveRefs) {
    if (ref.tabId === tabId) {
      liveRefs.delete(refId);
    }
  }
  persistLiveRefs();
}

// Auto-cleanup on tab close.
chrome.tabs.onRemoved.addListener((tabId) => {
  cleanupTabRefs(tabId);
});

// ---------------------------------------------------------------------------
// Directory / Namespace operations
// ---------------------------------------------------------------------------

/**
 * Mount a service in the governed directory.
 * @param {string} path - Full path (e.g., "/services/oracle").
 * @param {string} sturdyRef - URI to mount.
 * @param {string} kind - Entry kind (service, factory, data, dir).
 * @param {string[]} tags - Tags for discovery.
 */
async function mountService(path, sturdyRef, kind, tags) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  const body = {
    path,
    uri: sturdyRef,
    kind: kind || 'service',
    tags: tags || [],
  };
  const resp = await nodeRequest('/registry/mount', {
    method: 'POST',
    body: JSON.stringify(body),
  });

  if (!resp.ok) {
    return { error: `Failed to mount: ${resp.error}` };
  }

  return { path, version: resp.data?.version || 1, kind: kind || 'service' };
}

/**
 * Discover services by tags.
 * @param {string[]} tags - Tags to search for.
 * @returns {Promise<{results: Array}>}
 */
async function discoverServices(tags) {
  const queryParams = (tags || []).map(t => `tag=${encodeURIComponent(t)}`).join('&');
  const query = queryParams ? `?${queryParams}` : '';
  const resp = await nodeRequest(`/registry/discover${query}`);

  if (!resp.ok) {
    return { error: `Discovery failed: ${resp.error}` };
  }

  return { results: resp.data?.results || [] };
}

/**
 * Resolve a path to its sturdy ref and metadata.
 * @param {string} path - Directory path.
 */
async function resolvePath(path) {
  const encoded = encodeURIComponent(path);
  const resp = await nodeRequest(`/registry/get?path=${encoded}`);

  if (!resp.ok) {
    return { error: `Resolve failed: ${resp.error}` };
  }

  return resp.data || {};
}

// ---------------------------------------------------------------------------
// Storage operations (content-addressed)
// ---------------------------------------------------------------------------

/**
 * Write data to storage, returns content hash.
 * @param {string} dataBase64 - Base64-encoded data.
 */
async function storageWrite(dataBase64) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  // Decode base64 to binary
  const binary = Uint8Array.from(atob(dataBase64), c => c.charCodeAt(0));

  const resp = await nodeRequest('/files/write', {
    method: 'POST',
    headers: { 'Content-Type': 'application/octet-stream' },
    body: binary,
  });

  if (!resp.ok) {
    return { error: `Storage write failed: ${resp.error}` };
  }

  return { hash: resp.data?.hash || '', size: resp.data?.size || binary.length };
}

/**
 * Read data from storage by hash.
 * @param {string} hash - Content hash.
 */
async function storageRead(hash) {
  const url = nodeConfig.nodeUrl.replace(/\/$/, '') + `/files/read/${hash}`;
  try {
    const resp = await fetch(url, {
      signal: AbortSignal.timeout(15000),
      headers: getNodeHeaders(),
    });
    if (!resp.ok) {
      return { error: `Storage read failed: HTTP ${resp.status}` };
    }
    const buffer = await resp.arrayBuffer();
    // Return as base64
    const bytes = new Uint8Array(buffer);
    const base64 = btoa(String.fromCharCode(...bytes));
    return { hash, data: base64, size: bytes.length };
  } catch (e) {
    return { error: `Storage read failed: ${e.message}` };
  }
}

/**
 * Check storage quota.
 */
async function storageQuota() {
  const resp = await nodeRequest('/storage/quota');
  if (!resp.ok) {
    return { error: `Quota check failed: ${resp.error}` };
  }
  return {
    bytesStored: resp.data?.bytes_stored || 0,
    bytesLimit: resp.data?.bytes_limit || 0,
    computronsUsed: resp.data?.computrons_used || 0,
    computronsRemaining: resp.data?.computrons_remaining || 0,
    objectCount: resp.data?.object_count || 0,
  };
}

// ---------------------------------------------------------------------------
// Federation status and governance
// ---------------------------------------------------------------------------

/**
 * Get federation status information.
 */
async function getFederationStatus() {
  const resp = await nodeRequest('/status');
  if (!resp.ok) {
    return { error: `Federation status failed: ${resp.error}` };
  }
  return {
    mode: resp.data?.federation_mode || 'unknown',
    height: resp.data?.latest_height || 0,
    peerCount: resp.data?.peer_count || 0,
    merkleRoot: resp.data?.merkle_root || '',
  };
}

/**
 * Propose routes to the federation.
 */
async function proposeRoutes(routes) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  const body = { type: 'route-update', args: { routes } };
  const resp = await nodeRequest('/turn/atomic', {
    method: 'POST',
    body: JSON.stringify(body),
  });

  if (!resp.ok) {
    return { error: `Proposal failed: ${resp.error}` };
  }

  return { proposalId: resp.data?.proposal_id || '', submitted: true };
}

/**
 * Vote on a governance proposal.
 */
async function voteOnProposal(proposalId, approve) {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  const body = { proposal_id: proposalId, vote: !!approve };
  const resp = await nodeRequest('/turn/atomic/vote', {
    method: 'POST',
    body: JSON.stringify(body),
  });

  if (!resp.ok) {
    return { error: `Vote failed: ${resp.error}` };
  }

  return { accepted: resp.data?.accepted !== false, proposalId };
}

// ---------------------------------------------------------------------------
// Context menu for capability sharing
// ---------------------------------------------------------------------------

// Create context menu on extension install.
chrome.runtime.onInstalled.addListener(() => {
  chrome.contextMenus.create({
    id: 'pyana-share-capability',
    title: 'Share capability...',
    contexts: ['page', 'selection'],
  });
});

chrome.contextMenus.onClicked.addListener(async (info, tab) => {
  if (info.menuItemId === 'pyana-share-capability') {
    // Get selected text as cell ID or prompt.
    const cellId = info.selectionText?.trim() || '';
    if (cellId && /^[0-9a-fA-F]{64}$/.test(cellId)) {
      const result = await shareCapability(cellId);
      if (result.uri) {
        // Show the sharing popup with the URI.
        chrome.windows.create({
          url: chrome.runtime.getURL('share-capability.html') +
            '?uri=' + encodeURIComponent(result.uri) +
            '&cellId=' + encodeURIComponent(cellId),
          type: 'popup',
          width: 420,
          height: 380,
          focused: true,
        });
      }
    } else {
      // Open sharing UI without a pre-selected cell.
      chrome.windows.create({
        url: chrome.runtime.getURL('share-capability.html'),
        type: 'popup',
        width: 420,
        height: 380,
        focused: true,
      });
    }
  }
});

// ---------------------------------------------------------------------------
// Wallet state queries
// ---------------------------------------------------------------------------

async function getWalletState() {
  const wallet = await loadState();
  const internalKey = await getInternalEncryptionKey();
  return {
    locked: wallet.locked,
    tokenCount: wallet.tokens.length,
    chainLength: wallet.receiptChain.length,
    hasMnemonic: wallet.hasMnemonic || false,
    mnemonicShown: wallet.mnemonicShown || false,
    hasPassphrase: walletPassphrase !== null && walletPassphrase !== internalKey,
    needsPassphraseSetup: wallet.needsPassphraseSetup || false,
    hasStealthKeys: wallet.stealthMeta !== null && wallet.stealthMeta !== undefined,
    stealthNotesCount: (wallet.stealthNotes || []).length,
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
          await addOriginToAllowlist(origin, method);
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
// signTurn — build, sign, and submit a turn to the node
// ---------------------------------------------------------------------------

/**
 * Build a turn locally (via WASM), sign it with the wallet key, and submit
 * it to the configured pyana node via HTTP POST.
 *
 * @param {object} turnSpec - { action, resource, amount, recipient, metadata }
 * @returns {Promise<{turnId?: string, submitted: boolean, error?: string}>}
 */
async function signTurn(turnSpec) {
  requireWasm('signTurn');

  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }
  if (!wallet.secretKey) {
    return { error: 'Wallet secret key not available' };
  }

  // Build the turn via WASM.
  let turnData;
  if (wasm.build_turn) {
    turnData = wasm.build_turn(JSON.stringify({
      sender_pubkey: wallet.publicKey,
      sender_privkey: wallet.secretKey,
      action: turnSpec.action,
      resource: turnSpec.resource || '*',
      amount: turnSpec.amount || 0,
      recipient: turnSpec.recipient || null,
      metadata: turnSpec.metadata || null,
      timestamp: Date.now(),
    }));
  } else {
    // Minimal fallback: sign the turn spec directly.
    const turnJson = JSON.stringify({
      sender: wallet.publicKey,
      action: turnSpec.action,
      resource: turnSpec.resource || '*',
      amount: turnSpec.amount || 0,
      recipient: turnSpec.recipient || null,
      metadata: turnSpec.metadata || null,
      timestamp: Date.now(),
    });
    // Sign via WASM ed25519.
    if (!wasm.sign_message) {
      return { error: 'WASM sign_message export not available' };
    }
    const signature = wasm.sign_message(
      new Uint8Array(wallet.secretKey),
      new TextEncoder().encode(turnJson)
    );
    turnData = {
      turn_id: 'js:' + Array.from(crypto.getRandomValues(new Uint8Array(16)))
        .map(b => b.toString(16).padStart(2, '0')).join(''),
      turn_bytes: Array.from(new TextEncoder().encode(turnJson)),
      signature: Array.from(signature),
    };
  }

  // Submit to the node.
  const resp = await nodeRequest('/turns/submit', {
    method: 'POST',
    body: JSON.stringify({
      turn_id: turnData.turn_id,
      turn_bytes: Array.from(turnData.turn_bytes),
      signature: turnData.signature ? Array.from(turnData.signature) : undefined,
      sender_pubkey: wallet.publicKey,
    }),
  });

  if (!resp.ok) {
    return { error: `Failed to submit turn: ${resp.error}`, turnId: turnData.turn_id, submitted: false };
  }

  // Log the turn.
  wallet.log.push({
    action: turnSpec.action,
    resource: turnSpec.resource || '*',
    allowed: true,
    timestamp: Date.now(),
    mode: 'turn',
    turnId: turnData.turn_id,
  });
  await saveState();

  return { turnId: turnData.turn_id, submitted: true, nodeResult: resp.data };
}

/**
 * Query balance from the configured node.
 * @returns {Promise<{balance?: number, error?: string}>}
 */
async function queryBalance() {
  const wallet = await loadState();
  if (wallet.locked) {
    return { error: 'Wallet is locked' };
  }

  const pubkeyHex = Array.from(wallet.publicKey)
    .map(b => b.toString(16).padStart(2, '0')).join('');
  const resp = await nodeRequest(`/accounts/${pubkeyHex}/balance`);
  if (!resp.ok) {
    return { error: `Failed to query balance: ${resp.error}` };
  }
  return { balance: resp.data?.balance ?? 0, raw: resp.data };
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
  'pyana:getStealthAddress',
  'pyana:postEncryptedIntent',
  'pyana:privateTransfer',
  'pyana:createBearerCap',
  'pyana:verifyBearerCap',
  'pyana:createFromFactory',
  'pyana:verifyProvenance',
  'pyana:makeCellSovereign',
  'pyana:peerExchange',
  'pyana:composeProofs',
  'pyana:signTurn',
  'pyana:queryBalance',
  'pyana:getNodeConfig',
  // CapTP
  'pyana:shareCapability',
  'pyana:acceptCapability',
  'pyana:createHandoff',
  // Directory
  'pyana:mountService',
  'pyana:discoverServices',
  'pyana:resolvePath',
  // Storage
  'pyana:storageWrite',
  'pyana:storageRead',
  'pyana:storageQuota',
  // Federation
  'pyana:federationStatus',
  'pyana:proposeRoutes',
  'pyana:voteOnProposal',
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
  'pyana:fulfillIntent',
  'pyana:getFulfillableIntents',
  'pyana:revoke',
  'pyana:getState',
  'pyana:getFederation',
  'pyana:refreshDiscovery',
  'pyana:setPassphrase',
  'pyana:getMnemonic',
  'pyana:recover',
  'pyana:getDisclosurePrefs',
  'pyana:clearDisclosurePref',
  'pyana:getOriginPermissions',
  'pyana:revokeOriginPermission',
  'pyana:getPrivacyState',
  'pyana:setCommittedTransferMode',
  'pyana:getStealthNotes',
  'pyana:getNodeConfig',
  'pyana:setNodeConfig',
  'pyana:getLiveRefs',
  'pyana:dropLiveRef',
]);

async function handleMessage(message, sender) {
  // Security: strip _skipDisclosure from page-originated requests.
  // Only the extension popup may bypass the disclosure picker.
  if (sender?.tab && message?.request) {
    delete message.request._skipDisclosure;
  }

  switch (message.type) {
    case 'pyana:authorize': {
      // Page-originated authorize requests go through the disclosure picker.
      // Popup/internal requests bypass it (they already specify a mode).
      if (isContentScript(sender) && !message.request._skipDisclosure) {
        const origin = message._origin || sender?.tab?.url && new URL(sender.tab.url).origin || 'unknown';
        // Rate limit: max RATE_LIMIT_MAX_CALLS per origin per RATE_LIMIT_WINDOW_MS.
        if (!await checkRateLimit(origin)) {
          return { id: message.id, result: { allowed: false, error: 'Rate limited. Too many authorize requests. Try again later.' } };
        }
        const result = await authorizeWithDisclosure(message.request, origin);
        resetLockTimer();
        return { id: message.id, result };
      }
      resetLockTimer();
      return { id: message.id, result: await authorize(message.request) };
    }

    case 'pyana:isConnected':
      return { id: message.id, result: true };

    case 'pyana:canAuthorize':
      return { id: message.id, result: await canAuthorize(message.request) };

    case 'pyana:getCapabilities':
      return { id: message.id, result: await getCapabilities() };

    case 'pyana:getState':
      return { id: message.id, result: await getWalletState() };

    case 'pyana:lock': {
      await lockWallet();
      return { id: message.id, result: true };
    }

    case 'pyana:unlock': {
      // Bug 1 fix: unlock ONLY from extension popup.
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Unlock is only available from the extension popup.' };
      }
      const passphrase = message.passphrase || '';
      const result = await unlockWallet(passphrase);
      if (result.success) {
        notifySubscribers('ready', { locked: false });
      }
      return { id: message.id, result };
    }

    case 'pyana:setPassphrase': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      await setPassphrase(message.passphrase);
      return { id: message.id, result: true };
    }

    case 'pyana:getMnemonic': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      const wallet = await loadState();
      if (wallet.locked) {
        return { id: message.id, error: 'Wallet is locked' };
      }
      const mnemonic = await getMnemonic();
      if (state) state.mnemonicShown = true;
      await saveState();
      return { id: message.id, result: mnemonic };
    }

    case 'pyana:recover': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      const result = await recoverFromMnemonic(message.mnemonic, message.passphrase || '');
      return { id: message.id, result };
    }

    case 'pyana:provision': {
      const tabId = sender?.tab?.id;
      const result = await provisionToken(message.tokenData, tabId);
      resetLockTimer();
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

    case 'pyana:disclosureDecision':
      return { id: message.id, result: true };

    case 'pyana:getDisclosurePrefs': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      return { id: message.id, result: await getDisclosurePrefs() };
    }

    case 'pyana:clearDisclosurePref': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      const prefs = await getDisclosurePrefs();
      delete prefs[message.origin];
      await chrome.storage.local.set({ [DISCLOSURE_PREFS_KEY]: prefs });
      return { id: message.id, result: true };
    }

    case 'pyana:getOriginPermissions': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      return { id: message.id, result: await getAllOriginPermissions() };
    }

    case 'pyana:revokeOriginPermission': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      await revokeOriginPermissions(message.origin);
      return { id: message.id, result: true };
    }

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

    case 'pyana:fulfillIntent': {
      const result = await fulfillIntent(message.intentId, message.tokenId || null);
      return { id: message.id, result };
    }

    case 'pyana:getFulfillableIntents': {
      const result = await getFulfillableIntents();
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

    // --- Privacy features ---

    case 'pyana:getStealthAddress': {
      const meta = await getStealthMetaAddress();
      if (!meta) {
        return { id: message.id, error: 'Stealth keys not available (wallet locked or WASM missing)' };
      }
      return { id: message.id, result: meta };
    }

    case 'pyana:postEncryptedIntent': {
      const result = await postEncryptedIntent(message.matchSpec, message.options || {});
      return { id: message.id, result };
    }

    case 'pyana:privateTransfer': {
      const result = await privateTransfer(
        message.amount,
        message.assetType,
        message.recipientStealthMeta
      );
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:getPrivacyState': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      return { id: message.id, result: await getPrivacyState() };
    }

    case 'pyana:setCommittedTransferMode': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      const result = await setCommittedTransferMode(message.enabled);
      return { id: message.id, result };
    }

    case 'pyana:getStealthNotes': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from extension popup.' };
      }
      const wallet = await loadState();
      if (wallet.locked) {
        return { id: message.id, error: 'Wallet is locked' };
      }
      return { id: message.id, result: wallet.stealthNotes || [] };
    }

    // --- Bearer capabilities ---

    case 'pyana:createBearerCap': {
      requireWasm('createBearerCap');
      const wallet = await loadState();
      if (wallet.locked) {
        return { id: message.id, error: 'Wallet is locked' };
      }
      // Use wallet public key as delegator key.
      const delegatorKeyHex = Array.from(wallet.publicKey)
        .map(b => b.toString(16).padStart(2, '0')).join('');
      const result = wasm.create_bearer_cap(
        delegatorKeyHex,
        message.targetCellHex,
        message.action,
        message.expiry || 0
      );
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:verifyBearerCap': {
      requireWasm('verifyBearerCap');
      const currentTime = Math.floor(Date.now() / 1000);
      const result = wasm.verify_bearer_cap(
        message.bearerTokenHex,
        message.delegatorKeyHex,
        message.targetCellHex,
        message.action,
        message.expiry || 0,
        currentTime
      );
      return { id: message.id, result };
    }

    // --- Factory operations ---

    case 'pyana:createFromFactory': {
      requireWasm('createFromFactory');
      const result = wasm.create_from_factory(
        message.factoryVkHex,
        message.ownerPubkeyHex,
        message.initialBalance || 0
      );
      return { id: message.id, result };
    }

    case 'pyana:verifyProvenance': {
      requireWasm('verifyProvenance');
      const result = wasm.verify_provenance(
        message.cellVkHex,
        JSON.stringify(message.knownFactoryVks || [])
      );
      return { id: message.id, result };
    }

    // --- Sovereign cell operations ---

    case 'pyana:makeCellSovereign': {
      requireWasm('makeCellSovereign');
      const wallet = await loadState();
      if (wallet.locked) {
        return { id: message.id, error: 'Wallet is locked' };
      }
      // Get balance from node if possible, otherwise use 0.
      const result = wasm.make_cell_sovereign(message.cellIdHex, 0);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:peerExchange': {
      requireWasm('peerExchange');
      const wallet = await loadState();
      if (wallet.locked) {
        return { id: message.id, error: 'Wallet is locked' };
      }
      // Use wallet's cell as sender.
      const senderCellHex = wasm.blake3_hash(
        Array.from(wallet.publicKey).map(b => String.fromCharCode(b)).join('')
      );
      const result = wasm.peer_exchange_with_proof(
        senderCellHex,
        message.receiverCellHex,
        message.amount
      );
      resetLockTimer();
      return { id: message.id, result };
    }

    // --- Turn submission and balance ---

    case 'pyana:signTurn': {
      const result = await signTurn(message.turnSpec);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:queryBalance': {
      const result = await queryBalance();
      return { id: message.id, result };
    }

    // --- Node configuration (popup/settings only) ---

    case 'pyana:getNodeConfig': {
      return { id: message.id, result: { ...nodeConfig, devnetKey: nodeConfig.devnetKey ? '***' : '' } };
    }

    case 'pyana:setNodeConfig': {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: 'Only available from the extension popup or settings page.' };
      }
      await saveNodeConfig(message.config);
      return { id: message.id, result: { success: true, nodeUrl: nodeConfig.nodeUrl } };
    }

    // --- Proof composition ---

    case 'pyana:composeProofs': {
      requireWasm('composeProofs');
      const proofsInput = (message.proofs || []).map(p => ({
        proof_json: p.proofJson || p.proof_json || '',
        public_inputs: p.publicInputs || p.public_inputs || [],
      }));
      const result = wasm.compose_proofs(JSON.stringify(proofsInput), message.mode || 'and');
      return { id: message.id, result };
    }

    // --- CapTP operations ---

    case 'pyana:shareCapability': {
      const result = await shareCapability(message.cellId);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:acceptCapability': {
      const tabId = sender?.tab?.id || null;
      const result = await acceptCapability(message.uri, tabId);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:createHandoff': {
      const result = await createHandoff(message.cellId, message.recipientPk);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:getLiveRefs': {
      return { id: message.id, result: getLiveRefs() };
    }

    case 'pyana:dropLiveRef': {
      const result = await dropLiveRef(message.refId);
      return { id: message.id, result };
    }

    // --- Directory / Namespace operations ---

    case 'pyana:mountService': {
      const result = await mountService(message.path, message.sturdyRef, message.kind, message.tags);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:discoverServices': {
      const result = await discoverServices(message.tags);
      return { id: message.id, result };
    }

    case 'pyana:resolvePath': {
      const result = await resolvePath(message.path);
      return { id: message.id, result };
    }

    // --- Storage operations ---

    case 'pyana:storageWrite': {
      const result = await storageWrite(message.data);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:storageRead': {
      const result = await storageRead(message.hash);
      return { id: message.id, result };
    }

    case 'pyana:storageQuota': {
      const result = await storageQuota();
      return { id: message.id, result };
    }

    // --- Federation governance ---

    case 'pyana:federationStatus': {
      const result = await getFederationStatus();
      return { id: message.id, result };
    }

    case 'pyana:proposeRoutes': {
      const result = await proposeRoutes(message.routes);
      resetLockTimer();
      return { id: message.id, result };
    }

    case 'pyana:voteOnProposal': {
      const result = await voteOnProposal(message.proposalId, message.approve);
      resetLockTimer();
      return { id: message.id, result };
    }

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
const WS_AUTH_TIMEOUT_MS = 5000;
let nodePublicKey = null; // Learned from node /status endpoint on first connect.
let wsAuthenticated = false;

/**
 * Fetch the node's public key from its /status endpoint.
 * This is used to validate signatures on WebSocket messages.
 */
async function fetchNodePublicKey() {
  try {
    const statusUrl = nodeConfig.nodeUrl.replace(/\/$/, '') + '/status';
    const resp = await fetch(statusUrl, {
      signal: AbortSignal.timeout(3000),
      headers: getNodeHeaders(),
    });
    if (resp.ok) {
      const data = await resp.json();
      if (data.public_key) {
        nodePublicKey = data.public_key;
        console.log('[pyana] Learned node public key:', nodePublicKey.slice(0, 16) + '...');
      }
    }
  } catch (_e) {
    console.warn('[pyana] Could not fetch node public key from /status');
  }
}

/**
 * Validate a message signature from the node using its Ed25519 public key.
 * Returns true if signature is valid, false otherwise.
 */
function validateNodeSignature(payload, signature, pubKey) {
  if (!wasm || !wasmLoaded) return false;
  try {
    // payload and signature are hex strings; pubKey is hex.
    return wasm.verify_token(payload, pubKey, signature, 'node');
  } catch (_e) {
    return false;
  }
}

/**
 * Validate an incoming WebSocket message from the node.
 * Revocations and receipts MUST be signed. Other messages are allowed unsigned
 * (e.g., 'subscribed', 'error') but are not trusted for state mutations.
 */
function validateNodeMessage(msg) {
  // Messages that mutate wallet state require a valid signature.
  const SIGNED_TYPES = new Set(['revocation', 'receipt', 'root', 'intent', 'note_announcement']);
  if (!SIGNED_TYPES.has(msg.type)) return true; // informational, no signature needed
  if (!nodePublicKey) {
    console.warn('[pyana] No node public key available; rejecting signed message');
    return false;
  }
  if (!msg.signature || !msg.payload) {
    console.warn('[pyana] WS message missing signature/payload field, type:', msg.type);
    return false;
  }
  return validateNodeSignature(msg.payload, msg.signature, nodePublicKey);
}

async function connectNodeWs() {
  if (nodeWs && (nodeWs.readyState === WebSocket.CONNECTING || nodeWs.readyState === WebSocket.OPEN)) {
    return;
  }

  // Learn the node's public key before connecting (needed for message validation).
  if (!nodePublicKey) {
    await fetchNodePublicKey();
  }

  wsAuthenticated = false;

  // Try wss:// first. Fall back to ws:// ONLY for localhost (Bug 6 fix).
  const wssUrl = nodeConfig.wssUrl || DEFAULT_NODE_WSS_URL;
  const wsUrl = nodeConfig.wsUrl || DEFAULT_NODE_WS_URL;
  tryConnect(wssUrl, () => {
    console.warn('[pyana] wss:// connection failed, falling back to ws:// (localhost only)');
    const parsedWsUrl = new URL(wsUrl);
    if (parsedWsUrl.hostname === 'localhost' || parsedWsUrl.hostname === '127.0.0.1' || parsedWsUrl.hostname === '::1') {
      tryConnect(wsUrl, () => {
        scheduleReconnect();
      });
    } else {
      console.error('[pyana] Refusing ws:// fallback for non-localhost host:', parsedWsUrl.hostname);
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

    // Security: send a challenge for the node to prove its identity.
    const challenge = crypto.getRandomValues(new Uint8Array(32));
    const challengeHex = Array.from(challenge).map(b => b.toString(16).padStart(2, '0')).join('');
    nodeWs.send(JSON.stringify({
      type: 'auth_challenge',
      challenge: challengeHex,
    }));

    // If the node does not respond with a valid auth_response within 5s, disconnect.
    const authTimer = setTimeout(() => {
      if (!wsAuthenticated && nodeWs) {
        console.error('[pyana] WS auth timeout — node did not respond to challenge in time');
        nodeWs.close();
      }
    }, WS_AUTH_TIMEOUT_MS);

    // Store challenge info for validation in onmessage.
    nodeWs._authChallenge = challengeHex;
    nodeWs._authTimer = authTimer;
  };

  nodeWs.onmessage = async (event) => {
    let msg;
    try {
      msg = JSON.parse(event.data);
    } catch {
      return;
    }

    // Handle auth_response before any other processing.
    if (msg.type === 'auth_response') {
      if (nodePublicKey && msg.signature && nodeWs._authChallenge) {
        if (validateNodeSignature(nodeWs._authChallenge, msg.signature, nodePublicKey)) {
          wsAuthenticated = true;
          clearTimeout(nodeWs._authTimer);
          console.log('[pyana] WS node authenticated successfully');
          // Now subscribe after authentication.
          nodeWs.send(JSON.stringify({
            type: 'subscribe',
            topics: ['roots', 'revocations', 'receipts', 'intents', 'note_announcements'],
          }));
        } else {
          console.error('[pyana] WS auth failed — invalid signature from node');
          nodeWs.close();
        }
      } else if (!nodePublicKey) {
        // No public key available — accept connection but log warning.
        wsAuthenticated = true;
        clearTimeout(nodeWs._authTimer);
        console.warn('[pyana] WS auth skipped — no node public key available');
        nodeWs.send(JSON.stringify({
          type: 'subscribe',
          topics: ['roots', 'revocations', 'receipts', 'intents', 'note_announcements'],
        }));
      } else {
        console.error('[pyana] WS auth_response missing signature');
        nodeWs.close();
      }
      return;
    }

    // Reject state-mutating messages if authentication has not completed.
    if (!wsAuthenticated) {
      console.warn('[pyana] Ignoring WS message before authentication:', msg.type);
      return;
    }

    // Validate signature on state-mutating messages.
    if (!validateNodeMessage(msg)) {
      console.warn('[pyana] Rejecting WS message with invalid/missing signature:', msg.type);
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
      case 'note_announcement': {
        // Stealth note scanning: check if any announced notes are addressed to us.
        const announcements = msg.notes || (msg.note ? [msg.note] : []);
        if (announcements.length > 0) {
          const matched = await scanStealthNotes(announcements);
          if (matched.length > 0) {
            console.log('[pyana] Found', matched.length, 'stealth note(s) addressed to us');
          }
        }
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

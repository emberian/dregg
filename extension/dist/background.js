"use strict";
(() => {
  // src/api.ts
  var REQUEST_TIMEOUT_MS = 1e4;
  function getNodeHeaders(config) {
    const headers = { "Content-Type": "application/json" };
    if (config.devnetKey) {
      headers["X-Devnet-Key"] = config.devnetKey;
    }
    return headers;
  }
  async function nodeRequest(config, path, options = {}) {
    const url = config.nodeUrl.replace(/\/$/, "") + path;
    const baseHeaders = getNodeHeaders(config);
    const mergedHeaders = { ...baseHeaders, ...options.headers || {} };
    try {
      const resp = await fetch(url, {
        signal: AbortSignal.timeout(REQUEST_TIMEOUT_MS),
        ...options,
        headers: mergedHeaders
      });
      if (resp.ok) {
        const data = await resp.json().catch(() => null);
        return { ok: true, data: data ?? void 0, status: resp.status };
      } else {
        const errText = await resp.text().catch(() => "");
        return { ok: false, error: `HTTP ${resp.status}: ${errText}`, status: resp.status };
      }
    } catch (e) {
      const err = e;
      if (err.name === "TimeoutError" || err.name === "AbortError") {
        return { ok: false, error: "Node request timed out. Is the node online?" };
      }
      return { ok: false, error: `Network error: ${err.message}` };
    }
  }
  async function nodeRequestRaw(config, path) {
    const url = config.nodeUrl.replace(/\/$/, "") + path;
    const headers = getNodeHeaders(config);
    try {
      const resp = await fetch(url, {
        signal: AbortSignal.timeout(15e3),
        headers
      });
      if (!resp.ok) {
        return { ok: false, error: `Storage read failed: HTTP ${resp.status}` };
      }
      const buffer = await resp.arrayBuffer();
      return { ok: true, data: buffer };
    } catch (e) {
      const err = e;
      return { ok: false, error: `Storage read failed: ${err.message}` };
    }
  }

  // src/background.ts
  var STORAGE_KEY = "pyana_wallet";
  var ENCRYPTED_STATE_KEY = "pyana_wallet_encrypted";
  var MNEMONIC_KEY = "pyana_mnemonic_encrypted";
  var ALLOWED_ORIGINS_KEY = "pyana_allowed_origins";
  var NODE_CONFIG_KEY = "pyana_node_config";
  var DEFAULT_NODE_URL = "https://devnet.pyana.fg-goose.online";
  var DEFAULT_NODE_WSS_URL = "wss://devnet.pyana.fg-goose.online/ws";
  var DEFAULT_NODE_WS_URL = "ws://localhost:8420/ws";
  var DISCOVERY_URL = "https://emberian.github.io/pyana/discovery.json";
  var DISCOVERY_POLL_INTERVAL = 5 * 60 * 1e3;
  var PBKDF2_ITERATIONS = 6e5;
  var DISCLOSURE_PREFS_KEY = "pyana_disclosure_prefs";
  var LOCK_TIMEOUT_MS = 5 * 60 * 1e3;
  var ORIGIN_PERMISSION_EXPIRY_MS = 24 * 60 * 60 * 1e3;
  var RATE_LIMIT_MAX_CALLS = 5;
  var RATE_LIMIT_WINDOW_MS = 60 * 1e3;
  var DEFAULT_INTENT_EXPIRY_MS = 5 * 60 * 1e3;
  var INTENT_GC_INTERVAL = 6e4;
  var LIVE_REFS_KEY = "pyana_live_refs";
  var WS_MAX_RECONNECT_DELAY = 6e4;
  var WS_AUTH_TIMEOUT_MS = 5e3;
  var nodeConfig = {
    nodeUrl: DEFAULT_NODE_URL,
    wssUrl: DEFAULT_NODE_WSS_URL,
    wsUrl: DEFAULT_NODE_WS_URL,
    devnetKey: ""
  };
  async function loadNodeConfig() {
    const stored = await chrome.storage.local.get(NODE_CONFIG_KEY);
    if (stored[NODE_CONFIG_KEY]) {
      nodeConfig = { ...nodeConfig, ...stored[NODE_CONFIG_KEY] };
    }
    return nodeConfig;
  }
  async function saveNodeConfig(config) {
    nodeConfig = { ...nodeConfig, ...config };
    await chrome.storage.local.set({ [NODE_CONFIG_KEY]: nodeConfig });
    if (nodeWs) {
      nodeWs.close();
      nodeWs = null;
    }
    connectNodeWs();
  }
  var wasm = null;
  var wasmLoaded = false;
  var wasmLoadError = null;
  var wasmReady = (async () => {
    try {
      try {
        importScripts("./pyana_wasm.js");
      } catch (_importErr) {
      }
      if (typeof wasm_bindgen !== "undefined") {
        const wasmUrl = chrome.runtime.getURL("pyana_wasm_bg.wasm");
        await wasm_bindgen(wasmUrl);
        wasm = wasm_bindgen;
        wasmLoaded = true;
      } else if (typeof __pyana_wasm_init !== "undefined") {
        wasm = await __pyana_wasm_init();
        wasmLoaded = true;
      } else {
        const wasmUrl = chrome.runtime.getURL("pyana_wasm_bg.wasm");
        const response = await fetch(wasmUrl);
        if (!response.ok) {
          throw new Error(`Failed to fetch WASM: HTTP ${response.status}`);
        }
        const wasmBytes = await response.arrayBuffer();
        const { instance } = await WebAssembly.instantiate(wasmBytes, {});
        wasm = instance.exports;
        wasmLoaded = true;
      }
    } catch (e) {
      const err = e;
      wasm = null;
      wasmLoaded = false;
      wasmLoadError = err.message;
    }
  })();
  function requireWasm(operation) {
    if (!wasmLoaded || !wasm) {
      throw new Error(
        `WASM cryptographic module not loaded. Cannot perform ${operation}. ` + (wasmLoadError ? `Load error: ${wasmLoadError}` : "Module unavailable.")
      );
    }
  }
  var pendingQueue = [];
  var ready = false;
  wasmReady.then(() => {
    ready = true;
    for (const { msg, sender, resolve } of pendingQueue) {
      resolve(handleMessage(msg, sender));
    }
    pendingQueue.length = 0;
  });
  var lockTimer = null;
  function resetLockTimer() {
    if (lockTimer !== null) {
      clearTimeout(lockTimer);
    }
    lockTimer = setTimeout(async () => {
      await lockWallet();
      notifySubscribers("ready", { locked: true });
    }, LOCK_TIMEOUT_MS);
  }
  var rateLimits = /* @__PURE__ */ new Map();
  function checkRateLimit(tabId, origin) {
    const key = `${tabId ?? -1}::${origin}`;
    const now = Date.now();
    let entry = rateLimits.get(key);
    if (!entry || now - entry.windowStart > RATE_LIMIT_WINDOW_MS) {
      entry = { count: 0, windowStart: now };
    }
    if (entry.count >= RATE_LIMIT_MAX_CALLS) {
      rateLimits.set(key, entry);
      return false;
    }
    entry.count++;
    rateLimits.set(key, entry);
    return true;
  }
  var pendingDecisions = /* @__PURE__ */ new Map();
  var PENDING_DECISION_TTL_MS = 10 * 60 * 1e3;
  function generatePopupNonce() {
    const bytes = new Uint8Array(16);
    crypto.getRandomValues(bytes);
    return Array.from(bytes).map((b) => b.toString(16).padStart(2, "0")).join("");
  }
  function registerPendingDecision(popupPath, payload) {
    const now = Date.now();
    for (const [k, v] of pendingDecisions) {
      if (now - v.createdAt > PENDING_DECISION_TTL_MS) {
        pendingDecisions.delete(k);
      }
    }
    const nonce = generatePopupNonce();
    pendingDecisions.set(nonce, { popupPath, payload, createdAt: now });
    return nonce;
  }
  function consumePendingDecision(nonce) {
    const entry = pendingDecisions.get(nonce);
    if (!entry) return null;
    pendingDecisions.delete(nonce);
    return entry;
  }
  function validatePopupSender(message, sender, expectedNonce, expectedPopupPath) {
    if (sender?.tab != null) return false;
    if (!sender?.url) return false;
    const prefix = `chrome-extension://${chrome.runtime.id}/`;
    if (!sender.url.startsWith(prefix)) return false;
    const path = sender.url.slice(prefix.length).split(/[?#]/)[0];
    if (path !== expectedPopupPath) return false;
    const nonce = message.nonce;
    if (!nonce || nonce !== expectedNonce) return false;
    if (!pendingDecisions.has(nonce)) return false;
    return true;
  }
  async function getInternalEncryptionKey() {
    const stored = await chrome.storage.session.get("_internalKey");
    let key = stored._internalKey;
    if (!key) {
      const keyBytes = new Uint8Array(32);
      crypto.getRandomValues(keyBytes);
      key = Array.from(keyBytes).map((b) => b.toString(16).padStart(2, "0")).join("");
      await chrome.storage.session.set({ _internalKey: key });
    }
    return key;
  }
  async function deriveEncryptionKey(passphrase, salt) {
    const enc = new TextEncoder();
    const keyMaterial = await crypto.subtle.importKey(
      "raw",
      enc.encode(passphrase),
      "PBKDF2",
      false,
      ["deriveKey"]
    );
    return crypto.subtle.deriveKey(
      { name: "PBKDF2", salt, iterations: PBKDF2_ITERATIONS, hash: "SHA-256" },
      keyMaterial,
      { name: "AES-GCM", length: 256 },
      false,
      ["encrypt", "decrypt"]
    );
  }
  async function encryptWithPassphrase(plaintext, passphrase) {
    const salt = crypto.getRandomValues(new Uint8Array(16));
    const iv = crypto.getRandomValues(new Uint8Array(12));
    const key = await deriveEncryptionKey(passphrase, salt);
    const enc = new TextEncoder();
    const ciphertext = await crypto.subtle.encrypt(
      { name: "AES-GCM", iv },
      key,
      enc.encode(plaintext)
    );
    return {
      salt: Array.from(salt),
      iv: Array.from(iv),
      ciphertext: Array.from(new Uint8Array(ciphertext))
    };
  }
  async function decryptWithPassphrase(encrypted, passphrase) {
    const salt = new Uint8Array(encrypted.salt);
    const iv = new Uint8Array(encrypted.iv);
    const ciphertext = new Uint8Array(encrypted.ciphertext);
    const key = await deriveEncryptionKey(passphrase, salt);
    const plainBuffer = await crypto.subtle.decrypt(
      { name: "AES-GCM", iv },
      key,
      ciphertext
    );
    return new TextDecoder().decode(plainBuffer);
  }
  var _wordlistCache = null;
  async function getWordlist() {
    if (_wordlistCache) return _wordlistCache;
    try {
      const url = chrome.runtime.getURL("bip39_english.txt");
      const resp = await fetch(url);
      const text = await resp.text();
      _wordlistCache = text.trim().split("\n");
      if (_wordlistCache.length === 2048) return _wordlistCache;
    } catch (e) {
      const err = e;
      console.warn("[pyana] Failed to load wordlist from bundle:", err.message);
    }
    _wordlistCache = null;
    return null;
  }
  async function generateMnemonic() {
    if (wasm && wasm.generate_mnemonic) {
      try {
        return wasm.generate_mnemonic();
      } catch (e) {
        const err = e;
        console.warn("[pyana] WASM generate_mnemonic failed, using JS fallback:", err.message);
      }
    }
    const entropy = crypto.getRandomValues(new Uint8Array(32));
    const hashBuffer = await crypto.subtle.digest("SHA-256", entropy);
    const checksum = new Uint8Array(hashBuffer)[0];
    const bits = new Array(264);
    for (let i = 0; i < 32; i++) {
      for (let bit = 0; bit < 8; bit++) {
        bits[i * 8 + bit] = entropy[i] >> 7 - bit & 1;
      }
    }
    for (let bit = 0; bit < 8; bit++) {
      bits[256 + bit] = checksum >> 7 - bit & 1;
    }
    const indices = [];
    for (let i = 0; i < 24; i++) {
      let index = 0;
      for (let bit = 0; bit < 11; bit++) {
        if (bits[i * 11 + bit]) {
          index |= 1 << 10 - bit;
        }
      }
      indices.push(index);
    }
    const wordlist = await getWordlist();
    if (!wordlist) throw new Error("Wordlist unavailable for mnemonic generation");
    return indices.map((i) => wordlist[i]).join(" ");
  }
  async function validateMnemonic(mnemonic) {
    if (wasm && wasm.validate_mnemonic) {
      try {
        return wasm.validate_mnemonic(mnemonic);
      } catch (_e) {
      }
    }
    const words = mnemonic.trim().split(/\s+/);
    if (words.length !== 24) return false;
    const wordlist = await getWordlist();
    if (!wordlist) return false;
    const indices = [];
    for (const word of words) {
      const idx = wordlist.indexOf(word);
      if (idx === -1) return false;
      indices.push(idx);
    }
    const bits = new Array(264);
    for (let i = 0; i < 24; i++) {
      for (let bit = 0; bit < 11; bit++) {
        bits[i * 11 + bit] = indices[i] >> 10 - bit & 1;
      }
    }
    const entropyBytes = new Uint8Array(32);
    for (let i = 0; i < 32; i++) {
      for (let bit = 0; bit < 8; bit++) {
        if (bits[i * 8 + bit]) {
          entropyBytes[i] |= 1 << 7 - bit;
        }
      }
    }
    let checksumByte = 0;
    for (let bit = 0; bit < 8; bit++) {
      if (bits[256 + bit]) {
        checksumByte |= 1 << 7 - bit;
      }
    }
    const hashBuffer = await crypto.subtle.digest("SHA-256", entropyBytes);
    const expectedChecksum = new Uint8Array(hashBuffer)[0];
    return checksumByte === expectedChecksum;
  }
  async function deriveKeypairFromMnemonic(mnemonic, passphrase) {
    requireWasm("deriveKeypairFromMnemonic");
    const w = wasm;
    const result = w.derive_keypair_from_mnemonic(mnemonic, passphrase, "pyana/0");
    return { publicKey: result.public_key, secretKey: result.secret_key };
  }
  var subscribers = /* @__PURE__ */ new Map();
  function notifySubscribers(event, payload) {
    for (const [tabId, events] of subscribers) {
      if (events.has(event)) {
        chrome.tabs.sendMessage(tabId, { type: "pyana:event", event, payload }).catch(() => {
          subscribers.delete(tabId);
        });
      }
    }
  }
  var state = null;
  var walletPassphrase = null;
  async function loadState() {
    if (state) return state;
    const stored = await chrome.storage.local.get(STORAGE_KEY);
    if (stored[STORAGE_KEY]) {
      state = stored[STORAGE_KEY];
      state.needsPassphraseSetup = true;
      const internalKey2 = await getInternalEncryptionKey();
      walletPassphrase = internalKey2;
      state.locked = false;
      await saveState();
      state.locked = true;
      state.secretKey = null;
      walletPassphrase = null;
      return state;
    }
    const encrypted = await chrome.storage.local.get(ENCRYPTED_STATE_KEY);
    if (encrypted[ENCRYPTED_STATE_KEY]) {
      const envelope = encrypted[ENCRYPTED_STATE_KEY];
      state = {
        locked: true,
        publicKey: envelope.publicKey || [],
        secretKey: null,
        tokens: [],
        receiptChain: [],
        log: [],
        hasMnemonic: envelope.hasMnemonic || false,
        mnemonicShown: false,
        needsPassphraseSetup: envelope.needsPassphraseSetup || false,
        stealthMeta: null,
        stealthPrivate: null,
        stealthNotes: []
      };
      return state;
    }
    const mnemonic = await generateMnemonic();
    const keypair = await deriveKeypairFromMnemonic(mnemonic, "");
    state = {
      locked: true,
      publicKey: Array.from(keypair.publicKey),
      secretKey: Array.from(keypair.secretKey),
      tokens: [],
      receiptChain: [],
      log: [],
      hasMnemonic: true,
      mnemonicShown: false,
      needsPassphraseSetup: true,
      stealthMeta: null,
      stealthPrivate: null,
      stealthNotes: []
    };
    const internalKey = await getInternalEncryptionKey();
    walletPassphrase = internalKey;
    state.locked = false;
    await saveState();
    const encryptedMnemonic = await encryptWithPassphrase(mnemonic, internalKey);
    await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });
    state.locked = true;
    state.secretKey = null;
    walletPassphrase = null;
    state.needsPassphraseSetup = true;
    return state;
  }
  async function saveState() {
    if (!state) return;
    if (!walletPassphrase && !state.locked) {
      walletPassphrase = await getInternalEncryptionKey();
    }
    if (walletPassphrase && !state.locked) {
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
        stealthNotes: state.stealthNotes || []
      });
      const envelope = await encryptWithPassphrase(plaintext, walletPassphrase);
      envelope.publicKey = state.publicKey;
      envelope.hasMnemonic = state.hasMnemonic;
      envelope.needsPassphraseSetup = state.needsPassphraseSetup || false;
      await chrome.storage.local.set({ [ENCRYPTED_STATE_KEY]: envelope });
      await chrome.storage.local.remove(STORAGE_KEY);
    }
  }
  async function lockWallet() {
    if (!state) return;
    if (walletPassphrase) {
      state.locked = false;
      await saveState();
    }
    state.locked = true;
    state.secretKey = null;
    walletPassphrase = null;
    if (lockTimer !== null) {
      clearTimeout(lockTimer);
      lockTimer = null;
    }
  }
  async function unlockWallet(passphrase) {
    const encrypted = await chrome.storage.local.get(ENCRYPTED_STATE_KEY);
    if (!encrypted[ENCRYPTED_STATE_KEY]) {
      if (state) state.locked = false;
      return { success: true };
    }
    const envelope = encrypted[ENCRYPTED_STATE_KEY];
    const attempts = [passphrase];
    if (envelope.needsPassphraseSetup) {
      const internalKey = await getInternalEncryptionKey();
      attempts.push(internalKey);
    }
    for (const attempt of attempts) {
      try {
        const plaintext = await decryptWithPassphrase(envelope, attempt);
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
          stealthNotes: decrypted.stealthNotes || []
        };
        walletPassphrase = attempt;
        resetLockTimer();
        return { success: true, needsPassphraseSetup: state.needsPassphraseSetup };
      } catch (_e) {
      }
    }
    return { success: false, error: "Invalid passphrase" };
  }
  async function setPassphrase(newPassphrase) {
    const oldPassphrase = walletPassphrase;
    walletPassphrase = newPassphrase;
    if (state) {
      state.needsPassphraseSetup = false;
    }
    const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
    if (mnemonicStored[MNEMONIC_KEY]) {
      let mnemonic = null;
      const keysToTry = oldPassphrase ? [oldPassphrase] : [];
      const internalKey = await getInternalEncryptionKey();
      keysToTry.push(internalKey);
      for (const key of keysToTry) {
        try {
          mnemonic = await decryptWithPassphrase(mnemonicStored[MNEMONIC_KEY], key);
          break;
        } catch (_e) {
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
  async function getMnemonic() {
    const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
    if (!mnemonicStored[MNEMONIC_KEY]) return null;
    if (!walletPassphrase) return null;
    const keysToTry = [walletPassphrase];
    const internalKey = await getInternalEncryptionKey();
    if (walletPassphrase !== internalKey) {
      keysToTry.push(internalKey);
    }
    for (const key of keysToTry) {
      try {
        return await decryptWithPassphrase(mnemonicStored[MNEMONIC_KEY], key);
      } catch (_e) {
      }
    }
    return null;
  }
  async function recoverFromMnemonic(mnemonic, passphrase) {
    const valid = await validateMnemonic(mnemonic);
    if (!valid) {
      return { success: false, error: "Invalid mnemonic (bad checksum or unknown words)" };
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
      needsPassphraseSetup: !passphrase,
      stealthMeta: null,
      stealthPrivate: null,
      stealthNotes: []
    };
    const encryptionKey = passphrase || await getInternalEncryptionKey();
    walletPassphrase = encryptionKey;
    const encryptedMnemonic = await encryptWithPassphrase(mnemonic, encryptionKey);
    await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });
    await saveState();
    resetLockTimer();
    return { success: true, publicKey: state.publicKey };
  }
  async function getOriginAllowlist() {
    const stored = await chrome.storage.local.get(ALLOWED_ORIGINS_KEY);
    const raw = stored[ALLOWED_ORIGINS_KEY] || {};
    if (Array.isArray(raw)) {
      const cleared = {};
      await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: cleared });
      return cleared;
    }
    const sanitized = {};
    let dirty = false;
    for (const [origin, entry] of Object.entries(raw)) {
      if (Array.isArray(entry?.methods) && entry.methods.includes("*")) {
        dirty = true;
        continue;
      }
      sanitized[origin] = entry;
    }
    if (dirty) {
      await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: sanitized });
    }
    return sanitized;
  }
  async function addOriginToAllowlist(origin, method) {
    const allowlist = await getOriginAllowlist();
    if (!allowlist[origin]) {
      allowlist[origin] = { methods: [], expires: Date.now() + ORIGIN_PERMISSION_EXPIRY_MS };
    }
    if (!allowlist[origin].methods.includes(method)) {
      allowlist[origin].methods.push(method);
    }
    allowlist[origin].expires = Date.now() + ORIGIN_PERMISSION_EXPIRY_MS;
    await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
  }
  async function revokeOriginPermissions(origin) {
    const allowlist = await getOriginAllowlist();
    delete allowlist[origin];
    await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
  }
  async function getAllOriginPermissions() {
    const allowlist = await getOriginAllowlist();
    const result = [];
    const now = Date.now();
    for (const [origin, entry] of Object.entries(allowlist)) {
      if (entry.expires && entry.expires < now) continue;
      result.push({
        origin,
        methods: entry.methods,
        expires: entry.expires,
        expiresIn: entry.expires ? Math.max(0, entry.expires - now) : null
      });
    }
    return result;
  }
  function evaluateDatalog(token, request) {
    requireWasm("evaluateDatalog");
    const w = wasm;
    const facts = token.actions.map((a) => ({
      predicate: "grant",
      terms: [a, token.resource || "*"]
    }));
    const reqJson = JSON.stringify({
      action: request.action,
      service: request.resource
    });
    const result = w.evaluate_datalog(JSON.stringify(facts), reqJson);
    return {
      allowed: result.conclusion === "allow",
      trace: result.steps.map((s) => `rule(${s.rule_id}) derived ${s.derived_predicate_hex}`)
    };
  }
  function generateProof(witness, mode) {
    requireWasm("generateProof");
    const w = wasm;
    const hash = witness.reduce((acc, b, i) => acc ^ b << i % 4 * 8, 0) >>> 0;
    const depth = mode === "private" ? 8 : mode === "selective" ? 4 : 2;
    const result = w.generate_demo_stark_proof(hash, depth);
    return new TextEncoder().encode(result.proof_json);
  }
  function resolvePrivateValue(token, key) {
    const directMap = {
      expires: token.expiry,
      expiry: token.expiry,
      issued: token.provisioned,
      provisioned: token.provisioned,
      balance: token.balance,
      amount: token.amount,
      reputation: token.reputation,
      score: token.score,
      level: token.level,
      depth: token.depth,
      delegationDepth: token.delegationDepth,
      budget: token.budget
    };
    if (key in directMap && directMap[key] != null) {
      const val = directMap[key];
      return typeof val === "number" ? val : parseInt(String(val), 10) || null;
    }
    if (token.attributes && key in token.attributes) {
      const val = token.attributes[key];
      return typeof val === "number" ? val : parseInt(String(val), 10) || null;
    }
    if (token.meta && key in token.meta) {
      const val = token.meta[key];
      return typeof val === "number" ? val : parseInt(String(val), 10) || null;
    }
    return null;
  }
  async function authorize(request) {
    if (!wasmLoaded || !wasm) {
      return { allowed: false, error: "Cryptographic module unavailable. Cannot authorize securely." };
    }
    const wallet = await loadState();
    if (wallet.locked) {
      return { allowed: false, error: "Wallet is locked" };
    }
    const matchingToken = wallet.tokens.find(
      (t) => t.actions.includes(request.action) && (t.resource === "*" || t.resource === request.resource) && (!t.expiry || t.expiry > Date.now())
    );
    if (!matchingToken) {
      return { allowed: false, error: "No capability token grants this action" };
    }
    const evalResult = evaluateDatalog(matchingToken, request);
    if (!evalResult.allowed) {
      return { allowed: false, facts: evalResult.trace };
    }
    const mode = request.mode || "trusted";
    const witness = new TextEncoder().encode(
      JSON.stringify({ token: matchingToken.id, action: request.action, resource: request.resource })
    );
    const proof = generateProof(witness, mode);
    const receiptHash = Array.from(proof.slice(0, 16)).map((b) => b.toString(16).padStart(2, "0")).join("");
    wallet.receiptChain.push(receiptHash);
    wallet.log.push({
      action: request.action,
      resource: request.resource,
      allowed: true,
      timestamp: Date.now(),
      mode,
      disclosedFacts: request._disclosedFacts || null,
      predicateFacts: request._predicateFacts || null
    });
    await saveState();
    const result = { allowed: true, proof: Array.from(proof), facts: evalResult.trace, mode };
    if (mode === "selective" && request._disclosedFacts) {
      result.facts = evalResult.trace.filter(
        (traceEntry) => request._disclosedFacts.some(
          (key) => traceEntry.toLowerCase().includes(key.toLowerCase())
        )
      );
      result.disclosedFacts = request._disclosedFacts;
    }
    if (mode === "selective" && request._predicateFacts) {
      let stateRoot = 0;
      try {
        const statusResult = await nodeRequest(nodeConfig, "/status");
        if (statusResult.ok && statusResult.data) {
          const merkleRoot = statusResult.data.merkle_root || statusResult.data.state_root || "";
          if (merkleRoot) {
            stateRoot = parseInt(merkleRoot.slice(0, 8), 16) >>> 0;
          }
        }
      } catch (_e) {
        const stateRootInput = wallet.receiptChain.length > 0 ? wallet.receiptChain[wallet.receiptChain.length - 1] : "0";
        requireWasm("authorize:blake3_hash");
        const stateRootHash = wasm.blake3_hash(stateRootInput);
        stateRoot = parseInt(stateRootHash.slice(0, 8), 16) >>> 0;
      }
      result.predicateProofs = request._predicateFacts.map((pf) => {
        const privateValue = resolvePrivateValue(matchingToken, pf.key);
        if (privateValue === null) {
          return { key: pf.key, predicateType: pf.predicateType, threshold: pf.threshold, proof: null, error: `Attribute "${pf.key}" not found in token` };
        }
        const predicateTypeMap = {
          gte: "gte",
          ">=": "gte",
          lte: "lte",
          "<=": "lte",
          gt: "gt",
          ">": "gt",
          lt: "lt",
          "<": "lt",
          neq: "neq",
          "!=": "neq"
        };
        const wasmPredicateType = predicateTypeMap[pf.predicateType] || "gte";
        const thresholdValue = typeof pf.threshold === "number" ? pf.threshold : parseInt(String(pf.threshold), 10) || 0;
        try {
          requireWasm("authorize:generate_predicate_proof");
          const proofResult = wasm.generate_predicate_proof(
            wasmPredicateType,
            privateValue >>> 0,
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
            proofSizeBytes: proofResult.proof_size_bytes
          };
        } catch (e) {
          const err = e;
          return { key: pf.key, predicateType: pf.predicateType, threshold: pf.threshold, proof: null, error: err.message || "Predicate proof generation failed" };
        }
      });
    }
    if (mode === "private") {
      result.facts = [];
    }
    notifySubscribers("authorization", {
      action: request.action,
      resource: request.resource,
      allowed: true,
      mode
    });
    return result;
  }
  async function canAuthorize(request) {
    const wallet = await loadState();
    if (wallet.locked) return false;
    const matchingToken = wallet.tokens.find(
      (t) => t.actions.includes(request.action) && (t.resource === "*" || t.resource === request.resource) && (!t.expiry || t.expiry > Date.now())
    );
    if (!matchingToken) return false;
    const evalResult = evaluateDatalog(matchingToken, request);
    return evalResult.allowed;
  }
  function extractTokenFacts(token, request) {
    const facts = [];
    if (token.actions && token.actions.length > 0) {
      for (const act of token.actions) {
        facts.push({ key: "action", value: act, category: "permissions" });
      }
    }
    if (token.resource) {
      facts.push({ key: "resource", value: token.resource, category: "resource" });
    }
    if (token.userId) {
      facts.push({ key: "user", value: token.userId, category: "identity" });
    }
    if (token.org || token.organization) {
      facts.push({ key: "organization", value: token.org || token.organization, category: "identity" });
    }
    if (token.email) {
      facts.push({ key: "email", value: token.email, category: "identity" });
    }
    if (token.expiry) {
      facts.push({ key: "expires", value: token.expiry, category: "temporal" });
    }
    if (token.provisioned) {
      facts.push({ key: "issued", value: token.provisioned, category: "temporal" });
    }
    if (request.action && !facts.some((f) => f.key === "action" && f.value === request.action)) {
      facts.push({ key: "action", value: request.action, category: "permissions" });
    }
    if (request.resource && request.resource !== "*" && !facts.some((f) => f.key === "resource" && f.value === request.resource)) {
      facts.push({ key: "resource", value: request.resource, category: "resource" });
    }
    return facts;
  }
  function showDisclosurePicker(origin, request, tokenFacts) {
    return new Promise((resolve) => {
      const requiredFacts = tokenFacts.filter((f) => f.key === "action" || f.key === "resource");
      const siteRequested = request.requestedDisclosure || [];
      const nonce = registerPendingDecision("disclosure-picker.html", {
        origin,
        action: request.action,
        resource: request.resource,
        tokenFacts,
        requiredFacts,
        siteRequestedFacts: siteRequested
      });
      const popupUrl = chrome.runtime.getURL("disclosure-picker.html") + "#nonce=" + nonce;
      chrome.windows.create({
        url: popupUrl,
        type: "popup",
        width: 440,
        height: 620,
        focused: true
      }, (win) => {
        const listener = (message, sender) => {
          if (message.type !== "pyana:disclosureDecision") return;
          if (!validatePopupSender(message, sender, nonce, "disclosure-picker.html")) return;
          chrome.runtime.onMessage.removeListener(listener);
          resolve(message);
        };
        chrome.runtime.onMessage.addListener(listener);
        if (win?.id) {
          chrome.windows.onRemoved.addListener(function onClose(closedId) {
            if (closedId === win.id) {
              chrome.windows.onRemoved.removeListener(onClose);
              chrome.runtime.onMessage.removeListener(listener);
              consumePendingDecision(nonce);
              resolve({ authorized: false });
            }
          });
        }
      });
    });
  }
  async function authorizeWithDisclosure(request, origin) {
    const wallet = await loadState();
    if (wallet.locked) {
      return { allowed: false, error: "Wallet is locked" };
    }
    const matchingToken = wallet.tokens.find(
      (t) => t.actions.includes(request.action) && (t.resource === "*" || t.resource === request.resource) && (!t.expiry || t.expiry > Date.now())
    );
    if (!matchingToken) {
      return { allowed: false, error: "No capability token grants this action" };
    }
    const prefs = await getDisclosurePrefs();
    const savedPref = prefs[origin];
    let disclosureLevel;
    let disclosedFacts = [];
    let predicateFacts = [];
    if (savedPref && !request.forceDisclosurePicker) {
      disclosureLevel = savedPref.level;
    } else {
      const tokenFacts = extractTokenFacts(matchingToken, request);
      const decision = await showDisclosurePicker(origin, request, tokenFacts);
      if (!decision.authorized) {
        return { allowed: false, error: "User denied authorization" };
      }
      disclosureLevel = decision.level || "full";
      disclosedFacts = decision.disclosedFacts || [];
      if (decision.facts && Array.isArray(decision.facts)) {
        for (const factDecision of decision.facts) {
          if (factDecision.disclosure === "reveal") {
            const factObj = tokenFacts[factDecision.index];
            if (factObj && !disclosedFacts.includes(factObj.key)) {
              disclosedFacts.push(factObj.key);
            }
          } else if (factDecision.disclosure === "predicate") {
            const factObj = tokenFacts[factDecision.index];
            if (factObj) {
              predicateFacts.push({
                key: factObj.key,
                predicateType: factDecision.predicateType || "gte",
                threshold: factDecision.threshold || 0
              });
            }
          }
        }
      }
      if (decision.remember && origin) {
        await saveDisclosurePref(origin, disclosureLevel);
      }
    }
    const modeMap = { full: "trusted", selective: "selective", private: "private" };
    const mode = modeMap[disclosureLevel] || "trusted";
    return authorize({
      ...request,
      mode,
      _disclosedFacts: disclosedFacts.length > 0 ? disclosedFacts : null,
      _predicateFacts: predicateFacts.length > 0 ? predicateFacts : null
    });
  }
  async function getDisclosurePrefs() {
    const stored = await chrome.storage.local.get(DISCLOSURE_PREFS_KEY);
    return stored[DISCLOSURE_PREFS_KEY] || {};
  }
  async function saveDisclosurePref(origin, level) {
    const prefs = await getDisclosurePrefs();
    prefs[origin] = { level, savedAt: Date.now() };
    await chrome.storage.local.set({ [DISCLOSURE_PREFS_KEY]: prefs });
  }
  async function provisionToken(tokenData, _senderTabId) {
    return new Promise((resolve) => {
      const nonce = registerPendingDecision("provision.html", { tokenData });
      const popupUrl = chrome.runtime.getURL("provision.html") + "#nonce=" + nonce;
      chrome.windows.create({
        url: popupUrl,
        type: "popup",
        width: 400,
        height: 480,
        focused: true
      }, (win) => {
        const listener = async (message, sender) => {
          if (message.type !== "pyana:provisionDecision") return;
          if (!validatePopupSender(message, sender, nonce, "provision.html")) return;
          chrome.runtime.onMessage.removeListener(listener);
          if (message.accepted) {
            const wallet = await loadState();
            const token = {
              id: `tok_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`,
              actions: tokenData.actions || [],
              resource: tokenData.resource || "*",
              expiry: tokenData.expiry || null,
              issuer: tokenData.issuer || null,
              provisioned: Date.now()
            };
            wallet.tokens.push(token);
            await saveState();
            resolve({ accepted: true, tokenId: token.id });
          } else {
            resolve({ accepted: false });
          }
        };
        chrome.runtime.onMessage.addListener(listener);
        if (win?.id) {
          chrome.windows.onRemoved.addListener(function onClose(closedId) {
            if (closedId === win.id) {
              chrome.windows.onRemoved.removeListener(onClose);
              chrome.runtime.onMessage.removeListener(listener);
              consumePendingDecision(nonce);
              resolve({ accepted: false });
            }
          });
        }
      });
    });
  }
  var intentPool = /* @__PURE__ */ new Map();
  function showIntentConfirmation(action, matchSpec, options, origin) {
    return new Promise((resolve) => {
      const nonce = registerPendingDecision("confirm-intent.html", {
        action,
        matchSpec,
        options: options || {},
        origin: origin || "unknown"
      });
      const popupUrl = chrome.runtime.getURL("confirm-intent.html") + "#nonce=" + nonce;
      chrome.windows.create({
        url: popupUrl,
        type: "popup",
        width: 400,
        height: 380,
        focused: true
      }, (win) => {
        const listener = (message, sender) => {
          if (message.type !== "pyana:intentConfirmation") return;
          if (!validatePopupSender(message, sender, nonce, "confirm-intent.html")) return;
          chrome.runtime.onMessage.removeListener(listener);
          resolve(message.confirmed === true);
        };
        chrome.runtime.onMessage.addListener(listener);
        if (win?.id) {
          chrome.windows.onRemoved.addListener(function onClose(closedId) {
            if (closedId === win.id) {
              chrome.windows.onRemoved.removeListener(onClose);
              chrome.runtime.onMessage.removeListener(listener);
              consumePendingDecision(nonce);
              resolve(false);
            }
          });
        }
      });
    });
  }
  async function computeIntentId(kind, matchSpec, expiry) {
    const intentInput = {
      kind: kind === "need" ? "Need" : kind === "offer" ? "Offer" : "Query",
      actions: (matchSpec?.actions || []).map((a) => ({ action: a.action || null, resource: a.resource || null })),
      constraints: (matchSpec?.constraints || []).map((c) => {
        if (c.type === "appId") return { AppId: c.value };
        if (c.type === "service") return { Service: c.value };
        if (c.type === "userId") return { UserId: c.value };
        if (c.type === "notExpiredAt") return { NotExpiredAt: c.value };
        if (c.type === "feature") return { Feature: c.value };
        if (c.type === "oauthProvider") return { OAuthProvider: c.value };
        return { predicate: c.type || "", value: c.value || "" };
      }),
      min_budget: matchSpec?.minBudget || null,
      resource_pattern: matchSpec?.resourcePattern || null,
      expiry,
      creator: matchSpec?.creator || null,
      proof_of_stake: matchSpec?.proofOfStake || null
    };
    if (wasm && wasm.compute_intent_id) {
      try {
        return wasm.compute_intent_id(JSON.stringify(intentInput));
      } catch (_e) {
      }
    }
    const canonical = JSON.stringify({
      kind: intentInput.kind,
      actions: intentInput.actions,
      constraints: intentInput.constraints,
      min_budget: intentInput.min_budget,
      resource_pattern: intentInput.resource_pattern,
      expiry: intentInput.expiry
    });
    const encoded = new TextEncoder().encode(canonical);
    const hashBuffer = await crypto.subtle.digest("SHA-256", encoded);
    const hashArray = Array.from(new Uint8Array(hashBuffer));
    return "js:" + hashArray.map((b) => b.toString(16).padStart(2, "0")).join("");
  }
  async function postIntent(matchSpec, options, origin) {
    const confirmed = await showIntentConfirmation("postIntent", matchSpec, options, origin);
    if (!confirmed) {
      return { error: "User denied intent broadcast" };
    }
    const expiry = options?.expiry || Date.now() + DEFAULT_INTENT_EXPIRY_MS;
    const intentId = await computeIntentId("need", matchSpec, expiry);
    const intent = {
      id: intentId,
      kind: "need",
      matcher: matchSpec,
      expiry,
      createdAt: Date.now()
    };
    intentPool.set(intentId, { intent, receivedAt: Date.now() });
    if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
      nodeWs.send(JSON.stringify({ type: "broadcast_intent", intent }));
    }
    return { intentId, expiry };
  }
  function matchIntentLocally(intent, tokens, now) {
    const spec = intent.matcher;
    if (!spec) return null;
    for (const token of tokens) {
      if (token.expiry && token.expiry <= now) continue;
      if (spec.actions && spec.actions.length > 0) {
        const actionsSatisfied = spec.actions.every((pattern) => {
          if (!pattern.action) return true;
          return token.actions.includes(pattern.action) || token.actions.includes("*");
        });
        if (!actionsSatisfied) continue;
      }
      if (spec.resourcePattern) {
        const tokenResource = token.resource || "*";
        if (tokenResource !== "*" && tokenResource !== spec.resourcePattern) {
          if (!tokenResource.endsWith("/*") || !spec.resourcePattern.startsWith(tokenResource.slice(0, -2))) {
            continue;
          }
        }
      }
      if (spec.constraints && spec.constraints.length > 0) {
        let constraintsMet = true;
        for (const c of spec.constraints) {
          if (c.type === "appId" && token.appId !== c.value) {
            constraintsMet = false;
            break;
          }
          if (c.type === "service" && token.service !== c.value) {
            constraintsMet = false;
            break;
          }
          if (c.type === "notExpiredAt" && token.expiry && token.expiry <= c.value) {
            constraintsMet = false;
            break;
          }
        }
        if (!constraintsMet) continue;
      }
      const grantedActions = spec.actions ? spec.actions.map((p) => p.action).filter(Boolean) : token.actions;
      return { tokenId: token.id, grantedActions, resource: spec.resourcePattern || token.resource || "*" };
    }
    return null;
  }
  function listIntents(filter) {
    const now = Date.now();
    const results = [];
    for (const [, { intent }] of intentPool) {
      if (intent.expiry <= now) continue;
      if (filter?.kind && intent.kind !== filter.kind) continue;
      results.push({ id: intent.id, kind: intent.kind, matcher: intent.matcher, expiry: intent.expiry });
    }
    return results;
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
  var liveRefs = /* @__PURE__ */ new Map();
  async function shareCapability(cellId) {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    const resp = await nodeRequest(nodeConfig, "/turns/bearer-auth", {
      method: "POST",
      body: JSON.stringify({ cell_id: cellId })
    });
    if (!resp.ok) return { error: `Failed to export sturdy ref: ${resp.error}` };
    const nodeId = resp.data?.node_id || "local";
    const secret = resp.data?.secret || "";
    const uri = `pyana://${nodeId}/${cellId}/${secret}`;
    wallet.log.push({ action: "shareCapability", resource: cellId, allowed: true, timestamp: Date.now(), mode: "captp" });
    await saveState();
    return { uri, cellId, nodeId };
  }
  async function acceptCapability(uri, tabId) {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    if (!uri.startsWith("pyana://")) return { error: "Invalid URI: must start with pyana://" };
    const parts = uri.replace("pyana://", "").split("/");
    if (parts.length < 3) return { error: "Invalid URI format. Expected: pyana://<node>/<cell>/<secret>" };
    const [nodeId, cellId, secret] = parts;
    const resp = await nodeRequest(nodeConfig, "/turns/peer-exchange", {
      method: "POST",
      body: JSON.stringify({ node_id: nodeId, cell_id: cellId, secret })
    });
    if (!resp.ok) return { error: `Failed to enliven capability: ${resp.error}` };
    const refId = `ref_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
    const liveRef = {
      cellId,
      uri,
      nodeId,
      permissions: resp.data?.permissions || "full",
      tabId: tabId || null,
      createdAt: Date.now(),
      capId: resp.data?.cap_id || null
    };
    liveRefs.set(refId, liveRef);
    await persistLiveRefs();
    wallet.log.push({ action: "acceptCapability", resource: cellId, allowed: true, timestamp: Date.now(), mode: "captp" });
    await saveState();
    return { refId, cellId, nodeId, permissions: liveRef.permissions };
  }
  async function createHandoff(cellId, recipientPk) {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    const resp = await nodeRequest(nodeConfig, "/turns/peer-exchange", {
      method: "POST",
      body: JSON.stringify({ cell_id: cellId, recipient_pk: recipientPk })
    });
    if (!resp.ok) return { error: `Failed to create handoff: ${resp.error}` };
    return { certificateHash: resp.data?.certificate_hash || "", cellId, recipientPk };
  }
  function getLiveRefs() {
    const result = [];
    for (const [refId, ref] of liveRefs) {
      result.push({ refId, ...ref });
    }
    return result;
  }
  async function dropLiveRef(refId) {
    if (!liveRefs.has(refId)) return { error: "Live ref not found" };
    liveRefs.delete(refId);
    await persistLiveRefs();
    return { dropped: true, refId };
  }
  async function persistLiveRefs() {
    const summary = [];
    for (const [refId, ref] of liveRefs) {
      summary.push({ refId, cellId: ref.cellId, nodeId: ref.nodeId, createdAt: ref.createdAt });
    }
    await chrome.storage.session.set({ [LIVE_REFS_KEY]: summary });
  }
  function cleanupTabRefs(tabId) {
    for (const [refId, ref] of liveRefs) {
      if (ref.tabId === tabId) {
        liveRefs.delete(refId);
      }
    }
    persistLiveRefs();
  }
  chrome.tabs.onRemoved.addListener((tabId) => {
    cleanupTabRefs(tabId);
  });
  async function mountService(path, sturdyRef, kind, tags) {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    const resp = await nodeRequest(nodeConfig, "/registry/mount", {
      method: "POST",
      body: JSON.stringify({ path, uri: sturdyRef, kind: kind || "service", tags: tags || [] })
    });
    if (!resp.ok) return { error: `Failed to mount: ${resp.error}` };
    return { path, version: resp.data?.version || 1, kind: kind || "service" };
  }
  async function discoverServices(tags) {
    const queryParams = (tags || []).map((t) => `tag=${encodeURIComponent(t)}`).join("&");
    const query = queryParams ? `?${queryParams}` : "";
    const resp = await nodeRequest(nodeConfig, `/registry/discover${query}`);
    if (!resp.ok) return { error: `Discovery failed: ${resp.error}` };
    return { results: resp.data?.results || [] };
  }
  async function resolvePath(path) {
    const encoded = encodeURIComponent(path);
    const resp = await nodeRequest(nodeConfig, `/registry/get?path=${encoded}`);
    if (!resp.ok) return { error: `Resolve failed: ${resp.error}` };
    return resp.data || {};
  }
  async function storageWrite(dataBase64) {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    const binary = Uint8Array.from(atob(dataBase64), (c) => c.charCodeAt(0));
    const resp = await nodeRequest(nodeConfig, "/files/write", {
      method: "POST",
      headers: { "Content-Type": "application/octet-stream" },
      body: binary
    });
    if (!resp.ok) return { error: `Storage write failed: ${resp.error}` };
    return { hash: resp.data?.hash || "", size: resp.data?.size || binary.length };
  }
  async function storageRead(hash) {
    const result = await nodeRequestRaw(nodeConfig, `/files/read/${hash}`);
    if (!result.ok) return { error: result.error };
    const bytes = new Uint8Array(result.data);
    const base64 = btoa(String.fromCharCode(...bytes));
    return { hash, data: base64, size: bytes.length };
  }
  async function storageQuota() {
    const resp = await nodeRequest(nodeConfig, "/storage/quota");
    if (!resp.ok) return { bytesStored: 0, bytesLimit: 0, computronsUsed: 0, computronsRemaining: 0, objectCount: 0, error: `Quota check failed: ${resp.error}` };
    return {
      bytesStored: resp.data?.bytes_stored || 0,
      bytesLimit: resp.data?.bytes_limit || 0,
      computronsUsed: resp.data?.computrons_used || 0,
      computronsRemaining: resp.data?.computrons_remaining || 0,
      objectCount: resp.data?.object_count || 0
    };
  }
  async function getFederationStatus() {
    const resp = await nodeRequest(nodeConfig, "/status");
    if (!resp.ok) return { error: `Federation status failed: ${resp.error}` };
    return {
      mode: resp.data?.federation_mode || "unknown",
      height: resp.data?.latest_height || 0,
      peerCount: resp.data?.peer_count || 0,
      merkleRoot: resp.data?.merkle_root || ""
    };
  }
  async function proposeRoutes(routes) {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    const resp = await nodeRequest(nodeConfig, "/turn/atomic", {
      method: "POST",
      body: JSON.stringify({ type: "route-update", args: { routes } })
    });
    if (!resp.ok) return { error: `Proposal failed: ${resp.error}` };
    return { proposalId: resp.data?.proposal_id || "", submitted: true };
  }
  async function voteOnProposal(proposalId, approve) {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    const resp = await nodeRequest(nodeConfig, "/turn/atomic/vote", {
      method: "POST",
      body: JSON.stringify({ proposal_id: proposalId, vote: !!approve })
    });
    if (!resp.ok) return { error: `Vote failed: ${resp.error}` };
    return { accepted: resp.data?.accepted !== false, proposalId };
  }
  async function signTurn(turnSpec) {
    requireWasm("signTurn");
    const w = wasm;
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked", submitted: false };
    if (wallet.needsPassphraseSetup) {
      return { error: "Set a wallet passphrase before signing turns.", submitted: false };
    }
    if (!wallet.secretKey) return { error: "Wallet secret key not available", submitted: false };
    let turnData;
    if (w.build_turn) {
      turnData = w.build_turn(JSON.stringify({
        sender_pubkey: wallet.publicKey,
        sender_privkey: wallet.secretKey,
        action: turnSpec.action,
        resource: turnSpec.resource || "*",
        amount: turnSpec.amount || 0,
        recipient: turnSpec.recipient || null,
        metadata: turnSpec.metadata || null,
        timestamp: Date.now()
      }));
    } else {
      const turnJson = JSON.stringify({
        sender: wallet.publicKey,
        action: turnSpec.action,
        resource: turnSpec.resource || "*",
        amount: turnSpec.amount || 0,
        recipient: turnSpec.recipient || null,
        metadata: turnSpec.metadata || null,
        timestamp: Date.now()
      });
      if (!w.sign_message) {
        return { error: "WASM sign_message export not available", submitted: false };
      }
      const signature = w.sign_message(
        new Uint8Array(wallet.secretKey),
        new TextEncoder().encode(turnJson)
      );
      turnData = {
        turn_id: "js:" + Array.from(crypto.getRandomValues(new Uint8Array(16))).map((b) => b.toString(16).padStart(2, "0")).join(""),
        turn_bytes: new TextEncoder().encode(turnJson),
        signature
      };
    }
    const resp = await nodeRequest(nodeConfig, "/turns/submit", {
      method: "POST",
      body: JSON.stringify({
        turn_id: turnData.turn_id,
        turn_bytes: Array.from(turnData.turn_bytes),
        signature: turnData.signature ? Array.from(turnData.signature) : void 0,
        sender_pubkey: wallet.publicKey
      })
    });
    if (!resp.ok) {
      return { error: `Failed to submit turn: ${resp.error}`, turnId: turnData.turn_id, submitted: false };
    }
    wallet.log.push({ action: turnSpec.action, resource: turnSpec.resource || "*", allowed: true, timestamp: Date.now(), mode: "turn", turnId: turnData.turn_id });
    await saveState();
    return { turnId: turnData.turn_id, submitted: true, nodeResult: resp.data };
  }
  async function queryBalance() {
    const wallet = await loadState();
    if (wallet.locked) return { error: "Wallet is locked" };
    const pubkeyHex = Array.from(wallet.publicKey).map((b) => b.toString(16).padStart(2, "0")).join("");
    const resp = await nodeRequest(nodeConfig, `/accounts/${pubkeyHex}/balance`);
    if (!resp.ok) return { error: `Failed to query balance: ${resp.error}` };
    return { balance: resp.data?.balance ?? 0 };
  }
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
      hasStealthKeys: wallet.stealthMeta !== null && wallet.stealthMeta !== void 0,
      stealthNotesCount: (wallet.stealthNotes || []).length
    };
  }
  async function getCapabilities() {
    const wallet = await loadState();
    if (wallet.locked) return [];
    const actions = /* @__PURE__ */ new Set();
    for (const token of wallet.tokens) {
      for (const action of token.actions) {
        actions.add(action);
      }
    }
    return Array.from(actions);
  }
  async function revokeToken(tokenId) {
    const wallet = await loadState();
    const idx = wallet.tokens.findIndex((t) => t.id === tokenId);
    if (idx === -1) return { revoked: false, error: "Token not found" };
    wallet.tokens.splice(idx, 1);
    await saveState();
    notifySubscribers("revoked", { tokenId });
    return { revoked: true };
  }
  function isExtensionPopup(sender) {
    if (!sender?.url) return false;
    return sender.url.startsWith(`chrome-extension://${chrome.runtime.id}/`);
  }
  function isContentScript(sender) {
    return sender?.tab != null;
  }
  function handleOriginPermissionRequest(origin, method) {
    return new Promise((resolve) => {
      const nonce = registerPendingDecision("origin-permission.html", { origin, method });
      const popupUrl = chrome.runtime.getURL("origin-permission.html") + "#nonce=" + nonce;
      chrome.windows.create({
        url: popupUrl,
        type: "popup",
        width: 420,
        height: 320,
        focused: true
      }, (win) => {
        const listener = async (message, sender) => {
          if (message.type !== "pyana:originPermissionDecision") return;
          if (!validatePopupSender(message, sender, nonce, "origin-permission.html")) return;
          chrome.runtime.onMessage.removeListener(listener);
          if (message.granted) {
            await addOriginToAllowlist(origin, method);
            resolve({ granted: true });
          } else {
            resolve({ granted: false });
          }
        };
        chrome.runtime.onMessage.addListener(listener);
        if (win?.id) {
          chrome.windows.onRemoved.addListener(function onClose(closedId) {
            if (closedId === win.id) {
              chrome.windows.onRemoved.removeListener(onClose);
              chrome.runtime.onMessage.removeListener(listener);
              consumePendingDecision(nonce);
              resolve({ granted: false });
            }
          });
        }
      });
    });
  }
  var PAGE_ALLOWED_METHODS = /* @__PURE__ */ new Set([
    "pyana:authorize",
    "pyana:isConnected",
    "pyana:canAuthorize",
    "pyana:subscribe",
    "pyana:provision",
    "pyana:postIntent",
    "pyana:getStealthAddress",
    "pyana:postEncryptedIntent",
    "pyana:privateTransfer",
    "pyana:createBearerCap",
    "pyana:verifyBearerCap",
    "pyana:createFromFactory",
    "pyana:verifyProvenance",
    "pyana:makeCellSovereign",
    "pyana:peerExchange",
    "pyana:composeProofs",
    "pyana:signTurn",
    "pyana:queryBalance",
    "pyana:getNodeConfig",
    "pyana:shareCapability",
    "pyana:acceptCapability",
    "pyana:createHandoff",
    "pyana:mountService",
    "pyana:discoverServices",
    "pyana:resolvePath",
    "pyana:storageWrite",
    "pyana:storageRead",
    "pyana:storageQuota",
    "pyana:federationStatus",
    "pyana:proposeRoutes",
    "pyana:voteOnProposal"
  ]);
  var POPUP_ONLY_METHODS = /* @__PURE__ */ new Set([
    "pyana:unlock",
    "pyana:lock",
    "pyana:getCapabilities",
    "pyana:listIntents",
    "pyana:offerCapability",
    "pyana:fulfillIntent",
    "pyana:getFulfillableIntents",
    "pyana:revoke",
    "pyana:getState",
    "pyana:getFederation",
    "pyana:refreshDiscovery",
    "pyana:setPassphrase",
    "pyana:getMnemonic",
    "pyana:recover",
    "pyana:getDisclosurePrefs",
    "pyana:clearDisclosurePref",
    "pyana:getOriginPermissions",
    "pyana:revokeOriginPermission",
    "pyana:getPrivacyState",
    "pyana:setCommittedTransferMode",
    "pyana:getStealthNotes",
    "pyana:getNodeConfig",
    "pyana:setNodeConfig",
    "pyana:getLiveRefs",
    "pyana:dropLiveRef"
  ]);
  async function handleMessage(message, sender) {
    if (sender?.tab && message?.request) {
      delete message.request._skipDisclosure;
    }
    const msgType = message.type;
    switch (msgType) {
      case "pyana:authorize": {
        if (isContentScript(sender) && !message.request?._skipDisclosure) {
          const origin = message._origin || sender?.tab?.url && new URL(sender.tab.url).origin || "unknown";
          if (!checkRateLimit(sender?.tab?.id, origin)) {
            return { id: message.id, result: { allowed: false, error: "Rate limited. Too many authorize requests. Try again later." } };
          }
          const result = await authorizeWithDisclosure(message.request, origin);
          resetLockTimer();
          return { id: message.id, result };
        }
        resetLockTimer();
        return { id: message.id, result: await authorize(message.request) };
      }
      case "pyana:isConnected":
        return { id: message.id, result: true };
      case "pyana:canAuthorize":
        return { id: message.id, result: await canAuthorize(message.request) };
      case "pyana:getCapabilities":
        return { id: message.id, result: await getCapabilities() };
      case "pyana:getState":
        return { id: message.id, result: await getWalletState() };
      case "pyana:lock": {
        await lockWallet();
        return { id: message.id, result: true };
      }
      case "pyana:unlock": {
        if (!isExtensionPopup(sender)) {
          return { id: message.id, error: "Unlock is only available from the extension popup." };
        }
        const result = await unlockWallet(message.passphrase || "");
        if (result.success) {
          notifySubscribers("ready", { locked: false });
        }
        return { id: message.id, result };
      }
      case "pyana:setPassphrase": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        await setPassphrase(message.passphrase);
        return { id: message.id, result: true };
      }
      case "pyana:getMnemonic": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        const wallet = await loadState();
        if (wallet.locked) return { id: message.id, error: "Wallet is locked" };
        if (wallet.needsPassphraseSetup) {
          return { id: message.id, error: "Set a wallet passphrase before viewing the recovery phrase." };
        }
        const mnemonic = await getMnemonic();
        if (state) state.mnemonicShown = true;
        await saveState();
        return { id: message.id, result: mnemonic };
      }
      case "pyana:recover": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        const result = await recoverFromMnemonic(message.mnemonic, message.passphrase || "");
        return { id: message.id, result };
      }
      case "pyana:provision": {
        const result = await provisionToken(message.tokenData, sender?.tab?.id);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:revoke": {
        const result = await revokeToken(message.tokenId);
        return { id: message.id, result };
      }
      case "pyana:subscribe": {
        const tabId = sender?.tab?.id;
        if (tabId != null) {
          if (!subscribers.has(tabId)) subscribers.set(tabId, /* @__PURE__ */ new Set());
          subscribers.get(tabId).add(message.event);
        }
        return { id: message.id, result: true };
      }
      case "pyana:provisionDecision":
      case "pyana:intentConfirmation":
      case "pyana:disclosureDecision": {
        if (isContentScript(sender) || !isExtensionPopup(sender)) {
          return { id: message.id, error: "Decision messages may only come from extension popups." };
        }
        return { id: message.id, result: true };
      }
      case "pyana:getPendingDecision": {
        if (isContentScript(sender) || !isExtensionPopup(sender)) {
          return { id: message.id, error: "Only extension popups may fetch pending decisions." };
        }
        const nonce = message.nonce;
        if (!nonce) return { id: message.id, error: "Missing nonce." };
        const entry = pendingDecisions.get(nonce);
        if (!entry) return { id: message.id, error: "No such pending decision." };
        const prefix = `chrome-extension://${chrome.runtime.id}/`;
        const path = (sender.url || "").startsWith(prefix) ? (sender.url || "").slice(prefix.length).split(/[?#]/)[0] : "";
        if (path !== entry.popupPath) {
          return { id: message.id, error: "Popup path mismatch for this nonce." };
        }
        return { id: message.id, result: { payload: entry.payload } };
      }
      case "pyana:getDisclosurePrefs": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        return { id: message.id, result: await getDisclosurePrefs() };
      }
      case "pyana:clearDisclosurePref": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        const prefs = await getDisclosurePrefs();
        delete prefs[message.origin];
        await chrome.storage.local.set({ [DISCLOSURE_PREFS_KEY]: prefs });
        return { id: message.id, result: true };
      }
      case "pyana:getOriginPermissions": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        return { id: message.id, result: await getAllOriginPermissions() };
      }
      case "pyana:revokeOriginPermission": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        await revokeOriginPermissions(message.origin);
        return { id: message.id, result: true };
      }
      case "pyana:postIntent": {
        const origin = message._origin || sender?.tab?.url && new URL(sender.tab.url).origin || void 0;
        const result = await postIntent(message.matchSpec, message.options, origin);
        return { id: message.id, result };
      }
      case "pyana:offerCapability": {
        const origin = message._origin || sender?.tab?.url && new URL(sender.tab.url).origin || void 0;
        const confirmed = await showIntentConfirmation("offerCapability", message.matchSpec, message.options, origin);
        if (!confirmed) return { id: message.id, result: { error: "User denied capability offer" } };
        const expiry = message.options?.expiry || Date.now() + DEFAULT_INTENT_EXPIRY_MS;
        const intentId = await computeIntentId("offer", message.matchSpec, expiry);
        const intent = { id: intentId, kind: "offer", matcher: message.matchSpec, expiry, createdAt: Date.now() };
        intentPool.set(intentId, { intent, receivedAt: Date.now() });
        if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
          nodeWs.send(JSON.stringify({ type: "broadcast_intent", intent }));
        }
        return { id: message.id, result: { intentId, expiry } };
      }
      case "pyana:listIntents":
        return { id: message.id, result: listIntents(message.filter) };
      case "pyana:fulfillIntent": {
        return { id: message.id, result: { error: "Not yet migrated to TypeScript" } };
      }
      case "pyana:getFulfillableIntents": {
        const wallet = await loadState();
        if (wallet.locked) return { id: message.id, result: [] };
        const now = Date.now();
        const fulfillable = [];
        for (const [, { intent }] of intentPool) {
          if (intent.expiry <= now || intent.kind !== "need") continue;
          const matchResult = matchIntentLocally(intent, wallet.tokens, now);
          if (matchResult) {
            fulfillable.push({
              intentId: intent.id,
              kind: intent.kind,
              matcher: intent.matcher,
              expiry: intent.expiry,
              matchedTokenId: matchResult.tokenId,
              grantedActions: matchResult.grantedActions,
              resource: matchResult.resource
            });
          }
        }
        return { id: message.id, result: fulfillable };
      }
      case "pyana:getFederation":
        return { id: message.id, result: federationState };
      case "pyana:refreshDiscovery":
        await fetchDiscovery();
        return { id: message.id, result: federationState };
      case "pyana:requestOriginPermission": {
        const result = await handleOriginPermissionRequest(message.origin, message.method);
        return result;
      }
      case "pyana:originPermissionDecision": {
        if (isContentScript(sender) || !isExtensionPopup(sender)) {
          return { id: message.id, error: "Decision messages may only come from extension popups." };
        }
        return { id: message.id, result: true };
      }
      case "pyana:shareCapability": {
        const result = await shareCapability(message.cellId);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:acceptCapability": {
        const result = await acceptCapability(message.uri, sender?.tab?.id);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:createHandoff": {
        const result = await createHandoff(message.cellId, message.recipientPk);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:getLiveRefs":
        return { id: message.id, result: getLiveRefs() };
      case "pyana:dropLiveRef": {
        const result = await dropLiveRef(message.refId);
        return { id: message.id, result };
      }
      case "pyana:mountService": {
        const result = await mountService(message.path, message.sturdyRef, message.kind, message.tags);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:discoverServices":
        return { id: message.id, result: await discoverServices(message.tags) };
      case "pyana:resolvePath":
        return { id: message.id, result: await resolvePath(message.path) };
      case "pyana:storageWrite": {
        const result = await storageWrite(message.data);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:storageRead":
        return { id: message.id, result: await storageRead(message.hash) };
      case "pyana:storageQuota":
        return { id: message.id, result: await storageQuota() };
      case "pyana:federationStatus":
        return { id: message.id, result: await getFederationStatus() };
      case "pyana:proposeRoutes": {
        const result = await proposeRoutes(message.routes);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:voteOnProposal": {
        const result = await voteOnProposal(message.proposalId, message.approve);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:signTurn": {
        const result = await signTurn(message.turnSpec);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:queryBalance":
        return { id: message.id, result: await queryBalance() };
      case "pyana:getNodeConfig":
        return { id: message.id, result: { ...nodeConfig, devnetKey: nodeConfig.devnetKey ? "***" : "" } };
      case "pyana:setNodeConfig": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from the extension popup or settings page." };
        await saveNodeConfig(message.config);
        return { id: message.id, result: { success: true, nodeUrl: nodeConfig.nodeUrl } };
      }
      case "pyana:createBearerCap": {
        requireWasm("createBearerCap");
        const w = wasm;
        const wallet = await loadState();
        if (wallet.locked) return { id: message.id, error: "Wallet is locked" };
        const delegatorKeyHex = Array.from(wallet.publicKey).map((b) => b.toString(16).padStart(2, "0")).join("");
        const result = w.create_bearer_cap(delegatorKeyHex, message.targetCellHex, message.action, message.expiry || 0);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:verifyBearerCap": {
        requireWasm("verifyBearerCap");
        const w = wasm;
        const currentTime = Math.floor(Date.now() / 1e3);
        const result = w.verify_bearer_cap(
          message.bearerTokenHex,
          message.delegatorKeyHex,
          message.targetCellHex,
          message.action,
          message.expiry || 0,
          currentTime
        );
        return { id: message.id, result };
      }
      case "pyana:createFromFactory": {
        requireWasm("createFromFactory");
        const w = wasm;
        const result = w.create_from_factory(message.factoryVkHex, message.ownerPubkeyHex, message.initialBalance || 0);
        return { id: message.id, result };
      }
      case "pyana:verifyProvenance": {
        requireWasm("verifyProvenance");
        const w = wasm;
        const result = w.verify_provenance(message.cellVkHex, JSON.stringify(message.knownFactoryVks || []));
        return { id: message.id, result };
      }
      case "pyana:makeCellSovereign": {
        requireWasm("makeCellSovereign");
        const w = wasm;
        const wallet = await loadState();
        if (wallet.locked) return { id: message.id, error: "Wallet is locked" };
        const result = w.make_cell_sovereign(message.cellIdHex, 0);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:peerExchange": {
        requireWasm("peerExchange");
        const w = wasm;
        const wallet = await loadState();
        if (wallet.locked) return { id: message.id, error: "Wallet is locked" };
        const senderCellHex = w.blake3_hash(
          Array.from(wallet.publicKey).map((b) => String.fromCharCode(b)).join("")
        );
        const result = w.peer_exchange_with_proof(senderCellHex, message.receiverCellHex, message.amount);
        resetLockTimer();
        return { id: message.id, result };
      }
      case "pyana:composeProofs": {
        requireWasm("composeProofs");
        const w = wasm;
        const proofsInput = (message.proofs || []).map((p) => ({
          proof_json: p.proofJson || p.proof_json || "",
          public_inputs: p.publicInputs || p.public_inputs || []
        }));
        const result = w.compose_proofs(JSON.stringify(proofsInput), message.mode || "and");
        return { id: message.id, result };
      }
      case "pyana:getStealthAddress":
        return { id: message.id, result: state?.stealthMeta || null };
      case "pyana:getPrivacyState": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        const wallet = await loadState();
        if (wallet.locked) return { id: message.id, result: { active: false, locked: true } };
        return { id: message.id, result: { active: true, stealthMeta: wallet.stealthMeta } };
      }
      case "pyana:setCommittedTransferMode": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        return { id: message.id, result: { success: true, committedTransfersActive: !!message.enabled } };
      }
      case "pyana:getStealthNotes": {
        if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
        const wallet = await loadState();
        if (wallet.locked) return { id: message.id, error: "Wallet is locked" };
        return { id: message.id, result: wallet.stealthNotes || [] };
      }
      case "pyana:postEncryptedIntent":
      case "pyana:privateTransfer":
        return { id: message.id, result: { error: "Requires WASM module -- not yet migrated" } };
      default:
        return { id: message.id, error: "Unknown message type" };
    }
  }
  chrome.runtime.onMessage.addListener((message, sender, sendResponse) => {
    const dispatch = async () => {
      const msgType = message.type;
      if (POPUP_ONLY_METHODS.has(msgType) && !isExtensionPopup(sender)) {
        return { id: message.id, error: `"${msgType}" is only available from the extension popup.` };
      }
      if (isContentScript(sender) && !PAGE_ALLOWED_METHODS.has(msgType) && !POPUP_ONLY_METHODS.has(msgType)) {
        if (msgType !== "pyana:requestOriginPermission") {
          return { id: message.id, error: `"${msgType}" is not available from page context.` };
        }
      }
      if (message.type === "pyana:authorize" && !ready) {
        return new Promise((resolve) => {
          pendingQueue.push({ msg: message, sender, resolve });
        });
      }
      return handleMessage(message, sender);
    };
    dispatch().then(sendResponse).catch((err) => {
      sendResponse({ id: message.id, error: String(err) });
    });
    return true;
  });
  var nodeWs = null;
  var wsReconnectDelay = 1e3;
  var nodePublicKey = null;
  var wsAuthenticated = false;
  async function fetchNodePublicKey() {
    try {
      const resp = await nodeRequest(nodeConfig, "/status");
      if (resp.ok && resp.data?.public_key) {
        nodePublicKey = resp.data.public_key;
      }
    } catch (_e) {
    }
  }
  function validateNodeSignature(payload, signature, pubKey) {
    if (!wasm || !wasmLoaded) return false;
    try {
      return wasm.verify_token(payload, pubKey, signature, "node");
    } catch (_e) {
      return false;
    }
  }
  function validateNodeMessage(msg) {
    const SIGNED_TYPES = /* @__PURE__ */ new Set(["revocation", "receipt", "root", "intent", "note_announcement"]);
    if (!SIGNED_TYPES.has(msg.type)) return true;
    if (!nodePublicKey) return false;
    if (!msg.signature || !msg.payload) return false;
    return validateNodeSignature(msg.payload, msg.signature, nodePublicKey);
  }
  async function connectNodeWs() {
    if (nodeWs && (nodeWs.readyState === WebSocket.CONNECTING || nodeWs.readyState === WebSocket.OPEN)) {
      return;
    }
    if (!nodePublicKey) {
      await fetchNodePublicKey();
    }
    wsAuthenticated = false;
    const wssUrl = nodeConfig.wssUrl || DEFAULT_NODE_WSS_URL;
    const wsUrl = nodeConfig.wsUrl || DEFAULT_NODE_WS_URL;
    tryConnect(wssUrl, () => {
      const parsedWsUrl = new URL(wsUrl);
      if (parsedWsUrl.hostname === "localhost" || parsedWsUrl.hostname === "127.0.0.1" || parsedWsUrl.hostname === "::1") {
        tryConnect(wsUrl, () => scheduleReconnect());
      } else {
        scheduleReconnect();
      }
    });
  }
  function tryConnect(url, onFail) {
    try {
      nodeWs = new WebSocket(url);
    } catch (_e) {
      if (onFail) onFail();
      return;
    }
    nodeWs.onopen = () => {
      wsReconnectDelay = 1e3;
      const challenge = crypto.getRandomValues(new Uint8Array(32));
      const challengeHex = Array.from(challenge).map((b) => b.toString(16).padStart(2, "0")).join("");
      nodeWs.send(JSON.stringify({ type: "auth_challenge", challenge: challengeHex }));
      const authTimer = setTimeout(() => {
        if (!wsAuthenticated && nodeWs) {
          nodeWs.close();
        }
      }, WS_AUTH_TIMEOUT_MS);
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
      if (msg.type === "auth_response") {
        const ws = nodeWs;
        if (!nodePublicKey || !msg.signature || !ws._authChallenge) {
          nodeWs.close();
          return;
        }
        if (validateNodeSignature(ws._authChallenge, msg.signature, nodePublicKey)) {
          wsAuthenticated = true;
          clearTimeout(ws._authTimer);
          nodeWs.send(JSON.stringify({ type: "subscribe", topics: ["roots", "revocations", "receipts", "intents", "note_announcements"] }));
        } else {
          nodeWs.close();
        }
        return;
      }
      if (!wsAuthenticated) return;
      if (!validateNodeMessage(msg)) return;
      switch (msg.type) {
        case "revocation": {
          const wallet = await loadState();
          const idx = wallet.tokens.findIndex((t) => t.id === msg.token_id);
          if (idx !== -1) {
            wallet.tokens.splice(idx, 1);
            await saveState();
          }
          notifySubscribers("revoked", { tokenId: msg.token_id });
          break;
        }
        case "receipt": {
          const wallet = await loadState();
          wallet.receiptChain.push(msg.hash);
          await saveState();
          notifySubscribers("receipt", { hash: msg.hash });
          break;
        }
        case "root": {
          notifySubscribers("root", { height: msg.height, merkle_root: msg.merkle_root });
          break;
        }
        case "intent": {
          const intent = msg.intent;
          if (intent && intent.expiry > Date.now() && !intentPool.has(intent.id)) {
            intentPool.set(intent.id, { intent, receivedAt: Date.now() });
          }
          break;
        }
      }
    };
    nodeWs.onclose = () => {
      nodeWs = null;
      scheduleReconnect();
    };
    nodeWs.onerror = () => {
      nodeWs = null;
      if (onFail) onFail();
    };
  }
  function scheduleReconnect() {
    setTimeout(() => connectNodeWs(), wsReconnectDelay);
    wsReconnectDelay = Math.min(wsReconnectDelay * 2, WS_MAX_RECONNECT_DELAY);
  }
  var federationState = {
    nodes: [],
    intentService: null,
    lastUpdated: null,
    fetchError: null
  };
  async function fetchDiscovery() {
    try {
      const response = await fetch(DISCOVERY_URL, { cache: "no-cache", headers: { Accept: "application/json" } });
      if (!response.ok) throw new Error(`HTTP ${response.status}: ${response.statusText}`);
      const data = await response.json();
      federationState = {
        nodes: (data.federation || []).map((node) => ({
          nodeId: node.node_id,
          ticket: node.ticket,
          lastSeen: node.last_seen,
          role: node.role
        })),
        intentService: data.intent_service ? {
          nodeId: data.intent_service.node_id,
          ticket: data.intent_service.ticket,
          lastSeen: data.intent_service.last_seen
        } : null,
        lastUpdated: data.updated_at,
        commit: data.commit,
        fetchError: null
      };
      notifySubscribers("federation", {
        nodes: federationState.nodes,
        intentService: federationState.intentService,
        lastUpdated: federationState.lastUpdated
      });
    } catch (e) {
      const err = e;
      federationState.fetchError = err.message;
    }
  }
  var discoveryInterval = null;
  function startDiscoveryPolling() {
    fetchDiscovery();
    discoveryInterval = setInterval(fetchDiscovery, DISCOVERY_POLL_INTERVAL);
  }
  chrome.runtime.onInstalled.addListener(() => {
    chrome.contextMenus.create({
      id: "pyana-share-capability",
      title: "Share capability...",
      contexts: ["page", "selection"]
    });
  });
  chrome.contextMenus.onClicked.addListener(async (info) => {
    if (info.menuItemId === "pyana-share-capability") {
      const cellId = info.selectionText?.trim() || "";
      if (cellId && /^[0-9a-fA-F]{64}$/.test(cellId)) {
        const result = await shareCapability(cellId);
        if (result.uri) {
          const nonce = registerPendingDecision("share-capability.html", {
            uri: result.uri,
            cellId
          });
          chrome.windows.create({
            url: chrome.runtime.getURL("share-capability.html") + "#nonce=" + nonce,
            type: "popup",
            width: 420,
            height: 380,
            focused: true
          });
        }
      } else {
        const nonce = registerPendingDecision("share-capability.html", {});
        chrome.windows.create({
          url: chrome.runtime.getURL("share-capability.html") + "#nonce=" + nonce,
          type: "popup",
          width: 420,
          height: 380,
          focused: true
        });
      }
    }
  });
  loadNodeConfig();
  loadState();
  connectNodeWs();
  startDiscoveryPolling();
})();

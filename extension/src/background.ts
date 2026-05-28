/**
 * Dragon's Egg cipherclerk background service worker (TypeScript).
 * Manages cipherclerk state (signing keys, capability tokens, receipt chain),
 * evaluates authorization, and generates proofs via WASM.
 */

import { nodeRequest, nodeRequestRaw, getNodeHeaders } from "./api";
import { compatSession, extensionPrefix, isExtensionPageUrl } from "./browser-compat";
import type {
  AuthorizeRequest,
  AuthorizeResult,
  CapabilityToken,
  CipherclerkState,
  DisclosableFact,
  DisclosureDecision,
  EncryptedEnvelope,
  ExtensionLiveRef,
  FederationNode,
  FederationState,
  InternalCipherclerkState,
  Intent,
  IntentConstraint,
  KnownFederation,
  LogEntry,
  MatchSpec,
  MessageType,
  NodeConfig,
  NodeRequestResult,
  OriginPermission,
  OriginPermissionDisplay,
  OutboxEntry,
  PageResponseMessage,
  PredicateFact,
  PredicateProofResult,
  ReceiptWitnessArtifacts,
  DreggWasm,
  SignTurnResult,
  StealthMetaAddress,
  StealthNote,
  StealthPrivateKeys,
  StorageQuotaResult,
  TurnSpec,
} from "./types";

// ---------------------------------------------------------------------------
// Constants
// ---------------------------------------------------------------------------

// Storage keys — "dregg_cipherclerk*" keys are the legacy names kept for migration.
const STORAGE_KEY = "dregg_cipherclerk";
const ENCRYPTED_STATE_KEY = "dregg_cipherclerk_encrypted";
const MNEMONIC_KEY = "dregg_mnemonic_encrypted";
// Legacy key names; read-once migration copies them to the new keys on startup.
const LEGACY_STORAGE_KEY = "dregg_cipherclerk";
const LEGACY_ENCRYPTED_STATE_KEY = "dregg_wallet_encrypted";
const STEALTH_KEYS_KEY = "dregg_stealth_keys_encrypted";
const ALLOWED_ORIGINS_KEY = "dregg_allowed_origins";
const NODE_CONFIG_KEY = "dregg_node_config";
const DEFAULT_NODE_URL = "https://devnet.dregg.fg-goose.online";
const DEFAULT_NODE_WSS_URL = "wss://devnet.dregg.fg-goose.online/ws";
const DEFAULT_NODE_WS_URL = "ws://localhost:8420/ws";
const DISCOVERY_URL = "https://emberian.github.io/dregg/discovery.json";
const DISCOVERY_POLL_INTERVAL = 5 * 60 * 1000;
const PBKDF2_ITERATIONS = 600000;
const DISCLOSURE_PREFS_KEY = "dregg_disclosure_prefs";
const LOCK_TIMEOUT_MS = 5 * 60 * 1000;
const ORIGIN_PERMISSION_EXPIRY_MS = 24 * 60 * 60 * 1000;
const RATE_LIMIT_MAX_CALLS = 5;
const RATE_LIMIT_WINDOW_MS = 60 * 1000;
const PRIVACY_STATE_KEY = "dregg_privacy_state";
const DEFAULT_INTENT_EXPIRY_MS = 5 * 60 * 1000;
const INTENT_GC_INTERVAL = 60_000;
const LIVE_REFS_KEY = "dregg_live_refs";
const KNOWN_FEDERATIONS_KEY = "dregg_known_federations";
const OUTBOX_KEY = "dregg_extension_outbox";
const WS_MAX_RECONNECT_DELAY = 60000;
const WS_AUTH_TIMEOUT_MS = 5000;
const OUTBOX_MAX_ENTRIES = 200;
const OUTBOX_FLUSH_INTERVAL_MS = 30_000;
const OUTBOX_ALARM_NAME = "dregg-outbox-flush";

// ---------------------------------------------------------------------------
// Node configuration
// ---------------------------------------------------------------------------

let nodeConfig: NodeConfig = {
  nodeUrl: DEFAULT_NODE_URL,
  wssUrl: DEFAULT_NODE_WSS_URL,
  wsUrl: DEFAULT_NODE_WS_URL,
  devnetKey: "",
};

async function loadNodeConfig(): Promise<NodeConfig> {
  const stored = await chrome.storage.local.get(NODE_CONFIG_KEY);
  if (stored[NODE_CONFIG_KEY]) {
    nodeConfig = { ...nodeConfig, ...stored[NODE_CONFIG_KEY] };
  }
  return nodeConfig;
}

async function saveNodeConfig(config: Partial<NodeConfig>): Promise<void> {
  nodeConfig = { ...nodeConfig, ...config };
  await chrome.storage.local.set({ [NODE_CONFIG_KEY]: nodeConfig });
  if (nodeWs) {
    nodeWs.close();
    nodeWs = null;
  }
  connectNodeWs();
}

// ---------------------------------------------------------------------------
// WASM module
// ---------------------------------------------------------------------------

let wasm: DreggWasm | null = null;
let wasmLoaded = false;
let wasmLoadError: string | null = null;

declare function importScripts(...urls: string[]): void;
declare const wasm_bindgen: ((url: string) => Promise<void>) & Record<string, unknown>;
declare const __dregg_wasm_init: (() => Promise<DreggWasm>) | undefined;

const wasmReady = (async (): Promise<void> => {
  try {
    try {
      importScripts("./dregg_wasm.js");
    } catch (_importErr) {
      // importScripts failed -- dev mode, fall through.
    }

    if (typeof wasm_bindgen !== "undefined") {
      const wasmUrl = chrome.runtime.getURL("dregg_wasm_bg.wasm");
      await wasm_bindgen(wasmUrl);
      wasm = wasm_bindgen as unknown as DreggWasm;
      wasmLoaded = true;
    } else if (typeof __dregg_wasm_init !== "undefined") {
      wasm = await __dregg_wasm_init();
      wasmLoaded = true;
    } else {
      const wasmUrl = chrome.runtime.getURL("dregg_wasm_bg.wasm");
      const response = await fetch(wasmUrl);
      if (!response.ok) {
        throw new Error(`Failed to fetch WASM: HTTP ${response.status}`);
      }
      const wasmBytes = await response.arrayBuffer();
      const { instance } = await WebAssembly.instantiate(wasmBytes, {});
      wasm = instance.exports as unknown as DreggWasm;
      wasmLoaded = true;
    }
  } catch (e: unknown) {
    const err = e as Error;
    wasm = null;
    wasmLoaded = false;
    wasmLoadError = err.message;
  }
})();

function requireWasm(operation: string): void {
  if (!wasmLoaded || !wasm) {
    throw new Error(
      `WASM cryptographic module not loaded. Cannot perform ${operation}. ` +
      (wasmLoadError ? `Load error: ${wasmLoadError}` : "Module unavailable.")
    );
  }
}

// Queue for authorize calls that arrive before WASM is ready.
interface PendingQueueEntry {
  msg: chrome.runtime.MessageSender extends never ? never : Record<string, unknown>;
  sender: chrome.runtime.MessageSender;
  resolve: (value: unknown) => void;
}

const pendingQueue: PendingQueueEntry[] = [];
let ready = false;

wasmReady.then(() => {
  ready = true;
  for (const { msg, sender, resolve } of pendingQueue) {
    resolve(handleMessage(msg, sender));
  }
  pendingQueue.length = 0;
});

// ---------------------------------------------------------------------------
// Auto-lock timer
// ---------------------------------------------------------------------------

let lockTimer: ReturnType<typeof setTimeout> | null = null;

function resetLockTimer(): void {
  if (lockTimer !== null) {
    clearTimeout(lockTimer);
  }
  lockTimer = setTimeout(async () => {
    await lockCipherclerk();
    notifySubscribers("ready", { locked: true });
  }, LOCK_TIMEOUT_MS);
}

// ---------------------------------------------------------------------------
// Rate limiter — atomic, in-memory, keyed by (tabId, origin).
// P1-5: previous implementation stored counters in chrome.storage.session
// (async get→check→set race) and keyed off attacker-controllable URL strings.
// ---------------------------------------------------------------------------

interface RateLimitEntry {
  count: number;
  windowStart: number;
}

const rateLimits = new Map<string, RateLimitEntry>();

function checkRateLimit(tabId: number | undefined, origin: string): boolean {
  // Use tabId as the primary key (process-isolated; attacker can't forge);
  // origin is appended only for sub-keying within a tab.
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

// ---------------------------------------------------------------------------
// Popup decision framework — P0-1 / P0-2.
//
// Each user-approval popup is opened with a unique random nonce passed in the
// URL hash (so it doesn't appear in `document.referrer` or `URLSearchParams`).
// The popup retrieves its display payload via `dregg:getPendingDecision`
// (which validates the caller is the popup we opened, by extension URL +
// matching nonce) and sends decision messages including the nonce. Background
// `validatePopupSender()` confirms:
//   1. sender is an extension page (not a content script / tab),
//   2. the nonce matches a registered pending decision,
//   3. the sender.url path matches the expected popup HTML for that decision.
// Forged decisions from any web page's content script are dropped on (1);
// forged decisions from another extension page are dropped on (2)/(3).
// ---------------------------------------------------------------------------

interface PendingDecision {
  /** Which popup HTML this decision belongs to. */
  popupPath: string;
  /** The chrome.windows id, if known (used to clean up on close). */
  windowId?: number;
  /** Opaque display payload the popup will fetch via getPendingDecision. */
  payload: Record<string, unknown>;
  /** When this pending decision was created. */
  createdAt: number;
}

const pendingDecisions = new Map<string, PendingDecision>();
const PENDING_DECISION_TTL_MS = 10 * 60 * 1000;

function generatePopupNonce(): string {
  const bytes = new Uint8Array(16);
  crypto.getRandomValues(bytes);
  return Array.from(bytes).map(b => b.toString(16).padStart(2, "0")).join("");
}

function registerPendingDecision(popupPath: string, payload: Record<string, unknown>): string {
  // GC stale entries.
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

function consumePendingDecision(nonce: string): PendingDecision | null {
  const entry = pendingDecisions.get(nonce);
  if (!entry) return null;
  pendingDecisions.delete(nonce);
  return entry;
}

/**
 * Validate that the inbound message came from the popup we opened with this nonce.
 * Returns true iff:
 *   - sender is an extension page (url starts with the extension prefix)
 *   - sender is NOT a content script (sender.tab is undefined for popup windows)
 *   - the message's `nonce` field matches a registered pending decision
 *   - the popup's path matches the registered popupPath for that nonce
 *
 * On success the pending decision is consumed (one-shot).
 *
 * `expectedNonce` is the nonce we issued for this specific popup invocation;
 * the message MUST match it. (Even if an attacker steals/guesses another
 * extension page's nonce, it won't match this specific decision.)
 */
function validatePopupSender(
  message: Record<string, unknown>,
  sender: chrome.runtime.MessageSender,
  expectedNonce: string,
  expectedPopupPath: string,
): boolean {
  if (sender?.tab != null) return false;
  if (!sender?.url) return false;
  if (!isExtensionPageUrl(sender.url)) return false;
  const path = sender.url.slice(extensionPrefix.length).split(/[?#]/)[0];
  if (path !== expectedPopupPath) return false;
  const nonce = message.nonce as string | undefined;
  if (!nonce || nonce !== expectedNonce) return false;
  if (!pendingDecisions.has(nonce)) return false;
  return true;
}

// ---------------------------------------------------------------------------
// Internal encryption key
// ---------------------------------------------------------------------------

async function getInternalEncryptionKey(): Promise<string> {
  const stored = await compatSession.get("_internalKey");
  let key: string | undefined = stored._internalKey as string | undefined;
  if (!key) {
    const keyBytes = new Uint8Array(32);
    crypto.getRandomValues(keyBytes);
    key = Array.from(keyBytes).map(b => b.toString(16).padStart(2, "0")).join("");
    await compatSession.set({ _internalKey: key });
  }
  return key;
}

// ---------------------------------------------------------------------------
// Encryption helpers (PBKDF2 + AES-256-GCM)
// ---------------------------------------------------------------------------

async function deriveEncryptionKey(passphrase: string, salt: Uint8Array): Promise<CryptoKey> {
  const enc = new TextEncoder();
  const keyMaterial = await crypto.subtle.importKey(
    "raw", enc.encode(passphrase), "PBKDF2", false, ["deriveKey"]
  );
  return crypto.subtle.deriveKey(
    { name: "PBKDF2", salt: salt as unknown as BufferSource, iterations: PBKDF2_ITERATIONS, hash: "SHA-256" },
    keyMaterial,
    { name: "AES-GCM", length: 256 },
    false,
    ["encrypt", "decrypt"]
  );
}

async function encryptWithPassphrase(plaintext: string, passphrase: string): Promise<EncryptedEnvelope> {
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
    ciphertext: Array.from(new Uint8Array(ciphertext)),
  };
}

async function decryptWithPassphrase(encrypted: EncryptedEnvelope, passphrase: string): Promise<string> {
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

// ---------------------------------------------------------------------------
// BIP39 Mnemonic
// ---------------------------------------------------------------------------

let _wordlistCache: string[] | null = null;

async function getWordlist(): Promise<string[] | null> {
  if (_wordlistCache) return _wordlistCache;
  try {
    const url = chrome.runtime.getURL("bip39_english.txt");
    const resp = await fetch(url);
    const text = await resp.text();
    _wordlistCache = text.trim().split("\n");
    if (_wordlistCache.length === 2048) return _wordlistCache;
  } catch (e: unknown) {
    const err = e as Error;
    console.warn("[dregg] Failed to load wordlist from bundle:", err.message);
  }
  _wordlistCache = null;
  return null;
}

async function generateMnemonic(): Promise<string> {
  if (wasm && wasm.generate_mnemonic) {
    try {
      return wasm.generate_mnemonic();
    } catch (e: unknown) {
      const err = e as Error;
      console.warn("[dregg] WASM generate_mnemonic failed, using JS fallback:", err.message);
    }
  }
  const entropy = crypto.getRandomValues(new Uint8Array(32));
  const hashBuffer = await crypto.subtle.digest("SHA-256", entropy);
  const checksum = new Uint8Array(hashBuffer)[0];
  const bits = new Array<number>(264);
  for (let i = 0; i < 32; i++) {
    for (let bit = 0; bit < 8; bit++) {
      bits[i * 8 + bit] = (entropy[i] >> (7 - bit)) & 1;
    }
  }
  for (let bit = 0; bit < 8; bit++) {
    bits[256 + bit] = (checksum >> (7 - bit)) & 1;
  }
  const indices: number[] = [];
  for (let i = 0; i < 24; i++) {
    let index = 0;
    for (let bit = 0; bit < 11; bit++) {
      if (bits[i * 11 + bit]) {
        index |= 1 << (10 - bit);
      }
    }
    indices.push(index);
  }
  const wordlist = await getWordlist();
  if (!wordlist) throw new Error("Wordlist unavailable for mnemonic generation");
  return indices.map(i => wordlist[i]).join(" ");
}

async function validateMnemonic(mnemonic: string): Promise<boolean> {
  if (wasm && wasm.validate_mnemonic) {
    try {
      return wasm.validate_mnemonic(mnemonic);
    } catch (_e) {
      // Fall through to JS validation.
    }
  }
  const words = mnemonic.trim().split(/\s+/);
  if (words.length !== 24) return false;
  const wordlist = await getWordlist();
  if (!wordlist) return false;
  const indices: number[] = [];
  for (const word of words) {
    const idx = wordlist.indexOf(word);
    if (idx === -1) return false;
    indices.push(idx);
  }
  const bits = new Array<number>(264);
  for (let i = 0; i < 24; i++) {
    for (let bit = 0; bit < 11; bit++) {
      bits[i * 11 + bit] = (indices[i] >> (10 - bit)) & 1;
    }
  }
  const entropyBytes = new Uint8Array(32);
  for (let i = 0; i < 32; i++) {
    for (let bit = 0; bit < 8; bit++) {
      if (bits[i * 8 + bit]) {
        entropyBytes[i] |= 1 << (7 - bit);
      }
    }
  }
  let checksumByte = 0;
  for (let bit = 0; bit < 8; bit++) {
    if (bits[256 + bit]) {
      checksumByte |= 1 << (7 - bit);
    }
  }
  const hashBuffer = await crypto.subtle.digest("SHA-256", entropyBytes);
  const expectedChecksum = new Uint8Array(hashBuffer)[0];
  return checksumByte === expectedChecksum;
}

async function deriveKeypairFromMnemonic(
  mnemonic: string,
  passphrase: string,
): Promise<{ publicKey: Uint8Array; secretKey: Uint8Array }> {
  requireWasm("deriveKeypairFromMnemonic");
  const w = wasm!;
  const result = w.derive_keypair_from_mnemonic(mnemonic, passphrase, "dregg/0");
  return { publicKey: result.public_key, secretKey: result.secret_key };
}

// ---------------------------------------------------------------------------
// Event bus
// ---------------------------------------------------------------------------

const subscribers = new Map<number, Set<string>>();

// --- Passive event-feed debugger support (Phase 1, §6, STARBRIDGE-FOLLOWUP-06) ---
// In-memory trace feed in the exact shape expected by <dregg-activity> + getTraceEvents.
// Populated from node WS events (receipt/root/revocation/intent/note_announcement) +
// cclerk actions. Exposed via "dregg:activity" notifications and "dregg:getActivityFeed".
// This makes the live activity stream from the new observability wiring *usable* inside
// the extension without requiring a full runtime shim in Phase 1.
let activityFeed: { schema_version: number; event_count: number; events: Array<{ kind: string; envelope: any; payload: any }> } = {
  schema_version: 1,
  event_count: 0,
  events: [],
};

function pushActivity(kind: string, payload: unknown, envelopeExtras: Record<string, unknown> = {}): void {
  const env = {
    timestamp: new Date().toISOString(),
    seq: activityFeed.event_count,
    actor: 'extension-cclerk',
    ...envelopeExtras,
  };
  activityFeed.events.push({ kind, envelope: env, payload });
  activityFeed.event_count = activityFeed.events.length;
  // Cap to last 200 for memory (live feed, not archive).
  if (activityFeed.events.length > 200) activityFeed.events.shift();
  notifySubscribers('activity', activityFeed);
}

function notifySubscribers(event: string, payload: unknown): void {
  for (const [tabId, events] of subscribers) {
    if (events.has(event)) {
      chrome.tabs.sendMessage(tabId, { type: "dregg:event", event, payload }).catch(() => {
        subscribers.delete(tabId);
      });
    }
  }
}

// ---------------------------------------------------------------------------
// Durable outbox
// ---------------------------------------------------------------------------

type OutboxSubmitResult<T = unknown> =
  | { submitted: true; data?: T }
  | { submitted: false; queued: true; outboxId: string; error: string }
  | { submitted: false; queued: false; error: string; status?: number };

async function readOutbox(): Promise<OutboxEntry[]> {
  const stored = await chrome.storage.local.get(OUTBOX_KEY);
  const entries = stored[OUTBOX_KEY];
  if (!Array.isArray(entries)) return [];
  return entries
    .filter((entry): entry is OutboxEntry => !!entry && typeof entry.id === "string" && typeof entry.endpoint === "string")
    .sort((a, b) => a.createdAt - b.createdAt);
}

async function writeOutbox(entries: OutboxEntry[]): Promise<void> {
  const trimmed = entries
    .sort((a, b) => a.createdAt - b.createdAt)
    .slice(-OUTBOX_MAX_ENTRIES);
  await chrome.storage.local.set({ [OUTBOX_KEY]: trimmed });
  notifySubscribers("outbox", summarizeOutbox(trimmed));
  pushActivity("outbox", summarizeOutbox(trimmed), { source: "extension" });
}

function summarizeOutbox(entries: OutboxEntry[]): Record<string, unknown> {
  return {
    pending: entries.filter(e => e.status === "pending" || e.status === "submitting").length,
    failed: entries.filter(e => e.status === "failed").length,
    submitted: entries.filter(e => e.status === "submitted").length,
    total: entries.length,
  };
}

function shouldQueueNodeFailure(resp: NodeRequestResult<unknown>): boolean {
  return !resp.ok && (!resp.status || resp.status >= 500);
}

function outboxBackoffMs(attempts: number): number {
  return Math.min(5 * 60_000, 2_000 * Math.max(1, Math.pow(2, Math.min(attempts, 7))));
}

async function enqueueOutboxEntry(input: {
  kind: OutboxEntry["kind"];
  label: string;
  endpoint: string;
  body: string;
  headers?: Record<string, string>;
  turnId?: string;
  metadata?: Record<string, unknown>;
  error: string;
}): Promise<OutboxEntry> {
  const now = Date.now();
  const entries = await readOutbox();
  const existing = input.turnId
    ? entries.find(e => e.turnId === input.turnId && e.endpoint === input.endpoint && e.status !== "submitted")
    : null;
  if (existing) {
    existing.updatedAt = now;
    existing.lastError = input.error;
    existing.status = "pending";
    existing.nextAttemptAt = now + outboxBackoffMs(existing.attempts);
    await writeOutbox(entries);
    return existing;
  }
  const entry: OutboxEntry = {
    id: `outbox_${now.toString(36)}_${crypto.getRandomValues(new Uint32Array(1))[0].toString(36)}`,
    kind: input.kind,
    label: input.label,
    endpoint: input.endpoint,
    method: "POST",
    body: input.body,
    headers: input.headers,
    nodeUrl: nodeConfig.nodeUrl,
    turnId: input.turnId,
    createdAt: now,
    updatedAt: now,
    attempts: 0,
    nextAttemptAt: now + outboxBackoffMs(0),
    status: "pending",
    lastError: input.error,
    metadata: input.metadata,
  };
  entries.push(entry);
  await writeOutbox(entries);
  return entry;
}

async function submitNodeJsonWithOutbox<T = unknown>(input: {
  kind: OutboxEntry["kind"];
  label: string;
  endpoint: string;
  body: unknown;
  headers?: Record<string, string>;
  turnId?: string;
  metadata?: Record<string, unknown>;
}): Promise<OutboxSubmitResult<T>> {
  const body = typeof input.body === "string" ? input.body : JSON.stringify(input.body);
  const resp = await nodeRequest<T>(nodeConfig, input.endpoint, {
    method: "POST",
    body,
    headers: input.headers,
  });
  if (resp.ok) return { submitted: true, data: resp.data };
  if (!shouldQueueNodeFailure(resp as NodeRequestResult<unknown>)) {
    return { submitted: false, queued: false, error: resp.error || "node rejected submission", status: resp.status };
  }
  const entry = await enqueueOutboxEntry({
    kind: input.kind,
    label: input.label,
    endpoint: input.endpoint,
    body,
    headers: input.headers,
    turnId: input.turnId,
    metadata: input.metadata,
    error: resp.error || "node unavailable",
  });
  return { submitted: false, queued: true, outboxId: entry.id, error: entry.lastError || "queued" };
}

async function flushOutbox(options: { force?: boolean } = {}): Promise<{ submitted: number; failed: number; pending: number; entries: OutboxEntry[] }> {
  const entries = await readOutbox();
  const now = Date.now();
  let submitted = 0;
  let failed = 0;
  let changed = false;
  for (const entry of entries) {
    if (entry.status === "submitted") continue;
    if (!options.force && entry.nextAttemptAt > now && entry.status !== "failed") continue;
    changed = true;
    entry.status = "submitting";
    entry.updatedAt = Date.now();
    entry.attempts += 1;
    const targetConfig = entry.nodeUrl ? { ...nodeConfig, nodeUrl: entry.nodeUrl } : nodeConfig;
    const resp = await nodeRequest(targetConfig, entry.endpoint, {
      method: entry.method,
      body: entry.body,
      headers: entry.headers,
    });
    entry.updatedAt = Date.now();
    if (resp.ok) {
      entry.status = "submitted";
      entry.lastError = undefined;
      submitted += 1;
      continue;
    }
    if (shouldQueueNodeFailure(resp as NodeRequestResult<unknown>)) {
      entry.status = "pending";
      entry.lastError = resp.error || "node unavailable";
      entry.nextAttemptAt = Date.now() + outboxBackoffMs(entry.attempts);
    } else {
      entry.status = "failed";
      entry.lastError = resp.error || "node rejected submission";
      entry.nextAttemptAt = Date.now() + outboxBackoffMs(entry.attempts);
    }
    failed += 1;
  }
  const retained = entries.filter(entry => entry.status !== "submitted");
  if (changed || retained.length !== entries.length) {
    await writeOutbox(retained);
  }
  return {
    submitted,
    failed,
    pending: retained.filter(entry => entry.status === "pending" || entry.status === "submitting").length,
    entries: retained,
  };
}

async function dropOutboxEntry(id: string): Promise<{ dropped: boolean; id: string }> {
  const entries = await readOutbox();
  const next = entries.filter(entry => entry.id !== id);
  await writeOutbox(next);
  return { dropped: next.length !== entries.length, id };
}

// ---------------------------------------------------------------------------
// Cipherclerk state
// ---------------------------------------------------------------------------

let state: InternalCipherclerkState | null = null;
let cclerkPassphrase: string | null = null;

/**
 * One-time migration: copy legacy "dregg_cipherclerk*" storage keys to the new
 * "dregg_cipherclerk*" names.  Runs at most once per installation (guarded by
 * presence of the new key).  The old keys are removed after copying so the
 * migration is idempotent.
 */
async function migrateLegacyStorageKeys(): Promise<void> {
  // If the new encrypted key already exists, nothing to migrate.
  const newCheck = await chrome.storage.local.get(ENCRYPTED_STATE_KEY);
  if (newCheck[ENCRYPTED_STATE_KEY]) return;

  // Check whether the old encrypted key exists.
  const oldEncrypted = await chrome.storage.local.get(LEGACY_ENCRYPTED_STATE_KEY);
  if (oldEncrypted[LEGACY_ENCRYPTED_STATE_KEY]) {
    await chrome.storage.local.set({ [ENCRYPTED_STATE_KEY]: oldEncrypted[LEGACY_ENCRYPTED_STATE_KEY] });
    await chrome.storage.local.remove(LEGACY_ENCRYPTED_STATE_KEY);
  }

  // Also migrate the legacy plaintext key if present (belt-and-suspenders).
  const oldPlain = await chrome.storage.local.get(LEGACY_STORAGE_KEY);
  if (oldPlain[LEGACY_STORAGE_KEY]) {
    await chrome.storage.local.set({ [STORAGE_KEY]: oldPlain[LEGACY_STORAGE_KEY] });
    await chrome.storage.local.remove(LEGACY_STORAGE_KEY);
  }
}

async function loadState(): Promise<InternalCipherclerkState> {
  if (state) return state;

  // One-time storage key migration: copy dregg_cipherclerk* → dregg_cipherclerk* on first run.
  // This preserves data for users upgrading from the old "cclerk" naming.
  await migrateLegacyStorageKeys();

  // Try loading legacy unencrypted state and migrate.
  const stored = await chrome.storage.local.get(STORAGE_KEY);
  if (stored[STORAGE_KEY]) {
    state = stored[STORAGE_KEY] as InternalCipherclerkState;
    state.needsPassphraseSetup = true;
    const internalKey = await getInternalEncryptionKey();
    cclerkPassphrase = internalKey;
    state.locked = false;
    await saveState();
    state.locked = true;
    state.secretKey = null;
    cclerkPassphrase = null;
    return state;
  }

  // Try loading encrypted state.
  const encrypted = await chrome.storage.local.get(ENCRYPTED_STATE_KEY);
  if (encrypted[ENCRYPTED_STATE_KEY]) {
    const envelope = encrypted[ENCRYPTED_STATE_KEY] as EncryptedEnvelope & {
      publicKey?: number[];
      hasMnemonic?: boolean;
      needsPassphraseSetup?: boolean;
    };
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
      stealthNotes: [],
    };
    return state;
  }

  // First run: generate mnemonic and initialize cipherclerk.
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
    stealthNotes: [],
  };

  const internalKey = await getInternalEncryptionKey();
  cclerkPassphrase = internalKey;
  state.locked = false;
  await saveState();

  const encryptedMnemonic = await encryptWithPassphrase(mnemonic, internalKey);
  await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });

  state.locked = true;
  state.secretKey = null;
  cclerkPassphrase = null;
  state.needsPassphraseSetup = true;

  return state;
}

async function saveState(): Promise<void> {
  if (!state) return;
  if (!cclerkPassphrase && !state.locked) {
    cclerkPassphrase = await getInternalEncryptionKey();
  }
  if (cclerkPassphrase && !state.locked) {
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
    const envelope = await encryptWithPassphrase(plaintext, cclerkPassphrase);
    (envelope as EncryptedEnvelope & { publicKey?: number[]; hasMnemonic?: boolean; needsPassphraseSetup?: boolean }).publicKey = state.publicKey;
    (envelope as EncryptedEnvelope & { hasMnemonic?: boolean }).hasMnemonic = state.hasMnemonic;
    (envelope as EncryptedEnvelope & { needsPassphraseSetup?: boolean }).needsPassphraseSetup = state.needsPassphraseSetup || false;
    await chrome.storage.local.set({ [ENCRYPTED_STATE_KEY]: envelope });
    await chrome.storage.local.remove(STORAGE_KEY);
  }
}

async function lockCipherclerk(): Promise<void> {
  if (!state) return;
  if (cclerkPassphrase) {
    state.locked = false;
    await saveState();
  }
  state.locked = true;
  state.secretKey = null;
  cclerkPassphrase = null;
  if (lockTimer !== null) {
    clearTimeout(lockTimer);
    lockTimer = null;
  }
}

async function unlockCipherclerk(passphrase: string): Promise<{ success: boolean; error?: string; needsPassphraseSetup?: boolean }> {
  const encrypted = await chrome.storage.local.get(ENCRYPTED_STATE_KEY);
  if (!encrypted[ENCRYPTED_STATE_KEY]) {
    if (state) state.locked = false;
    return { success: true };
  }

  const envelope = encrypted[ENCRYPTED_STATE_KEY] as EncryptedEnvelope & { needsPassphraseSetup?: boolean };
  const attempts: string[] = [passphrase];
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
        stealthNotes: decrypted.stealthNotes || [],
      };
      cclerkPassphrase = attempt;
      resetLockTimer();
      return { success: true, needsPassphraseSetup: state.needsPassphraseSetup };
    } catch (_e) {
      // Try next attempt.
    }
  }

  return { success: false, error: "Invalid passphrase" };
}

async function setPassphrase(newPassphrase: string): Promise<void> {
  const oldPassphrase = cclerkPassphrase;
  cclerkPassphrase = newPassphrase;
  if (state) {
    state.needsPassphraseSetup = false;
  }

  const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
  if (mnemonicStored[MNEMONIC_KEY]) {
    let mnemonic: string | null = null;
    const keysToTry: string[] = oldPassphrase ? [oldPassphrase] : [];
    const internalKey = await getInternalEncryptionKey();
    keysToTry.push(internalKey);

    for (const key of keysToTry) {
      try {
        mnemonic = await decryptWithPassphrase(mnemonicStored[MNEMONIC_KEY], key);
        break;
      } catch (_e) {
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

async function getMnemonic(): Promise<string | null> {
  const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
  if (!mnemonicStored[MNEMONIC_KEY]) return null;
  if (!cclerkPassphrase) return null;

  const keysToTry: string[] = [cclerkPassphrase];
  const internalKey = await getInternalEncryptionKey();
  if (cclerkPassphrase !== internalKey) {
    keysToTry.push(internalKey);
  }

  for (const key of keysToTry) {
    try {
      return await decryptWithPassphrase(mnemonicStored[MNEMONIC_KEY], key);
    } catch (_e) {
      // Try next.
    }
  }
  return null;
}

async function recoverFromMnemonic(
  mnemonic: string,
  passphrase: string,
): Promise<{ success: boolean; publicKey?: number[]; error?: string }> {
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
    stealthNotes: [],
  };
  const encryptionKey = passphrase || await getInternalEncryptionKey();
  cclerkPassphrase = encryptionKey;
  const encryptedMnemonic = await encryptWithPassphrase(mnemonic, encryptionKey);
  await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });
  await saveState();
  resetLockTimer();
  return { success: true, publicKey: state.publicKey };
}

// ---------------------------------------------------------------------------
// Origin allowlist
// ---------------------------------------------------------------------------

async function getOriginAllowlist(): Promise<Record<string, OriginPermission>> {
  const stored = await chrome.storage.local.get(ALLOWED_ORIGINS_KEY);
  const raw = stored[ALLOWED_ORIGINS_KEY] || {};
  // P1-2: drop the legacy array form entirely; force re-prompt per method.
  // Previous migration silently upgraded any prior approval to a wildcard
  // "*" grant for every restricted method (including signTurn).
  if (Array.isArray(raw)) {
    const cleared: Record<string, OriginPermission> = {};
    await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: cleared });
    return cleared;
  }
  // Additionally, sanitize any "*" wildcard methods that might exist from old data.
  const sanitized: Record<string, OriginPermission> = {};
  let dirty = false;
  for (const [origin, entry] of Object.entries(raw as Record<string, OriginPermission>)) {
    if (Array.isArray(entry?.methods) && entry.methods.includes("*")) {
      // Drop the entry — user must re-prompt per method.
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

async function isOriginAllowedForMethod(origin: string, method: string): Promise<boolean> {
  const allowlist = await getOriginAllowlist();
  const entry = allowlist[origin];
  if (!entry) return false;
  if (entry.expires && entry.expires < Date.now()) {
    delete allowlist[origin];
    await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
    return false;
  }
  // P1-2: no wildcard semantic — exact method match only.
  return entry.methods.includes(method);
}

async function addOriginToAllowlist(origin: string, method: string): Promise<void> {
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

async function revokeOriginPermissions(origin: string): Promise<void> {
  const allowlist = await getOriginAllowlist();
  delete allowlist[origin];
  await chrome.storage.local.set({ [ALLOWED_ORIGINS_KEY]: allowlist });
}

async function getAllOriginPermissions(): Promise<OriginPermissionDisplay[]> {
  const allowlist = await getOriginAllowlist();
  const result: OriginPermissionDisplay[] = [];
  const now = Date.now();
  for (const [origin, entry] of Object.entries(allowlist)) {
    if (entry.expires && entry.expires < now) continue;
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
// Authorization logic
// ---------------------------------------------------------------------------

function evaluateDatalog(token: CapabilityToken, request: AuthorizeRequest): { allowed: boolean; trace: string[] } {
  requireWasm("evaluateDatalog");
  const w = wasm!;
  const facts = token.actions.map(a => ({
    predicate: "grant",
    terms: [a, token.resource || "*"],
  }));
  const reqJson = JSON.stringify({
    action: request.action,
    service: request.resource,
  });
  const result = w.evaluate_datalog(JSON.stringify(facts), reqJson);
  return {
    allowed: result.conclusion === "allow",
    trace: result.steps.map(s => `rule(${s.rule_id}) derived ${s.derived_predicate_hex}`),
  };
}

function generateProof(witness: Uint8Array, mode: string): Uint8Array {
  requireWasm("generateProof");
  const w = wasm!;
  const hash = witness.reduce((acc, b, i) => acc ^ (b << ((i % 4) * 8)), 0) >>> 0;
  const depth = mode === "private" ? 8 : mode === "selective" ? 4 : 2;
  const result = w.generate_demo_stark_proof(hash, depth);
  return new TextEncoder().encode(result.proof_json);
}

function resolvePrivateValue(token: CapabilityToken, key: string): number | null {
  const directMap: Record<string, unknown> = {
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
    budget: token.budget,
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

async function authorize(request: AuthorizeRequest): Promise<AuthorizeResult> {
  if (!wasmLoaded || !wasm) {
    return { allowed: false, error: "Cryptographic module unavailable. Cannot authorize securely." };
  }
  const cc = await loadState();
  if (cc.locked) {
    return { allowed: false, error: "Cipherclerk is locked" };
  }
  const matchingToken = cc.tokens.find(
    t => t.actions.includes(request.action) &&
         (t.resource === "*" || t.resource === request.resource) &&
         (!t.expiry || t.expiry > Date.now())
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
  const receiptHash = Array.from(proof.slice(0, 16))
    .map(b => b.toString(16).padStart(2, "0"))
    .join("");
  cc.receiptChain.push(receiptHash);
  cc.log.push({
    action: request.action,
    resource: request.resource,
    allowed: true,
    timestamp: Date.now(),
    mode,
    disclosedFacts: request._disclosedFacts || null,
    predicateFacts: request._predicateFacts || null,
  });
  await saveState();

  const result: AuthorizeResult = { allowed: true, proof: Array.from(proof), facts: evalResult.trace, mode };

  if (mode === "selective" && request._disclosedFacts) {
    result.facts = evalResult.trace.filter(traceEntry =>
      request._disclosedFacts!.some(key =>
        traceEntry.toLowerCase().includes(key.toLowerCase())
      )
    );
    result.disclosedFacts = request._disclosedFacts;
  }

  if (mode === "selective" && request._predicateFacts) {
    let stateRoot = 0;
    try {
      const statusResult = await nodeRequest<{ merkle_root?: string; state_root?: string }>(nodeConfig, "/status");
      if (statusResult.ok && statusResult.data) {
        const merkleRoot = statusResult.data.merkle_root || statusResult.data.state_root || "";
        if (merkleRoot) {
          stateRoot = parseInt(merkleRoot.slice(0, 8), 16) >>> 0;
        }
      }
    } catch (_e) {
      const stateRootInput = cc.receiptChain.length > 0
        ? cc.receiptChain[cc.receiptChain.length - 1]
        : "0";
      requireWasm("authorize:blake3_hash");
      const stateRootHash = wasm!.blake3_hash(stateRootInput);
      stateRoot = parseInt(stateRootHash.slice(0, 8), 16) >>> 0;
    }

    result.predicateProofs = request._predicateFacts.map((pf): PredicateProofResult => {
      const privateValue = resolvePrivateValue(matchingToken, pf.key);
      if (privateValue === null) {
        return { key: pf.key, predicateType: pf.predicateType, threshold: pf.threshold, proof: null, error: `Attribute "${pf.key}" not found in token` };
      }
      const predicateTypeMap: Record<string, string> = {
        gte: "gte", ">=": "gte",
        lte: "lte", "<=": "lte",
        gt: "gt", ">": "gt",
        lt: "lt", "<": "lt",
        neq: "neq", "!=": "neq",
      };
      const wasmPredicateType = predicateTypeMap[pf.predicateType] || "gte";
      const thresholdValue = typeof pf.threshold === "number" ? pf.threshold : parseInt(String(pf.threshold), 10) || 0;
      try {
        requireWasm("authorize:generate_predicate_proof");
        const proofResult = wasm!.generate_predicate_proof(
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
          proofSizeBytes: proofResult.proof_size_bytes,
        };
      } catch (e: unknown) {
        const err = e as Error;
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
    mode,
  });
  pushActivity('authorization', { auth_kind: mode, action: request.action, resource: request.resource }, { source: 'cclerk' });
  return result;
}

async function canAuthorize(request: AuthorizeRequest): Promise<boolean> {
  const cc = await loadState();
  if (cc.locked) return false;
  const matchingToken = cc.tokens.find(
    t => t.actions.includes(request.action) &&
         (t.resource === "*" || t.resource === request.resource) &&
         (!t.expiry || t.expiry > Date.now())
  );
  if (!matchingToken) return false;
  const evalResult = evaluateDatalog(matchingToken, request);
  return evalResult.allowed;
}

// ---------------------------------------------------------------------------
// Disclosure picker
// ---------------------------------------------------------------------------

function extractTokenFacts(token: CapabilityToken, request: AuthorizeRequest): DisclosableFact[] {
  const facts: DisclosableFact[] = [];
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
    facts.push({ key: "organization", value: (token.org || token.organization)!, category: "identity" });
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
  if (request.action && !facts.some(f => f.key === "action" && f.value === request.action)) {
    facts.push({ key: "action", value: request.action, category: "permissions" });
  }
  if (request.resource && request.resource !== "*" && !facts.some(f => f.key === "resource" && f.value === request.resource)) {
    facts.push({ key: "resource", value: request.resource, category: "resource" });
  }
  return facts;
}

function showDisclosurePicker(origin: string, request: AuthorizeRequest, tokenFacts: DisclosableFact[]): Promise<DisclosureDecision> {
  return new Promise((resolve) => {
    const requiredFacts = tokenFacts.filter(f => f.key === "action" || f.key === "resource");
    const siteRequested = request.requestedDisclosure || [];
    // P0-2: pass only opaque nonce in URL; PII (facts including email/userId/org)
    // stays in background memory and is fetched via dregg:getPendingDecision.
    const nonce = registerPendingDecision("disclosure-picker.html", {
      origin,
      action: request.action,
      resource: request.resource,
      tokenFacts,
      requiredFacts,
      siteRequestedFacts: siteRequested,
    });
    const popupUrl = chrome.runtime.getURL("disclosure-picker.html") + "#nonce=" + nonce;

    chrome.windows.create({
      url: popupUrl,
      type: "popup",
      width: 440,
      height: 620,
      focused: true,
    }, (win) => {
      const listener = (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): void => {
        if (message.type !== "dregg:disclosureDecision") return;
        // P0-1: validate the sender is the popup we opened.
        if (!validatePopupSender(message, sender, nonce, "disclosure-picker.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        resolve(message as unknown as DisclosureDecision);
      };
      chrome.runtime.onMessage.addListener(listener);
      if (win?.id) {
        chrome.windows.onRemoved.addListener(function onClose(closedId: number) {
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

async function authorizeWithDisclosure(request: AuthorizeRequest, origin: string): Promise<AuthorizeResult> {
  const cc = await loadState();
  if (cc.locked) {
    return { allowed: false, error: "Cipherclerk is locked" };
  }
  const matchingToken = cc.tokens.find(
    t => t.actions.includes(request.action) &&
         (t.resource === "*" || t.resource === request.resource) &&
         (!t.expiry || t.expiry > Date.now())
  );
  if (!matchingToken) {
    return { allowed: false, error: "No capability token grants this action" };
  }

  const prefs = await getDisclosurePrefs();
  const savedPref = prefs[origin];
  let disclosureLevel: string;
  let disclosedFacts: string[] = [];
  let predicateFacts: PredicateFact[] = [];

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
              predicateType: (factDecision.predicateType || "gte") as PredicateFact["predicateType"],
              threshold: factDecision.threshold || 0,
            });
          }
        }
      }
    }

    if (decision.remember && origin) {
      await saveDisclosurePref(origin, disclosureLevel);
    }
  }

  const modeMap: Record<string, string> = { full: "trusted", selective: "selective", private: "private" };
  const mode = modeMap[disclosureLevel] || "trusted";

  return authorize({
    ...request,
    mode: mode as AuthorizeRequest["mode"],
    _disclosedFacts: disclosedFacts.length > 0 ? disclosedFacts : null,
    _predicateFacts: predicateFacts.length > 0 ? predicateFacts : null,
  });
}

// ---------------------------------------------------------------------------
// Disclosure preferences
// ---------------------------------------------------------------------------

interface DisclosurePref {
  level: string;
  savedAt: number;
}

async function getDisclosurePrefs(): Promise<Record<string, DisclosurePref>> {
  const stored = await chrome.storage.local.get(DISCLOSURE_PREFS_KEY);
  return (stored[DISCLOSURE_PREFS_KEY] || {}) as Record<string, DisclosurePref>;
}

async function saveDisclosurePref(origin: string, level: string): Promise<void> {
  const prefs = await getDisclosurePrefs();
  prefs[origin] = { level, savedAt: Date.now() };
  await chrome.storage.local.set({ [DISCLOSURE_PREFS_KEY]: prefs });
}

// ---------------------------------------------------------------------------
// Token provisioning
// ---------------------------------------------------------------------------

async function provisionToken(tokenData: Record<string, unknown>, _senderTabId?: number): Promise<{ accepted: boolean; tokenId?: string }> {
  return new Promise((resolve) => {
    // P0-2: keep token payload (which may include email/userId/org) in background memory.
    const nonce = registerPendingDecision("provision.html", { tokenData });
    const popupUrl = chrome.runtime.getURL("provision.html") + "#nonce=" + nonce;

    chrome.windows.create({
      url: popupUrl,
      type: "popup",
      width: 400,
      height: 480,
      focused: true,
    }, (win) => {
      const listener = async (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): Promise<void> => {
        if (message.type !== "dregg:provisionDecision") return;
        // P0-1: validate the sender is the provision popup we opened.
        if (!validatePopupSender(message, sender, nonce, "provision.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        if (message.accepted) {
          const cc = await loadState();
          const token: CapabilityToken = {
            id: `tok_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`,
            actions: (tokenData.actions as string[]) || [],
            resource: (tokenData.resource as string) || "*",
            expiry: (tokenData.expiry as number) || null,
            issuer: (tokenData.issuer as string) || null,
            provisioned: Date.now(),
          };
          cc.tokens.push(token);
          await saveState();
          resolve({ accepted: true, tokenId: token.id });
        } else {
          resolve({ accepted: false });
        }
      };
      chrome.runtime.onMessage.addListener(listener);
      if (win?.id) {
        chrome.windows.onRemoved.addListener(function onClose(closedId: number) {
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

// ---------------------------------------------------------------------------
// Intent engine
// ---------------------------------------------------------------------------

const intentPool = new Map<string, { intent: Intent; receivedAt: number }>();

function showIntentConfirmation(action: string, matchSpec: MatchSpec | unknown, options: unknown, origin?: string): Promise<boolean> {
  return new Promise((resolve) => {
    // P0-2 + P2-5: payload (including origin) fetched via getPendingDecision.
    const nonce = registerPendingDecision("confirm-intent.html", {
      action,
      matchSpec,
      options: options || {},
      origin: origin || "unknown",
    });
    const popupUrl = chrome.runtime.getURL("confirm-intent.html") + "#nonce=" + nonce;

    chrome.windows.create({
      url: popupUrl,
      type: "popup",
      width: 400,
      height: 380,
      focused: true,
    }, (win) => {
      const listener = (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): void => {
        if (message.type !== "dregg:intentConfirmation") return;
        // P0-1: validate the sender is the confirm-intent popup.
        if (!validatePopupSender(message, sender, nonce, "confirm-intent.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        resolve(message.confirmed === true);
      };
      chrome.runtime.onMessage.addListener(listener);
      if (win?.id) {
        chrome.windows.onRemoved.addListener(function onClose(closedId: number) {
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

async function computeIntentId(kind: string, matchSpec: MatchSpec, expiry: number): Promise<string> {
  const intentInput = {
    kind: kind === "need" ? "Need" : kind === "offer" ? "Offer" : "Query",
    actions: (matchSpec?.actions || []).map(a => ({ action: a.action || null, resource: a.resource || null })),
    constraints: (matchSpec?.constraints || []).map((c: IntentConstraint) => {
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
    proof_of_stake: matchSpec?.proofOfStake || null,
  };

  if (wasm && wasm.compute_intent_id) {
    try {
      return wasm.compute_intent_id(JSON.stringify(intentInput));
    } catch (_e) {
      // Fallback below.
    }
  }

  const canonical = JSON.stringify({
    kind: intentInput.kind,
    actions: intentInput.actions,
    constraints: intentInput.constraints,
    min_budget: intentInput.min_budget,
    resource_pattern: intentInput.resource_pattern,
    expiry: intentInput.expiry,
  });
  const encoded = new TextEncoder().encode(canonical);
  const hashBuffer = await crypto.subtle.digest("SHA-256", encoded);
  const hashArray = Array.from(new Uint8Array(hashBuffer));
  return "js:" + hashArray.map(b => b.toString(16).padStart(2, "0")).join("");
}

async function postIntent(matchSpec: MatchSpec, options?: { expiry?: number }, origin?: string): Promise<{ intentId?: string; expiry?: number; error?: string }> {
  const confirmed = await showIntentConfirmation("postIntent", matchSpec, options, origin);
  if (!confirmed) {
    return { error: "User denied intent broadcast" };
  }
  const expiry = options?.expiry || (Date.now() + DEFAULT_INTENT_EXPIRY_MS);
  const intentId = await computeIntentId("need", matchSpec, expiry);
  const intent: Intent = {
    id: intentId,
    kind: "need",
    matcher: matchSpec,
    expiry,
    createdAt: Date.now(),
  };
  intentPool.set(intentId, { intent, receivedAt: Date.now() });
  if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
    nodeWs.send(JSON.stringify({ type: "broadcast_intent", intent }));
  }
  return { intentId, expiry };
}

function matchIntentLocally(
  intent: Intent,
  tokens: CapabilityToken[],
  now: number,
): { tokenId: string; grantedActions: string[]; resource: string } | null {
  const spec = intent.matcher;
  if (!spec) return null;

  for (const token of tokens) {
    if (token.expiry && token.expiry <= now) continue;
    if (spec.actions && spec.actions.length > 0) {
      const actionsSatisfied = spec.actions.every(pattern => {
        if (!pattern.action) return true;
        return token.actions.includes(pattern.action) || token.actions.includes("*");
      });
      if (!actionsSatisfied) continue;
    }
    if (spec.resourcePattern) {
      const tokenResource = token.resource || "*";
      if (tokenResource !== "*" && tokenResource !== spec.resourcePattern) {
        if (!tokenResource.endsWith("/*") ||
            !spec.resourcePattern.startsWith(tokenResource.slice(0, -2))) {
          continue;
        }
      }
    }
    if (spec.constraints && spec.constraints.length > 0) {
      let constraintsMet = true;
      for (const c of spec.constraints) {
        if (c.type === "appId" && token.appId !== c.value) { constraintsMet = false; break; }
        if (c.type === "service" && token.service !== c.value) { constraintsMet = false; break; }
        if (c.type === "notExpiredAt" && token.expiry && token.expiry <= (c.value as number)) { constraintsMet = false; break; }
      }
      if (!constraintsMet) continue;
    }
    const grantedActions = spec.actions
      ? spec.actions.map(p => p.action).filter(Boolean)
      : token.actions;
    return { tokenId: token.id, grantedActions, resource: spec.resourcePattern || token.resource || "*" };
  }
  return null;
}

function listIntents(filter?: { kind?: string }): Array<{ id: string; kind: string; matcher: MatchSpec; expiry: number }> {
  const now = Date.now();
  const results: Array<{ id: string; kind: string; matcher: MatchSpec; expiry: number }> = [];
  for (const [, { intent }] of intentPool) {
    if (intent.expiry <= now) continue;
    if (filter?.kind && intent.kind !== filter.kind) continue;
    results.push({ id: intent.id, kind: intent.kind, matcher: intent.matcher, expiry: intent.expiry });
  }
  return results;
}

function gcIntentPool(): void {
  const now = Date.now();
  for (const [id, { intent }] of intentPool) {
    if (intent.expiry <= now) {
      intentPool.delete(id);
    }
  }
}

setInterval(gcIntentPool, INTENT_GC_INTERVAL);

// ---------------------------------------------------------------------------
// CapTP operations
// ---------------------------------------------------------------------------

const liveRefs = new Map<string, Omit<ExtensionLiveRef, "refId">>();

async function shareCapability(cellId: string): Promise<{ uri?: string; cellId?: string; nodeId?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  const resp = await nodeRequest<{ node_id?: string; secret?: string }>(nodeConfig, "/turns/bearer-auth", {
    method: "POST",
    body: JSON.stringify({ cell_id: cellId }),
  });
  if (!resp.ok) return { error: `Failed to export sturdy ref: ${resp.error}` };
  const nodeId = resp.data?.node_id || "local";
  const secret = resp.data?.secret || "";
  const uri = `dregg://${nodeId}/${cellId}/${secret}`;
  cc.log.push({ action: "shareCapability", resource: cellId, allowed: true, timestamp: Date.now(), mode: "captp" });
  await saveState();
  return { uri, cellId, nodeId };
}

async function acceptCapability(uri: string, tabId?: number): Promise<{ refId?: string; cellId?: string; nodeId?: string; permissions?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  if (!uri.startsWith("dregg://")) return { error: "Invalid URI: must start with dregg://" };
  const parts = uri.replace("dregg://", "").split("/");
  if (parts.length < 3) return { error: "Invalid URI format. Expected: dregg://<node>/<cell>/<secret>" };
  const [nodeId, cellId, secret] = parts;
  const resp = await nodeRequest<{ permissions?: string; cap_id?: string }>(nodeConfig, "/turns/peer-exchange", {
    method: "POST",
    body: JSON.stringify({ node_id: nodeId, cell_id: cellId, secret }),
  });
  if (!resp.ok) return { error: `Failed to enliven capability: ${resp.error}` };
  const refId = `ref_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
  const liveRef: Omit<ExtensionLiveRef, "refId"> = {
    cellId,
    uri,
    nodeId,
    permissions: resp.data?.permissions || "full",
    tabId: tabId || null,
    createdAt: Date.now(),
    capId: resp.data?.cap_id || null,
  };
  liveRefs.set(refId, liveRef);
  await persistLiveRefs();
  cc.log.push({ action: "acceptCapability", resource: cellId, allowed: true, timestamp: Date.now(), mode: "captp" });
  await saveState();
  return { refId, cellId, nodeId, permissions: liveRef.permissions };
}

async function createHandoff(cellId: string, recipientPk: string): Promise<{ certificateHash?: string; cellId?: string; recipientPk?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  const resp = await nodeRequest<{ certificate_hash?: string }>(nodeConfig, "/turns/peer-exchange", {
    method: "POST",
    body: JSON.stringify({ cell_id: cellId, recipient_pk: recipientPk }),
  });
  if (!resp.ok) return { error: `Failed to create handoff: ${resp.error}` };
  return { certificateHash: resp.data?.certificate_hash || "", cellId, recipientPk };
}

function getLiveRefs(): Array<ExtensionLiveRef> {
  const result: ExtensionLiveRef[] = [];
  for (const [refId, ref] of liveRefs) {
    result.push({ refId, ...ref });
  }
  return result;
}

async function dropLiveRef(refId: string): Promise<{ dropped?: boolean; refId?: string; error?: string }> {
  if (!liveRefs.has(refId)) return { error: "Live ref not found" };
  liveRefs.delete(refId);
  await persistLiveRefs();
  return { dropped: true, refId };
}

async function persistLiveRefs(): Promise<void> {
  const summary: Array<{ refId: string; cellId: string; nodeId: string; createdAt: number }> = [];
  for (const [refId, ref] of liveRefs) {
    summary.push({ refId, cellId: ref.cellId, nodeId: ref.nodeId, createdAt: ref.createdAt });
  }
  await compatSession.set({ [LIVE_REFS_KEY]: summary });
}

function cleanupTabRefs(tabId: number): void {
  for (const [refId, ref] of liveRefs) {
    if (ref.tabId === tabId) {
      liveRefs.delete(refId);
    }
  }
  persistLiveRefs();
}

chrome.tabs.onRemoved.addListener((tabId: number) => {
  cleanupTabRefs(tabId);
});

// ---------------------------------------------------------------------------
// Directory operations
// ---------------------------------------------------------------------------

async function mountService(path: string, sturdyRef: string, kind?: string, tags?: string[]): Promise<{ path?: string; version?: number; kind?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  const resp = await nodeRequest<{ version?: number }>(nodeConfig, "/registry/mount", {
    method: "POST",
    body: JSON.stringify({ path, uri: sturdyRef, kind: kind || "service", tags: tags || [] }),
  });
  if (!resp.ok) return { error: `Failed to mount: ${resp.error}` };
  return { path, version: resp.data?.version || 1, kind: kind || "service" };
}

async function discoverServices(tags?: string[]): Promise<{ results?: unknown[]; error?: string }> {
  const queryParams = (tags || []).map(t => `tag=${encodeURIComponent(t)}`).join("&");
  const query = queryParams ? `?${queryParams}` : "";
  const resp = await nodeRequest<{ results?: unknown[] }>(nodeConfig, `/registry/discover${query}`);
  if (!resp.ok) return { error: `Discovery failed: ${resp.error}` };
  return { results: resp.data?.results || [] };
}

async function resolvePath(path: string): Promise<Record<string, unknown>> {
  const encoded = encodeURIComponent(path);
  const resp = await nodeRequest<Record<string, unknown>>(nodeConfig, `/registry/get?path=${encoded}`);
  if (!resp.ok) return { error: `Resolve failed: ${resp.error}` };
  return resp.data || {};
}

// ---------------------------------------------------------------------------
// Storage operations
// ---------------------------------------------------------------------------

async function storageWrite(dataBase64: string): Promise<{ hash?: string; size?: number; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  const binary = Uint8Array.from(atob(dataBase64), c => c.charCodeAt(0));
  const resp = await nodeRequest<{ hash?: string; size?: number }>(nodeConfig, "/files/write", {
    method: "POST",
    headers: { "Content-Type": "application/octet-stream" },
    body: binary,
  });
  if (!resp.ok) return { error: `Storage write failed: ${resp.error}` };
  return { hash: resp.data?.hash || "", size: resp.data?.size || binary.length };
}

async function storageRead(hash: string): Promise<{ hash?: string; data?: string; size?: number; error?: string }> {
  const result = await nodeRequestRaw(nodeConfig, `/files/read/${hash}`);
  if (!result.ok) return { error: result.error };
  const bytes = new Uint8Array(result.data);
  const base64 = btoa(String.fromCharCode(...bytes));
  return { hash, data: base64, size: bytes.length };
}

async function storageQuota(): Promise<StorageQuotaResult> {
  const resp = await nodeRequest<{
    bytes_stored?: number;
    bytes_limit?: number;
    computrons_used?: number;
    computrons_remaining?: number;
    object_count?: number;
  }>(nodeConfig, "/storage/quota");
  if (!resp.ok) return { bytesStored: 0, bytesLimit: 0, computronsUsed: 0, computronsRemaining: 0, objectCount: 0, error: `Quota check failed: ${resp.error}` };
  return {
    bytesStored: resp.data?.bytes_stored || 0,
    bytesLimit: resp.data?.bytes_limit || 0,
    computronsUsed: resp.data?.computrons_used || 0,
    computronsRemaining: resp.data?.computrons_remaining || 0,
    objectCount: resp.data?.object_count || 0,
  };
}

// ---------------------------------------------------------------------------
// Federation / governance
// ---------------------------------------------------------------------------

async function getFederationStatus(): Promise<{ mode?: string; height?: number; peerCount?: number; merkleRoot?: string; error?: string }> {
  const resp = await nodeRequest<{ federation_mode?: string; latest_height?: number; peer_count?: number; merkle_root?: string }>(nodeConfig, "/status");
  if (!resp.ok) return { error: `Federation status failed: ${resp.error}` };
  return {
    mode: resp.data?.federation_mode || "unknown",
    height: resp.data?.latest_height || 0,
    peerCount: resp.data?.peer_count || 0,
    merkleRoot: resp.data?.merkle_root || "",
  };
}

async function proposeRoutes(routes: unknown[]): Promise<{ proposalId?: string; submitted?: boolean; queued?: boolean; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  if (!cc.secretKey) return { error: "Cipherclerk secret key not available" };
  if (cc.needsPassphraseSetup) {
    return { error: "Set a cipherclerk passphrase before signing federation proposals." };
  }
  requireWasm("proposeRoutes");
  const w = wasm!;
  try {
    const built = w.cipherclerk_make_action_turn(JSON.stringify({
      sender_privkey: cc.secretKey,
      method: "propose_routes",
      memo_json: JSON.stringify({ routes }),
    }));
    const submit = await submitNodeJsonWithOutbox<{ proposal_id?: string }>({
      kind: "turn",
      label: "propose routes",
      endpoint: "/turns/submit",
      turnId: built.turn_id,
      body: {
        turn_id: built.turn_id,
        turn_bytes: Array.from(built.turn_bytes),
        sender_pubkey: cc.publicKey,
      },
      metadata: { action: "proposeRoutes", routes },
    });
    if (submit.submitted) return { proposalId: submit.data?.proposal_id || built.turn_id, submitted: true };
    if (submit.queued) return { proposalId: built.turn_id, submitted: false, queued: true, error: `Queued for retry: ${submit.error}` };
    return { error: `Proposal failed: ${submit.error}` };
  } catch (e: unknown) {
    const err = e as Error;
    return { error: err.message || "cipherclerk_make_action_turn failed" };
  }
}

async function voteOnProposal(proposalId: string, approve: boolean): Promise<{ accepted?: boolean; proposalId?: string; queued?: boolean; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  if (!cc.secretKey) return { error: "Cipherclerk secret key not available" };
  if (cc.needsPassphraseSetup) {
    return { error: "Set a cipherclerk passphrase before signing federation votes." };
  }
  requireWasm("voteOnProposal");
  const w = wasm!;
  try {
    const built = w.cipherclerk_make_action_turn(JSON.stringify({
      sender_privkey: cc.secretKey,
      method: "vote_on_proposal",
      memo_json: JSON.stringify({ proposal_id: proposalId, vote: !!approve }),
    }));
    const submit = await submitNodeJsonWithOutbox<{ accepted?: boolean }>({
      kind: "turn",
      label: "vote on proposal",
      endpoint: "/turns/submit",
      turnId: built.turn_id,
      body: {
        turn_id: built.turn_id,
        turn_bytes: Array.from(built.turn_bytes),
        sender_pubkey: cc.publicKey,
      },
      metadata: { action: "voteOnProposal", proposalId, approve },
    });
    if (submit.submitted) return { accepted: submit.data?.accepted !== false, proposalId };
    if (submit.queued) return { accepted: false, proposalId, queued: true, error: `Queued for retry: ${submit.error}` };
    return { error: `Vote failed: ${submit.error}` };
  } catch (e: unknown) {
    const err = e as Error;
    return { error: err.message || "cipherclerk_make_action_turn failed" };
  }
}

// ---------------------------------------------------------------------------
// Turn submission / balance
// ---------------------------------------------------------------------------

async function signTurn(turnSpec: TurnSpec): Promise<SignTurnResult> {
  requireWasm("signTurn");
  const w = wasm!;
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked", submitted: false };
  // P1-1: refuse to sign turns until the user has set a real passphrase.
  // While `needsPassphraseSetup === true` the cipherclerk is encrypted under
  // an internal ephemeral key that's not a user secret.
  if (cc.needsPassphraseSetup) {
    return { error: "Set a cipherclerk passphrase before signing turns.", submitted: false };
  }
  if (!cc.secretKey) return { error: "Cipherclerk secret key not available", submitted: false };

  // Hard-error: JSON fallback removed per §4.3 Task #28 item 2 (post-soundness v3 required).
  // Legacy signTurn(JSON) path produced non-canonical turns rejected by executor.
  // starbridge-apps must use signTurnV3(turnBytes: Uint8Array) with bytes from
  // their postcard turn-builders (or the wasm build_turn when bound to V3 surface).
  if (!w.build_turn) {
    throw new Error("build_turn export required (v3 message format)");
  }
  throw new Error("signTurn JSON fallback removed; v3 required. Use dregg.signTurnV3(turnBytes) for postcard-encoded turns from starbridge-apps turn-builders.");
}

async function queryBalance(): Promise<{ balance?: number; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  const pubkeyHex = Array.from(cc.publicKey).map(b => b.toString(16).padStart(2, "0")).join("");
  const resp = await nodeRequest<{ balance?: number }>(nodeConfig, `/accounts/${pubkeyHex}/balance`);
  if (!resp.ok) return { error: `Failed to query balance: ${resp.error}` };
  return { balance: resp.data?.balance ?? 0 };
}

/**
 * Sign and submit a pre-built postcard-encoded Turn (v3 wire format).
 * starbridge-apps turn-builders produce raw bytes; this is the canonical
 * surface for that path.
 *
 * Wired to the wasm `sign_turn_v3` export, which decodes the postcard Turn,
 * replaces every `Authorization::Unchecked` action with a real Ed25519
 * signature via the canonical `AgentCipherclerk::sign_action` path (the same
 * path `DreggRuntime::execute_turn_for_agent` uses), and re-encodes. The
 * federation_id is all-zeros for the devnet/sim genesis the extension submits
 * against. The signed bytes are then submitted via the node /turns/submit
 * outbox path, mirroring the other turn builders.
 */
async function signTurnV3(turnBytes: Uint8Array): Promise<SignTurnResult> {
  requireWasm("signTurnV3");
  const w = wasm!;
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked", submitted: false };
  if (cc.needsPassphraseSetup) {
    return { error: "Set a cipherclerk passphrase before signing turns.", submitted: false };
  }
  if (!cc.secretKey) return { error: "Cipherclerk secret key not available", submitted: false };

  let signed: { turn_id: string; turn_bytes: Uint8Array; signer_pubkey: string };
  try {
    // federation_id = all-zeros (devnet/sim genesis). 32 bytes.
    const federationId = new Uint8Array(32);
    signed = w.sign_turn_v3(turnBytes, new Uint8Array(cc.secretKey), federationId);
  } catch (e: unknown) {
    const err = e as Error;
    return { error: err.message || "sign_turn_v3 failed", submitted: false };
  }

  const submit = await submitNodeJsonWithOutbox<{ turn_id?: string }>({
    kind: "turn",
    label: "sign turn (v3)",
    endpoint: "/turns/submit",
    turnId: signed.turn_id,
    body: {
      turn_id: signed.turn_id,
      turn_bytes: Array.from(signed.turn_bytes),
      sender_pubkey: cc.publicKey,
    },
    metadata: { action: "signTurnV3" },
  });
  if (submit.submitted) return { turnId: submit.data?.turn_id || signed.turn_id, submitted: true };
  if (submit.queued) return { turnId: signed.turn_id, submitted: false, queued: true, error: `Queued for retry: ${submit.error}` };
  return { error: `Turn submission failed: ${submit.error}`, submitted: false };
}

/**
 * Register a known federation in local chrome.storage.local.
 * Keyed by federation_id under KNOWN_FEDERATIONS_KEY.
 */
async function registerFederation(federationId: string, name: string, committeePubkeys: string[]): Promise<{ success: boolean }> {
  const stored = await chrome.storage.local.get(KNOWN_FEDERATIONS_KEY);
  const registry: Record<string, KnownFederation> = stored[KNOWN_FEDERATIONS_KEY] || {};
  registry[federationId] = { federationId, name, committeePubkeys, registeredAt: Date.now() };
  await chrome.storage.local.set({ [KNOWN_FEDERATIONS_KEY]: registry });
  return { success: true };
}

/**
 * List all known federations from the local registry.
 */
async function listKnownFederations(): Promise<KnownFederation[]> {
  const stored = await chrome.storage.local.get(KNOWN_FEDERATIONS_KEY);
  const registry: Record<string, KnownFederation> = stored[KNOWN_FEDERATIONS_KEY] || {};
  return Object.values(registry);
}

/**
 * Build a serialized Authorization::CapTpDelivered envelope for attaching
 * to a turn during a CapTP handoff.
 *
 * Wired to the wasm `create_captp_delivered_auth` export, which decodes the
 * handoff certificate (compact `dregg-handoff:<base58>` or bare base58),
 * assembles the canonical `Authorization::CapTpDelivered { handoff_cert,
 * introducer_pk, sender_pk, sender_signature }`, and postcard-encodes it. The
 * recipient signature is produced upstream by the recipient cipherclerk over
 * `captp_delivered_signing_message`; the executor's `verify_captp_delivered`
 * does the real verification at apply time.
 */
function createCapTpDeliveredAuth(
  handoffCertB58: string,
  introducerPk: string,
  senderPk: string,
  senderSig: string,
): { authBytes: number[]; recipientPk?: string; introducerFederation?: string; error?: string } {
  requireWasm("createCapTpDeliveredAuth");
  const w = wasm!;
  try {
    const result = w.create_captp_delivered_auth(handoffCertB58, introducerPk, senderPk, senderSig);
    return {
      authBytes: Array.from(result.auth_bytes as Uint8Array),
      recipientPk: result.recipient_pk as string,
      introducerFederation: result.introducer_federation as string,
    };
  } catch (e: unknown) {
    const err = e as Error;
    return { authBytes: [], error: err.message || "create_captp_delivered_auth failed" };
  }
}

// ---------------------------------------------------------------------------
// Cipherclerk state queries
// ---------------------------------------------------------------------------

async function getCipherclerkState(): Promise<CipherclerkState> {
  const cc = await loadState();
  const internalKey = await getInternalEncryptionKey();
  return {
    locked: cc.locked,
    tokenCount: cc.tokens.length,
    chainLength: cc.receiptChain.length,
    hasMnemonic: cc.hasMnemonic || false,
    mnemonicShown: cc.mnemonicShown || false,
    hasPassphrase: cclerkPassphrase !== null && cclerkPassphrase !== internalKey,
    needsPassphraseSetup: cc.needsPassphraseSetup || false,
    hasStealthKeys: cc.stealthMeta !== null && cc.stealthMeta !== undefined,
    stealthNotesCount: (cc.stealthNotes || []).length,
  };
}

async function getCapabilities(): Promise<string[]> {
  const cc = await loadState();
  if (cc.locked) return [];
  const actions = new Set<string>();
  for (const token of cc.tokens) {
    for (const action of token.actions) {
      actions.add(action);
    }
  }
  return Array.from(actions);
}

async function revokeToken(tokenId: string): Promise<{ revoked: boolean; error?: string }> {
  const cc = await loadState();
  const idx = cc.tokens.findIndex(t => t.id === tokenId);
  if (idx === -1) return { revoked: false, error: "Token not found" };
  cc.tokens.splice(idx, 1);
  await saveState();
  notifySubscribers("revoked", { tokenId });
  return { revoked: true };
}

// ---------------------------------------------------------------------------
// Sender validation helpers
// ---------------------------------------------------------------------------

function isExtensionPopup(sender: chrome.runtime.MessageSender): boolean {
  if (!sender?.url) return false;
  return isExtensionPageUrl(sender.url);
}

function isContentScript(sender: chrome.runtime.MessageSender): boolean {
  return sender?.tab != null;
}

// ---------------------------------------------------------------------------
// Origin permission request handler
// ---------------------------------------------------------------------------

function handleOriginPermissionRequest(origin: string, method: string): Promise<{ granted: boolean }> {
  return new Promise((resolve) => {
    const nonce = registerPendingDecision("origin-permission.html", { origin, method });
    const popupUrl = chrome.runtime.getURL("origin-permission.html") + "#nonce=" + nonce;

    chrome.windows.create({
      url: popupUrl,
      type: "popup",
      width: 420,
      height: 320,
      focused: true,
    }, (win) => {
      const listener = async (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): Promise<void> => {
        if (message.type !== "dregg:originPermissionDecision") return;
        // P0-1: validate the sender is the origin-permission popup.
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
        chrome.windows.onRemoved.addListener(function onClose(closedId: number) {
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

// ---------------------------------------------------------------------------
// Message router
// ---------------------------------------------------------------------------

const PAGE_ALLOWED_METHODS = new Set<MessageType>([
  "dregg:authorize", "dregg:isConnected", "dregg:canAuthorize", "dregg:subscribe",
  "dregg:getActivityFeed",  // Phase 1: live activity feed for <dregg-activity> / debugger
  "dregg:provision", "dregg:postIntent", "dregg:getStealthAddress",
  "dregg:postEncryptedIntent", "dregg:privateTransfer",
  "dregg:createBearerCap", "dregg:verifyBearerCap",
  "dregg:createFromFactory", "dregg:verifyProvenance",
  "dregg:makeCellSovereign", "dregg:peerExchange", "dregg:composeProofs",
  "dregg:signTurn", "dregg:signTurnV3", "dregg:queryBalance",
  "dregg:shareCapability", "dregg:acceptCapability", "dregg:createHandoff",
  "dregg:mountService", "dregg:discoverServices", "dregg:resolvePath",
  "dregg:storageWrite", "dregg:storageRead", "dregg:storageQuota",
  "dregg:listOutbox", "dregg:flushOutbox", "dregg:dropOutboxEntry",
  "dregg:federationStatus", "dregg:proposeRoutes", "dregg:voteOnProposal",
  "dregg:registerFederation", "dregg:listKnownFederations",
  "dregg:createCapTpDeliveredAuth", "dregg:getReceiptWitnesses",
]);

const POPUP_ONLY_METHODS = new Set<MessageType>([
  "dregg:unlock", "dregg:lock", "dregg:getCapabilities", "dregg:listIntents",
  "dregg:offerCapability", "dregg:fulfillIntent", "dregg:getFulfillableIntents",
  "dregg:revoke", "dregg:getState", "dregg:getFederation", "dregg:refreshDiscovery",
  "dregg:setPassphrase", "dregg:getMnemonic", "dregg:recover",
  "dregg:getDisclosurePrefs", "dregg:clearDisclosurePref",
  "dregg:getOriginPermissions", "dregg:revokeOriginPermission",
  "dregg:getPrivacyState", "dregg:setCommittedTransferMode", "dregg:getStealthNotes",
  "dregg:getNodeConfig", "dregg:setNodeConfig",
  "dregg:getLiveRefs", "dregg:dropLiveRef",
]);

async function handleMessage(message: Record<string, unknown>, sender: chrome.runtime.MessageSender): Promise<Record<string, unknown>> {
  // Security: strip _skipDisclosure from page-originated requests.
  if (sender?.tab && message?.request) {
    delete (message.request as Record<string, unknown>)._skipDisclosure;
  }

  const msgType = message.type as MessageType;

  switch (msgType) {
    case "dregg:authorize": {
      if (isContentScript(sender) && !(message.request as AuthorizeRequest)?._skipDisclosure) {
        const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || "unknown";
        // P1-5: rate-limit keyed off (tabId, origin) using in-memory map.
        if (!checkRateLimit(sender?.tab?.id, origin)) {
          return { id: message.id, result: { allowed: false, error: "Rate limited. Too many authorize requests. Try again later." } };
        }
        const result = await authorizeWithDisclosure(message.request as AuthorizeRequest, origin);
        resetLockTimer();
        return { id: message.id, result };
      }
      resetLockTimer();
      return { id: message.id, result: await authorize(message.request as AuthorizeRequest) };
    }

    case "dregg:isConnected":
      return { id: message.id, result: true };

    case "dregg:canAuthorize":
      return { id: message.id, result: await canAuthorize(message.request as AuthorizeRequest) };

    case "dregg:getCapabilities":
      return { id: message.id, result: await getCapabilities() };

    case "dregg:getState":
      return { id: message.id, result: await getCipherclerkState() };

    case "dregg:lock": {
      await lockCipherclerk();
      return { id: message.id, result: true };
    }

    case "dregg:unlock": {
      if (!isExtensionPopup(sender)) {
        return { id: message.id, error: "Unlock is only available from the extension popup." };
      }
      const result = await unlockCipherclerk((message.passphrase as string) || "");
      if (result.success) {
        notifySubscribers("ready", { locked: false });
      }
      return { id: message.id, result };
    }

    case "dregg:setPassphrase": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      await setPassphrase(message.passphrase as string);
      return { id: message.id, result: true };
    }

    case "dregg:getMnemonic": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      // P1-1: don't reveal the mnemonic while the cipherclerk is encrypted under the
      // ephemeral internal key.
      if (cc.needsPassphraseSetup) {
        return { id: message.id, error: "Set a cipherclerk passphrase before viewing the recovery phrase." };
      }
      const mnemonic = await getMnemonic();
      if (state) state.mnemonicShown = true;
      await saveState();
      return { id: message.id, result: mnemonic };
    }

    case "dregg:recover": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      const result = await recoverFromMnemonic(message.mnemonic as string, (message.passphrase as string) || "");
      return { id: message.id, result };
    }

    case "dregg:provision": {
      const result = await provisionToken(message.tokenData as Record<string, unknown>, sender?.tab?.id);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:revoke": {
      const result = await revokeToken(message.tokenId as string);
      return { id: message.id, result };
    }

    case "dregg:subscribe": {
      const tabId = sender?.tab?.id;
      if (tabId != null) {
        if (!subscribers.has(tabId)) subscribers.set(tabId, new Set());
        subscribers.get(tabId)!.add(message.event as string);
      }
      return { id: message.id, result: true };
    }

    // Phase 1 passive debugger: expose the synthesized activity feed (TraceEvent shape)
    // consumable by <dregg-activity> (or direct .on('activity')) and for RemoteRuntime bridge.
    case "dregg:getActivityFeed": {
      return { id: message.id, result: activityFeed };
    }

    case "dregg:getReceiptWitnesses": {
      const receiptHash = String(message.receiptHash || message.hash || "");
      if (!/^[0-9a-fA-F]{64}$/.test(receiptHash)) {
        return { id: message.id, error: "receiptHash must be a 32-byte hex string" };
      }
      const resp = await nodeRequest<Partial<ReceiptWitnessArtifacts>>(nodeConfig, `/api/receipts/${encodeURIComponent(receiptHash)}/witnesses`);
      if (!resp.ok) return { id: message.id, error: resp.error || "Unable to fetch receipt witnesses" };
      const payload = resp.data || {};
      const witnessArtifacts = Array.isArray(payload.witness_artifacts)
        ? payload.witness_artifacts.filter((artifact): artifact is string => typeof artifact === "string" && artifact.length > 0)
        : [];
      const legacyReceipts = Array.isArray(payload.witnessed_receipts) ? payload.witnessed_receipts : [];
      return {
        id: message.id,
        result: {
          ...payload,
          receipt_hash: payload.receipt_hash || receiptHash,
          witness_count: Number(payload.witness_count ?? witnessArtifacts.length ?? legacyReceipts.length ?? 0),
          artifact_format: witnessArtifacts.length > 0 ? (payload.artifact_format || "DWR1") : (payload.artifact_format || "legacy-json"),
          witness_artifacts: witnessArtifacts,
          witnessed_receipts: legacyReceipts,
        } satisfies ReceiptWitnessArtifacts,
      };
    }

    case "dregg:listOutbox": {
      return { id: message.id, result: await readOutbox() };
    }

    case "dregg:flushOutbox": {
      const result = await flushOutbox({ force: true });
      return { id: message.id, result };
    }

    case "dregg:dropOutboxEntry": {
      const result = await dropOutboxEntry(String(message.outboxId || message.idToDrop || message.entryId || ""));
      return { id: message.id, result };
    }

    case "dregg:provisionDecision":
    case "dregg:intentConfirmation":
    case "dregg:disclosureDecision": {
      // P0-1: decision messages may only come from extension popup pages.
      // The actual resolution is handled by the per-popup listener registered
      // in show*() functions, which also validates the nonce. This main-router
      // case just ACKs the popup; if a content script forges this message
      // type, we explicitly refuse here (defense in depth).
      if (isContentScript(sender) || !isExtensionPopup(sender)) {
        return { id: message.id, error: "Decision messages may only come from extension popups." };
      }
      return { id: message.id, result: true };
    }

    case "dregg:getPendingDecision": {
      // P0-2: popups fetch their display payload via this message rather than
      // receiving PII in the URL. Caller must be an extension page (not a tab
      // / content script), the nonce must match a registered pending decision,
      // and the caller's URL path must match the registered popup path.
      if (isContentScript(sender) || !isExtensionPopup(sender)) {
        return { id: message.id, error: "Only extension popups may fetch pending decisions." };
      }
      const nonce = message.nonce as string | undefined;
      if (!nonce) return { id: message.id, error: "Missing nonce." };
      const entry = pendingDecisions.get(nonce);
      if (!entry) return { id: message.id, error: "No such pending decision." };
      // Confirm caller is the right popup HTML.
      const prefix = extensionPrefix;
      const path = (sender.url || "").startsWith(prefix)
        ? (sender.url || "").slice(prefix.length).split(/[?#]/)[0]
        : "";
      if (path !== entry.popupPath) {
        return { id: message.id, error: "Popup path mismatch for this nonce." };
      }
      return { id: message.id, result: { payload: entry.payload } };
    }

    case "dregg:getDisclosurePrefs": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      return { id: message.id, result: await getDisclosurePrefs() };
    }

    case "dregg:clearDisclosurePref": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      const prefs = await getDisclosurePrefs();
      delete prefs[message.origin as string];
      await chrome.storage.local.set({ [DISCLOSURE_PREFS_KEY]: prefs });
      return { id: message.id, result: true };
    }

    case "dregg:getOriginPermissions": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      return { id: message.id, result: await getAllOriginPermissions() };
    }

    case "dregg:revokeOriginPermission": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      await revokeOriginPermissions(message.origin as string);
      return { id: message.id, result: true };
    }

    case "dregg:postIntent": {
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const result = await postIntent(message.matchSpec as MatchSpec, message.options as { expiry?: number } | undefined, origin);
      return { id: message.id, result };
    }

    case "dregg:offerCapability": {
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const confirmed = await showIntentConfirmation("offerCapability", message.matchSpec, message.options, origin);
      if (!confirmed) return { id: message.id, result: { error: "User denied capability offer" } };
      const expiry = (message.options as { expiry?: number })?.expiry || (Date.now() + DEFAULT_INTENT_EXPIRY_MS);
      const intentId = await computeIntentId("offer", message.matchSpec as MatchSpec, expiry);
      const intent: Intent = { id: intentId, kind: "offer", matcher: message.matchSpec as MatchSpec, expiry, createdAt: Date.now() };
      intentPool.set(intentId, { intent, receivedAt: Date.now() });
      if (nodeWs && nodeWs.readyState === WebSocket.OPEN) {
        nodeWs.send(JSON.stringify({ type: "broadcast_intent", intent }));
      }
      return { id: message.id, result: { intentId, expiry } };
    }

    case "dregg:listIntents":
      return { id: message.id, result: listIntents(message.filter as { kind?: string } | undefined) };

    case "dregg:fulfillIntent": {
      // Simplified: delegate to postIntent-like pattern; full implementation in legacy
      return { id: message.id, result: { error: "Not yet migrated to TypeScript" } };
    }

    case "dregg:getFulfillableIntents": {
      const cc = await loadState();
      if (cc.locked) return { id: message.id, result: [] };
      const now = Date.now();
      const fulfillable: unknown[] = [];
      for (const [, { intent }] of intentPool) {
        if (intent.expiry <= now || intent.kind !== "need") continue;
        const matchResult = matchIntentLocally(intent, cc.tokens, now);
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
      return { id: message.id, result: fulfillable };
    }

    case "dregg:getFederation":
      return { id: message.id, result: federationState };

    case "dregg:refreshDiscovery":
      await fetchDiscovery();
      return { id: message.id, result: federationState };

    case "dregg:requestOriginPermission": {
      const result = await handleOriginPermissionRequest(message.origin as string, message.method as string);
      return result;
    }

    case "dregg:originPermissionDecision": {
      // P0-1: same as above — only popups may send decision messages.
      if (isContentScript(sender) || !isExtensionPopup(sender)) {
        return { id: message.id, error: "Decision messages may only come from extension popups." };
      }
      return { id: message.id, result: true };
    }

    // CapTP
    case "dregg:shareCapability": {
      const result = await shareCapability(message.cellId as string);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:acceptCapability": {
      const result = await acceptCapability(message.uri as string, sender?.tab?.id);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:createHandoff": {
      const result = await createHandoff(message.cellId as string, message.recipientPk as string);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:getLiveRefs":
      return { id: message.id, result: getLiveRefs() };

    case "dregg:dropLiveRef": {
      const result = await dropLiveRef(message.refId as string);
      return { id: message.id, result };
    }

    // Directory
    case "dregg:mountService": {
      const result = await mountService(message.path as string, message.sturdyRef as string, message.kind as string | undefined, message.tags as string[] | undefined);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:discoverServices":
      return { id: message.id, result: await discoverServices(message.tags as string[] | undefined) };

    case "dregg:resolvePath":
      return { id: message.id, result: await resolvePath(message.path as string) };

    // Storage
    case "dregg:storageWrite": {
      const result = await storageWrite(message.data as string);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:storageRead":
      return { id: message.id, result: await storageRead(message.hash as string) };

    case "dregg:storageQuota":
      return { id: message.id, result: await storageQuota() };

    // Federation
    case "dregg:federationStatus":
      return { id: message.id, result: await getFederationStatus() };

    case "dregg:proposeRoutes": {
      const result = await proposeRoutes(message.routes as unknown[]);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:voteOnProposal": {
      const result = await voteOnProposal(message.proposalId as string, message.approve as boolean);
      resetLockTimer();
      return { id: message.id, result };
    }

    // Turn / balance
    case "dregg:signTurn": {
      const result = await signTurn(message.turnSpec as TurnSpec);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:queryBalance":
      return { id: message.id, result: await queryBalance() };

    // Node config
    case "dregg:getNodeConfig":
      return { id: message.id, result: { ...nodeConfig, devnetKey: nodeConfig.devnetKey ? "***" : "" } };

    case "dregg:setNodeConfig": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from the extension popup or settings page." };
      await saveNodeConfig(message.config as Partial<NodeConfig>);
      return { id: message.id, result: { success: true, nodeUrl: nodeConfig.nodeUrl } };
    }

    // Bearer caps
    case "dregg:createBearerCap": {
      requireWasm("createBearerCap");
      const w = wasm!;
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      const delegatorKeyHex = Array.from(cc.publicKey).map(b => b.toString(16).padStart(2, "0")).join("");
      const result = w.create_bearer_cap(delegatorKeyHex, message.targetCellHex as string, message.action as string, (message.expiry as number) || 0);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:verifyBearerCap": {
      requireWasm("verifyBearerCap");
      const w = wasm!;
      const currentTime = Math.floor(Date.now() / 1000);
      const result = w.verify_bearer_cap(
        message.bearerTokenHex as string, message.delegatorKeyHex as string,
        message.targetCellHex as string, message.action as string,
        (message.expiry as number) || 0, currentTime
      );
      return { id: message.id, result };
    }

    // Factory: canonical constructor-transparency mint.
    //
    // Routes through `cipherclerk_create_from_factory` (AgentCipherclerk::create_from_factory)
    // — the canonical SDK path — to build a real signed
    // `Effect::CreateCellFromFactory` turn, submit it via /turns/submit,
    // and return the new cell's `(child_vk, param_hash, factory_vk)`
    // identity tuple to the caller. This replaces the prior shape that
    // only hash-derived (child_vk, param_hash) client-side and never
    // actually minted a cell.
    case "dregg:createFromFactory": {
      requireWasm("createFromFactory");
      const w = wasm!;
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      if (cc.needsPassphraseSetup) {
        return { id: message.id, error: "Set a cipherclerk passphrase before minting cells from a factory." };
      }
      if (!cc.secretKey) return { id: message.id, error: "Cipherclerk secret key not available" };

      const factoryVkHex = message.factoryVkHex as string;
      const ownerPubkeyHex = message.ownerPubkeyHex as string;
      // Token-id is domain-scoped; default to BLAKE3-derive of the canonical
      // signing domain so the resulting cell shares the token namespace with
      // other extension-minted cells.
      const tokenIdHex = (message.tokenIdHex as string | undefined)
        ?? w.blake3_hash("dregg-cipherclerk-default-token-domain");
      const mode = (message.mode as string | undefined) ?? "Hosted";
      const initialFields = (message.initialFields as Array<[number, number]> | undefined) ?? [];

      const specJson = JSON.stringify({
        sender_privkey: cc.secretKey,
        factory_vk_hex: factoryVkHex,
        owner_pubkey_hex: ownerPubkeyHex,
        token_id_hex: tokenIdHex,
        mode,
        program_vk_hex: message.programVkHex || null,
        initial_fields: initialFields,
        federation_id_hex: message.federationIdHex || null,
      });

      let turnData: {
        turn_id: string;
        turn_bytes: Uint8Array;
        agent_cell_id: string;
        child_vk: string;
        param_hash: string;
        factory_vk: string;
      };
      try {
        turnData = w.cipherclerk_create_from_factory(specJson);
      } catch (e: unknown) {
        const err = e as Error;
        return { id: message.id, error: `Failed to build factory turn: ${err.message || String(err)}` };
      }

      // Submit the signed factory turn to the node. The node's executor
      // validates the factory descriptor + params and mints the cell,
      // tracking provenance for downstream verifyProvenance calls.
      const submit = await submitNodeJsonWithOutbox<Record<string, unknown>>({
        kind: "turn",
        label: "create cell from factory",
        endpoint: "/turns/submit",
        turnId: turnData.turn_id,
        body: {
          turn_id: turnData.turn_id,
          turn_bytes: Array.from(turnData.turn_bytes),
          sender_pubkey: cc.publicKey,
        },
        metadata: {
          action: "createFromFactory",
          childVk: turnData.child_vk,
          paramHash: turnData.param_hash,
          factoryVk: turnData.factory_vk,
          agentCellId: turnData.agent_cell_id,
        },
      });

      if (!submit.submitted) {
        return {
          id: message.id,
          // Even when submission fails the caller can still display the
          // derived (child_vk, param_hash, factory_vk) — they are
          // deterministic functions of the inputs.
          result: {
            childVk: turnData.child_vk,
            paramHash: turnData.param_hash,
            factoryVk: turnData.factory_vk,
            submitted: false,
            queued: submit.queued,
            outboxId: submit.queued ? submit.outboxId : undefined,
            error: submit.queued ? `Queued for retry: ${submit.error}` : `Factory turn rejected by node: ${submit.error}`,
            turnId: turnData.turn_id,
          },
        };
      }

      cc.log.push({
        action: "createFromFactory",
        resource: turnData.child_vk,
        allowed: true,
        timestamp: Date.now(),
        mode: "factory",
        turnId: turnData.turn_id,
      });
      await saveState();

      return {
        id: message.id,
        result: {
          childVk: turnData.child_vk,
          paramHash: turnData.param_hash,
          factoryVk: turnData.factory_vk,
          submitted: true,
          turnId: turnData.turn_id,
          agentCellId: turnData.agent_cell_id,
          nodeResult: submit.data as Record<string, unknown> | undefined,
        },
      };
    }

    case "dregg:verifyProvenance": {
      requireWasm("verifyProvenance");
      const w = wasm!;
      const result = w.verify_provenance(message.cellVkHex as string, JSON.stringify(message.knownFactoryVks || []));
      return { id: message.id, result };
    }

    // Sovereign cells
    case "dregg:makeCellSovereign": {
      requireWasm("makeCellSovereign");
      const w = wasm!;
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      const result = w.make_cell_sovereign(message.cellIdHex as string, 0);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:peerExchange": {
      requireWasm("peerExchange");
      const w = wasm!;
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      if (!cc.secretKey) return { id: message.id, error: "Cipherclerk secret key not available" };
      // Route through the cipherclerk's canonical `PeerExchange` session so
      // the emitted `PeerStateTransition` is signed by the cipherclerk's
      // Ed25519 key. The previous binding (`peer_exchange_with_proof`)
      // used canonical types but bypassed signing entirely.
      try {
        const result = w.cipherclerk_peer_exchange(JSON.stringify({
          sender_privkey: cc.secretKey,
          receiver_cell_hex: message.receiverCellHex as string,
          amount: message.amount as number,
          timestamp: Math.floor(Date.now() / 1000),
        }));
        resetLockTimer();
        return {
          id: message.id,
          result: {
            exchangeId: result.exchange_id,
            proofCommitment: result.proof_commitment,
            senderCell: result.sender_cell,
            receiverCell: result.receiver_cell,
            transitionBytes: Array.from(result.transition_bytes),
          },
        };
      } catch (e: unknown) {
        const err = e as Error;
        return { id: message.id, error: err.message || "peer_exchange failed" };
      }
    }

    // Proof composition
    case "dregg:composeProofs": {
      requireWasm("composeProofs");
      const w = wasm!;
      const proofsInput = ((message.proofs as Array<Record<string, unknown>>) || []).map(p => ({
        proof_json: (p.proofJson || p.proof_json || "") as string,
        public_inputs: (p.publicInputs || p.public_inputs || []) as number[],
      }));
      const result = w.compose_proofs(JSON.stringify(proofsInput), (message.mode as string) || "and");
      return { id: message.id, result };
    }

    // Privacy
    case "dregg:getStealthAddress":
      return { id: message.id, result: state?.stealthMeta || null };

    case "dregg:getPrivacyState": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      const cc = await loadState();
      if (cc.locked) return { id: message.id, result: { active: false, locked: true } };
      return { id: message.id, result: { active: true, stealthMeta: cc.stealthMeta } };
    }

    case "dregg:setCommittedTransferMode": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      return { id: message.id, result: { success: true, committedTransfersActive: !!(message.enabled) } };
    }

    case "dregg:getStealthNotes": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      return { id: message.id, result: cc.stealthNotes || [] };
    }

    case "dregg:postEncryptedIntent": {
      requireWasm("postEncryptedIntent");
      const w = wasm!;
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      if (!cc.secretKey) return { id: message.id, error: "Cipherclerk secret key not available" };
      const matchSpec = (message.matchSpec as MatchSpec) || {};
      const options = (message.options as { expiry?: number; kind?: string } | undefined) || {};
      const kind = options.kind || "need";
      // The canonical Rust `MatchSpec` shape uses snake_case field names
      // (resource_pattern, min_budget). Coerce the camelCase form that the
      // extension's TS types use over to the canonical shape.
      const canonicalMatchSpec = {
        actions: (matchSpec.actions || []).map(a => ({ action: a.action || null, resource: a.resource || null })),
        constraints: (matchSpec.constraints || []).map((c: IntentConstraint) => {
          if (c.type === "appId") return { AppId: c.value };
          if (c.type === "service") return { Service: c.value };
          if (c.type === "userId") return { UserId: c.value };
          if (c.type === "notExpiredAt") return { NotExpiredAt: c.value };
          if (c.type === "feature") return { Feature: c.value };
          if (c.type === "oauthProvider") return { OAuthProvider: c.value };
          return { Custom: { predicate: String(c.type || ""), value: String(c.value ?? "") } };
        }),
        min_budget: matchSpec.minBudget ?? null,
        resource_pattern: matchSpec.resourcePattern ?? null,
        compound: null,
        predicate_requirements: [],
        strict_resource_matching: false,
      };
      const expiry = options.expiry ?? null;
      try {
        const result = w.cipherclerk_post_encrypted_intent(JSON.stringify({
          sender_privkey: cc.secretKey,
          match_spec: canonicalMatchSpec,
          kind: kind === "offer" ? "Offer" : kind === "query" ? "Query" : "Need",
          expiry,
        }));
        // Forward the canonical `EncryptedIntent` JSON to the node for
        // gossip propagation. The wasm binding emits both the
        // postcard bytes (for direct-peer use) and an axum-compatible
        // JSON form for the `/intents/encrypted` HTTP endpoint.
        const submit = await submitNodeJsonWithOutbox({
          kind: "encrypted_intent",
          label: "encrypted intent",
          endpoint: "/intents/encrypted",
          body: result.encrypted_intent_json,
          headers: { "Content-Type": "application/json" },
          metadata: { action: "postEncryptedIntent", intentId: result.intent_id, kind },
        });
        resetLockTimer();
        return {
          id: message.id,
          result: {
            intentId: result.intent_id,
            expiry: result.expiry,
            encrypted: true,
            submitted: submit.submitted,
            queued: !submit.submitted && submit.queued,
            outboxId: !submit.submitted && submit.queued ? submit.outboxId : undefined,
            submitError: submit.submitted ? undefined : submit.error,
          },
        };
      } catch (e: unknown) {
        const err = e as Error;
        return { id: message.id, error: err.message || "post_encrypted_intent failed" };
      }
    }

    case "dregg:privateTransfer": {
      requireWasm("privateTransfer");
      const w = wasm!;
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      if (!cc.secretKey) return { id: message.id, error: "Cipherclerk secret key not available" };
      if (cc.needsPassphraseSetup) {
        return { id: message.id, error: "Set a cipherclerk passphrase before signing private transfers." };
      }
      const amount = message.amount as number;
      const assetType = message.assetType as string | number | undefined;
      const recipientMeta = message.recipientStealthMeta as StealthMetaAddress | undefined;
      if (!recipientMeta || !recipientMeta.spendPubkey || !recipientMeta.viewPubkey) {
        return { id: message.id, error: "recipientStealthMeta must include spendPubkey and viewPubkey" };
      }
      // Coerce the page-side `assetType` (commonly a symbolic string like
      // "credit") to the canonical u64 the SDK expects. The wasm
      // `cipherclerk_private_transfer` binding treats this as the asset_type
      // tag carried on every committed note.
      const assetTypeU64 = typeof assetType === "number"
        ? assetType
        : (typeof assetType === "string" && /^[0-9]+$/.test(assetType) ? parseInt(assetType, 10) : 0);
      try {
        const result = w.cipherclerk_private_transfer(JSON.stringify({
          sender_privkey: cc.secretKey,
          amount,
          asset_type: assetTypeU64,
          recipient_meta: {
            spend_pubkey: recipientMeta.spendPubkey,
            view_pubkey: recipientMeta.viewPubkey,
          },
        }));
        const submit = await submitNodeJsonWithOutbox({
          kind: "turn",
          label: "private transfer",
          endpoint: "/turns/submit",
          turnId: result.turn_id,
          body: {
            turn_id: result.turn_id,
            turn_bytes: Array.from(result.turn_bytes),
            sender_pubkey: cc.publicKey,
          },
          metadata: { action: "privateTransfer", amount, assetType: assetTypeU64 },
        });
        cc.log.push({
          action: "privateTransfer",
          resource: "*",
          allowed: true,
          timestamp: Date.now(),
          mode: "private",
          turnId: result.turn_id,
          amount,
          recipientStealthMeta: recipientMeta,
        });
        await saveState();
        resetLockTimer();
        notifySubscribers("privateTransfer", { turnId: result.turn_id, amount });
        return {
          id: message.id,
          result: {
            success: submit.submitted,
            turnId: result.turn_id,
            queued: !submit.submitted && submit.queued,
            outboxId: !submit.submitted && submit.queued ? submit.outboxId : undefined,
            error: submit.submitted ? undefined : `Submit failed: ${submit.error}`,
          },
        };
      } catch (e: unknown) {
        const err = e as Error;
        return { id: message.id, error: err.message || "private_transfer failed" };
      }
    }

    // Turn v3: pre-built postcard-encoded Turn bytes signed by the cipherclerk.
    case "dregg:signTurnV3": {
      const turnBytes = new Uint8Array(message.turnBytes as number[]);
      const result = await signTurnV3(turnBytes);
      resetLockTimer();
      return { id: message.id, result };
    }

    // Federation registry
    case "dregg:registerFederation": {
      const result = await registerFederation(
        message.federationId as string,
        message.name as string,
        message.committeePubkeys as string[],
      );
      return { id: message.id, result };
    }

    case "dregg:listKnownFederations": {
      const result = await listKnownFederations();
      return { id: message.id, result };
    }

    // CapTP delivered authorization
    case "dregg:createCapTpDeliveredAuth": {
      const result = createCapTpDeliveredAuth(
        message.handoffCertB58 as string,
        message.introducerPk as string,
        message.senderPk as string,
        message.senderSig as string,
      );
      return { id: message.id, result };
    }

    default:
      return { id: message.id, error: "Unknown message type" };
  }
}

chrome.runtime.onMessage.addListener((message: Record<string, unknown>, sender: chrome.runtime.MessageSender, sendResponse: (response: unknown) => void) => {
  const dispatch = async (): Promise<unknown> => {
    const msgType = message.type as MessageType;
    if (POPUP_ONLY_METHODS.has(msgType) && !isExtensionPopup(sender)) {
      return { id: message.id, error: `"${msgType}" is only available from the extension popup.` };
    }
    if (isContentScript(sender) && !PAGE_ALLOWED_METHODS.has(msgType) && !POPUP_ONLY_METHODS.has(msgType)) {
      if (msgType !== "dregg:requestOriginPermission") {
        return { id: message.id, error: `"${msgType}" is not available from page context.` };
      }
    }
    if (message.type === "dregg:authorize" && !ready) {
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
// WebSocket connection
// ---------------------------------------------------------------------------

let nodeWs: WebSocket | null = null;
let wsReconnectDelay = 1000;
let nodePublicKey: string | null = null;
let wsAuthenticated = false;

async function fetchNodePublicKey(): Promise<void> {
  try {
    const resp = await nodeRequest<{ public_key?: string }>(nodeConfig, "/status");
    if (resp.ok && resp.data?.public_key) {
      nodePublicKey = resp.data.public_key;
    }
  } catch (_e) {
    // Ignore.
  }
}

function validateNodeSignature(payload: string, signature: string, pubKey: string): boolean {
  if (!wasm || !wasmLoaded) return false;
  try {
    return wasm.verify_token(payload, pubKey, signature, "node");
  } catch (_e) {
    return false;
  }
}

function validateNodeMessage(msg: Record<string, unknown>): boolean {
  const SIGNED_TYPES = new Set(["revocation", "receipt", "root", "intent", "note_announcement"]);
  if (!SIGNED_TYPES.has(msg.type as string)) return true;
  if (!nodePublicKey) return false;
  if (!msg.signature || !msg.payload) return false;
  return validateNodeSignature(msg.payload as string, msg.signature as string, nodePublicKey);
}

async function connectNodeWs(): Promise<void> {
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

function tryConnect(url: string, onFail: () => void): void {
  try {
    nodeWs = new WebSocket(url);
  } catch (_e) {
    if (onFail) onFail();
    return;
  }

  nodeWs.onopen = (): void => {
    wsReconnectDelay = 1000;
    const challenge = crypto.getRandomValues(new Uint8Array(32));
    const challengeHex = Array.from(challenge).map(b => b.toString(16).padStart(2, "0")).join("");
    nodeWs!.send(JSON.stringify({ type: "auth_challenge", challenge: challengeHex }));

    const authTimer = setTimeout(() => {
      if (!wsAuthenticated && nodeWs) {
        nodeWs.close();
      }
    }, WS_AUTH_TIMEOUT_MS);

    (nodeWs as WebSocket & { _authChallenge?: string; _authTimer?: ReturnType<typeof setTimeout> })._authChallenge = challengeHex;
    (nodeWs as WebSocket & { _authTimer?: ReturnType<typeof setTimeout> })._authTimer = authTimer;
  };

  nodeWs.onmessage = async (event: MessageEvent): Promise<void> => {
    let msg: Record<string, unknown>;
    try {
      msg = JSON.parse(event.data as string);
    } catch {
      return;
    }

    if (msg.type === "auth_response") {
      const ws = nodeWs as WebSocket & { _authChallenge?: string; _authTimer?: ReturnType<typeof setTimeout> };
      // P1-3: fail closed when nodePublicKey is unknown.
      // Previously the extension marked the socket authenticated when
      // /status had failed; a MITM could then send forged revocation/receipt
      // messages. Now if we don't know the node pubkey, drop the connection.
      if (!nodePublicKey || !msg.signature || !ws._authChallenge) {
        nodeWs!.close();
        return;
      }
      if (validateNodeSignature(ws._authChallenge, msg.signature as string, nodePublicKey)) {
        wsAuthenticated = true;
        clearTimeout(ws._authTimer!);
        nodeWs!.send(JSON.stringify({ type: "subscribe", topics: ["roots", "revocations", "receipts", "intents", "note_announcements"] }));
        flushOutbox({ force: true }).catch(() => {});
      } else {
        nodeWs!.close();
      }
      return;
    }

    if (!wsAuthenticated) return;
    if (!validateNodeMessage(msg)) return;

    switch (msg.type) {
      case "revocation": {
        const cc = await loadState();
        const idx = cc.tokens.findIndex(t => t.id === msg.token_id);
        if (idx !== -1) {
          cc.tokens.splice(idx, 1);
          await saveState();
        }
        notifySubscribers("revoked", { tokenId: msg.token_id });
        pushActivity('turn_lifecycle', { phase: 'revoked', token_id: msg.token_id }, { source: 'node-ws' });
        break;
      }
      case "receipt": {
        const cc = await loadState();
        cc.receiptChain.push(msg.hash as string);
        await saveState();
        notifySubscribers("receipt", { hash: msg.hash });
        pushActivity('turn_lifecycle', { phase: 'committed', receipt_hash: msg.hash }, { source: 'node-ws' });
        break;
      }
      case "root": {
        notifySubscribers("root", { height: msg.height, merkle_root: msg.merkle_root });
        pushActivity('federation', { event: 'root', height: msg.height, merkle_root: msg.merkle_root }, { source: 'node-ws' });
        break;
      }
      case "intent": {
        const intent = msg.intent as Intent;
        if (intent && intent.expiry > Date.now() && !intentPool.has(intent.id)) {
          intentPool.set(intent.id, { intent, receivedAt: Date.now() });
        }
        notifySubscribers("intent", { intent });
        pushActivity('turn_lifecycle', { phase: 'intent_received', intent_id: intent?.id, ...intent }, { source: 'node-ws' });
        break;
      }
      case "note_announcement": {
        // Check whether any held stealth keypair owns this note.
        if (!wasm || !wasmLoaded) break;
        const w = wasm;
        const cc = await loadState();
        if (cc.locked || !cc.stealthPrivate || !cc.stealthMeta) break;
        const ephemeralPubkey = new Uint8Array(msg.ephemeral_pubkey as number[]);
        const oneTimePubkey = new Uint8Array(msg.one_time_pubkey as number[]);
        const viewPrivkey = new Uint8Array(cc.stealthPrivate.viewPrivkey);
        const spendPubkey = new Uint8Array(cc.stealthMeta.spendPubkey);
        let ownershipResult: { is_ours: boolean; one_time_privkey: Uint8Array | null };
        try {
          ownershipResult = w.check_stealth_ownership(viewPrivkey, spendPubkey, ephemeralPubkey, oneTimePubkey);
        } catch (_e) {
          break;
        }
        if (!ownershipResult.is_ours) break;
        const note: StealthNote = {
          noteId: msg.note_id as string,
          amount: (msg.amount as number) ?? null,
          assetType: (msg.asset_type as string) || "unknown",
          oneTimePrivkey: ownershipResult.one_time_privkey ? Array.from(ownershipResult.one_time_privkey) : null,
          ephemeralPubkey: Array.from(ephemeralPubkey),
          memo: (msg.memo as string) || null,
          receivedAt: Date.now(),
        };
        cc.stealthNotes.push(note);
        await saveState();
        notifySubscribers("stealthNoteReceived", { note });
        notifySubscribers("note_announcement", { note_id: msg.note_id, ...msg });
        pushActivity('bilateral_receipt', { direction: 'inbound', note_id: msg.note_id, amount: msg.amount }, { source: 'node-ws' });
        break;
      }
    }
  };

  nodeWs.onclose = (): void => {
    nodeWs = null;
    scheduleReconnect();
  };

  nodeWs.onerror = (): void => {
    nodeWs = null;
    if (onFail) onFail();
  };
}

function scheduleReconnect(): void {
  setTimeout(() => connectNodeWs(), wsReconnectDelay);
  wsReconnectDelay = Math.min(wsReconnectDelay * 2, WS_MAX_RECONNECT_DELAY);
}

// ---------------------------------------------------------------------------
// Federation Discovery
// ---------------------------------------------------------------------------

let federationState: FederationState = {
  nodes: [],
  intentService: null,
  lastUpdated: null,
  fetchError: null,
};

async function fetchDiscovery(): Promise<void> {
  try {
    const response = await fetch(DISCOVERY_URL, { cache: "no-cache", headers: { Accept: "application/json" } });
    if (!response.ok) throw new Error(`HTTP ${response.status}: ${response.statusText}`);
    const data = await response.json();
    federationState = {
      nodes: ((data.federation || []) as Array<Record<string, unknown>>).map((node): FederationNode => ({
        nodeId: node.node_id as string,
        ticket: node.ticket as string,
        lastSeen: node.last_seen as number,
        role: node.role as string,
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
    notifySubscribers("federation", {
      nodes: federationState.nodes,
      intentService: federationState.intentService,
      lastUpdated: federationState.lastUpdated,
    });
    pushActivity('federation', { event: 'discovery_update', ...federationState }, { source: 'extension' });
  } catch (e: unknown) {
    const err = e as Error;
    federationState.fetchError = err.message;
  }
}

let discoveryInterval: ReturnType<typeof setInterval> | null = null;
let outboxFlushInterval: ReturnType<typeof setInterval> | null = null;

function startDiscoveryPolling(): void {
  fetchDiscovery();
  discoveryInterval = setInterval(fetchDiscovery, DISCOVERY_POLL_INTERVAL);
}

function startOutboxFlushLoop(): void {
  flushOutbox().catch(() => {});
  outboxFlushInterval = setInterval(() => {
    flushOutbox().catch(() => {});
  }, OUTBOX_FLUSH_INTERVAL_MS);
  chrome.alarms.create(OUTBOX_ALARM_NAME, { periodInMinutes: 1 });
}

// ---------------------------------------------------------------------------
// Context menu
// ---------------------------------------------------------------------------

chrome.runtime.onInstalled.addListener(() => {
  chrome.contextMenus.create({
    id: "dregg-share-capability",
    title: "Share capability...",
    contexts: ["page", "selection"],
  });
});

chrome.contextMenus.onClicked.addListener(async (info: chrome.contextMenus.OnClickData) => {
  if (info.menuItemId === "dregg-share-capability") {
    const cellId = info.selectionText?.trim() || "";
    if (cellId && /^[0-9a-fA-F]{64}$/.test(cellId)) {
      const result = await shareCapability(cellId);
      if (result.uri) {
        // P0-2: keep bearer secret (URI contains node host + secret) out of the URL.
        const nonce = registerPendingDecision("share-capability.html", {
          uri: result.uri,
          cellId,
        });
        chrome.windows.create({
          url: chrome.runtime.getURL("share-capability.html") + "#nonce=" + nonce,
          type: "popup",
          width: 420,
          height: 380,
          focused: true,
        });
      }
    } else {
      // No pre-generated URI; popup will let user paste a cellId and call
      // dregg:shareCapability itself.
      const nonce = registerPendingDecision("share-capability.html", {});
      chrome.windows.create({
        url: chrome.runtime.getURL("share-capability.html") + "#nonce=" + nonce,
        type: "popup",
        width: 420,
        height: 380,
        focused: true,
      });
    }
  }
});

chrome.alarms.onAlarm.addListener((alarm) => {
  if (alarm.name === OUTBOX_ALARM_NAME) {
    flushOutbox().catch(() => {});
  }
});

// ---------------------------------------------------------------------------
// Initialization
// ---------------------------------------------------------------------------

loadNodeConfig();
loadState();
connectNodeWs();
startDiscoveryPolling();
startOutboxFlushLoop();

/**
 * Dragon's Egg cipherclerk background service worker (TypeScript).
 * Manages cipherclerk state (signing keys, capability tokens, receipt chain),
 * evaluates authorization, and generates proofs via WASM.
 */

import { nodeRequest, nodeRequestRaw, getNodeHeaders } from "./api";
import { compatSession, extensionPrefix, isExtensionPageUrl } from "./browser-compat";
import { explainTurn } from "./explain";
import { createSseParser } from "./sse";
import { mnemonicConfirmed, walletPassphraseOk } from "./onboarding";
import { defaultNodeUrl, defaultNodeWssUrl } from "./endpoints";
import { CustodyWasm, bytesEqual } from "./custody";
import { ChromeCustodyStore } from "./passkey";
import { resolveCustody } from "./custody-resolve";
import { validateFederationDomain, ZERO_FEDERATION_DOMAIN_HEX } from "./federation-domain";
import { resolveActiveDreggIdentity } from "./active-identity";
import {
  bytesToHex as offeringBytesToHex,
  counterWire,
  parseOfferingTurnParams,
  signingMessage as offeringSigningMessage,
  type OfferingSignResult,
  type ParsedOfferingTurn,
} from "./offering-sign";
import {
  SignalSessionGrantBook,
  createSignalSessionGrant,
  describeSignalSessionGrant,
  parseSignalSessionRequest,
  signalSessionStatement,
  type ParsedSignalSessionRequest,
  type SignalSessionSignResult,
} from "./signal-session";
import {
  deriveEvmIdentity,
  personalSign as evmPersonalSign,
  personalSignDigest as evmPersonalSignDigest,
  signTypedData as evmSignTypedData,
  eip712Digest as evmEip712Digest,
  hex0x as evmHex0x,
  type Eip712Domain,
  type Eip712Types,
  type EvmIdentity,
} from "./evm";
import {
  buildCommitment,
  checkReveal,
  orderHash as sealedOrderHash,
  sealedAuctionDomain,
  SEALED_BID_TYPES,
  REVEAL_BID_TYPES,
} from "./sealedbid";
import {
  DreggLaunchpadClient,
  LaunchpadOpeningStore,
  OpeningLostError,
  OpeningTamperedError,
  launchpadFromRequest,
  txGasFromRequest,
  signedOrUnsignedTx,
  REFUND_GRACE_SECONDS,
  type LaunchpadOpening,
  type OpeningRef,
  type TxRequest,
} from "./launchpad";
import {
  PollEngine,
  CellEngine,
  DocEngine,
  DocTextEngine,
  StoryEngine,
  DescentEngine,
  MapWebOfCells,
  defaultResolveObject,
  defaultResolveDoc,
  defaultResolveDocText,
  defaultResolveStory,
  defaultResolveDescent,
  type PollPortRequest,
  type PollWorldCtor,
  type CellPortRequest,
  type DocPortRequest,
  type DocWorldCtor,
  type DocTextPortRequest,
  type DocTextWorldCtor,
  type StoryPortRequest,
  type StoryWorldCtor,
  type DescentPortRequest,
  type DescentWorldCtor,
} from "./port";
import {
  Netlayer,
  wasmNetlayerCrypto,
  httpsNetlayerTransport,
  netlayerResolveObject,
  netlayerResolveDoc,
  netlayerResolveStory,
  netlayerResolveCell,
  netlayerResolveValue,
  type NetlayerWasmLike,
} from "./netlayer";
import {
  createStoredPoAEngine,
  type PoACompanionRequest,
  type PoAEngine,
} from "./poa";
import {
  POA_GALLEY_API_PATH,
  POA_GALLEY_ACTOR_HEADER,
  POA_GALLEY_PENDING_JOURNAL_FORMAT,
  checkPoAGalleyPreparationDigest,
  checkPoAGalleyReceiptPostcardSha256,
  decodePoAGalleyPostcard,
  findPoAGalleyAction,
  findPoAGalleyEvent,
  makePoAGalleyPendingIntent,
  makePoAGalleyPrepare,
  parsePoAGalleyBinding,
  parsePoAGalleyPendingJournal,
  parsePoAGalleySession,
  parsePoAGalleyStatus,
  parsePoAGalleyUnsignedTurn,
  poAGalleyAvailableAtSequence,
  poAGalleyActorHeaders,
  poAGalleyPendingIntentKey,
  reconcilePoAGalleyPendingIntents,
  type PoAGalleyBinding,
  type PoAGalleyPendingIntent,
  type PoAGalleyPortResponse,
  type PoAGalleySession,
  type PoAGalleyStatus,
  type PoAGalleyUnsignedTurn,
} from "./poa-galley";
import {
  POA_SIGNAL_BETA_ORIGIN,
  POA_SIGNAL_FEDERATION_HEX,
  POA_SIGNAL_MISSION_ID,
  POA_SIGNAL_NODE_URL,
  explainPoASignalClaim,
  parsePoASignalClaim,
  type PoASignalSubmitResult,
} from "./poa-signal";
import {
  AUTH_CHALLENGE_PATH,
  AUTH_LOGIN_PATH,
  AUTH_LOGOUT_PATH,
  bytesToHex as loginBytesToHex,
  challengeRequestBody,
  cloudBaseUrl,
  loginRequestBody,
  parseChallengeResponse,
  parseLoginResponse,
  statusFromSession,
  utf8Bytes,
  type CapLoginSession,
  type CapLoginStatus,
} from "./login";
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
  ProfileEntry,
  ProfileInfo,
  ReceiptEventSummary,
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
// Production-sane defaults: a public install talks to the dregg network over
// TLS only. Plaintext localhost is NOT a silent default; it is reachable as an
// explicit developer toggle (optional host permission + a settings override).
const DEFAULT_NODE_URL = defaultNodeUrl();
const DEFAULT_NODE_WSS_URL = defaultNodeWssUrl();
const DEFAULT_NODE_WS_URL = defaultNodeWssUrl();
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
const POA_GALLEY_PENDING_INTENTS_KEY = "dregg_poa_galley_pending_intents_v1";
// Receipt stream (node SSE /api/events/stream).
const RECENT_RECEIPTS_KEY = "dregg_recent_receipts";
const RECENT_RECEIPTS_MAX = 50;
const RECEIPT_STREAM_MAX_BACKOFF_MS = 60_000;
// Per-profile mnemonics for profiles created after the first (the first
// profile's mnemonic stays at MNEMONIC_KEY for migration compatibility).
const PROFILE_MNEMONICS_KEY = "dregg_profile_mnemonics_encrypted";
const DEFAULT_PROFILE_NAME = "default";
// Cap-account cloud session (challenge–response login). The bearer session
// token is kept in memory-only `chrome.storage.session` where available (never
// persisted to disk), falling back to local storage otherwise.
const CAP_SESSION_KEY = "dregg_cap_session";

// ---------------------------------------------------------------------------
// Node configuration
// ---------------------------------------------------------------------------

/** Heights past the node's `latest_height` a turn this extension builds stays admissible.
 * Mirrors `dregg_turn::DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS`. */
const TURN_VALIDITY_HORIZON_BLOCKS = 1800;

let nodeConfig: NodeConfig = {
  nodeUrl: DEFAULT_NODE_URL,
  wssUrl: DEFAULT_NODE_WSS_URL,
  wsUrl: DEFAULT_NODE_WS_URL,
  devnetKey: "",
};

// PoA is a distinct deployment. This target and federation are extension-owned
// policy: neither the beta page nor the user's generic node settings can swap
// where a consented Signal claim is signed or retried. There is intentionally
// no Basic-Auth credential or shared beta password here.
const POA_SIGNAL_NODE_CONFIG: NodeConfig = Object.freeze({
  nodeUrl: POA_SIGNAL_NODE_URL,
  wssUrl: "wss://node.pathofangels.network",
  wsUrl: "wss://node.pathofangels.network",
  devnetKey: "",
});

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
  restartReceiptStream();
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
      // Absolute URL: the SW lives at dist/background.js, the wasm-bindgen
      // no-modules glue at the extension root — a "./" relative path would
      // (silently) look in dist/ and leave the broken fallback to run.
      importScripts(chrome.runtime.getURL("dregg_wasm.js"));
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
 *   - sender is an extension page (url starts with the extension prefix;
 *     sender.url is browser-set and unforgeable, so a content script — whose
 *     sender.url is the web page's — can never pass; note current Chromium
 *     sets sender.tab even for chrome.windows.create popups, so tab presence
 *     is NOT a usable popup/content-script discriminator)
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
// BIP39 Mnemonic — ONE implementation, and it is `dregg_sdk::mnemonic`'s
// ---------------------------------------------------------------------------
//
// ⚑ This block used to hold a SECOND BIP39 implementation: an entropy → 24-words
// encoder and a checksum validator, written in TypeScript, reading a SECOND copy of
// the wordlist (`bip39_english.txt`). They were framed as fallbacks — `if (wasm &&
// wasm.generate_mnemonic)` — but the wasm never exported `generate_mnemonic` or
// `validate_mnemonic`, so the "fallback" was the ONLY path that ever ran. A guard that
// cannot be reached is not a fallback, it is the implementation, hidden.
//
// That is the same class of wound as the one this commit closes in
// `wasm/src/lib.rs`: N implementations of one derivation, no test forcing them to
// agree, drift invisible because everything compiles and every screen looks right. The
// wasm now exports both (routing to `dregg_sdk::mnemonic`, the same code the `dregg`
// CLI and `dreggnet-web`'s `/identity` run), so these are thin calls and there is
// nothing left to diverge.
//
// The refusals below are deliberate, and they are NOT a regression in resilience: a
// phrase this worker generates is useless without `derive_keypair_from_mnemonic`, which
// already hard-required the wasm (`requireWasm`). Minting a phrase we cannot turn into a
// key was never a working degraded mode — it was a way to hand somebody 24 words that
// name nothing. Refusing names the real problem (a stale bundle) instead.
//
// `bip39_english.txt` is consequently no longer read by any extension script. It is
// still SHIPPED (`manifest.json` `web_accessible_resources`, `build.sh`'s `BASE_FILES`)
// and is pinned word-for-word to `dregg_sdk::wordlist` by
// `wasm/tests/mnemonic_derivation_matches_the_sdk.rs`; dropping it from the package is a
// packaging decision, not a code one.

/** The message for a bundle whose glue predates a wasm export this code needs. */
function staleBundle(exportName: string): Error {
  return new Error(
    `WASM module does not export ${exportName} — extension/dregg_wasm.js and ` +
    `dregg_wasm_bg.wasm are stale relative to wasm/src. Rebuild: ./extension/build.sh wasm`
  );
}

/** A fresh 24-word BIP39 phrase from `dregg_sdk::mnemonic::generate_mnemonic`. */
async function generateMnemonic(): Promise<string> {
  requireWasm("generateMnemonic");
  if (typeof wasm!.generate_mnemonic !== "function") throw staleBundle("generate_mnemonic");
  return wasm!.generate_mnemonic();
}

/**
 * Whether these words are a valid BIP39 phrase — count, wordlist membership, and the
 * SHA-256 checksum — via `dregg_sdk::mnemonic::validate_mnemonic`.
 *
 * THROWS (rather than returning `false`) when the wasm cannot answer, so a missing
 * module is never reported to the user as "your recovery phrase is wrong".
 */
async function validateMnemonic(mnemonic: string): Promise<boolean> {
  requireWasm("validateMnemonic");
  if (typeof wasm!.validate_mnemonic !== "function") throw staleBundle("validate_mnemonic");
  return wasm!.validate_mnemonic(mnemonic);
}

/**
 * The 24 words to the dregg identity keypair.
 *
 * ⚑ The `"dregg/0"` third argument is now HONORED. It used to be silently discarded:
 * the wasm export took only `(mnemonic, passphrase)`, so wasm-bindgen dropped the extra
 * argument and the path was a hardcoded constant inside the wasm that merely happened to
 * match. See `wasm/src/lib.rs::DERIVATION_PATH`.
 */
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

function bytesToBase64(bytes: Uint8Array): string {
  let binary = "";
  for (let i = 0; i < bytes.length; i++) binary += String.fromCharCode(bytes[i]);
  return btoa(binary);
}

function base64ToBytes(b64: string): Uint8Array {
  return Uint8Array.from(atob(b64), (c) => c.charCodeAt(0));
}

function hexToBytes(hex: string): Uint8Array {
  const out = new Uint8Array(hex.length >> 1);
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(hex.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
}

/** Materialize an outbox entry's stored body for fetch. */
function outboxBody(entry: { body: string; bodyEncoding?: "utf8" | "base64" }): string | Uint8Array {
  return entry.bodyEncoding === "base64" ? base64ToBytes(entry.body) : entry.body;
}

async function enqueueOutboxEntry(input: {
  kind: OutboxEntry["kind"];
  label: string;
  endpoint: string;
  body: string;
  bodyEncoding?: "utf8" | "base64";
  headers?: Record<string, string>;
  turnId?: string;
  metadata?: Record<string, unknown>;
  nodeUrl?: string;
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
    bodyEncoding: input.bodyEncoding,
    headers: input.headers,
    nodeUrl: input.nodeUrl ?? nodeConfig.nodeUrl,
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

async function submitNodeBytesWithOutbox<T = unknown>(input: {
  kind: OutboxEntry["kind"];
  label: string;
  endpoint: string;
  body: Uint8Array;
  headers?: Record<string, string>;
  turnId?: string;
  metadata?: Record<string, unknown>;
  targetConfig?: NodeConfig;
}): Promise<OutboxSubmitResult<T>> {
  const targetConfig = input.targetConfig ?? nodeConfig;
  const headers = { "Content-Type": "application/octet-stream", ...(input.headers || {}) };
  const resp = await nodeRequest<T>(targetConfig, input.endpoint, {
    method: "POST",
    body: input.body as unknown as BodyInit,
    headers,
  });
  if (resp.ok) return { submitted: true, data: resp.data };
  if (!shouldQueueNodeFailure(resp as NodeRequestResult<unknown>)) {
    return { submitted: false, queued: false, error: resp.error || "node rejected submission", status: resp.status };
  }
  const entry = await enqueueOutboxEntry({
    kind: input.kind,
    label: input.label,
    endpoint: input.endpoint,
    body: bytesToBase64(input.body),
    bodyEncoding: "base64",
    headers,
    turnId: input.turnId,
    metadata: input.metadata,
    nodeUrl: targetConfig.nodeUrl,
    error: resp.error || "node unavailable",
  });
  return { submitted: false, queued: true, outboxId: entry.id, error: entry.lastError || "queued" };
}

/** The node's signed-turn commit response (`SubmitSignedTurnResponse`). */
interface SubmitSignedTurnResponse {
  accepted?: boolean;
  turn_hash?: string | null;
  signer?: string | null;
  action_count?: number;
  proof_status?: string;
  has_witness?: boolean;
  witness_count?: number;
  error?: string | null;
}

/**
 * The extension's own custody as a mnemonic unlock for `resolveCustody`: recover
 * the ACTIVE profile's recovery phrase (via the existing `getMnemonic`), so the
 * extension key can be expressed as a `MnemonicCustody`. The BIP39 passphrase is
 * the standard-dregg empty string; `resolveCustody` re-derives and compares to the
 * active public key, falling back to the byte-exact seed provider on any mismatch
 * (e.g. a BIP39-passphrase wallet) — signing never blocks on the phrase.
 */
function activeMnemonicUnlock(
  publicKey?: number[],
): (() => Promise<{ mnemonic: string; passphrase: string } | null>) | undefined {
  if (!publicKey || publicKey.length !== 32) return undefined;
  return async () => {
    const mnemonic = await getMnemonic();
    if (!mnemonic) return null;
    return { mnemonic, passphrase: "" };
  };
}

/**
 * Wrap a signed, encoded `Turn` in the HYBRID `SignedTurn` envelope the node's
 * `/turns/submit` (alias `/api/turns/submit-signed`) expects, and submit.
 *
 * The envelope is assembled by the wasm `assemble_signed_turn_envelope` export,
 * which routes through the SDK's canonical `AgentCipherclerk::sign_turn`:
 * `SignedTurn { turn, signature, signer, pq_signature, pq_signer }` is postcard-
 * serialized by the SDK's own serializer — no hand-rolled layout. The clerk signs
 * the canonical `Turn::hash` (v3) with BOTH the Ed25519 identity AND the ML-DSA-65
 * (FIPS 204) key derived from the same seed, so the post-quantum half rides
 * end-to-end; the node re-derives `turn.hash()`, verifies the Ed25519 half, checks
 * the PQ half fail-closed when present, and checks
 * `turn.agent == CellId::derive_raw(signer, blake3("default"))`.
 *
 * `turnBytesJson` MUST be the round-trippable JSON `Turn` encoding (postcard `Turn`
 * is not self-describing); `sign_turn_v3` emits it as `turn_bytes_json`. The 32-byte
 * Ed25519 seed is the only key material the assembler needs (the PQ key is derived
 * from it inside the SDK).
 */
async function submitSignedTurnBytes(input: {
  turnBytesJson: Uint8Array;
  turnIdHex: string;
  secretKey: number[];
  publicKey?: number[];
  label: string;
  metadata?: Record<string, unknown>;
  expectedSigner?: Uint8Array;
  targetConfig?: NodeConfig;
  endpoint?: string;
}): Promise<OutboxSubmitResult<SubmitSignedTurnResponse>> {
  requireWasm("submitSignedTurn");
  // The SIGNATURE now comes from the active CustodyProvider (§4.5 chain), not a
  // hard-wired `assemble_signed_turn_envelope`: the extension's own key is a
  // MnemonicCustody (byte-identical to the old direct path) / SeedCustody, and a
  // passkey is the SAME interface. FAIL-CLOSED when no custody is available.
  const custodyWasm = wasm! as unknown as CustodyWasm;
  const { provider, tier } = await resolveCustody({
    wasm: custodyWasm,
    extension:
      input.secretKey && input.secretKey.length === 32
        ? {
            secretKey: new Uint8Array(input.secretKey),
            publicKey: new Uint8Array(input.publicKey ?? []),
            getMnemonic: activeMnemonicUnlock(input.publicKey),
          }
        : undefined,
    passkeyStore: new ChromeCustodyStore(),
  });
  if (!provider) {
    return {
      submitted: false,
      queued: false,
      error: `no custody available (tier=${tier}): refusing to sign a write`,
    };
  }
  let providerPublicKey: Uint8Array;
  try {
    providerPublicKey = await provider.publicKey();
  } catch (e: unknown) {
    return {
      submitted: false,
      queued: false,
      error: `custody identity unavailable (tier=${tier}): ${(e as Error).message || String(e)}`,
    };
  }
  if (input.expectedSigner && !bytesEqual(providerPublicKey, input.expectedSigner)) {
    return {
      submitted: false,
      queued: false,
      error: "custody signer does not match the player identity shown for consent",
    };
  }
  let envelope: Uint8Array;
  try {
    const signed = await provider.signTurn(input.turnBytesJson);
    if (!bytesEqual(signed.signer, providerPublicKey)
        || (input.expectedSigner && !bytesEqual(signed.signer, input.expectedSigner))) {
      return {
        submitted: false,
        queued: false,
        error: "custody returned an envelope for a different signer",
      };
    }
    envelope = signed.bytes;
  } catch (e: unknown) {
    return {
      submitted: false,
      queued: false,
      error: `custody sign failed (tier=${tier}): ${(e as Error).message || String(e)}`,
    };
  }

  const headers: Record<string, string> = {};
  const targetConfig = input.targetConfig ?? nodeConfig;
  if (targetConfig.devnetKey) headers["Authorization"] = `Bearer ${targetConfig.devnetKey}`;
  return submitNodeBytesWithOutbox<SubmitSignedTurnResponse>({
    kind: "turn",
    label: input.label,
    endpoint: input.endpoint ?? "/api/turns/submit-signed",
    body: envelope,
    headers,
    turnId: input.turnIdHex,
    metadata: input.metadata,
    targetConfig,
  });
}

/**
 * Canonicalize + submit a wasm-built turn.
 *
 * The `cipherclerk_*` turn builders return `turn_id = blake3(turn_bytes)` —
 * an encoding hash, NOT the canonical `Turn::hash` (v3) the node verifies the
 * `SignedTurn` envelope signature against. Route the built bytes through
 * `sign_turn_v3` (idempotent for already-signed actions) to obtain the
 * canonical hash + re-encoded bytes, then submit on the signed-byte path.
 */
async function signAndSubmitBuiltTurn(input: {
  turnBytes: Uint8Array;
  secretKey: number[];
  publicKey: number[];
  label: string;
  metadata?: Record<string, unknown>;
}): Promise<{ turnId: string; submit: OutboxSubmitResult<SubmitSignedTurnResponse> } | { error: string }> {
  requireWasm("signAndSubmitBuiltTurn");
  const w = wasm!;
  let signed: { turn_id: string; turn_bytes: Uint8Array; turn_bytes_json: Uint8Array };
  try {
    signed = w.sign_turn_v3(input.turnBytes, new Uint8Array(input.secretKey), new Uint8Array(32));
  } catch (e: unknown) {
    return { error: (e as Error).message || "sign_turn_v3 failed" };
  }
  const submit = await submitSignedTurnBytes({
    // The round-trippable JSON `Turn` encoding — the assembler re-signs it into
    // the canonical HYBRID `SignedTurn` (Ed25519 + ML-DSA-65).
    turnBytesJson: new Uint8Array(signed.turn_bytes_json),
    turnIdHex: signed.turn_id,
    secretKey: input.secretKey,
    publicKey: input.publicKey,
    label: input.label,
    metadata: input.metadata,
  });
  return { turnId: signed.turn_id, submit };
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
      body: outboxBody(entry) as unknown as BodyInit,
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

// ---------------------------------------------------------------------------
// Named identity profiles
//
// Mirrors the CLI/SDK profile store semantics (`dregg id create/list/use`,
// sdk/src/profiles.rs): an identity is a *name you chose*. The active
// profile's keypair is mirrored into the top-level publicKey/secretKey so
// every existing signing path reads the active identity. Key derivation is
// the SAME as the CLI/SDK: blake3 derive_key("dregg/0", seed) → Ed25519
// (performed in wasm; the golden vector is pinned in
// test/derivation.test.mjs alongside sdk/src/profiles.rs and
// cli/src/commands/id.rs so all three drift-fail together).
// ---------------------------------------------------------------------------

/** Same name rule as the CLI/SDK store: 1-64 chars of [a-z0-9-_]. */
function validProfileName(name: string): boolean {
  return /^[a-z0-9_-]{1,64}$/.test(name);
}

/** Migrate a pre-profile state in place: the existing key becomes "default". */
function ensureProfiles(s: InternalCipherclerkState): void {
  if (!Array.isArray(s.profiles) || s.profiles.length === 0) {
    s.profiles = [{
      name: DEFAULT_PROFILE_NAME,
      publicKey: s.publicKey,
      secretKey: s.secretKey,
      createdAt: Date.now(),
    }];
    s.activeProfile = DEFAULT_PROFILE_NAME;
  }
  if (!s.activeProfile || !s.profiles.some(p => p.name === s.activeProfile)) {
    s.activeProfile = s.profiles[0].name;
  }
}

function profileInfos(s: InternalCipherclerkState): ProfileInfo[] {
  return (s.profiles || []).map(p => ({
    name: p.name,
    publicKeyHex: p.publicKey.map(b => b.toString(16).padStart(2, "0")).join(""),
    createdAt: p.createdAt,
    active: p.name === s.activeProfile,
  }));
}

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
    ensureProfiles(state);
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
      profilesPublic?: Array<{ name: string; publicKey: number[]; createdAt: number }>;
      activeProfile?: string;
    };
    state = {
      locked: true,
      publicKey: envelope.publicKey || [],
      secretKey: null,
      // Public faces only while locked (names + pubkeys are not secret);
      // secret keys come back on unlock.
      profiles: (envelope.profilesPublic || []).map(p => ({
        name: p.name,
        publicKey: p.publicKey,
        secretKey: null,
        createdAt: p.createdAt,
      })),
      activeProfile: envelope.activeProfile || DEFAULT_PROFILE_NAME,
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
    ensureProfiles(state);
    return state;
  }

  // First run: NO wallet exists yet. We deliberately do NOT auto-generate a
  // keypair here. The previous design encrypted a fresh wallet under a random
  // "internal key" kept in chrome.storage.session, which Chrome clears on
  // browser restart — orphaning the state AND the recovery phrase (silent fund
  // loss), and on Firefox sitting in plaintext local storage. Instead we return
  // an uninitialized state; the popup runs onboarding (set passphrase + back up
  // the recovery phrase), and only then is a key generated, encrypted under the
  // user's passphrase (see completeOnboarding). No key ever exists protected
  // solely by an ephemeral session key.
  state = {
    locked: true,
    uninitialized: true,
    publicKey: [],
    secretKey: null,
    profiles: [],
    activeProfile: DEFAULT_PROFILE_NAME,
    tokens: [],
    receiptChain: [],
    log: [],
    hasMnemonic: false,
    mnemonicShown: false,
    needsPassphraseSetup: false,
    stealthMeta: null,
    stealthPrivate: null,
    stealthNotes: [],
  };
  return state;
}

// ---------------------------------------------------------------------------
// First-run onboarding (MF-1)
//
// A two-step flow that guarantees a wallet is only ever created once the user
// has (a) chosen a real passphrase and (b) backed up + confirmed the recovery
// phrase. The candidate mnemonic is held in service-worker memory ONLY between
// the two steps — never persisted — until completeOnboarding encrypts it under
// the chosen passphrase.
// ---------------------------------------------------------------------------

let pendingOnboardingMnemonic: string | null = null;

async function walletExists(): Promise<boolean> {
  const stored = await chrome.storage.local.get([
    STORAGE_KEY,
    ENCRYPTED_STATE_KEY,
    MNEMONIC_KEY,
    LEGACY_ENCRYPTED_STATE_KEY,
  ]);
  return Boolean(
    stored[STORAGE_KEY] ||
    stored[ENCRYPTED_STATE_KEY] ||
    stored[MNEMONIC_KEY] ||
    stored[LEGACY_ENCRYPTED_STATE_KEY],
  );
}

/**
 * Begin onboarding: generate a fresh candidate recovery phrase and return it
 * so the popup can display it for the user to write down. The phrase is held in
 * memory only; nothing is persisted until completeOnboarding. Refuses if a
 * wallet already exists.
 */
async function beginOnboarding(): Promise<{ mnemonic?: string; error?: string }> {
  if (await walletExists()) {
    return { error: "A wallet already exists. Recover or unlock it instead." };
  }
  try {
    pendingOnboardingMnemonic = await generateMnemonic();
  } catch (e: unknown) {
    return { error: (e as Error).message || "Failed to generate recovery phrase" };
  }
  return { mnemonic: pendingOnboardingMnemonic };
}

/**
 * Complete onboarding: the user has set a passphrase and re-entered the
 * recovery phrase to confirm they backed it up. We require BOTH before any key
 * is written, then derive the keypair and persist the state + mnemonic
 * encrypted under the user's passphrase (never an internal session key).
 */
async function completeOnboarding(
  passphrase: string,
  confirmMnemonic: string,
): Promise<{ success: boolean; publicKey?: number[]; error?: string }> {
  if (await walletExists()) {
    return { success: false, error: "A wallet already exists." };
  }
  if (!pendingOnboardingMnemonic) {
    return { success: false, error: "Onboarding not started — generate a recovery phrase first." };
  }
  const passCheck = walletPassphraseOk(passphrase);
  if (!passCheck.ok) {
    return { success: false, error: passCheck.error };
  }
  if (!mnemonicConfirmed(pendingOnboardingMnemonic, confirmMnemonic)) {
    return { success: false, error: "Recovery phrase confirmation does not match. Check the words you wrote down." };
  }

  const mnemonic = pendingOnboardingMnemonic;
  // BIP39 passphrase is empty (the standard dregg derivation); the user's
  // passphrase is the at-rest encryption secret, kept separate.
  const keypair = await deriveKeypairFromMnemonic(mnemonic, "");
  state = {
    locked: false,
    uninitialized: false,
    publicKey: Array.from(keypair.publicKey),
    secretKey: Array.from(keypair.secretKey),
    profiles: [{
      name: DEFAULT_PROFILE_NAME,
      publicKey: Array.from(keypair.publicKey),
      secretKey: Array.from(keypair.secretKey),
      createdAt: Date.now(),
    }],
    activeProfile: DEFAULT_PROFILE_NAME,
    tokens: [],
    receiptChain: [],
    log: [],
    hasMnemonic: true,
    // The user just confirmed the phrase; it is backed up.
    mnemonicShown: true,
    needsPassphraseSetup: false,
    stealthMeta: null,
    stealthPrivate: null,
    stealthNotes: [],
  };
  cclerkPassphrase = passphrase;
  await saveState();
  const encryptedMnemonic = await encryptWithPassphrase(mnemonic, passphrase);
  await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });
  pendingOnboardingMnemonic = null;
  resetLockTimer();
  restartReceiptStream();
  return { success: true, publicKey: state.publicKey };
}

async function saveState(): Promise<void> {
  if (!state) return;
  if (!cclerkPassphrase && !state.locked) {
    cclerkPassphrase = await getInternalEncryptionKey();
  }
  if (cclerkPassphrase && !state.locked) {
    ensureProfiles(state);
    const plaintext = JSON.stringify({
      publicKey: state.publicKey,
      secretKey: state.secretKey,
      profiles: state.profiles,
      activeProfile: state.activeProfile,
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
    const env = envelope as EncryptedEnvelope & {
      publicKey?: number[];
      hasMnemonic?: boolean;
      needsPassphraseSetup?: boolean;
      profilesPublic?: Array<{ name: string; publicKey: number[]; createdAt: number }>;
      activeProfile?: string;
    };
    env.publicKey = state.publicKey;
    env.hasMnemonic = state.hasMnemonic;
    env.needsPassphraseSetup = state.needsPassphraseSetup || false;
    // Public faces ride outside the ciphertext so the locked popup can show
    // names + pubkeys (not secret); secret keys only live in the ciphertext.
    env.profilesPublic = state.profiles.map(p => ({
      name: p.name,
      publicKey: p.publicKey,
      createdAt: p.createdAt,
    }));
    env.activeProfile = state.activeProfile;
    await chrome.storage.local.set({ [ENCRYPTED_STATE_KEY]: envelope });
    await chrome.storage.local.remove(STORAGE_KEY);
  }
}

async function lockCipherclerk(): Promise<void> {
  if (!state) return;
  // Locking drops the judged-run grant. Defence in depth rather than the
  // mechanism: `grantCovers` compares `playerKeyHex` against custody at spend
  // time, so a different identity is already structurally unable to reuse one.
  // What this closes is the same identity, unlocked again later, silently
  // resuming a scope the player last thought about before they locked.
  signalSessionGrants.clear();
  if (cclerkPassphrase) {
    state.locked = false;
    await saveState();
  }
  state.locked = true;
  state.secretKey = null;
  for (const p of state.profiles || []) p.secretKey = null;
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
        profiles: decrypted.profiles || [],
        activeProfile: decrypted.activeProfile || DEFAULT_PROFILE_NAME,
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
      ensureProfiles(state);
      cclerkPassphrase = attempt;
      resetLockTimer();
      restartReceiptStream();
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

    // Re-encrypt per-profile mnemonics under the new passphrase too.
    const profileMnemonics = await readProfileMnemonics();
    let changed = false;
    for (const [name, envelope] of Object.entries(profileMnemonics)) {
      for (const key of keysToTry) {
        try {
          const plain = await decryptWithPassphrase(envelope, key);
          profileMnemonics[name] = await encryptWithPassphrase(plain, newPassphrase);
          changed = true;
          break;
        } catch (_e) {
          // Try next key.
        }
      }
    }
    if (changed) {
      await chrome.storage.local.set({ [PROFILE_MNEMONICS_KEY]: profileMnemonics });
    }
  }

  await saveState();
  resetLockTimer();
}

async function getMnemonic(): Promise<string | null> {
  if (!cclerkPassphrase) return null;

  // The ACTIVE profile's recovery phrase: the first profile's lives at
  // MNEMONIC_KEY (migration-compatible); later profiles in the map.
  let envelope: EncryptedEnvelope | undefined;
  const active = state?.activeProfile || DEFAULT_PROFILE_NAME;
  if (active === DEFAULT_PROFILE_NAME) {
    const mnemonicStored = await chrome.storage.local.get(MNEMONIC_KEY);
    envelope = mnemonicStored[MNEMONIC_KEY];
  } else {
    envelope = (await readProfileMnemonics())[active];
  }
  if (!envelope) return null;

  const keysToTry: string[] = [cclerkPassphrase];
  const internalKey = await getInternalEncryptionKey();
  if (cclerkPassphrase !== internalKey) {
    keysToTry.push(internalKey);
  }

  for (const key of keysToTry) {
    try {
      return await decryptWithPassphrase(envelope, key);
    } catch (_e) {
      // Try next.
    }
  }
  return null;
}

async function recoverFromMnemonic(
  mnemonic: string,
  bip39Passphrase: string,
  walletPassphrase: string,
): Promise<{ success: boolean; publicKey?: number[]; error?: string }> {
  // `validateMnemonic` THROWS when the wasm cannot answer, so distinguish "your phrase is
  // wrong" from "this build cannot check it" — telling somebody holding a correct piece of
  // paper that their words are bad is the worst possible message here.
  let valid: boolean;
  try {
    valid = await validateMnemonic(mnemonic);
  } catch (e: unknown) {
    return { success: false, error: (e as Error).message || "Cannot validate recovery phrase" };
  }
  if (!valid) {
    return { success: false, error: "Invalid mnemonic (bad checksum or unknown words)" };
  }
  // A wallet-encryption passphrase is REQUIRED: recovering under the ephemeral
  // internal key would re-create the same restart-orphan footgun MF-1 closes.
  // The (optional) BIP39 passphrase only affects key derivation and is kept
  // separate from the at-rest encryption secret.
  const walletCheck = walletPassphraseOk(walletPassphrase);
  if (!walletCheck.ok) {
    return { success: false, error: walletCheck.error };
  }
  const keypair = await deriveKeypairFromMnemonic(mnemonic, bip39Passphrase);
  state = {
    locked: false,
    uninitialized: false,
    publicKey: Array.from(keypair.publicKey),
    secretKey: Array.from(keypair.secretKey),
    profiles: [{
      name: DEFAULT_PROFILE_NAME,
      publicKey: Array.from(keypair.publicKey),
      secretKey: Array.from(keypair.secretKey),
      createdAt: Date.now(),
    }],
    activeProfile: DEFAULT_PROFILE_NAME,
    tokens: [],
    receiptChain: [],
    log: [],
    hasMnemonic: true,
    mnemonicShown: true,
    needsPassphraseSetup: false,
    stealthMeta: null,
    stealthPrivate: null,
    stealthNotes: [],
  };
  cclerkPassphrase = walletPassphrase;
  const encryptedMnemonic = await encryptWithPassphrase(mnemonic, walletPassphrase);
  await chrome.storage.local.set({ [MNEMONIC_KEY]: encryptedMnemonic });
  await saveState();
  resetLockTimer();
  return { success: true, publicKey: state.publicKey };
}

// ─── profile verbs (mirror `dregg id create / list / use`) ───

/** Read the per-profile encrypted-mnemonic map (profiles beyond the first). */
async function readProfileMnemonics(): Promise<Record<string, EncryptedEnvelope>> {
  const stored = await chrome.storage.local.get(PROFILE_MNEMONICS_KEY);
  return (stored[PROFILE_MNEMONICS_KEY] || {}) as Record<string, EncryptedEnvelope>;
}

/**
 * Create a named profile with a fresh mnemonic-derived Ed25519 keypair
 * (the same `blake3 derive_key("dregg/0", seed)` derivation as the CLI/SDK
 * store). Fails if the name is taken. Does NOT switch the active profile.
 */
async function createProfile(name: string): Promise<{ created?: ProfileInfo; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  if (!validProfileName(name)) {
    return { error: `Invalid profile name ${JSON.stringify(name)}: use 1-64 chars of [a-z0-9-_]` };
  }
  if (cc.profiles.some(p => p.name === name)) {
    return { error: `Profile "${name}" already exists` };
  }
  let mnemonic: string;
  let keypair: { publicKey: Uint8Array; secretKey: Uint8Array };
  try {
    mnemonic = await generateMnemonic();
    keypair = await deriveKeypairFromMnemonic(mnemonic, "");
  } catch (e: unknown) {
    return { error: (e as Error).message || "key derivation failed" };
  }
  const entry: ProfileEntry = {
    name,
    publicKey: Array.from(keypair.publicKey),
    secretKey: Array.from(keypair.secretKey),
    createdAt: Date.now(),
  };
  cc.profiles.push(entry);
  // The profile's recovery phrase, encrypted under the same passphrase as
  // the state envelope.
  const key = cclerkPassphrase || await getInternalEncryptionKey();
  const mnemonics = await readProfileMnemonics();
  mnemonics[name] = await encryptWithPassphrase(mnemonic, key);
  await chrome.storage.local.set({ [PROFILE_MNEMONICS_KEY]: mnemonics });
  await saveState();
  notifySubscribers("profiles", { profiles: profileInfos(cc) });
  return {
    created: {
      name,
      publicKeyHex: entry.publicKey.map(b => b.toString(16).padStart(2, "0")).join(""),
      createdAt: entry.createdAt,
      active: false,
    },
  };
}

/** Switch the active profile (the keypair every signing path reads). */
async function useProfile(name: string): Promise<{ active?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  const profile = cc.profiles.find(p => p.name === name);
  if (!profile) return { error: `Profile "${name}" not found` };
  cc.activeProfile = name;
  cc.publicKey = profile.publicKey;
  cc.secretKey = profile.secretKey;
  await saveState();
  notifySubscribers("profiles", { profiles: profileInfos(cc) });
  // The receipt stream filters on the active profile's cell.
  restartReceiptStream();
  return { active: name };
}

async function listProfiles(): Promise<ProfileInfo[]> {
  const cc = await loadState();
  return profileInfos(cc);
}

async function getActiveIdentity(): Promise<{ publicKeyHex: string; profileName?: string } | { error: string }> {
  const resolved = resolveActiveDreggIdentity(await loadState());
  return resolved.ok ? resolved.identity : { error: resolved.error };
}

// ---------------------------------------------------------------------------
// Cap-account login — log the wallet into the live cloud (console / attach)
//
// A cap-account is a pseudonymous identity: a key you hold, not a username +
// password. Login proves possession of the selected profile's Ed25519 key
// against a server-issued nonce (the SESSION-LOGIN.md §2.1 challenge–response
// floor), then holds the returned session. The wire-shaping + validation is
// the pure `src/login.ts` module; here we own the two impure steps — the fetch
// and the signature. We implement the CLIENT half only; the server (the
// cap-auth lane's webauth control plane) owns account-id derivation + session
// minting.
// ---------------------------------------------------------------------------

/** Memory-only session store where available; disk-backed local otherwise. */
function capSessionStore(): chrome.storage.StorageArea {
  const anyChrome = chrome.storage as unknown as { session?: chrome.storage.StorageArea };
  return anyChrome.session ?? chrome.storage.local;
}

async function loadCapSession(): Promise<CapLoginSession | null> {
  const stored = await capSessionStore().get(CAP_SESSION_KEY);
  return (stored[CAP_SESSION_KEY] as CapLoginSession | undefined) ?? null;
}

async function saveCapSession(session: CapLoginSession | null): Promise<void> {
  if (session) {
    await capSessionStore().set({ [CAP_SESSION_KEY]: session });
  } else {
    await capSessionStore().remove(CAP_SESSION_KEY);
  }
}

/** The cloud base URL the login handshake targets. */
function cloudUrlBase(): string {
  return cloudBaseUrl(nodeConfig.nodeUrl, nodeConfig.cloudUrl ?? null);
}

/** Public login status for the popup. */
async function getLoginStatus(): Promise<CapLoginStatus> {
  const session = await loadCapSession();
  const status = statusFromSession(session, cloudUrlBase(), Math.floor(Date.now() / 1000));
  // Drop a stored-but-expired session so we don't present a stale token.
  if (session && status.expired) await saveCapSession(null);
  return status;
}

/**
 * Log the wallet into the live cloud: fetch a challenge, sign it with the
 * selected profile's key, exchange the signed challenge for a session.
 */
async function capLogin(profileName?: string): Promise<CapLoginStatus | { error: string }> {
  const cc = await loadState();
  if (cc.uninitialized) return { error: "Create a wallet before logging in." };
  if (cc.locked) return { error: "Unlock the wallet before logging in." };
  requireWasm("capLogin");
  const w = wasm!;

  const profile = profileName
    ? cc.profiles.find(p => p.name === profileName)
    : cc.profiles.find(p => p.name === cc.activeProfile);
  if (!profile) return { error: `Profile "${profileName ?? cc.activeProfile}" not found.` };
  if (!profile.secretKey) return { error: "Profile signing key unavailable (locked?)." };

  const pubkeyHex = loginBytesToHex(profile.publicKey);
  const cloud = cloudUrlBase();
  const cloudCfg: NodeConfig = { ...nodeConfig, nodeUrl: cloud };

  // 1. Challenge.
  const chResp = await nodeRequest<Record<string, unknown>>(cloudCfg, AUTH_CHALLENGE_PATH, {
    method: "POST",
    body: JSON.stringify(challengeRequestBody(pubkeyHex)),
  });
  if (!chResp.ok) return { error: `Could not reach the cloud login: ${chResp.error}` };
  const challenge = parseChallengeResponse(chResp.data);
  if ("error" in challenge) return { error: challenge.error };

  // 2. Sign the challenge bytes with the profile's Ed25519 key.
  let signatureHex: string;
  try {
    const sig = w.sign_message(new Uint8Array(profile.secretKey), utf8Bytes(challenge.challenge));
    signatureHex = loginBytesToHex(sig);
  } catch (e: unknown) {
    return { error: `Could not sign the login challenge: ${(e as Error).message}` };
  }

  // 3. Exchange the signed challenge for a session.
  const loginResp = await nodeRequest<Record<string, unknown>>(cloudCfg, AUTH_LOGIN_PATH, {
    method: "POST",
    body: JSON.stringify(loginRequestBody(pubkeyHex, challenge.challenge, signatureHex, profile.name)),
  });
  if (!loginResp.ok) return { error: `Cloud rejected the login: ${loginResp.error}` };
  const session = parseLoginResponse(loginResp.data, {
    publicKeyHex: pubkeyHex,
    cloudUrl: cloud,
    profile: profile.name,
    nowMs: Date.now(),
  });
  if ("error" in session) return { error: session.error };

  await saveCapSession(session);
  resetLockTimer();
  notifySubscribers("login", statusFromSession(session, cloud, Math.floor(Date.now() / 1000)));
  return statusFromSession(session, cloud, Math.floor(Date.now() / 1000));
}

/** Log out: best-effort revoke on the server, then discard the local session. */
async function capLogout(): Promise<CapLoginStatus> {
  const session = await loadCapSession();
  if (session) {
    const cloudCfg: NodeConfig = { ...nodeConfig, nodeUrl: session.cloudUrl };
    // Best-effort: tell the server to drop the session. A network failure here
    // must not strand the local session, so ignore the result.
    await nodeRequest(cloudCfg, AUTH_LOGOUT_PATH, {
      method: "POST",
      headers: { Authorization: `Bearer ${session.token}` },
      body: "{}",
    }).catch(() => undefined);
  }
  await saveCapSession(null);
  const status = statusFromSession(null, cloudUrlBase(), Math.floor(Date.now() / 1000));
  notifySubscribers("login", status);
  return status;
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

// MED-3: produce the authorization receipt seed with a REAL collision-resistant
// hash (blake3, from the dregg wasm crypto core). The authorization decision is
// the datalog evaluation (sound); this value only SEEDS the receipt chain, so it
// is a plain CR commitment and is never advertised as a zero-knowledge proof —
// membership proving (now the sound Poseidon2 descriptor) is a separate path.
function generateAuthReceiptSeed(witness: Uint8Array, mode: string): Uint8Array {
  requireWasm("generateAuthReceiptSeed");
  const w = wasm!;
  const witnessHex = Array.from(witness).map(b => b.toString(16).padStart(2, "0")).join("");
  const digestHex = w.blake3_hash(`${mode}:${witnessHex}`);
  // Pack the hex digest back to bytes for the receipt-chain seed.
  const out = new Uint8Array(digestHex.length / 2);
  for (let i = 0; i < out.length; i++) {
    out[i] = parseInt(digestHex.slice(i * 2, i * 2 + 2), 16);
  }
  return out;
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
  const proof = generateAuthReceiptSeed(witness, mode);
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
      const statusResult = await nodeRequest<{ merkle_root?: string; state_root?: string }>(nodeConfig, "/api/node/status");
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
      // MUST be synchronous (not async): see the origin-permission decision
      // listener — an async listener's returned Promise claims the response
      // channel for EVERY message under Chromium's promise-based onMessage.
      // Same close-race guard as the origin-permission popup: a valid
      // decision marks `decided` synchronously so the popup's window.close()
      // cannot resolve a decline while the accept's state write is in flight.
      let decided = false;
      const listener = (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): void => {
        if (message.type !== "dregg:provisionDecision") return;
        // P0-1: validate the sender is the provision popup we opened.
        if (!validatePopupSender(message, sender, nonce, "provision.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        decided = true;
        if (message.accepted) {
          void (async (): Promise<void> => {
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
          })().catch(() => resolve({ accepted: false }));
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
            if (!decided) {
              consumePendingDecision(nonce);
              resolve({ accepted: false });
            }
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

/**
 * Authorization-first signing surface: show the citizen the clerk's faithful
 * reading of the turn (src/explain.ts — the same human terms
 * sdk/src/explain.rs renders) before any signature is released. Returns true
 * only when the user explicitly accepts in the nonce-bound popup.
 */
function showTurnConfirmation(input: {
  explanation: string;
  turnId: string;
  origin?: string;
  hasUnknown: boolean;
  /**
   * Full lowercase hex (64 chars) of the 32-byte federation domain the turn
   * was SIGNED under. Optional for legacy internal flows (poll/doc/story
   * engines), which sign under the all-zero genesis domain; absent defaults
   * to that zero-domain hex so the popup always states what was signed.
   */
  federationDomainHex?: string;
}): Promise<boolean> {
  const federationDomainHex = input.federationDomainHex ?? ZERO_FEDERATION_DOMAIN_HEX;
  return new Promise((resolve) => {
    const nonce = registerPendingDecision("confirm-intent.html", {
      action: "signTurn",
      explanation: input.explanation,
      turnId: input.turnId,
      hasUnknown: input.hasUnknown,
      origin: input.origin || "unknown",
      federationDomainHex,
    });
    const popupUrl = chrome.runtime.getURL("confirm-intent.html") + "#nonce=" + nonce;

    chrome.windows.create({
      url: popupUrl,
      type: "popup",
      width: 460,
      height: 560,
      focused: true,
    }, (win) => {
      const listener = (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): void => {
        if (message.type !== "dregg:intentConfirmation") return;
        if (!validatePopupSender(message, sender, nonce, "confirm-intent.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        if (message.confirmed !== true) {
          resolve(false);
          return;
        }
        // The ACCEPT decision must bind what the popup DISPLAYED: the popup
        // echoes the turn id and federation domain it rendered, and both must
        // equal what this flow signed. Any post-confirmation substitution
        // (or a stale/forged accept that omits or alters the echo) is
        // REFUSED — treated as a decline, never as consent.
        if (message.turnId !== input.turnId || message.federationDomainHex !== federationDomainHex) {
          resolve(false);
          return;
        }
        resolve(true);
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

// ---------------------------------------------------------------------------
// EVM signing leg + fhEgg sealed-bid ceremony.
//
// The EVM key is DERIVED from the same sealed wallet seed the Ed25519 identity
// expands from (see `./evm`), so one recovery phrase restores both faces and no
// out-of-band binding is needed. Every EVM/sealed-bid signature is gated by the
// same un-overlayable confirm-intent consent chrome that turn-signing uses
// (`showTurnConfirmation`), bound to the digest actually being signed.
// ---------------------------------------------------------------------------

const SEALED_BID_OPENINGS_KEY = "dregg_sealed_bid_openings";

interface SealedOpening {
  commitment: string;
  orderHash: string;
  salt: string;
  order: Record<string, unknown>;
  bidder: string;
  chainId: number;
  verifyingContract: string;
  deadline: number;
  createdAt: number;
}

/** Derive the EVM identity from the UNLOCKED wallet seed, or an error. */
async function requireEvmIdentity(): Promise<
  { ok: true; id: EvmIdentity } | { ok: false; error: string }
> {
  const cc = await loadState();
  if (cc.locked) return { ok: false, error: "Cipherclerk is locked" };
  if (cc.needsPassphraseSetup) {
    return { ok: false, error: "Set a cipherclerk passphrase before signing." };
  }
  if (!cc.secretKey) return { ok: false, error: "Cipherclerk secret key not available" };
  return { ok: true, id: deriveEvmIdentity(new Uint8Array(cc.secretKey)) };
}

async function storeSealedOpening(auctionId: number, opening: SealedOpening): Promise<void> {
  const stored = await chrome.storage.local.get(SEALED_BID_OPENINGS_KEY);
  const map = (stored[SEALED_BID_OPENINGS_KEY] as Record<string, SealedOpening>) || {};
  map[String(auctionId)] = opening;
  await chrome.storage.local.set({ [SEALED_BID_OPENINGS_KEY]: map });
}

async function loadSealedOpening(auctionId: number): Promise<SealedOpening | null> {
  const stored = await chrome.storage.local.get(SEALED_BID_OPENINGS_KEY);
  const map = (stored[SEALED_BID_OPENINGS_KEY] as Record<string, SealedOpening>) || {};
  return map[String(auctionId)] || null;
}

// ---------------------------------------------------------------------------
// The DreggLaunchpad bidder leg — the real contract's commit → reveal.
//
// `sealedbid.ts` derives the seal `chain/contracts/launchpad/DreggLaunchpad.sol`
// recomputes; `launchpad.ts` is its client (ABI derived from that contract, the
// opening store, the transaction builder). Here that client meets the wallet: the
// bidder address is the EVM identity derived from the sealed seed
// (`requireEvmIdentity`), both turns are gated by the same un-overlayable
// confirm-intent chrome every other key-touching operation uses, and the openings
// live in the extension's own local storage.
//
// THE OPENING IS THE WHOLE GAME. The launchpad only ever sees
// `keccak256(price, qty, salt, bidder)`; the `(price, qty, salt)` that opens it
// exists nowhere else. So the opening is persisted BEFORE the commit transaction
// is ever handed out — a bid whose opening was never written is a bid that can
// never be revealed, and no operator, key, or support path can undo that.
// ---------------------------------------------------------------------------

const LAUNCHPAD_OPENINGS_KEY = "dregg_launchpad_openings";

const launchpadOpenings = new LaunchpadOpeningStore({
  async get(): Promise<Record<string, LaunchpadOpening>> {
    const stored = await chrome.storage.local.get(LAUNCHPAD_OPENINGS_KEY);
    return (stored[LAUNCHPAD_OPENINGS_KEY] as Record<string, LaunchpadOpening>) || {};
  },
  async set(map: Record<string, LaunchpadOpening>): Promise<void> {
    await chrome.storage.local.set({ [LAUNCHPAD_OPENINGS_KEY]: map });
  },
});

// The request adapters (`launchpadFromRequest`, `txGasFromRequest`,
// `signedOrUnsignedTx`) live in `./launchpad` beside the client they configure —
// so the node suite drives exactly the code this worker runs.

function launchpadRefOf(pad: DreggLaunchpadClient, launchId: string, bidder: string): OpeningRef {
  return { chainId: pad.chainId, launchpad: pad.address, launchId, bidder };
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

async function fulfillIntent(intentId: string, tokenId: string | null): Promise<{
  fulfilled?: boolean;
  intentId?: string;
  tokenId?: string;
  nodeResult?: unknown;
  error?: string;
}> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };

  const entry = intentPool.get(intentId);
  if (!entry) return { error: "Intent not found in local pool" };
  const intent = entry.intent;

  if (intent.expiry <= Date.now()) {
    intentPool.delete(intentId);
    return { error: "Intent has expired" };
  }

  // Resolve the fulfilling token: explicit id if given, else auto-match.
  let matchingToken: CapabilityToken | undefined;
  if (tokenId) {
    matchingToken = cc.tokens.find(t => t.id === tokenId);
    if (!matchingToken) return { error: `Token "${tokenId}" not found in cipherclerk` };
  } else {
    const matchResult = matchIntentLocally(intent, cc.tokens, Date.now());
    if (!matchResult) return { error: "No matching token found for this intent" };
    matchingToken = cc.tokens.find(t => t.id === matchResult.tokenId);
    if (!matchingToken) return { error: "Matched token no longer available" };
  }

  const confirmed = await showIntentConfirmation("fulfillIntent", intent.matcher, {
    intentId,
    tokenId: matchingToken.id,
    intentKind: intent.kind,
  });
  if (!confirmed) return { error: "User denied intent fulfillment" };

  const fulfillmentPayload = {
    intent_id: intentId,
    fulfiller_token: {
      id: matchingToken.id,
      actions: matchingToken.actions,
      resource: matchingToken.resource || "*",
      expiry: matchingToken.expiry || null,
    },
    fulfiller_public_key: cc.publicKey,
    timestamp: Date.now(),
  };

  const resp = await nodeRequest<unknown>(nodeConfig, "/intents/fulfill", {
    method: "POST",
    body: JSON.stringify(fulfillmentPayload),
  });
  if (!resp.ok) return { error: `Node rejected fulfillment: ${resp.error}` };

  cc.log.push({
    action: "fulfillIntent",
    resource: intent.matcher?.resourcePattern || "*",
    allowed: true,
    timestamp: Date.now(),
    mode: "trusted",
    intentId,
    tokenId: matchingToken.id,
  });
  await saveState();
  intentPool.delete(intentId);

  notifySubscribers("intentFulfilled", { intentId, tokenId: matchingToken.id, result: resp.data });
  pushActivity("turn_lifecycle", { phase: "intent_fulfilled", intent_id: intentId, token_id: matchingToken.id }, { source: "cclerk" });

  return { fulfilled: true, intentId, tokenId: matchingToken.id, nodeResult: resp.data };
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

async function shareCapability(_cellId: string): Promise<{ uri?: string; cellId?: string; nodeId?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  // `/api/turns/bearer-auth` is an actor-bound VERIFIER. It neither exports a
  // capability nor mints the swiss secret required by a sturdy reference. The
  // old call sent `{cell_id}` and then treated a test mock's invented
  // `{node_id,secret}` response as authority. Refuse until an actual export
  // route exists; never relabel structural proof checking as capability minting.
  return {
    error:
      "Capability export route not implemented; bearer-auth verifies an existing actor-bound proof and cannot mint a sturdy reference.",
  };
}

// Enliven a `dregg://<node>/<cell>/<secret>` sturdy reference. This is LOCAL
// BOOKKEEPING and nothing more — the same thing `dregg cap enliven` does
// (`cli/src/commands/cap.rs`): resolve the URI back into the node, cell and
// swiss secret it names and record it. Exercising the reference is a TURN that
// carries the bearer proof, gated by the executor.
//
// ⚑ It used to POST `{node_id, cell_id, secret}` to `/api/turns/peer-exchange`
// and take the answer as authority. Three things were wrong with that, and the
// third is the one that mattered: (1) that endpoint's body was
// `{sender_cell, receiver_cell, amount}`, so the request never deserialized
// against a real node (422); (2) it never returned `permissions` or `cap_id` at
// all; (3) when the field came back absent the code wrote
// `permissions: "full"` — the widest grant in the vocabulary, minted from a
// missing field. The only server that ever answered the shape this code read
// was `extension/tests/fixtures/node-mock.ts`. That is verbatim the defect
// `shareCapability` (just above) was fixed for on 2026-07; this is the same
// wound, two functions over. The endpoint is deleted as of 2026-08-06.
async function acceptCapability(uri: string, tabId?: number): Promise<{ refId?: string; cellId?: string; nodeId?: string; permissions?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  if (!uri.startsWith("dregg://")) return { error: "Invalid URI: must start with dregg://" };
  const parts = uri.replace("dregg://", "").split("/");
  if (parts.length < 3) return { error: "Invalid URI format. Expected: dregg://<node>/<cell>/<secret>" };
  const [nodeId, cellId, secret] = parts;
  if (!nodeId || !cellId || !secret) {
    return { error: "Invalid URI format: <node>, <cell> and <secret> must all be non-empty" };
  }
  const refId = `ref_${Date.now()}_${Math.random().toString(36).slice(2, 8)}`;
  const liveRef: Omit<ExtensionLiveRef, "refId"> = {
    cellId,
    uri,
    nodeId,
    // NOT a grant. Nothing here has been checked against a ledger; the swiss
    // secret names a capability whose permissions the EXECUTOR decides when a
    // turn presents the bearer proof. Recording anything else — least of all
    // "full" — would be this extension granting itself a capability.
    permissions: "unattested (decided by the executor when the reference is exercised)",
    tabId: tabId || null,
    createdAt: Date.now(),
    capId: null,
  };
  liveRefs.set(refId, liveRef);
  await persistLiveRefs();
  // `allowed` records that the URI was IMPORTED, not that any access was
  // authorized — nothing was asked and nothing answered.
  cc.log.push({ action: "acceptCapability", resource: cellId, allowed: true, timestamp: Date.now(), mode: "captp" });
  await saveState();
  return { refId, cellId, nodeId, permissions: liveRef.permissions };
}

// ⚑ A handoff certificate cannot be minted from here, and this refuses instead
// of pretending. The real object is `dregg_captp::HandoffCertificate::create`
// (`captp/src/handoff.rs:245`) — introducer-signed over
// (introducer, target federation, target cell, recipient, permissions, swiss).
// Its `swiss` must ALREADY be registered in the target federation's
// `SwissTable`, and no route mints or registers one, so a certificate built
// here would carry a locally invented swiss and resolve to nothing.
//
// What this used to do: POST `{cell_id, recipient_pk}` to
// `/api/turns/peer-exchange` and return `certificate_hash` from the response.
// The endpoint's body was `{sender_cell, receiver_cell, amount}` (so the
// request 422'd against a real node), it never returned `certificate_hash`,
// and `|| ""` turned the absence into an empty string a caller reads as a
// certificate. The endpoint is deleted as of 2026-08-06.
async function createHandoff(_cellId: string, _recipientPk: string): Promise<{ certificateHash?: string; cellId?: string; recipientPk?: string; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  return {
    error:
      "Handoff certificates are not mintable from the extension: HandoffCertificate binds a swiss " +
      "secret that must already be registered in the target federation's SwissTable, and no route " +
      "registers one. Nothing was signed and nothing was sent.",
  };
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

// The node's storage routes are admitted by the StorageGatewayMandate cell
// (op allowlist + key-prefix scope + volume budget — each op commits a real
// debit turn). GETs additionally present the read-compartment clearance label.
const STORAGE_READ_CLEARANCE = "storage-read";

async function storageWrite(dataBase64: string): Promise<{ hash?: string; size?: number; error?: string }> {
  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked" };
  const binary = Uint8Array.from(atob(dataBase64), c => c.charCodeAt(0));
  const resp = await nodeRequest<{ hash?: string; size?: number }>(nodeConfig, "/storage/put", {
    method: "POST",
    headers: { "Content-Type": "application/octet-stream" },
    body: binary,
  });
  if (!resp.ok) return { error: `Storage write failed: ${resp.error}` };
  return { hash: resp.data?.hash || "", size: resp.data?.size || binary.length };
}

async function storageRead(hash: string): Promise<{ hash?: string; data?: string; size?: number; error?: string }> {
  const result = await nodeRequestRaw(nodeConfig, `/storage/get/${hash}`, {
    "X-Dregg-Clearance": STORAGE_READ_CLEARANCE,
  });
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
  const resp = await nodeRequest<{ federation_mode?: string; latest_height?: number; peer_count?: number; merkle_root?: string }>(nodeConfig, "/api/node/status");
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
    const result = await signAndSubmitBuiltTurn({
      turnBytes: new Uint8Array(built.turn_bytes),
      secretKey: cc.secretKey,
      publicKey: cc.publicKey,
      label: "propose routes",
      metadata: { action: "proposeRoutes", routes },
    });
    if ("error" in result) return { error: `Proposal failed: ${result.error}` };
    const { turnId, submit } = result;
    if (submit.submitted) return { proposalId: turnId, submitted: true };
    if (submit.queued) return { proposalId: turnId, submitted: false, queued: true, error: `Queued for retry: ${submit.error}` };
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
    const result = await signAndSubmitBuiltTurn({
      turnBytes: new Uint8Array(built.turn_bytes),
      secretKey: cc.secretKey,
      publicKey: cc.publicKey,
      label: "vote on proposal",
      metadata: { action: "voteOnProposal", proposalId, approve },
    });
    if ("error" in result) return { error: `Vote failed: ${result.error}` };
    const { submit } = result;
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
  // The node exposes per-cell balance at `/api/cell/{id}` (the explorer read
  // path), not a `/accounts/{pubkey}/balance` route — that endpoint does not
  // exist and always 404'd. The client cipherclerk's own cell id is
  // `derive_raw(public_key, blake3("default"))`. We derive it via the wasm
  // helper when available, falling back to the node-operator agent cell from
  // `/api/node/identity` (the cell that JSON turns commit as).
  const cellId = await clientCellIdHex(cc);
  if (!cellId) return { error: "Could not derive cell id (wasm unavailable)" };
  const resp = await nodeRequest<{ balance?: number }>(nodeConfig, `/api/cell/${cellId}`);
  if (!resp.ok) return { error: `Failed to query balance: ${resp.error}` };
  return { balance: resp.data?.balance ?? 0 };
}

/**
 * Derive the client cipherclerk's own cell id (`derive_raw(pubkey, H("default"))`)
 * via the wasm helper if present. Returns null when wasm cannot derive it.
 */
async function clientCellIdHex(cc: InternalCipherclerkState): Promise<string | null> {
  const pubkeyHex = Array.from(cc.publicKey).map((b) => b.toString(16).padStart(2, "0")).join("");
  const w = wasm as unknown as { cell_id_for_pubkey?: (pkHex: string, domain: string) => string };
  if (w && typeof w.cell_id_for_pubkey === "function") {
    try {
      return w.cell_id_for_pubkey(pubkeyHex, "default");
    } catch {
      /* fall through */
    }
  }
  return null;
}

// ---------------------------------------------------------------------------
// Devnet account view (node-API path; no wasm required)
//
// These route through the node's REAL verified executor. JSON turns submitted
// via POST /api/turns/submit are signed by the NODE OPERATOR's cipherclerk
// (the node derives the agent from its own pubkey and ignores the body
// `agent` — confused-deputy hardening, see node/src/api.rs). So the account
// shown here is the operator's agent cell, the identity whose turns commit.
// This is the realistic "interact with the devnet node you trust/operate"
// surface; user-sovereign turns go through the wasm signTurnV3 +
// /api/turns/submit-signed byte path.
// ---------------------------------------------------------------------------

interface NodeIdentity {
  publicKey: string;
  agentCell: string;
  unlocked: boolean;
  agentBalance: number | null;
  agentNonce: number | null;
  error?: string;
}

/** Fetch the node operator's identity (agent cell, balance, nonce, unlocked). */
async function nodeIdentity(): Promise<NodeIdentity> {
  const resp = await nodeRequest<{
    public_key?: string;
    agent_cell?: string;
    unlocked?: boolean;
    agent_balance?: number | null;
    agent_nonce?: number | null;
  }>(nodeConfig, "/api/node/identity");
  if (!resp.ok || !resp.data) {
    return {
      publicKey: "",
      agentCell: "",
      unlocked: false,
      agentBalance: null,
      agentNonce: null,
      error: resp.ok ? "empty identity response" : resp.error,
    };
  }
  return {
    publicKey: resp.data.public_key ?? "",
    agentCell: resp.data.agent_cell ?? "",
    unlocked: resp.data.unlocked ?? false,
    agentBalance: resp.data.agent_balance ?? null,
    agentNonce: resp.data.agent_nonce ?? null,
  };
}

/**
 * Request computrons from the devnet faucet for a cell.
 *
 * When `publicKey` is supplied (and derives the cell), the node materializes
 * the cell with that real Ed25519 key. This is REQUIRED for any cell that
 * will later submit operator-signed turns: a faucet cell materialized without
 * a pubkey gets an all-zero key and every later turn fails Ed25519
 * verification (the cell pubkey, not the signer's, is the verifying key).
 */
async function faucetFund(
  cellId: string,
  amount: number,
  publicKey?: string,
): Promise<{ success: boolean; amount?: number; txHash?: string; error?: string }> {
  if (!/^[0-9a-fA-F]{64}$/.test(cellId)) {
    return { success: false, error: "cell id must be 64 hex chars" };
  }
  const body: Record<string, unknown> = { recipient: cellId, amount };
  if (publicKey && /^[0-9a-fA-F]{64}$/.test(publicKey)) body.public_key = publicKey;
  const resp = await nodeRequest<{ success?: boolean; amount?: number; tx_hash?: string; error?: string }>(
    nodeConfig,
    "/api/faucet",
    { method: "POST", body: JSON.stringify(body) },
  );
  if (!resp.ok) return { success: false, error: resp.error };
  if (!resp.data?.success) return { success: false, error: resp.data?.error || "faucet rejected" };
  return { success: true, amount: resp.data.amount, txHash: resp.data.tx_hash };
}

/**
 * Submit a JSON turn to the node's operator-signed path
 * (POST /api/turns/submit). The node signs each action with its own
 * cipherclerk, runs it through the verified executor, and returns the
 * committed turn hash + proof status. `fee` is the computron budget: it must
 * cover the effects (e.g. a Transfer costs ~100 + accounting; ~500 is a safe
 * default for a single transfer). Requires the operator to be unlocked.
 */
async function submitJsonTurn(spec: {
  agent: string;
  nonce: number;
  fee: number;
  memo?: string;
  effects: Array<Record<string, unknown>>;
}): Promise<{
  accepted: boolean;
  turnHash?: string;
  proofStatus?: string;
  witnessCount?: number;
  error?: string;
}> {
  const body = {
    agent: spec.agent,
    nonce: spec.nonce,
    fee: spec.fee,
    memo: spec.memo,
    actions: [{ effects: spec.effects }],
  };
  const headers: Record<string, string> = {};
  if (nodeConfig.devnetKey) headers["Authorization"] = `Bearer ${nodeConfig.devnetKey}`;
  const resp = await nodeRequest<{
    accepted?: boolean;
    turn_hash?: string | null;
    proof_status?: string;
    witness_count?: number;
    error?: string | null;
  }>(nodeConfig, "/api/turns/submit", {
    method: "POST",
    body: JSON.stringify(body),
    headers,
  });
  if (!resp.ok) return { accepted: false, error: resp.error };
  const d = resp.data ?? {};
  return {
    accepted: d.accepted ?? false,
    turnHash: d.turn_hash ?? undefined,
    proofStatus: d.proof_status,
    witnessCount: d.witness_count,
    error: d.error ?? undefined,
  };
}

/**
 * Sign and submit a pre-built encoded Turn (v3 wire format) — the
 * authorization-first signing surface.
 *
 * Wired to the wasm `sign_turn_v3` export, which decodes the Turn (postcard
 * or JSON), replaces every `Authorization::Unchecked` action with a real
 * Ed25519 signature via the canonical `AgentCipherclerk::sign_action` path
 * (the same path `DreggRuntime::execute_turn_for_agent` uses), and re-encodes.
 * The federation_id is all-zeros for the devnet/sim genesis the extension
 * submits against.
 *
 * BEFORE anything leaves the extension, the clerk's faithful reading of the
 * decoded turn (src/explain.ts — the same human terms `sdk/src/explain.rs`
 * renders, bound to the canonical `Turn::hash`) is shown in a nonce-bound
 * confirmation popup. Only on explicit acceptance is the `SignedTurn`
 * envelope built and submitted to the node's signed-byte path
 * (`/api/turns/submit-signed`, durable-outbox-backed). The result carries the
 * node's receipt fields (turn hash / proof status / witness count) — the
 * Receipt is the result noun.
 *
 * `federationIdInput` is the OPTIONAL federation domain from the page bridge
 * (`number[]` after the nonce-bound message; see federation-domain.ts). It is
 * revalidated here with the same exact checks the page ran — never trust the
 * page-side validation alone — and rejected BEFORE any signing. When absent,
 * the legacy all-zero devnet/sim genesis domain applies (backward compatible
 * one-argument callers). The signed domain travels with the flow: it is shown
 * in full (64 lowercase hex chars) in the confirmation popup, bound into the
 * popup decision, and retained in outbox metadata so a retry can never
 * silently fall back to zero.
 */
async function signTurnV3(
  turnBytes: Uint8Array,
  origin?: string,
  federationIdInput?: unknown,
  options: {
    expectedTurnHash?: string;
    targetConfig?: NodeConfig;
    label?: string;
    metadata?: Record<string, unknown>;
    beforeSubmit?: (signedTurnHash: string) => Promise<string | null>;
  } = {},
): Promise<SignTurnResult> {
  requireWasm("signTurnV3");
  const w = wasm!;

  // Decode + revalidate the optional domain BEFORE touching key material or
  // signing anything. Only ABSENCE defaults to the all-zero genesis domain.
  let federationId: Uint8Array;
  let federationDomainHex: string;
  if (federationIdInput === undefined || federationIdInput === null) {
    federationId = new Uint8Array(32); // legacy zero domain (devnet/sim genesis)
    federationDomainHex = ZERO_FEDERATION_DOMAIN_HEX;
  } else {
    const validated = validateFederationDomain(federationIdInput);
    if (!validated.ok) {
      return { error: `signTurnV3: ${validated.error}`, submitted: false };
    }
    federationId = validated.bytes;
    federationDomainHex = validated.hex;
  }

  const cc = await loadState();
  if (cc.locked) return { error: "Cipherclerk is locked", submitted: false };
  if (cc.needsPassphraseSetup) {
    return { error: "Set a cipherclerk passphrase before signing turns.", submitted: false };
  }
  if (!cc.secretKey) return { error: "Cipherclerk secret key not available", submitted: false };

  let signed: { turn_id: string; turn_bytes: Uint8Array; turn_bytes_json: Uint8Array; signer_pubkey: string };
  try {
    signed = w.sign_turn_v3(turnBytes, new Uint8Array(cc.secretKey), federationId);
  } catch (e: unknown) {
    const err = e as Error;
    return { error: err.message || "sign_turn_v3 failed", submitted: false };
  }
  if (options.expectedTurnHash !== undefined && signed.turn_id !== options.expectedTurnHash) {
    return {
      error: "Server-authored turn hash does not match the canonical turn decoded by Cipherclerk",
      submitted: false,
    };
  }

  // The clerk's reading of exactly the term that was signed: decode the
  // round-trippable JSON encoding the signer emitted alongside the postcard
  // bytes and render it. A decode failure is shown as such — never sign blind.
  let explanation: string;
  let hasUnknown = false;
  try {
    const turnJson = JSON.parse(new TextDecoder().decode(new Uint8Array(signed.turn_bytes_json)));
    const rendered = explainTurn(turnJson, signed.turn_id);
    explanation = rendered.text;
    hasUnknown = rendered.hasUnknown;
  } catch (_e) {
    explanation = `COULD NOT DECODE this turn for display.\n[turn ${signed.turn_id}]`;
    hasUnknown = true;
  }

  const confirmed = await showTurnConfirmation({
    explanation,
    turnId: signed.turn_id,
    origin,
    hasUnknown,
    // The domain that WAS signed (the flow signs before confirm, so
    // display-consistency is the property): full 64 lowercase hex chars.
    federationDomainHex,
  });
  if (!confirmed) {
    return { error: "User declined to sign this turn", submitted: false };
  }
  if (options.beforeSubmit) {
    try {
      const refusal = await options.beforeSubmit(signed.turn_id);
      if (refusal) return { error: refusal, submitted: false };
    } catch {
      return { error: "Could not revalidate the browser tab before submission", submitted: false };
    }
  }

  const submit = await submitSignedTurnBytes({
    // The round-trippable JSON `Turn` the signer emitted — the assembler re-signs
    // it into the canonical HYBRID `SignedTurn` envelope (Ed25519 + ML-DSA-65).
    turnBytesJson: new Uint8Array(signed.turn_bytes_json),
    turnIdHex: signed.turn_id,
    secretKey: cc.secretKey,
    publicKey: cc.publicKey,
    label: options.label ?? "sign turn (v3)",
    // Retain the SELECTED domain: a queued retry re-POSTs the stored signed
    // envelope (the domain is baked into its action signatures), and the
    // metadata records which domain that is — a retry can never silently
    // fall back to zero.
    metadata: { action: "signTurnV3", federationDomainHex, ...(options.metadata ?? {}) },
    targetConfig: options.targetConfig,
  });
  if (submit.submitted) {
    const d = submit.data ?? {};
    if (d.accepted === false) {
      return { turnId: signed.turn_id, submitted: false, error: d.error || "node rejected turn" };
    }
    if (d.turn_hash !== undefined && d.turn_hash !== signed.turn_id) {
      return { turnId: signed.turn_id, submitted: false, error: "Node response named a different turn hash" };
    }
    return {
      turnId: d.turn_hash || signed.turn_id,
      submitted: true,
      receipt: {
        turnHash: d.turn_hash ?? undefined,
        proofStatus: d.proof_status,
        witnessCount: d.witness_count,
      },
    };
  }
  if (submit.queued) return { turnId: signed.turn_id, submitted: false, queued: true, outboxId: submit.outboxId, error: `Queued for retry: ${submit.error}` };
  return { error: `Turn submission failed: ${submit.error}`, submitted: false };
}

interface PoASignalStatusView {
  authority_id?: string;
  federation_id?: string;
  installed?: boolean;
  head?: { transition_count?: number } | null;
}

interface PoASignalTransitionView {
  sequence?: number;
  turn_hash?: string;
}

interface PoASignalCellView {
  found?: boolean;
  nonce?: number;
  public_key?: string | null;
  last_receipt_hash?: string | null;
}

function poaSignalRefused(error: string): PoASignalSubmitResult {
  return { admission: "refused", transition: "not_observed", error };
}

function exactHex32(value: unknown): value is string {
  return typeof value === "string" && /^[0-9a-f]{64}$/.test(value);
}

async function observePoaSignalTransition(
  turnHash: string,
  observedBefore: number,
): Promise<number | null> {
  let nextSequence = observedBefore + 1;
  const deadline = Date.now() + 8_000;
  while (Date.now() < deadline) {
    const status = await nodeRequest<PoASignalStatusView>(
      POA_SIGNAL_NODE_CONFIG,
      `/api/poa/signal/${POA_SIGNAL_FEDERATION_HEX}/status`,
    );
    const count = status.ok ? status.data?.head?.transition_count : undefined;
    if (Number.isSafeInteger(count) && (count as number) >= nextSequence) {
      // A concurrent claim may occupy the immediately next sequence, so scan
      // every bounded successor rather than assuming this turn is `before + 1`.
      const ceiling = Math.min(count as number, observedBefore + 64);
      for (; nextSequence <= ceiling; nextSequence++) {
        const transition = await nodeRequest<PoASignalTransitionView>(
          POA_SIGNAL_NODE_CONFIG,
          `/api/poa/signal/${POA_SIGNAL_FEDERATION_HEX}/transitions/${nextSequence}`,
        );
        if (transition.ok
            && transition.data?.turn_hash?.toLowerCase() === turnHash.toLowerCase()) {
          return nextSequence;
        }
      }
    }
    await new Promise<void>((resolve) => setTimeout(resolve, 750));
  }
  return null;
}

/**
 * Deployment-owned PoA Signal publication. The page contributes only the
 * public mission/code tuple; authority and replay state are derived from the
 * pinned deployment, extension custody, and the live node, then re-read from
 * the signed bytes before consent.
 */
/**
 * Exact round-for-round comparison of two Signal transcripts.
 *
 * ⚠ LENGTH FIRST, and it is not defensive noise: the post-signing substitution
 * check exists to catch a carrier that says something other than what consent
 * was painted for, and a transcript that agrees on every round it HAS while
 * carrying a different number of them is exactly such a carrier. A per-index
 * comparison alone would pass a truncated run.
 */
function sameSignalTranscript(
  built: readonly (readonly number[])[],
  claimed: readonly (readonly number[])[],
): boolean {
  if (built.length !== claimed.length) return false;
  return built.every((round, index) =>
    round.length === 3
    && claimed[index]?.length === 3
    && round.every((band, i) => band === claimed[index][i]));
}

async function submitPoaSignalClaim(
  claimInput: unknown,
  origin: string,
): Promise<PoASignalSubmitResult> {
  if (origin !== POA_SIGNAL_BETA_ORIGIN) {
    return poaSignalRefused("PoA Signal claims are accepted only from beta.pathofangels.network");
  }
  const parsed = parsePoASignalClaim(claimInput);
  if (!parsed.ok) return poaSignalRefused(parsed.error);

  requireWasm("submitPoaSignalClaim");
  const w = wasm!;
  if (typeof w.build_poa_signal_claim_turn !== "function"
      || typeof w.inspect_poa_signal_claim_turn !== "function") {
    return poaSignalRefused("installed dregg WASM does not include the PoA Signal carrier");
  }
  const cc = await loadState();
  if (cc.locked) return poaSignalRefused("Cipherclerk is locked");
  if (cc.needsPassphraseSetup) {
    return poaSignalRefused("Set a cipherclerk passphrase before publishing a Signal claim");
  }
  if (!cc.secretKey || cc.secretKey.length !== 32 || cc.publicKey.length !== 32) {
    // Passkey-only action authorization is not implemented; do not imply that
    // outer-envelope passkey custody can originate this action today.
    return poaSignalRefused("An unlocked extension identity is required for PoA Signal claims");
  }
  const publicKey = new Uint8Array(cc.publicKey);
  const publicKeyHex = offeringBytesToHex(publicKey);
  const agentCellId = await clientCellIdHex(cc);
  if (!agentCellId || !exactHex32(agentCellId)) {
    return poaSignalRefused("Could not derive the active player's canonical cell");
  }

  const status = await nodeRequest<PoASignalStatusView>(
    POA_SIGNAL_NODE_CONFIG,
    `/api/poa/signal/${POA_SIGNAL_FEDERATION_HEX}/status`,
  );
  if (!status.ok) {
    return poaSignalRefused(`PoA Signal authority is unreachable: ${status.error || "node request failed"}`);
  }
  const statusBody = status.data;
  if (!statusBody?.installed
      || statusBody.authority_id?.toLowerCase() !== POA_SIGNAL_FEDERATION_HEX
      || statusBody.federation_id?.toLowerCase() !== POA_SIGNAL_FEDERATION_HEX) {
    return poaSignalRefused("PoA Signal authority is not installed under the pinned federation");
  }
  const transitionCount = statusBody.head?.transition_count;
  if (!Number.isSafeInteger(transitionCount) || (transitionCount as number) < 0) {
    return poaSignalRefused("PoA Signal status returned an invalid transition count");
  }

  const cell = await nodeRequest<PoASignalCellView>(
    POA_SIGNAL_NODE_CONFIG,
    `/api/poa/signal/${POA_SIGNAL_FEDERATION_HEX}/players/${agentCellId}/head`,
  );
  if (!cell.ok) {
    return poaSignalRefused(`Could not read the player's live nonce and receipt head: ${cell.error || "node request failed"}`);
  }
  const nonce = cell.data?.nonce;
  if (!Number.isSafeInteger(nonce) || (nonce as number) < 0) {
    return poaSignalRefused("Player cell returned an invalid nonce");
  }
  if (cell.data?.found && cell.data.public_key?.toLowerCase() !== publicKeyHex) {
    return poaSignalRefused("Player cell is bound to a different public key");
  }
  const previousReceiptHash = cell.data?.last_receipt_hash ?? null;
  if (previousReceiptHash !== null && !exactHex32(previousReceiptHash)) {
    return poaSignalRefused("Player cell returned an invalid previous receipt hash");
  }

  let built: ReturnType<DreggWasm["build_poa_signal_claim_turn"]>;
  let signed: ReturnType<DreggWasm["sign_turn_v3"]>;
  let inspected: ReturnType<DreggWasm["inspect_poa_signal_claim_turn"]>;
  try {
    built = w.build_poa_signal_claim_turn(JSON.stringify({
      schema: parsed.claim.schema,
      signer_public_key_hex: publicKeyHex,
      nonce,
      previous_receipt_hash_hex: previousReceiptHash,
      mission_id: parsed.claim.missionId,
      // ⚑ THE PLAYED TRANSCRIPT, not the solving code. The wasm `Spec` is
      // `deny_unknown_fields`, so the old `code:` key is a refusal here rather
      // than a carrier the node would reject later.
      transcript: parsed.claim.transcript,
    }));
    if (built.agent_cell_id !== agentCellId
        || built.nonce !== nonce
        || (built.previous_receipt_hash_hex ?? null) !== previousReceiptHash
        || built.mission_id !== POA_SIGNAL_MISSION_ID
        || !sameSignalTranscript(built.transcript, parsed.claim.transcript)) {
      return poaSignalRefused("PoA Signal builder output does not match the live player claim");
    }
    signed = w.sign_turn_v3(
      new Uint8Array(built.turn_bytes_json),
      new Uint8Array(cc.secretKey),
      hexToBytes(POA_SIGNAL_FEDERATION_HEX),
    );
    if (signed.signer_pubkey.toLowerCase() !== publicKeyHex) {
      return poaSignalRefused("PoA Signal action was signed by a different identity");
    }
    inspected = w.inspect_poa_signal_claim_turn(new Uint8Array(signed.turn_bytes_json));
  } catch (e: unknown) {
    return poaSignalRefused(`PoA Signal carrier refused: ${(e as Error).message || String(e)}`);
  }

  const inspectedPrevious = inspected.previous_receipt_hash_hex ?? null;
  if (inspected.schema !== parsed.claim.schema
      || inspected.agent_cell_id !== agentCellId
      || inspected.nonce !== nonce
      || inspectedPrevious !== previousReceiptHash
      || inspected.mission_id !== parsed.claim.missionId
      || !sameSignalTranscript(inspected.transcript, parsed.claim.transcript)
      || inspected.turn_hash !== signed.turn_id
      || inspected.fee !== built.fee) {
    return poaSignalRefused("signed PoA Signal bytes failed the exact post-signing substitution check");
  }

  const explanation = explainPoASignalClaim({
    missionId: inspected.mission_id,
    transcript: inspected.transcript,
    signerPublicKeyHex: publicKeyHex,
    agentCellId,
    nonce,
    previousReceiptHashHex: inspectedPrevious,
    federationHex: POA_SIGNAL_FEDERATION_HEX,
    fee: inspected.fee,
    turnHash: inspected.turn_hash,
  });
  const confirmed = await showTurnConfirmation({
    explanation,
    turnId: inspected.turn_hash,
    origin,
    hasUnknown: false,
    federationDomainHex: POA_SIGNAL_FEDERATION_HEX,
  });
  if (!confirmed) return poaSignalRefused("User declined to publish this PoA Signal claim");

  const submit = await submitSignedTurnBytes({
    turnBytesJson: new Uint8Array(signed.turn_bytes_json),
    turnIdHex: signed.turn_id,
    secretKey: cc.secretKey,
    publicKey: cc.publicKey,
    expectedSigner: publicKey,
    targetConfig: POA_SIGNAL_NODE_CONFIG,
    endpoint: `/api/poa/signal/${POA_SIGNAL_FEDERATION_HEX}/claims`,
    label: "Path of Angels Signal claim",
    metadata: {
      action: "submitPoaSignalClaim",
      application: "poa-signal-v1",
      federationDomainHex: POA_SIGNAL_FEDERATION_HEX,
      missionId: POA_SIGNAL_MISSION_ID,
      transcript: parsed.claim.transcript.map((code) => [...code]),
      agentCellId,
      nonce,
      previousReceiptHash,
    },
  });
  if (!submit.submitted) {
    if (submit.queued) {
      return {
        turnId: signed.turn_id,
        admission: "queued",
        transition: "not_observed",
        queued: true,
        outboxId: submit.outboxId,
        error: `Signed claim queued for the pinned PoA node: ${submit.error}`,
      };
    }
    return poaSignalRefused(submit.error);
  }
  if (submit.data?.accepted === false) {
    return poaSignalRefused(submit.data.error || "PoA node refused the signed claim");
  }
  const admittedHash = submit.data?.turn_hash || signed.turn_id;
  if (admittedHash.toLowerCase() !== signed.turn_id.toLowerCase()) {
    return {
      turnId: signed.turn_id,
      admission: "admitted",
      transition: "not_observed",
      error: "PoA node admitted the request but echoed a different turn hash",
    };
  }
  const observedSequence = await observePoaSignalTransition(
    signed.turn_id,
    transitionCount as number,
  );
  return {
    turnId: signed.turn_id,
    admission: "admitted",
    transition: observedSequence === null ? "not_observed" : "observed",
    ...(observedSequence === null ? {} : { transitionSequence: observedSequence }),
  };
}

/**
 * The offering-turn consent surface (G1 rung 2): a nonce-bound popup rendering
 * the human-readable intent — offering, session, move, arg, optional text, the
 * replay counter, and the signing identity — before any signature is released.
 * Same un-overlayable popup-decision framework as `showTurnConfirmation`
 * (P0-1/P0-2 sender validation), with the ACCEPT bound to `bindingHex` (the
 * SHA-256 of the exact canonical message about to be signed): the popup echoes
 * the binding it displayed, and any accept whose echo differs — a stale or
 * post-confirmation-substituted decision — is treated as a decline.
 */
function showOfferingConfirmation(input: {
  origin?: string;
  offeringKey: string;
  sessionId: string;
  moveTurn: string;
  argDecimal: string;
  text: string | null;
  counterDecimal: string;
  signerPubkeyHex: string;
  signerProfile?: string;
  /** Lowercase hex SHA-256 of the canonical signing message — the echo binding. */
  bindingHex: string;
}): Promise<boolean> {
  return new Promise((resolve) => {
    const nonce = registerPendingDecision("confirm-intent.html", {
      action: "signOfferingTurn",
      origin: input.origin || "unknown",
      offeringKey: input.offeringKey,
      sessionId: input.sessionId,
      moveTurn: input.moveTurn,
      argDecimal: input.argDecimal,
      text: input.text,
      counterDecimal: input.counterDecimal,
      signerPubkeyHex: input.signerPubkeyHex,
      signerProfile: input.signerProfile,
      bindingHex: input.bindingHex,
    });
    const popupUrl = chrome.runtime.getURL("confirm-intent.html") + "#nonce=" + nonce;

    chrome.windows.create({
      url: popupUrl,
      type: "popup",
      width: 460,
      height: 560,
      focused: true,
    }, (win) => {
      const listener = (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): void => {
        if (message.type !== "dregg:intentConfirmation") return;
        if (!validatePopupSender(message, sender, nonce, "confirm-intent.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        if (message.confirmed !== true) {
          resolve(false);
          return;
        }
        // The accept must bind what the popup DISPLAYED.
        if (message.offeringBindingHex !== input.bindingHex) {
          resolve(false);
          return;
        }
        resolve(true);
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

/**
 * Sign one dreggnet-offerings move with the extension-held identity key —
 * the SIGNER half (rung 2, browser-held key) of the seam whose VERIFIER half
 * is `OfferingHost::advance_signed` (`dreggnet-offerings/src/signed.rs`,
 * rung 1). The signature is raw Ed25519 (wasm `sign_message`, the same
 * `SigningKey::from_bytes` derivation the server's `TurnSigner` uses) over the
 * canonical `dregg-offering-turn-v1:` message built by
 * `src/offering-sign.ts::signingMessage` — pin-tested byte-for-byte against
 * the Rust builder.
 *
 * REPLAY SAFETY IS ENFORCED SERVER-SIDE: the host's strictly-increasing
 * counter ledger (per offering/session/pubkey) refuses a stale counter, so a
 * captured wire result cannot land twice. The page supplies the counter (from
 * the server's floor); this handler's job is honest display — the confirm
 * surface shows the exact counter, and refuses non-integer / negative / >u64
 * values via `parseOfferingTurnParams` — and correct bytes.
 *
 * Fail-closed order: params → custody (locked / no passphrase / no key) →
 * user consent → signature. Every refusal carries a typed `code` the page can
 * distinguish (`user-declined` ≠ `sign-failed`).
 */
async function signOfferingTurn(paramsInput: unknown, origin?: string): Promise<OfferingSignResult> {
  if (!wasmLoaded || !wasm) {
    return {
      ok: false,
      code: "wasm-unavailable",
      error: `WASM cryptographic module not loaded. ${wasmLoadError ? `Load error: ${wasmLoadError}` : "Module unavailable."}`,
    };
  }
  const w = wasm;

  // Revalidate independently of the page bridge — never trust page-side
  // validation alone.
  const parsed = parseOfferingTurnParams(paramsInput);
  if (!parsed.ok) return { ok: false, code: "invalid-params", error: parsed.error };
  const p: ParsedOfferingTurn = parsed.params;

  const cc = await loadState();
  if (cc.locked) return { ok: false, code: "custody-locked", error: "Cipherclerk is locked" };
  if (cc.needsPassphraseSetup) {
    return { ok: false, code: "custody-locked", error: "Set a cipherclerk passphrase before signing." };
  }
  if (!cc.secretKey || cc.secretKey.length !== 32) {
    return { ok: false, code: "custody-locked", error: "Cipherclerk secret key not available" };
  }
  if (!cc.publicKey || cc.publicKey.length !== 32) {
    return { ok: false, code: "custody-locked", error: "Cipherclerk public key not available" };
  }
  const actorPubkeyHex = offeringBytesToHex(cc.publicKey);

  // The exact bytes about to be signed, and their digest — the consent
  // binding: the popup's ACCEPT echoes the digest it displayed, so consent
  // covers precisely this message and nothing else.
  const message = offeringSigningMessage(p);
  const bindingHex = offeringBytesToHex(
    new Uint8Array(await crypto.subtle.digest("SHA-256", message as Uint8Array<ArrayBuffer>)),
  );

  const confirmed = await showOfferingConfirmation({
    origin,
    offeringKey: p.offeringKey,
    sessionId: p.sessionId,
    moveTurn: p.turn,
    argDecimal: p.arg.toString(),
    text: p.text,
    counterDecimal: p.counter.toString(),
    signerPubkeyHex: actorPubkeyHex,
    signerProfile: cc.activeProfile || undefined,
    bindingHex,
  });
  if (!confirmed) {
    return { ok: false, code: "user-declined", error: "User declined to sign this offering turn" };
  }

  let signature: Uint8Array;
  try {
    signature = w.sign_message(new Uint8Array(cc.secretKey), message);
  } catch (e: unknown) {
    return { ok: false, code: "sign-failed", error: (e as Error).message || "sign_message failed" };
  }
  if (signature.length !== 64) {
    return { ok: false, code: "sign-failed", error: `expected a 64-byte Ed25519 signature, got ${signature.length}` };
  }

  cc.log.push({
    action: "signOfferingTurn",
    resource: `${p.offeringKey}/${p.sessionId}`,
    allowed: true,
    timestamp: Date.now(),
    mode: "signed",
  });
  await saveState();

  return {
    ok: true,
    actorPubkeyHex,
    counter: counterWire(p.counter),
    signatureHex: offeringBytesToHex(signature),
  };
}

/**
 * The judged-Signal-session consent surface: a nonce-bound popup rendering the
 * EXACT statement about to be signed — schema, authority, slot, and for a guess
 * the round and the three bands — plus the signing identity.
 *
 * Same un-overlayable popup-decision framework as `showOfferingConfirmation`,
 * with the ACCEPT bound to `bindingHex` (the SHA-256 of the exact statement
 * bytes): the popup echoes the binding it displayed, and any accept whose echo
 * differs — a stale or post-confirmation-substituted decision — is a decline.
 */
function showSignalSessionConfirmation(input: {
  origin?: string;
  kind: string;
  schema: string;
  authorityId: string;
  slotDecimal: string;
  roundDecimal: string | null;
  guessText: string | null;
  /** The full statement text, shown verbatim — this is what is being signed. */
  statement: string;
  signerPubkeyHex: string;
  signerProfile?: string;
  /** Lowercase hex SHA-256 of the exact statement bytes — the echo binding. */
  bindingHex: string;
  /**
   * ⚠ WHAT ACCEPTING ALSO AUTHORIZES. `bindingHex` covers this statement and no
   * other; the remaining signatures of the run are covered by this scope. A
   * surface that omits it displays consent for less than it grants.
   */
  grantScope: string;
}): Promise<boolean> {
  return new Promise((resolve) => {
    const nonce = registerPendingDecision("confirm-intent.html", {
      action: "signSignalSession",
      origin: input.origin || "unknown",
      sessionKind: input.kind,
      sessionSchema: input.schema,
      sessionAuthorityId: input.authorityId,
      sessionSlotDecimal: input.slotDecimal,
      sessionRoundDecimal: input.roundDecimal,
      sessionGuessText: input.guessText,
      sessionStatement: input.statement,
      signerPubkeyHex: input.signerPubkeyHex,
      signerProfile: input.signerProfile,
      bindingHex: input.bindingHex,
      sessionGrantScope: input.grantScope,
    });
    const popupUrl = chrome.runtime.getURL("confirm-intent.html") + "#nonce=" + nonce;

    chrome.windows.create({
      url: popupUrl,
      type: "popup",
      width: 460,
      height: 600,
      focused: true,
    }, (win) => {
      const listener = (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): void => {
        if (message.type !== "dregg:intentConfirmation") return;
        if (!validatePopupSender(message, sender, nonce, "confirm-intent.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        if (message.confirmed !== true) {
          resolve(false);
          return;
        }
        // The accept must bind what the popup DISPLAYED.
        if (message.sessionBindingHex !== input.bindingHex) {
          resolve(false);
          return;
        }
        resolve(true);
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

/**
 * THE JUDGED-RUN CONSENT LEDGER — at most one live grant, and the reason it
 * exists is that six popups per run is not a consent surface, it is a surface
 * players click through.
 *
 * A judged Signal run is `open` plus up to five `guess` signatures against ONE
 * (authority, slot, playerKey, origin). Asking six times taught the player to
 * accept without reading, which is strictly worse for them than asking once
 * about the whole scope — the popup that is read is the one that is rare.
 *
 * ⚠ IT IS SCOPE, NOT A TOKEN. `grantCovers` compares authority, slot, custody
 * key and origin for EQUALITY and counts down a per-kind budget, so a new slot,
 * a rotated identity, another page or a sixth guess all fall back to asking.
 * The failure direction is always a popup, never a signature.
 */
const signalSessionGrants = new SignalSessionGrantBook();

/**
 * Sign ONE judged Signal session statement with the extension-held player key.
 *
 * The verifying half is `node/src/poa_signal_session.rs::verify_player_signature`,
 * which RE-DERIVES the statement from the structured request fields and never
 * accepts it pre-encoded. This handler does the same thing from the other side:
 * it takes structured fields, re-derives the statement in `src/signal-session.ts`
 * (pin-tested byte-for-byte against the Rust encodings), and signs THAT.
 *
 * ⚑ The player key comes from CUSTODY, not from the request — see the module
 * header of `signal-session.ts`. The statement's subject is the signer, so the
 * consent surface cannot display a subject the signature does not have.
 *
 * ⚑ REPLAY SAFETY IS NODE-SIDE and it is the `round` field: a guess signature
 * covers exactly one round, so a captured request refuses as
 * `session-round-mismatch` rather than spending a second burst. That is why no
 * session token exists and why this handler holds no session state.
 *
 * Fail-closed order: params → custody → user consent → signature. Every refusal
 * carries a typed `code` the page can distinguish.
 */
async function signSignalSession(paramsInput: unknown, origin?: string): Promise<SignalSessionSignResult> {
  if (!wasmLoaded || !wasm) {
    return {
      ok: false,
      code: "wasm-unavailable",
      error: `WASM cryptographic module not loaded. ${wasmLoadError ? `Load error: ${wasmLoadError}` : "Module unavailable."}`,
    };
  }
  const w = wasm;

  // Revalidate independently of the page bridge.
  const parsed = parseSignalSessionRequest(paramsInput);
  if (!parsed.ok) return { ok: false, code: "invalid-params", error: parsed.error };
  const r: ParsedSignalSessionRequest = parsed.request;

  const cc = await loadState();
  if (cc.locked) return { ok: false, code: "custody-locked", error: "Cipherclerk is locked" };
  if (cc.needsPassphraseSetup) {
    return { ok: false, code: "custody-locked", error: "Set a cipherclerk passphrase before signing." };
  }
  if (!cc.secretKey || cc.secretKey.length !== 32) {
    return { ok: false, code: "custody-locked", error: "Cipherclerk secret key not available" };
  }
  if (!cc.publicKey || cc.publicKey.length !== 32) {
    return { ok: false, code: "custody-locked", error: "Cipherclerk public key not available" };
  }
  const playerKeyHex = offeringBytesToHex(cc.publicKey);

  // The exact bytes about to be signed, and their digest — the consent binding.
  const statement = signalSessionStatement(r, playerKeyHex);
  const bindingHex = offeringBytesToHex(
    new Uint8Array(await crypto.subtle.digest("SHA-256", statement.bytes as Uint8Array<ArrayBuffer>)),
  );

  // ⚑ ONE CONSENT PER RUN, and the popup that asks for it must name the SCOPE.
  //
  // `bindingHex` binds THIS statement only — it is a digest of these exact bytes.
  // The other five signatures of a run are covered by the grant's scope and by
  // nothing else, so a popup that showed only the statement would be asking about
  // one burst while authorizing six. `grantScope` is therefore not decoration:
  // it is the part of the consent that covers everything after the first.
  //
  // The order is: try to spend, and only ask if the grant does not cover it. A
  // spend is recorded BEFORE the signature (`SignalSessionGrantBook.consume`), so
  // a failure after this point costs a unit rather than leaving one silently
  // retryable.
  const grantOrigin = origin || "unknown";
  if (!signalSessionGrants.consume(r, playerKeyHex, grantOrigin).ok) {
    // Mint the grant this consent is FOR, so the surface can show what it covers
    // rather than a description assembled beside it. Nothing is remembered until
    // the player accepts.
    const pending = createSignalSessionGrant({
      authorityId: r.authorityId,
      slot: r.slot,
      playerKeyHex,
      origin: grantOrigin,
    });
    const confirmed = await showSignalSessionConfirmation({
      origin,
      kind: r.kind,
      schema: statement.schema,
      authorityId: r.authorityId,
      slotDecimal: r.slot.toString(),
      roundDecimal: r.round === null ? null : String(r.round),
      guessText: r.guess === null ? null : `${r.guess.low} · ${r.guess.mid} · ${r.guess.high}`,
      statement: statement.text,
      signerPubkeyHex: playerKeyHex,
      signerProfile: cc.activeProfile || undefined,
      bindingHex,
      grantScope: describeSignalSessionGrant(pending),
    });
    if (!confirmed) {
      return { ok: false, code: "user-declined", error: "User declined to sign this judged session statement" };
    }
    signalSessionGrants.remember(pending);
    // Spend THIS statement's unit out of the grant just consented to. If it
    // somehow does not cover its own first request, refuse rather than sign
    // outside a grant — the whole point is that no signature happens uncovered.
    const first = signalSessionGrants.consume(r, playerKeyHex, grantOrigin);
    if (!first.ok) {
      signalSessionGrants.clear();
      return { ok: false, code: "user-declined", error: first.error };
    }
  }

  let signature: Uint8Array;
  try {
    signature = w.sign_message(new Uint8Array(cc.secretKey), statement.bytes);
  } catch (e: unknown) {
    return { ok: false, code: "sign-failed", error: (e as Error).message || "sign_message failed" };
  }
  if (signature.length !== 64) {
    return { ok: false, code: "sign-failed", error: `expected a 64-byte Ed25519 signature, got ${signature.length}` };
  }

  cc.log.push({
    action: "signSignalSession",
    resource: `${r.kind}/${r.authorityId}/${r.slot.toString()}`,
    allowed: true,
    timestamp: Date.now(),
    mode: "signed",
  });
  await saveState();

  return {
    ok: true,
    kind: r.kind,
    schema: statement.schema,
    playerKeyHex,
    statement: statement.text,
    signatureHex: offeringBytesToHex(signature),
  };
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
  // Only consult the internal key when a passphrase is actually loaded — never
  // lazily mint a session-only internal key just to render the popup (and never
  // for an uninitialized wallet).
  let hasPassphrase = false;
  if (cclerkPassphrase !== null) {
    const internalKey = await getInternalEncryptionKey();
    hasPassphrase = cclerkPassphrase !== internalKey;
  }
  return {
    locked: cc.locked,
    uninitialized: cc.uninitialized || false,
    tokenCount: cc.tokens.length,
    chainLength: cc.receiptChain.length,
    hasMnemonic: cc.hasMnemonic || false,
    mnemonicShown: cc.mnemonicShown || false,
    hasPassphrase,
    needsPassphraseSetup: cc.needsPassphraseSetup || false,
    hasStealthKeys: cc.stealthMeta !== null && cc.stealthMeta !== undefined,
    stealthNotesCount: (cc.stealthNotes || []).length,
    profiles: profileInfos(cc),
    activeProfile: cc.activeProfile,
    wasmReady: wasmLoaded,
    wasmError: wasmLoadError,
  };
}

/**
 * Return the most recent cipherclerk activity-log entries for the popup.
 *
 * The log lives in the in-memory (decrypted) cipherclerk state, NOT in a
 * plaintext `chrome.storage.local` key — `saveState()` removes the legacy
 * plaintext `dregg_cipherclerk` key after migration, so reading storage
 * directly always yields an empty log. The popup must fetch it through this
 * message instead. Returns `[]` while the cipherclerk is locked.
 */
async function getLog(limit = 20): Promise<LogEntry[]> {
  const cc = await loadState();
  if (cc.locked) return [];
  const log = cc.log || [];
  return log.slice(-limit).reverse();
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
  // A content script's sender.url is the WEB page's URL (the browser sets it;
  // pages cannot forge it) — never this extension's chrome-extension:// URL.
  // Checking sender.tab alone misclassifies our own popups: on current
  // Chromium, extension pages opened via chrome.windows.create message with
  // sender.tab SET, which used to make the router drop every popup decision
  // as "page context".
  return sender?.tab != null && !isExtensionPageUrl(sender?.url || "");
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
      // MUST be synchronous: an async onMessage listener returns a Promise
      // for EVERY message, and Chromium's promise-based onMessage support
      // treats that as claiming the response channel — its undefined
      // resolution is delivered (as null) before the real router responds,
      // breaking unrelated messages like dregg:getPendingDecision.
      // Set synchronously on a valid decision so the popup's immediate
      // window.close() (whose onRemoved fires while the allowlist write is
      // still in flight) cannot race a decline over a real grant.
      let decided = false;
      const listener = (message: Record<string, unknown>, sender: chrome.runtime.MessageSender): void => {
        if (message.type !== "dregg:originPermissionDecision") return;
        // P0-1: validate the sender is the origin-permission popup.
        if (!validatePopupSender(message, sender, nonce, "origin-permission.html")) return;
        chrome.runtime.onMessage.removeListener(listener);
        decided = true;
        if (message.granted) {
          void addOriginToAllowlist(origin, method).then(
            () => resolve({ granted: true }),
            () => resolve({ granted: false }),
          );
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
            if (!decided) {
              consumePendingDecision(nonce);
              resolve({ granted: false });
            }
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
  "dregg:evmGetAddress", "dregg:evmPersonalSign", "dregg:evmSignTypedData",
  "dregg:sealedBidCommit", "dregg:sealedBidReveal", "dregg:drexPlaceOrder",
  "dregg:launchpadCommit", "dregg:launchpadReveal", "dregg:launchpadStatus",
  "dregg:launchpadReclaimTx",
  "dregg:signTurn", "dregg:signTurnV3", "dregg:submitPoaSignalClaim", "dregg:queryBalance",
  "dregg:getActiveIdentity",
  "dregg:shareCapability", "dregg:acceptCapability", "dregg:createHandoff",
  "dregg:mountService", "dregg:discoverServices", "dregg:resolvePath",
  "dregg:storageWrite", "dregg:storageRead", "dregg:storageQuota",
  "dregg:listOutbox", "dregg:flushOutbox", "dregg:dropOutboxEntry",
  "dregg:federationStatus", "dregg:proposeRoutes", "dregg:voteOnProposal",
  "dregg:registerFederation", "dregg:listKnownFederations",
  "dregg:createCapTpDeliveredAuth", "dregg:getReceiptWitnesses",
  "dregg:poll",  // quiet-upgrade thin-view port (§3): resolve/render/fire/verify
  "dregg:cell",  // composition port: <dregg-embed> / <dregg-transclude>
  "dregg:doc",   // verifiable-document authoring port: <dregg-doc>
  "dregg:doctext", // free-text authoring port: <dregg-doc editable>
  "dregg:story", // verifiable choose-your-own-adventure port: <dregg-story>
  "dregg:descent", // The Descent played in-tab: <dregg-descent>
  "dregg:poa", // signed/allowlisted Path of Angels YouTube companion: <dregg-poa>
  // Internal content-element port. page.ts exposes no method, and content.ts
  // rejects unknown page messages before they can reach this route.
  "dregg:poaGalley",
  // ⚑ 2026-08-07 — ADDED AFTER AN END-TO-END DRIVE FOUND THEM MISSING. Both were
  // fully implemented, dispatched in the message switch, and exposed by `page.ts`,
  // and `content.ts` restricted them — every side correct, and THIS list is the one
  // that decides. A judged Signal run could not be played from a browser at all
  // ("dregg:signSignalSession is not available from page context"), while a read of
  // page.ts + content.ts + the handler said the chain was complete. Reading four
  // agreeing files cannot see a fifth that disagrees; only driving it can.
  "dregg:signSignalSession",
  "dregg:signOfferingTurn",
]);

const POPUP_ONLY_METHODS = new Set<MessageType>([
  "dregg:unlock", "dregg:lock", "dregg:getLog", "dregg:getCapabilities", "dregg:listIntents",
  "dregg:offerCapability", "dregg:fulfillIntent", "dregg:getFulfillableIntents",
  "dregg:revoke", "dregg:getState", "dregg:getFederation", "dregg:refreshDiscovery",
  "dregg:setPassphrase", "dregg:getMnemonic", "dregg:recover",
  "dregg:beginOnboarding", "dregg:completeOnboarding",
  "dregg:getDisclosurePrefs", "dregg:clearDisclosurePref",
  "dregg:getOriginPermissions", "dregg:revokeOriginPermission",
  "dregg:getPrivacyState", "dregg:setCommittedTransferMode", "dregg:getStealthNotes",
  "dregg:getNodeConfig", "dregg:setNodeConfig",
  "dregg:getLiveRefs", "dregg:dropLiveRef",
  "dregg:nodeIdentity", "dregg:faucetFund", "dregg:submitJsonTurn",
  "dregg:listProfiles", "dregg:createProfile", "dregg:useProfile",
  "dregg:getRecentReceipts",
  "dregg:capLogin", "dregg:capLogout", "dregg:getLoginStatus",
]);

// ---------------------------------------------------------------------------
// Quiet-upgrade poll engine (DREGG-QUIET-UPGRADE.md §3, steps 1–3).
//
// The ENGINE side of the split: it owns the wasm PollWorld, resolves the
// content-addressed poll, renders/fires/verifies, and routes custody consent to
// the un-overlayable confirm-intent chrome (`showTurnConfirmation`). The thin
// view (<dregg-poll>, in the content-script world) reaches it ONLY through the
// "dregg:poll" message — no wasm, no keys ever leave this context.
// ---------------------------------------------------------------------------

let pollEngine: PollEngine | null = null;

function getPollEngine(): PollEngine {
  requireWasm("poll");
  if (!pollEngine) {
    const PollWorld = (wasm as unknown as { PollWorld?: PollWorldCtor }).PollWorld;
    if (!PollWorld) throw new Error("PollWorld unavailable in wasm module");
    // THE NETLAYER (DREGG-QUIET-UPGRADE.md §0–3): retire the FNV content-addressing
    // stand-in with the real substrate resolve — a content-addressed (blake3) fetch
    // over the UNTRUSTED node transport, verified CLIENT-SIDE (recomputed digest ==
    // addr; receipt/proof chain; committee-anchored quorum). Fail-closed: an
    // unverifiable object resolves to `null`, so the thin view shows only the
    // original link. `defaultResolveObject` remains the fixture/test stand-in only.
    const net = new Netlayer(
      httpsNetlayerTransport(() => ({ nodeUrl: nodeConfig.nodeUrl, devnetKey: nodeConfig.devnetKey })),
      wasmNetlayerCrypto(wasm as unknown as NetlayerWasmLike),
      // The trusted committee (checkpoint config) anchors a cross-fed resolve; an
      // empty committee runs the same-fed structural quorum gate. TODO: wire from
      // the light-client checkpoint once the extension carries it.
      {},
    );
    pollEngine = new PollEngine({
      PollWorld,
      resolveObject: nodeConfig.nodeUrl ? netlayerResolveObject(net) : defaultResolveObject,
      // Custody consent: the faithful reading shown in extension chrome the
      // page cannot overlay or clickjack (§3 — the load-bearing property).
      consent: (req) =>
        showTurnConfirmation({
          explanation: req.explanation,
          turnId: req.turnId,
          origin: req.origin,
          hasUnknown: false,
        }),
    });
  }
  return pollEngine;
}

// ---------------------------------------------------------------------------
// Quiet-upgrade composition engine — <dregg-embed> (whole child cell, recursive)
// and <dregg-transclude> (value quote). DOC-CELL-COMPOSITION.md §1.
//
// The SAME split as the poll engine: this ENGINE (background, wasm-side) resolves
// + verifies + makes the CAP/TRUST decision (darkening is engine-side — the bytes
// of an out-of-cap child never leave here) + the CYCLE decision; the element is a
// thin, closed-shadow VIEW reachable ONLY through the "dregg:cell" message. Real
// cells resolve over the NETLAYER (content-addressed blake3 fetch, verified
// client-side, committee-anchored quorum) — fail-closed: an unverifiable child is
// `unresolved`, a bad value quote fails closed, neither is ever fabricated. Absent
// a configured node, an EMPTY web-of-cells is the stand-in (every child resolves
// to `unresolved` — fail-closed, never a forged shape).
// ---------------------------------------------------------------------------

let cellEngine: CellEngine | null = null;

function getCellEngine(): CellEngine {
  requireWasm("cell");
  if (!cellEngine) {
    if (nodeConfig.nodeUrl) {
      // THE NETLAYER: resolve each child cell / value quote as a verified cross-cell
      // read (recomputed digest == addr; receipt/proof chain; committee-anchored
      // quorum). Unverified ⇒ `unresolved` / fail-closed — the membrane/darkening
      // and the five-state discipline stay intact on the engine side.
      const net = new Netlayer(
        httpsNetlayerTransport(() => ({ nodeUrl: nodeConfig.nodeUrl, devnetKey: nodeConfig.devnetKey })),
        wasmNetlayerCrypto(wasm as unknown as NetlayerWasmLike),
        {},
      );
      cellEngine = new CellEngine({
        resolveCell: netlayerResolveCell(net),
        resolveValue: netlayerResolveValue(net),
      });
    } else {
      // No node configured: an empty web-of-cells — every child is `unresolved`
      // (fail-closed), a value quote fails closed. Never a fabricated cell.
      const web = new MapWebOfCells();
      cellEngine = new CellEngine({ resolveCell: web.resolveCell, resolveValue: web.resolveValue });
    }
  }
  return cellEngine;
}

// ---------------------------------------------------------------------------
// Verifiable-document authoring engine — <dregg-doc>. DREGG-DOCUMENT-FOUNDATION.md,
// wasm/src/bindings_doc.rs (`DocCollabWorld`).
//
// The SAME split again: this ENGINE (background, wasm-side) owns the real wasm
// `DocCollabWorld`, resolves the document over the NETLAYER, renders the
// ConflictView (BOTH alternatives, attributed — NEVER hidden), stages a resolution
// pick, and PUBLISHES a real cap-gated verified turn (reseal the umem `heap_root`)
// ONLY after the un-overlayable confirm-intent consent approves the faithful
// reading. The element reaches it ONLY through the "dregg:doc" message — no wasm,
// no keys, no doc graph ever leave this context. Absent a node, `defaultResolveDoc`
// is the stand-in (a fresh document; a malformed addr fails closed) — mirrors the
// poll engine's `defaultResolveObject` exactly.
// ---------------------------------------------------------------------------

let docEngine: DocEngine | null = null;

function getDocEngine(): DocEngine {
  requireWasm("doc");
  if (!docEngine) {
    const DocWorld = (wasm as unknown as { DocCollabWorld?: DocWorldCtor }).DocCollabWorld;
    if (!DocWorld) throw new Error("DocCollabWorld unavailable in wasm module");
    const net = new Netlayer(
      httpsNetlayerTransport(() => ({ nodeUrl: nodeConfig.nodeUrl, devnetKey: nodeConfig.devnetKey })),
      wasmNetlayerCrypto(wasm as unknown as NetlayerWasmLike),
      {},
    );
    docEngine = new DocEngine({
      DocWorld,
      resolveDoc: nodeConfig.nodeUrl ? netlayerResolveDoc(net) : defaultResolveDoc,
      // Custody consent for PUBLISH: the faithful reading shown in extension chrome
      // the page cannot overlay or clickjack (the load-bearing property). Every
      // publish is a real verified turn, so every publish asks — BEFORE any commit.
      consent: (req) =>
        showTurnConfirmation({
          explanation: req.explanation,
          turnId: req.turnId,
          origin: req.origin,
          hasUnknown: false,
        }),
    });
  }
  return docEngine;
}

// ---------------------------------------------------------------------------
// Free-text authoring engine — <dregg-doc editable>. wasm/src/bindings_doc.rs
// (`DocTextWorld`). The SAME split again: this ENGINE (background, wasm-side) owns
// the real wasm `DocTextWorld`, diffs each keystroke into the minimal patch
// (`Doc::edit`'s token-LCS), renders the working reading, and PUBLISHES a real
// cap-gated verified turn (reseal the umem `heap_root`) ONLY after the
// un-overlayable confirm-intent consent approves the faithful reading. The element
// reaches it ONLY through the "dregg:doctext" message — no wasm, no keys, no doc
// graph ever leave this context. `defaultResolveDocText` is the seeded stand-in
// (a fresh doc-cell; a malformed addr fails closed) until a free-text netlayer
// fetch lands — mirrors the doc/poll engines' `default*` resolvers exactly.
// ---------------------------------------------------------------------------

let docTextEngine: DocTextEngine | null = null;

function getDocTextEngine(): DocTextEngine {
  requireWasm("doctext");
  if (!docTextEngine) {
    const DocTextWorld = (wasm as unknown as { DocTextWorld?: DocTextWorldCtor }).DocTextWorld;
    if (!DocTextWorld) throw new Error("DocTextWorld unavailable in wasm module");
    docTextEngine = new DocTextEngine({
      DocTextWorld,
      // TODO: a free-text netlayer fetch (content-addressed document → seed prose);
      // until then the seeded stand-in resolver (a malformed addr fails closed).
      resolveDocText: defaultResolveDocText,
      // Custody consent for PUBLISH: the faithful reading shown in extension chrome
      // the page cannot overlay or clickjack. Every publish is a real verified turn,
      // so every publish asks — BEFORE any commit.
      consent: (req) =>
        showTurnConfirmation({
          explanation: req.explanation,
          turnId: req.turnId,
          origin: req.origin,
          hasUnknown: false,
        }),
    });
  }
  return docTextEngine;
}

// ---------------------------------------------------------------------------
// Verifiable choose-your-own-adventure engine — <dregg-story>.
// docs/MEGASPEC-worlds-ide-and-the-verified-web.md §4.
//
// The SAME split again: this ENGINE (background, wasm-side) owns the real wasm
// `StoryWorld`, resolves the story over the netlayer, renders the current passage
// (prose + choices), and ADVANCES the story (a real cap-gated verified turn) ONLY
// after the un-overlayable confirm-intent consent approves the faithful reading of
// the choice — a gated/invalid choice fails closed WITHOUT prompting. READ + VERIFY
// need NO custody (the free, trustless tier). The element reaches it ONLY through
// the "dregg:story" message — no wasm, no keys, no story graph ever leave this
// context. `defaultResolveStory` is the stand-in until a story netlayer fetch lands.
// ---------------------------------------------------------------------------

let storyEngine: StoryEngine | null = null;

function getStoryEngine(): StoryEngine {
  requireWasm("story");
  if (!storyEngine) {
    const StoryWorld = (wasm as unknown as { StoryWorld?: StoryWorldCtor }).StoryWorld;
    if (!StoryWorld) throw new Error("StoryWorld unavailable in wasm module");
    // THE NETLAYER (mirrors the poll/doc engines): a `dregg://story/<addr>` resolve is
    // a content-addressed fetch of the `.scene` SOURCE over the UNTRUSTED node
    // transport, verified CLIENT-SIDE (recomputed blake3 == addr; receipt/proof chain;
    // committee-anchored quorum). Only the verified, content-matched scene reaches
    // `new StoryWorld(scene)`; a hostile/mismatched story fails closed (no scene, no
    // world). `defaultResolveStory` remains the no-node/fixture stand-in only.
    const net = new Netlayer(
      httpsNetlayerTransport(() => ({ nodeUrl: nodeConfig.nodeUrl, devnetKey: nodeConfig.devnetKey })),
      wasmNetlayerCrypto(wasm as unknown as NetlayerWasmLike),
      {},
    );
    storyEngine = new StoryEngine({
      StoryWorld,
      resolveStory: nodeConfig.nodeUrl ? netlayerResolveStory(net) : defaultResolveStory,
      // Custody consent for a CHOICE: the faithful reading shown in extension chrome
      // the page cannot overlay or clickjack (the load-bearing property). Every choice
      // is a real verified turn, so every choice asks — BEFORE the story advances.
      consent: (req) =>
        showTurnConfirmation({
          explanation: req.explanation,
          turnId: req.turnId,
          origin: req.origin,
          hasUnknown: false,
        }),
      // The collective VOTER identity — the active profile's ed25519 public key
      // (hex). Public, so no unlock is needed to establish WHO is voting; the vote
      // itself is a custody write (consent-gated above). Stable across the session,
      // so `castVote`'s one-vote-per-voter holds. `null` (no profile) ⇒ the engine
      // refuses the vote (fail-closed). (The extension-less passkey voter derives its
      // id from the PRF-wrapped key in the page-bundled SDK runtime, not here.)
      voterIdentity: async () => {
        const s = await loadState();
        const p =
          s.profiles.find((pr) => pr.name === s.activeProfile) ?? s.profiles[0];
        return p?.publicKey?.length
          ? p.publicKey.map((b) => b.toString(16).padStart(2, "0")).join("")
          : null;
      },
    });
  }
  return storyEngine;
}

// ---------------------------------------------------------------------------
// The Descent, played IN THE TAB — <dregg-descent>. docs/GAME-STRATEGY.md;
// wasm/src/bindings_descent.rs (`DescentWorld`).
//
// The action sibling of the story engine, with ONE difference in the trust split:
// The Descent PLAYS PRIVATELY. Opening today's beacon-seeded day, rendering the room +
// moves, ADVANCING a move (a real cap-gated verified turn the in-tab executor admits iff
// the scene gate passes — a gated/invalid move fails closed in-band), reading state, and
// REPLAY-VERIFYING are ALL the free, private, in-tab tier (NO per-move consent). The
// ONLY custody write is the OPT-IN SETTLE/PUBLISH to the node's no-cheat leaderboard.
//
// `defaultResolveDescent` derives a deterministic committed epoch (today's day) from the
// addr for now; the real beacon-client path fetches TODAY'S drand `quicknet` round and
// hands it as `beacon` — the wasm `DescentWorld::fromBeacon` VERIFIES the BLS pairing
// in-tab before opening (a forged reveal opens no day). Fetching the round is the
// browser's client seam. The settle hook is left UNWIRED (null) — a named seam; the run
// stays private until the leaderboard-publish leg (signTurnV3 + the node) lands.
// ---------------------------------------------------------------------------

let descentEngine: DescentEngine | null = null;

function getDescentEngine(): DescentEngine {
  requireWasm("descent");
  if (!descentEngine) {
    const DescentWorld = (wasm as unknown as { DescentWorld?: DescentWorldCtor }).DescentWorld;
    if (!DescentWorld) throw new Error("DescentWorld unavailable in wasm module");
    descentEngine = new DescentEngine({
      DescentWorld,
      resolveDescent: defaultResolveDescent,
      // The OPT-IN settle/publish hook is a NAMED SEAM: publishing a private run to the
      // node's no-cheat leaderboard (consent + signTurnV3 + the node) is not wired here,
      // so `settleDescent` degrades to the honest "opt-in named hook" note. Play + verify
      // are fully live (the free, private, in-tab tier). Leaving this `null` keeps the run
      // PRIVATE until the leaderboard-publish leg lands.
      settle: null,
    });
  }
  return descentEngine;
}

// ---------------------------------------------------------------------------
// Path of Angels media companion — <dregg-poa>.
//
// This engine recognizes context and verifies a routing manifest; it does not
// implement game rules. The browser-provided sender.tab.url is authoritative.
// A signed route to `dregg://descent/...` is subsequently played by the normal
// DescentEngine above.
// ---------------------------------------------------------------------------

let poaEngine: PoAEngine | null = null;

function getPoAEngine(): PoAEngine {
  if (!poaEngine) poaEngine = createStoredPoAEngine(chrome.storage.local);
  return poaEngine;
}

function poaGalleyError(op: "status" | "command", error: string): PoAGalleyPortResponse {
  return { ok: false, op, error: error.slice(0, 320) };
}

async function readPoAGalleyPendingIntents(): Promise<PoAGalleyPendingIntent[]> {
  const stored = await chrome.storage.local.get(POA_GALLEY_PENDING_INTENTS_KEY);
  const payload = stored[POA_GALLEY_PENDING_INTENTS_KEY];
  if (payload === undefined) return [];
  const journal = parsePoAGalleyPendingJournal(payload);
  if (journal) return [...journal.entries];
  await chrome.storage.local.remove(POA_GALLEY_PENDING_INTENTS_KEY);
  return [];
}

async function writePoAGalleyPendingIntents(entries: readonly PoAGalleyPendingIntent[]): Promise<void> {
  await chrome.storage.local.set({
    [POA_GALLEY_PENDING_INTENTS_KEY]: {
      format: POA_GALLEY_PENDING_JOURNAL_FORMAT,
      entries: [...entries].slice(-64),
    },
  });
}

// The service worker can receive overlapping messages. Serialize this
// read-modify-write so one tab cannot erase another tab's durable intent.
let poaGalleyPendingMutation: Promise<void> = Promise.resolve();

function mutatePoAGalleyPending<T>(mutation: () => Promise<T>): Promise<T> {
  const result = poaGalleyPendingMutation.then(mutation, mutation);
  poaGalleyPendingMutation = result.then(() => undefined, () => undefined);
  return result;
}

async function recordPoAGalleyPendingIntent(
  session: PoAGalleySession,
  prepared: PoAGalleyUnsignedTurn,
  signedTurnHash: string,
): Promise<PoAGalleyPendingIntent | null> {
  return mutatePoAGalleyPending(async () => {
    const intent = makePoAGalleyPendingIntent(session, prepared, signedTurnHash);
    if (!intent) return null;
    const key = poAGalleyPendingIntentKey(intent);
    const entries = (await readPoAGalleyPendingIntents())
      .filter((candidate) => poAGalleyPendingIntentKey(candidate) !== key);
    entries.push(intent);
    await writePoAGalleyPendingIntents(entries);
    return intent;
  });
}

/** Remove only sequence-expired intents or exact-turn events whose adjacent
 * receipt-postcard checksum matches. Canonical receipt verification is a later
 * WASM boundary and is deliberately not claimed here. */
async function reconcileStoredPoAGalleyPendingIntents(status: PoAGalleyStatus): Promise<void> {
  await mutatePoAGalleyPending(async () => {
    const entries = await readPoAGalleyPendingIntents();
    if (entries.length === 0) return;
    const reconciliation = reconcilePoAGalleyPendingIntents(entries, status);
    const retained = [...reconciliation.pending];
    for (const intent of reconciliation.observed) {
      const event = findPoAGalleyEvent(status, intent.turn_hash);
      if (!event || !await checkPoAGalleyReceiptPostcardSha256(event)) retained.push(intent);
    }
    await writePoAGalleyPendingIntents(retained);
  });
}

async function authorizePoAGalleyBinding(
  value: unknown,
  sender: chrome.runtime.MessageSender,
): Promise<{ binding: PoAGalleyBinding; pageOrigin: string } | { error: string }> {
  const binding = parsePoAGalleyBinding(value);
  if (!binding) return { error: "Malformed Path of Angels manifest binding." };
  const pageUrl = sender.tab?.url;
  if (!pageUrl) return { error: "A browser-authenticated YouTube/X tab is required." };
  let pageOrigin: string;
  try {
    pageOrigin = new URL(pageUrl).origin;
  } catch {
    return { error: "The browser tab URL is invalid." };
  }
  const context = await getPoAEngine().handle({ op: "openContext", context: { href: pageUrl } });
  if (!context.ok || !context.recognized || !context.verified || context.tier !== "extension" ||
      !context.model || context.model.trust !== "signed_manifest") {
    return { error: "This tab has no current curator-signed Path of Angels route." };
  }
  const model = context.model;
  if (model.platform !== binding.platform || model.contextId !== binding.contextId ||
      model.experienceId !== binding.experienceId || model.manifestDigest !== binding.manifestDigest) {
    return { error: "The live tab no longer matches the signed companion binding." };
  }
  return { binding, pageOrigin };
}

async function readPoAGalleyStatus(
  actorHeaders: Readonly<Record<typeof POA_GALLEY_ACTOR_HEADER, string>>,
): Promise<PoAGalleyStatus | { error: string }> {
  const response = await nodeRequest<unknown>(POA_SIGNAL_NODE_CONFIG, `${POA_GALLEY_API_PATH}/status`, {
    method: "GET",
    cache: "no-store",
    headers: actorHeaders,
  });
  if (!response.ok) return { error: response.error || "Galley status request failed" };
  const status = parsePoAGalleyStatus(response.data);
  if (!status) return { error: "The node returned a non-canonical Galley status envelope." };
  await reconcileStoredPoAGalleyPendingIntents(status);
  return status;
}

async function handlePoAGalley(
  message: Record<string, unknown>,
  sender: chrome.runtime.MessageSender,
): Promise<PoAGalleyPortResponse> {
  const op = message.op === "command" ? "command" : message.op === "status" ? "status" : null;
  if (!op) return poaGalleyError("status", "Unknown Galley operation.");
  if (["actor", "actorPublicKeyHex", "playerPublicKey", "player_public_key", "headers"].some((field) => field in message)) {
    return poaGalleyError(op, "Galley preparation identity is background-owned and cannot be supplied by the page.");
  }
  const authorized = await authorizePoAGalleyBinding(message.binding, sender);
  if ("error" in authorized) return poaGalleyError(op, authorized.error);
  const identity = await getActiveIdentity();
  if ("error" in identity) {
    return poaGalleyError(op, `Active Dregg preparation identity unavailable: ${identity.error}`);
  }
  const actorHeaders = poAGalleyActorHeaders(identity.publicKeyHex);
  if (!actorHeaders) return poaGalleyError(op, "The background resolved a non-canonical active Dregg public key.");

  if (op === "status") {
    const status = await readPoAGalleyStatus(actorHeaders);
    if ("error" in status) return poaGalleyError("status", status.error);
    return { ok: true, op: "status", status };
  }

  if (typeof message.actionToken !== "string") return poaGalleyError("command", "Missing opaque Galley action token.");
  const sessionResponse = await nodeRequest<unknown>(POA_SIGNAL_NODE_CONFIG, `${POA_GALLEY_API_PATH}/session`, {
    method: "GET",
    cache: "no-store",
    headers: actorHeaders,
  });
  if (!sessionResponse.ok) return poaGalleyError("command", sessionResponse.error || "Galley session request failed");
  const session = parsePoAGalleySession(sessionResponse.data);
  if (!session) return poaGalleyError("command", "The node returned a non-canonical Galley session envelope.");
  if (!session.replay.audited) return poaGalleyError("command", "The node has not audited this journal replay.");
  const action = findPoAGalleyAction(session, message.actionToken);
  if (!action || !poAGalleyAvailableAtSequence(action.expires_after_sequence, session.sequence)) {
    return poaGalleyError("command", "That server-issued action is absent or expired. Refresh the shift.");
  }
  if (action.kind === "holder_sponsorship") {
    return poaGalleyError(
      "command",
      "Holder sponsorship is disabled until the V2 holding receipt binds the active Dregg player key.",
    );
  }
  const prepare = makePoAGalleyPrepare(action.action_token);
  if (!prepare) return poaGalleyError("command", "The server-issued action token is not canonical.");
  const preparedResponse = await nodeRequest<unknown>(POA_SIGNAL_NODE_CONFIG, `${POA_GALLEY_API_PATH}/command`, {
    method: "POST",
    body: JSON.stringify(prepare),
    cache: "no-store",
    headers: actorHeaders,
  });
  if (!preparedResponse.ok) return poaGalleyError("command", preparedResponse.error || "Galley command preparation failed");
  const prepared = parsePoAGalleyUnsignedTurn(preparedResponse.data);
  if (!prepared || prepared.federation_id !== session.federation_id ||
      !poAGalleyAvailableAtSequence(prepared.expires_after_sequence, session.sequence)) {
    return poaGalleyError("command", "The prepared turn is invalid, expired, or belongs to another federation.");
  }
  const turnBytes = decodePoAGalleyPostcard(prepared.turn_postcard_base64);
  if (!turnBytes) return poaGalleyError("command", "The prepared turn postcard is not canonical.");
  if (!await checkPoAGalleyPreparationDigest(prepared)) {
    return poaGalleyError("command", "The prepared turn postcard does not match its preparation digest.");
  }

  let pendingIntent: PoAGalleyPendingIntent | null = null;
  const signed = await signTurnV3(
    turnBytes,
    authorized.pageOrigin,
    Array.from(Uint8Array.from(prepared.federation_id.match(/.{2}/g)!, (pair) => Number.parseInt(pair, 16))),
    {
      targetConfig: POA_SIGNAL_NODE_CONFIG,
      label: "Path of Angels Galley shift",
      metadata: {
        action: "poaGalley",
        intentId: prepared.intent_id,
        preparationDigest: prepared.preparation_digest,
        dailyId: session.daily_id,
        aggregateId: session.aggregate_id,
        expiresAfterSequence: prepared.expires_after_sequence,
        platform: authorized.binding.platform,
        contextId: authorized.binding.contextId,
        manifestDigest: authorized.binding.manifestDigest,
      },
      beforeSubmit: async (signedTurnHash) => {
        if (sender.tab?.id === undefined) return "The originating Path of Angels tab no longer exists.";
        const currentTab = await chrome.tabs.get(sender.tab.id);
        const current = await authorizePoAGalleyBinding(
          authorized.binding,
          { ...sender, tab: currentTab },
        );
        if ("error" in current) return current.error;
        pendingIntent = await recordPoAGalleyPendingIntent(session, prepared, signedTurnHash);
        return pendingIntent
          ? null
          : "The signed turn could not be durably bound to this Galley intent before submission.";
      },
    },
  );
  const finalTurnHash = signed.turnId;
  if (!signed.submitted) {
    if (signed.queued) {
      if (!finalTurnHash || !/^[0-9a-f]{64}$/.test(finalTurnHash) || !pendingIntent) {
        return poaGalleyError("command", "Cipherclerk queued no canonical signed turn bound to the durable Galley intent.");
      }
      return {
        ok: true,
        op: "command",
        admission: "queued",
        observation: "not_observed",
        turnHash: finalTurnHash,
        error: signed.error,
      };
    }
    return poaGalleyError("command", signed.error || "Cipherclerk refused the Galley turn.");
  }
  if (!finalTurnHash || !/^[0-9a-f]{64}$/.test(finalTurnHash) || !pendingIntent) {
    return poaGalleyError("command", "Cipherclerk submitted no canonical signed turn bound to the durable Galley intent.");
  }

  // Finality discovery is by the exact canonical turn hash in the replayed
  // status journal.  Never synthesize a receipt URL from a hash.
  let latestStatus: PoAGalleyStatus | undefined;
  for (let attempt = 0; attempt < 7; attempt += 1) {
    const observed = await readPoAGalleyStatus(actorHeaders);
    if (!("error" in observed) && observed.federation_id === session.federation_id &&
        observed.daily_id === session.daily_id && observed.aggregate_id === session.aggregate_id) {
      latestStatus = observed;
      const event = findPoAGalleyEvent(observed, finalTurnHash);
      if (event) {
        if (!await checkPoAGalleyReceiptPostcardSha256(event)) {
          return poaGalleyError("command", "The matching journal receipt postcard failed its adjacent SHA-256 checksum.");
        }
        return {
          ok: true,
          op: "command",
          admission: "submitted",
          observation: "receipt_observed",
          turnHash: finalTurnHash,
          event,
          status: observed,
        };
      }
    }
    if (attempt < 6) await new Promise<void>((resolve) => setTimeout(resolve, 250));
  }
  return {
    ok: true,
    op: "command",
    admission: "submitted",
    observation: "not_observed",
    turnHash: finalTurnHash,
    ...(latestStatus ? { status: latestStatus } : {}),
  };
}

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

    case "dregg:poll": {
      const origin =
        (message._origin as string) ||
        (sender?.tab?.url ? new URL(sender.tab.url).origin : undefined) ||
        "unknown";
      const req: PollPortRequest = {
        op: message.op as PollPortRequest["op"],
        uri: message.uri as string,
        turn: message.turn as string,
        arg: Number(message.arg ?? 0),
      } as PollPortRequest;
      const result = await getPollEngine().handle(req, origin);
      return { id: message.id, result };
    }

    case "dregg:cell": {
      // <dregg-embed> / <dregg-transclude>: resolve a whole child cell (five states,
      // engine-side darkening) or a value quote (fail-closed) over the real Netlayer.
      // The engine makes the cap/cycle decision — the page never sees the bytes.
      const req: CellPortRequest = {
        op: message.op as CellPortRequest["op"],
        uri: message.uri as string,
        pin: message.pin,
        ancestors: message.ancestors,
      } as CellPortRequest;
      const result = await getCellEngine().handle(req);
      return { id: message.id, result };
    }

    case "dregg:doc": {
      // <dregg-doc>: resolve / render (ConflictView — both alternatives) / stitch /
      // resolveConflict (stage a pick) / publish (a real verified turn, consent
      // BEFORE commit) / verify (the stranger's light-client re-check). Conflict is
      // never silently resolved or hidden — only a consented publish collapses it.
      const origin =
        (message._origin as string) ||
        (sender?.tab?.url ? new URL(sender.tab.url).origin : undefined) ||
        "unknown";
      const req: DocPortRequest = {
        op: message.op as DocPortRequest["op"],
        uri: message.uri as string,
        choice: Number(message.choice ?? 0),
      } as DocPortRequest;
      const result = await getDocEngine().handle(req, origin);
      return { id: message.id, result };
    }

    case "dregg:doctext": {
      // <dregg-doc editable>: resolveText / renderText / applyEdit (diff a keystroke
      // into the minimal patch) / publishText (a real verified turn, consent BEFORE
      // commit) / verifyText (the stranger's light-client re-check). An unpublished
      // edit is a first-class `dirty` state — surfaced, never an unverified render.
      const origin =
        (message._origin as string) ||
        (sender?.tab?.url ? new URL(sender.tab.url).origin : undefined) ||
        "unknown";
      const req: DocTextPortRequest = {
        op: message.op as DocTextPortRequest["op"],
        uri: message.uri as string,
        text: message.text as string,
      } as DocTextPortRequest;
      const result = await getDocTextEngine().handle(req, origin);
      return { id: message.id, result };
    }

    case "dregg:story": {
      // <dregg-story>: resolveStory / renderStory (passage prose + choices) /
      // chooseChoice (a real verified turn — consent BEFORE the advance, fail-closed
      // on a gated/invalid choice) / verifyStory (the stranger's receipt-chain replay).
      // READ + VERIFY need no custody; choosing is a custody write.
      const origin =
        (message._origin as string) ||
        (sender?.tab?.url ? new URL(sender.tab.url).origin : undefined) ||
        "unknown";
      const req: StoryPortRequest = {
        op: message.op as StoryPortRequest["op"],
        uri: message.uri as string,
        index: Number(message.index ?? 0),
      } as StoryPortRequest;
      const result = await getStoryEngine().handle(req, origin);
      return { id: message.id, result };
    }

    case "dregg:descent": {
      // <dregg-descent>: openDescent / renderDescent (room prose + moves + state) /
      // advanceMove (a real cap-gated verified turn on the in-tab executor — fail-closed
      // in-band on a gated/invalid move, NO consent: the run is private + local) /
      // verifyDescent (the stranger's replay against a fresh, identically-seeded day) /
      // settleDescent (the OPT-IN publish hook — a named seam until the leaderboard leg).
      const origin =
        (message._origin as string) ||
        (sender?.tab?.url ? new URL(sender.tab.url).origin : undefined) ||
        "unknown";
      const req: DescentPortRequest = {
        op: message.op as DescentPortRequest["op"],
        uri: message.uri as string,
        index: Number(message.index ?? 0),
      } as DescentPortRequest;
      const result = await getDescentEngine().handle(req, origin);
      return { id: message.id, result };
    }

    case "dregg:poa": {
      // Never trust a page-provided href. `sender.tab.url` is supplied by the
      // browser and binds recognition to the tab that actually sent the request.
      const pageUrl = sender?.tab?.url;
      if (!pageUrl) return { id: message.id, error: "Path of Angels context requires a browser tab." };
      const supplied = message.context && typeof message.context === "object"
        ? message.context as Record<string, unknown>
        : {};
      const req: PoACompanionRequest = {
        op: "openContext",
        context: {
          href: pageUrl,
          ...(typeof supplied.channelHint === "string" ? { channelHint: supplied.channelHint } : {}),
        },
      };
      return { id: message.id, result: await getPoAEngine().handle(req) };
    }

    case "dregg:poaGalley":
      return { id: message.id, result: await handlePoAGalley(message, sender) };

    case "dregg:canAuthorize":
      return { id: message.id, result: await canAuthorize(message.request as AuthorizeRequest) };

    case "dregg:getCapabilities":
      return { id: message.id, result: await getCapabilities() };

    case "dregg:getState":
      return { id: message.id, result: await getCipherclerkState() };

    case "dregg:getLog": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      return { id: message.id, result: await getLog() };
    }

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
      const result = await recoverFromMnemonic(
        message.mnemonic as string,
        (message.bip39Passphrase as string) || "",
        (message.walletPassphrase as string) || (message.passphrase as string) || "",
      );
      return { id: message.id, result };
    }

    case "dregg:beginOnboarding": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      return { id: message.id, result: await beginOnboarding() };
    }

    case "dregg:completeOnboarding": {
      if (!isExtensionPopup(sender)) return { id: message.id, error: "Only available from extension popup." };
      const result = await completeOnboarding(
        (message.passphrase as string) || "",
        (message.confirmMnemonic as string) || "",
      );
      if (result.success) notifySubscribers("ready", { locked: false });
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
      const result = await fulfillIntent(message.intentId as string, (message.tokenId as string) || null);
      resetLockTimer();
      return { id: message.id, result };
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

    // Devnet account view (node-API path; routes through the verified executor)
    case "dregg:nodeIdentity":
      return { id: message.id, result: await nodeIdentity() };

    case "dregg:faucetFund":
      return {
        id: message.id,
        result: await faucetFund(
          message.cellId as string,
          (message.amount as number) ?? 0,
          message.publicKey as string | undefined,
        ),
      };

    case "dregg:submitJsonTurn":
      return {
        id: message.id,
        result: await submitJsonTurn(
          message.spec as {
            agent: string;
            nonce: number;
            fee: number;
            memo?: string;
            effects: Array<Record<string, unknown>>;
          },
        ),
      };

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
      if (!cc.secretKey) return { id: message.id, error: "Cipherclerk secret key not available" };
      if (cc.needsPassphraseSetup) {
        return { id: message.id, error: "Set a cipherclerk passphrase before issuing bearer capabilities." };
      }
      // The WASM `create_bearer_cap` first argument is the delegator's 32-byte
      // Ed25519 *signing seed* (secret), NOT a pubkey: it does
      // `SigningKey::from_bytes(&seed).sign(&binding)`. Passing the public key
      // would silently derive an unrelated (and publicly reconstructable)
      // signing key, issuing the cap under a garbage delegator identity. Hex the
      // real secret seed so the cap is signed by — and bound to — the user's
      // actual key (its `delegator_pubkey` then equals `cc.publicKey`).
      const delegatorKeyHex = Array.from(cc.secretKey).map(b => b.toString(16).padStart(2, "0")).join("");
      // The WASM expiry parameter is a u64 (Unix seconds; 0 = no expiry) and
      // crosses the wasm-bindgen boundary as a BigInt — a plain JS number throws
      // "Cannot convert N to a BigInt". Coerce here (the popup can only send a
      // JSON number over runtime messaging, so the fix belongs at the call site).
      const result = w.create_bearer_cap(delegatorKeyHex, message.targetCellHex as string, message.action as string, BigInt((message.expiry as number) || 0));
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
      const submitResult = await signAndSubmitBuiltTurn({
        turnBytes: new Uint8Array(turnData.turn_bytes),
        secretKey: cc.secretKey,
        publicKey: cc.publicKey,
        label: "create cell from factory",
        metadata: {
          action: "createFromFactory",
          childVk: turnData.child_vk,
          paramHash: turnData.param_hash,
          factoryVk: turnData.factory_vk,
          agentCellId: turnData.agent_cell_id,
        },
      });
      if ("error" in submitResult) {
        return { id: message.id, error: `Failed to sign factory turn: ${submitResult.error}` };
      }
      const submit = submitResult.submit;
      turnData.turn_id = submitResult.turnId;

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
      if (cc.needsPassphraseSetup) {
        return { id: message.id, error: "Set a cipherclerk passphrase before running a peer exchange." };
      }
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

    // Proof composition (shielded membership + range + conservation)
    case "dregg:composeProofs": {
      // The STARK Merkle-membership seam is now SOUND: the wasm crate migrated
      // off the forgeable linear `MerkleStarkAir` onto a REAL arity-4 Poseidon2
      // Merkle descriptor (`merkle-membership::poseidon2-4ary-general-depthN`),
      // proven by `prove_vm_descriptor2` and checked by the deployed
      // `verify_vm_descriptor2` — a genuine member ACCEPTS, and a forged/tampered
      // claim is REJECTED (host-probe: `probe-membership.mjs`). So composition is
      // re-enabled and routes to `compose_and_verify_proofs`, which discharges
      // each tagged proof against its canonical verifier (membership via the
      // Poseidon2 descriptor consumer, range via Bulletproofs, conservation via
      // the Schnorr excess) and returns the REAL boolean composition — never a
      // BLAKE3 content-hash stand-in.
      requireWasm("composeProofs");
      const w = wasm!;
      const proofs = (message.proofs as Array<Record<string, unknown>>) || [];
      const mode = (message.mode as string) || "and";
      // Map the page shape { proofJson, publicInputs } onto the wasm's tagged
      // envelope; a bare `proofJson` is a membership (Ir2ProofEnvelope) proof.
      const tagged = proofs.map((p) => {
        if (p.kind) return p; // already a tagged {kind, ...} envelope
        return { kind: "membership", proof_json: p.proofJson ?? p.proof_json };
      });
      try {
        const res = w.compose_and_verify_proofs(JSON.stringify(tagged), mode) as {
          composed_proof: string; mode: string; input_count: number; valid: boolean;
          results?: Array<{ kind: string; valid: boolean; error: string | null }>;
        };
        return {
          id: message.id,
          result: {
            composedProof: res.composed_proof,
            mode: res.mode,
            inputCount: res.input_count,
            valid: res.valid,
            results: res.results ?? [],
          },
        };
      } catch (e: unknown) {
        return { id: message.id, error: (e as Error).message || "compose failed" };
      }
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
      if (cc.needsPassphraseSetup) {
        return { id: message.id, error: "Set a cipherclerk passphrase before posting an encrypted intent." };
      }
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
      // The turn's deadline is a BLOCK HEIGHT: the node's latest_height plus the default
      // horizon (dregg_turn::DEFAULT_TURN_VALIDITY_HORIZON_BLOCKS). It is bound into the turn
      // hash the conservation proof covers, so it is decided before the turn is built.
      const heightResp = await nodeRequest<{ latest_height?: number }>(nodeConfig, "/status");
      if (!heightResp.ok || typeof heightResp.data?.latest_height !== "number") {
        return {
          id: message.id,
          error: `private transfer needs the node's latest_height for its deadline: ${
            heightResp.ok ? "/status carries no latest_height" : heightResp.error
          }`,
        };
      }
      const validUntil = heightResp.data.latest_height + TURN_VALIDITY_HORIZON_BLOCKS;
      try {
        const result = w.cipherclerk_private_transfer(JSON.stringify({
          sender_privkey: cc.secretKey,
          amount,
          asset_type: assetTypeU64,
          recipient_meta: {
            spend_pubkey: recipientMeta.spendPubkey,
            view_pubkey: recipientMeta.viewPubkey,
          },
          valid_until: validUntil,
        }));
        const submitResult = await signAndSubmitBuiltTurn({
          turnBytes: new Uint8Array(result.turn_bytes),
          secretKey: cc.secretKey,
          publicKey: cc.publicKey,
          label: "private transfer",
          metadata: { action: "privateTransfer", amount, assetType: assetTypeU64 },
        });
        if ("error" in submitResult) {
          return { id: message.id, error: `Failed to sign private transfer: ${submitResult.error}` };
        }
        const submit = submitResult.submit;
        result.turn_id = submitResult.turnId;
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

    // Turn v3: pre-built encoded Turn bytes signed by the cipherclerk
    // (authorization-first: the explain rendering is confirmed by the user
    // before the signature leaves the extension).
    case "dregg:signTurnV3": {
      const turnBytes = new Uint8Array(message.turnBytes as number[]);
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      // Optional federation domain — handed through RAW; signTurnV3 itself
      // revalidates with exact checks (absence = legacy zero domain).
      const result = await signTurnV3(turnBytes, origin, message.federationId);
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:getActiveIdentity": {
      let tabOrigin: string | undefined;
      try {
        tabOrigin = sender.tab?.url ? new URL(sender.tab.url).origin : undefined;
      } catch {
        tabOrigin = undefined;
      }
      const bridgedOrigin = typeof message._origin === "string" ? message._origin : undefined;
      if (!tabOrigin || bridgedOrigin !== tabOrigin) {
        return { id: message.id, error: "Active identity requires an origin-bound page request." };
      }
      const identity = await getActiveIdentity();
      return "error" in identity
        ? { id: message.id, error: identity.error }
        : { id: message.id, result: identity };
    }

    case "dregg:submitPoaSignalClaim": {
      let tabOrigin: string | undefined;
      try {
        tabOrigin = sender?.tab?.url ? new URL(sender.tab.url).origin : undefined;
      } catch {
        tabOrigin = undefined;
      }
      const bridgedOrigin = typeof message._origin === "string" ? message._origin : undefined;
      // Require both browser-owned tab authority and the content-script bridge
      // to agree. A direct runtime message, forged `_origin`, or non-beta tab
      // never reaches state reads, signing, or a permission/consent surface.
      if (tabOrigin !== POA_SIGNAL_BETA_ORIGIN || bridgedOrigin !== POA_SIGNAL_BETA_ORIGIN) {
        return {
          id: message.id,
          result: poaSignalRefused("PoA Signal claims require the exact authenticated beta tab"),
        };
      }
      const result = await submitPoaSignalClaim(message.claim, tabOrigin);
      if (result.admission !== "refused") resetLockTimer();
      return { id: message.id, result };
    }

    // Offering turn (G1 rung 2): sign a dreggnet-offerings move with the
    // extension-held identity key. Consent-gated; the typed failure codes
    // ride in `result` so the page can distinguish a user decline from a
    // signature failure.
    case "dregg:signOfferingTurn": {
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const result = await signOfferingTurn(message.params, origin);
      if (result.ok) resetLockTimer();
      return { id: message.id, result };
    }

    // Judged Signal session: sign one of exactly two documented session
    // statements with the player key. Consent-gated; typed failure codes ride
    // in `result` so the page distinguishes a decline from a signing failure.
    case "dregg:signSignalSession": {
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const result = await signSignalSession(message.params, origin);
      if (result.ok) resetLockTimer();
      return { id: message.id, result };
    }

    // Named identity profiles (mirrors `dregg id create / list / use`).
    case "dregg:listProfiles":
      return { id: message.id, result: await listProfiles() };

    case "dregg:createProfile": {
      const result = await createProfile(String(message.name || ""));
      resetLockTimer();
      return { id: message.id, result };
    }

    case "dregg:useProfile": {
      const result = await useProfile(String(message.name || ""));
      resetLockTimer();
      return { id: message.id, result };
    }

    // Cap-account login to the live cloud (challenge → sign → session).
    case "dregg:getLoginStatus":
      return { id: message.id, result: await getLoginStatus() };

    case "dregg:capLogin": {
      const result = await capLogin(message.profile ? String(message.profile) : undefined);
      return { id: message.id, result };
    }

    case "dregg:capLogout":
      return { id: message.id, result: await capLogout() };

    // Recent receipts from the node's SSE stream; reading clears the badge.
    case "dregg:getRecentReceipts":
      return { id: message.id, result: await getRecentReceipts() };

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

    // ── EVM signing leg (secp256k1) ──
    case "dregg:evmGetAddress": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      resetLockTimer();
      return { id: message.id, result: { address: idr.id.address } };
    }

    case "dregg:evmPersonalSign": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const msg = typeof message.message === "string"
        ? message.message
        : new TextDecoder().decode(new Uint8Array((message.message as number[]) || []));
      const digest = evmPersonalSignDigest(new TextEncoder().encode(msg));
      const confirmed = await showTurnConfirmation({
        explanation: `EVM personal_sign (secp256k1)\n\naddress: ${idr.id.address}\n\nmessage:\n${msg}`,
        turnId: `evm-personal-sign:${evmHex0x(digest)}`,
        origin,
        hasUnknown: false,
      });
      if (!confirmed) return { id: message.id, error: "User declined the EVM signature" };
      const sig = evmPersonalSign(idr.id.privateKey, msg);
      resetLockTimer();
      return { id: message.id, result: { address: idr.id.address, signature: sig.signature, v: sig.v, digest: sig.digest } };
    }

    case "dregg:evmSignTypedData": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const domain = (message.domain as Eip712Domain) || {};
      const types = (message.types as Eip712Types) || {};
      const primaryType = String(message.primaryType || "");
      const data = (message.messageData as Record<string, unknown>) || {};
      let digest: Uint8Array;
      try {
        digest = evmEip712Digest(domain, types, primaryType, data);
      } catch (e: unknown) {
        return { id: message.id, error: `EIP-712: ${(e as Error).message}` };
      }
      const confirmed = await showTurnConfirmation({
        explanation: `EVM EIP-712 sign (secp256k1)\n\naddress: ${idr.id.address}\ntype: ${primaryType}\ndomain: ${domain.name ?? "?"} v${domain.version ?? "?"} chain ${domain.chainId ?? "?"}\ncontract: ${domain.verifyingContract ?? "-"}\n\n${JSON.stringify(data, null, 2)}`,
        turnId: `evm-712:${evmHex0x(digest)}`,
        origin,
        hasUnknown: false,
      });
      if (!confirmed) return { id: message.id, error: "User declined the EVM signature" };
      const sig = evmSignTypedData(idr.id.privateKey, domain, types, primaryType, data);
      resetLockTimer();
      return { id: message.id, result: { address: idr.id.address, signature: sig.signature, v: sig.v, digest: sig.digest } };
    }

    // ── fhEgg sealed-bid commit → reveal ceremony ──
    case "dregg:sealedBidCommit": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const auctionId = Number(message.auctionId ?? 0);
      const order = (message.order as Record<string, unknown>) || {};
      const chainId = Number(message.chainId ?? 0);
      const verifyingContract = String(message.verifyingContract ?? "0x0000000000000000000000000000000000000000");
      const deadline = Number(message.deadline ?? 0);
      const salt = new Uint8Array(32);
      crypto.getRandomValues(salt);
      let commit;
      try {
        commit = buildCommitment(idr.id.address, order, salt);
      } catch (e: unknown) {
        return { id: message.id, error: `sealed-bid commit: ${(e as Error).message}` };
      }
      const confirmed = await showTurnConfirmation({
        explanation: `fhEgg SEALED BID — COMMIT (auction #${auctionId})\n\nbidder: ${idr.id.address}\ncommitment: ${commit.commitment}\ndeadline: ${deadline || "none"}\n\norder (hidden until reveal):\n${JSON.stringify(order, null, 2)}`,
        turnId: `sealed-commit:${commit.commitment}`,
        origin,
        hasUnknown: false,
      });
      if (!confirmed) return { id: message.id, error: "User declined the sealed-bid commit" };
      const domain = sealedAuctionDomain(chainId, verifyingContract);
      const sig = evmSignTypedData(idr.id.privateKey, domain, SEALED_BID_TYPES, "SealedBid", {
        auctionId, commitment: commit.commitment, deadline,
      });
      await storeSealedOpening(auctionId, {
        commitment: commit.commitment, orderHash: commit.orderHash, salt: commit.salt,
        order, bidder: idr.id.address, chainId, verifyingContract, deadline, createdAt: Date.now(),
      });
      resetLockTimer();
      return {
        id: message.id,
        result: {
          phase: "commit", auctionId, bidder: idr.id.address,
          commitment: commit.commitment, signature: sig.signature, digest: sig.digest,
          escrow: { domain, primaryType: "SealedBid", message: { auctionId, commitment: commit.commitment, deadline } },
        },
      };
    }

    case "dregg:sealedBidReveal": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      const auctionId = Number(message.auctionId ?? 0);
      const opening = await loadSealedOpening(auctionId);
      if (!opening) return { id: message.id, error: `no stored sealed bid for auction #${auctionId}` };
      const check = checkReveal(opening.bidder, opening.order, opening.salt, opening.commitment);
      if (!check.ok) {
        return { id: message.id, error: "stored opening does not bind to its commitment (corrupt state)" };
      }
      const domain = sealedAuctionDomain(opening.chainId, opening.verifyingContract);
      const sig = evmSignTypedData(idr.id.privateKey, domain, REVEAL_BID_TYPES, "RevealBid", {
        auctionId, orderHash: opening.orderHash, salt: opening.salt,
      });
      resetLockTimer();
      return {
        id: message.id,
        result: {
          phase: "reveal", auctionId, bidder: opening.bidder, order: opening.order,
          salt: opening.salt, orderHash: opening.orderHash, commitment: opening.commitment,
          bindsCommitment: check.ok, signature: sig.signature, digest: sig.digest,
          escrow: { domain, primaryType: "RevealBid", message: { auctionId, orderHash: opening.orderHash, salt: opening.salt } },
        },
      };
    }

    // ── The DreggLaunchpad: a sealed bid on the REAL launch contract ──
    case "dregg:launchpadCommit": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;

      let pad: DreggLaunchpadClient;
      let built: ReturnType<DreggLaunchpadClient["commitBid"]>;
      let launchId: string;
      try {
        pad = launchpadFromRequest(message as Record<string, unknown>);
        launchId = String(message.launchId ?? "");
        if (!launchId) throw new Error("a launchId is required");
        // A fresh 32-byte hiding nonce per bid — the thing that makes the seal
        // hiding, and the thing that is unrecoverable if the opening is lost.
        const salt = new Uint8Array(32);
        crypto.getRandomValues(salt);
        built = pad.commitBid({
          launchId,
          price: BigInt(String(message.price ?? "")),
          qty: BigInt(String(message.qty ?? "")),
          salt: evmHex0x(salt),
          bidder: idr.id.address,
          proof: message.proof ? String(message.proof) : undefined,
        });
      } catch (e: unknown) {
        return { id: message.id, error: `launchpad commit: ${(e as Error).message}` };
      }

      // Refuse a second commit BEFORE prompting: the launchpad takes one
      // commitment per address, so a second local opening could only overwrite
      // the one that opens an already-escrowed bid.
      const already = await launchpadOpenings.get(launchpadRefOf(pad, launchId, idr.id.address));
      if (already) {
        return {
          id: message.id,
          error:
            `launchpad commit: this wallet already has a stored bid on launch ${launchId} `
            + `(sealed ${already.seal}). The launchpad accepts ONE commitment per address `
            + `(AlreadyCommitted); reveal the stored bid instead.`,
        };
      }

      const deposit = BigInt(built.opening.deposit);
      const confirmed = await showTurnConfirmation({
        explanation:
          `DREGG LAUNCHPAD — SEALED BID COMMIT (launch #${launchId})\n\n`
          + `bidder: ${idr.id.address}\nlaunchpad: ${pad.address}\nchain: ${pad.chainId}\n\n`
          + `price: ${built.opening.price} wei per whole token\nquantity: ${built.opening.qty} whole tokens\n`
          + `ESCROW NOW: ${deposit} wei (price × qty — your maximum payment)\n\n`
          + `Only the sealed hash ${built.seal.seal} goes on-chain now; nothing about this bid is `
          + `observable until you reveal it. Every winner pays the SAME uniform clearing price and the `
          + `rest of the escrow is refunded at settlement.\n\n`
          + `You MUST reveal during the reveal window or this bid does not clear.`,
        turnId: `launchpad-commit:${built.seal.seal}`,
        origin,
        hasUnknown: false,
      });
      if (!confirmed) return { id: message.id, error: "User declined the launchpad commit" };

      // PERSIST THE OPENING FIRST. Before a signature exists, before anything is
      // returnable, before it could possibly be broadcast — a commit whose
      // opening was never written is an unrevealable bid.
      try {
        await launchpadOpenings.put(built.opening);
      } catch (e: unknown) {
        return { id: message.id, error: `launchpad commit: ${(e as Error).message}` };
      }

      resetLockTimer();
      return {
        id: message.id,
        result: {
          phase: "commit",
          launchId,
          launchpad: pad.address,
          chainId: pad.chainId,
          bidder: idr.id.address,
          seal: built.seal.seal,
          price: built.opening.price,
          qty: built.opening.qty,
          deposit: built.opening.deposit,
          openingStored: true,
          ...signedOrUnsignedTx(idr.id.privateKey, built.tx, txGasFromRequest(message as Record<string, unknown>)),
        },
      };
    }

    case "dregg:launchpadReveal": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;

      let pad: DreggLaunchpadClient;
      let launchId: string;
      try {
        pad = launchpadFromRequest(message as Record<string, unknown>);
        launchId = String(message.launchId ?? "");
        if (!launchId) throw new Error("a launchId is required");
      } catch (e: unknown) {
        return { id: message.id, error: `launchpad reveal: ${(e as Error).message}` };
      }

      // The ONLY route to a reveal. A missing opening is unrecoverable by
      // construction and a corrupt one would earn `BidMismatch` on-chain; both
      // are reported by name, with the escrow's refund path, and NEITHER is
      // swallowed into a quiet "nothing to reveal".
      let opening: LaunchpadOpening;
      try {
        opening = await launchpadOpenings.requireForReveal(
          launchpadRefOf(pad, launchId, idr.id.address),
        );
      } catch (e: unknown) {
        if (e instanceof OpeningLostError || e instanceof OpeningTamperedError) {
          return { id: message.id, error: `launchpad reveal: ${e.message}` };
        }
        return { id: message.id, error: `launchpad reveal: ${(e as Error).message}` };
      }

      let tx: TxRequest;
      try {
        tx = pad.revealBid(opening).tx;
      } catch (e: unknown) {
        return { id: message.id, error: `launchpad reveal: ${(e as Error).message}` };
      }

      const confirmed = await showTurnConfirmation({
        explanation:
          `DREGG LAUNCHPAD — REVEAL YOUR SEALED BID (launch #${launchId})\n\n`
          + `bidder: ${opening.bidder}\nlaunchpad: ${pad.address}\nchain: ${pad.chainId}\n\n`
          + `price: ${opening.price} wei per whole token\nquantity: ${opening.qty} whole tokens\n`
          + `escrowed: ${opening.deposit} wei\n\n`
          + `This opens the commitment ${opening.seal} you escrowed. Your bid becomes public and `
          + `joins the book that clears at ONE uniform price. The opening has been checked to bind: `
          + `the launchpad will recompute the same hash.`,
        turnId: `launchpad-reveal:${opening.seal}`,
        origin,
        hasUnknown: false,
      });
      if (!confirmed) return { id: message.id, error: "User declined the launchpad reveal" };

      resetLockTimer();
      return {
        id: message.id,
        result: {
          phase: "reveal",
          launchId,
          launchpad: pad.address,
          chainId: pad.chainId,
          bidder: opening.bidder,
          price: opening.price,
          qty: opening.qty,
          salt: opening.salt,
          seal: opening.seal,
          bindsSeal: true,
          ...signedOrUnsignedTx(idr.id.privateKey, tx, txGasFromRequest(message as Record<string, unknown>)),
        },
      };
    }

    case "dregg:launchpadStatus": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      let pad: DreggLaunchpadClient;
      try {
        pad = launchpadFromRequest(message as Record<string, unknown>);
      } catch (e: unknown) {
        return { id: message.id, error: `launchpad status: ${(e as Error).message}` };
      }
      const launchId = message.launchId !== undefined ? String(message.launchId) : null;

      // The local view of one's own bids: is the opening still here, i.e. is this
      // bid still revealable at all? On-chain phase/fill state is a read this
      // background cannot make (no EVM RPC) — the dapp reads that itself.
      if (launchId === null) {
        const mine = await launchpadOpenings.list({ chainId: pad.chainId, launchpad: pad.address, bidder: idr.id.address });
        return {
          id: message.id,
          result: {
            bidder: idr.id.address,
            launchpad: pad.address,
            chainId: pad.chainId,
            // The salt is deliberately NOT listed: it is the hiding nonce, and it
            // leaves the extension only inside the reveal transaction itself.
            bids: mine.map(o => ({
              launchId: o.launchId, seal: o.seal, price: o.price, qty: o.qty,
              deposit: o.deposit, createdAt: o.createdAt, hasOpening: true, revealable: true,
            })),
          },
        };
      }

      const ref = launchpadRefOf(pad, launchId, idr.id.address);
      const opening = await launchpadOpenings.get(ref);
      if (!opening) {
        // HONEST: if this wallet did commit, the bid is gone — say exactly that
        // and point at the escrow's two permissionless exits.
        const lost = new OpeningLostError(ref);
        return {
          id: message.id,
          result: {
            launchId, launchpad: pad.address, chainId: pad.chainId, bidder: idr.id.address,
            hasOpening: false,
            revealable: false,
            unrecoverable: true,
            explanation: lost.message,
            recovery: { ...lost.recovery, refundGraceSeconds: REFUND_GRACE_SECONDS },
          },
        };
      }
      return {
        id: message.id,
        result: {
          launchId, launchpad: pad.address, chainId: pad.chainId, bidder: idr.id.address,
          hasOpening: true, revealable: true,
          seal: opening.seal, price: opening.price, qty: opening.qty,
          deposit: opening.deposit, createdAt: opening.createdAt,
        },
      };
    }

    case "dregg:launchpadReclaimTx": {
      const idr = await requireEvmIdentity();
      if (!idr.ok) return { id: message.id, error: idr.error };
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      let pad: DreggLaunchpadClient;
      let launchId: string;
      let tx: TxRequest;
      try {
        pad = launchpadFromRequest(message as Record<string, unknown>);
        launchId = String(message.launchId ?? "");
        if (!launchId) throw new Error("a launchId is required");
        tx = pad.reclaimEscrowTx({ launchId, from: idr.id.address });
      } catch (e: unknown) {
        return { id: message.id, error: `launchpad reclaim: ${(e as Error).message}` };
      }

      const confirmed = await showTurnConfirmation({
        explanation:
          `DREGG LAUNCHPAD — RECLAIM YOUR ESCROW (launch #${launchId})\n\n`
          + `bidder: ${idr.id.address}\nlaunchpad: ${pad.address}\nchain: ${pad.chainId}\n\n`
          + `The stuck-launch backstop: if this launch never cleared, your full escrow is `
          + `permissionlessly reclaimable once it is past revealEnd + ${REFUND_GRACE_SECONDS}s `
          + `(REFUND_GRACE). If it is not yet reclaimable the chain refuses this by name `
          + `(RefundNotYetAvailable); if the launch DID clear, settleBid is the exit instead `
          + `(LaunchAlreadyCleared).`,
        turnId: `launchpad-reclaim:${pad.chainId}:${pad.address}:${launchId}`,
        origin,
        hasUnknown: false,
      });
      if (!confirmed) return { id: message.id, error: "User declined the launchpad escrow reclaim" };

      resetLockTimer();
      return {
        id: message.id,
        result: {
          phase: "reclaim",
          launchId, launchpad: pad.address, chainId: pad.chainId, bidder: idr.id.address,
          ...signedOrUnsignedTx(idr.id.privateKey, tx, txGasFromRequest(message as Record<string, unknown>)),
        },
      };
    }

    // ── DrEX order routed THROUGH the extension (dregg-native sealed order) ──
    case "dregg:drexPlaceOrder": {
      requireWasm("drexPlaceOrder");
      const w = wasm!;
      const cc = await loadState();
      if (cc.locked) return { id: message.id, error: "Cipherclerk is locked" };
      if (!cc.secretKey) return { id: message.id, error: "Cipherclerk secret key not available" };
      const origin = (message._origin as string) || (sender?.tab?.url && new URL(sender.tab.url).origin) || undefined;
      const order = (message.order as Record<string, unknown>) || {};
      const holdings = message.holdings != null ? Number(message.holdings) : null;
      const offer = message.offer != null ? Number(message.offer) : null;
      const traderId = message.traderId != null ? String(message.traderId) : null;
      const ring = (message.ring as string[]) || null;
      const orderId = evmHex0x(sealedOrderHash(order));
      const confirmed = await showTurnConfirmation({
        explanation: `DrEX place order (dregg-native, sealed key)\n\norder:\n${JSON.stringify(order, null, 2)}${holdings != null && offer != null ? `\n\nsolvency: holdings ${holdings} ≥ offer ${offer}` : ""}${ring ? `\n\neligibility: blinded ring membership (ring size ${ring.length})` : ""}`,
        turnId: `drex-order:${orderId}`,
        origin,
        hasUnknown: false,
      });
      if (!confirmed) return { id: message.id, error: "User declined the DrEX order" };
      // STEP A — sign the order-turn with the SEALED key (real Ed25519 over the canonical action).
      const spec = JSON.stringify({
        sender_privkey: Array.from(cc.secretKey),
        method: "drex_place_order",
        memo_json: JSON.stringify(order),
      });
      const turn = w.cipherclerk_make_action_turn(spec);
      const result: Record<string, unknown> = {
        turnId: turn.turn_id, agentCell: turn.agent_cell_id, orderHash: orderId, routedThroughExtension: true,
      };
      // STEP B — optional REAL solvency (conservation) proof bound to the order-turn id.
      if (holdings != null && offer != null) {
        if (holdings < offer) {
          result.solvency = { ok: false, reason: "insufficient holdings — cannot construct a non-negative change output (fail-closed)" };
        } else {
          const randHex = (): string => {
            const b = new Uint8Array(32); crypto.getRandomValues(b);
            return Array.from(b).map(x => x.toString(16).padStart(2, "0")).join("");
          };
          const inputs = JSON.stringify([{ value: holdings, blinding_hex: randHex() }]);
          const outputs = JSON.stringify([
            { value: offer, blinding_hex: randHex() },
            { value: holdings - offer, blinding_hex: randHex() },
          ]);
          const proof = w.prove_conservation(inputs, outputs, turn.turn_id);
          const v = w.verify_conservation_proof(
            JSON.stringify(proof.input_commitments),
            JSON.stringify(proof.output_commitments),
            JSON.stringify(proof.proof),
            proof.message_hex,
            JSON.stringify(proof.output_range_proofs),
          );
          result.solvency = { ok: v.valid && v.range_proofs_checked, valid: v.valid, rangeProofsChecked: v.range_proofs_checked, boundTo: turn.turn_id };
        }
      }
      // STEP C — optional REAL blinded ring-membership (sealed-bid trader anonymity).
      if (ring && traderId) {
        const r = w.prove_anonymous_membership(traderId, JSON.stringify(ring));
        result.eligibility = { presentationTag: r.presentation_tag_full_hex, setRoot: r.set_root, ringSize: r.ring_size };
      }
      resetLockTimer();
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
    // Queue turns that need the wasm world until it is ready (the SW may still
    // be instantiating on wake) so a quiet-upgrade poll never fails closed on a
    // transient cold start rather than a real verification failure.
    if ((message.type === "dregg:authorize" || message.type === "dregg:poll" ||
         message.type === "dregg:cell" || message.type === "dregg:doc" ||
         message.type === "dregg:doctext" || message.type === "dregg:story" ||
         message.type === "dregg:descent" || message.type === "dregg:poaGalley") && !ready) {
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
// Receipt stream — the node's SSE nervous-system edge
// (`GET /api/events/stream`, node/src/events.rs).
//
// MV3 service workers have no EventSource, so this consumes the stream via
// fetch + ReadableStream through the parser in src/sse.ts. Each event's
// `id:` is the node's receipt-chain index; on reconnect we send
// `Last-Event-ID` so the node resumes from the next entry (at-least-once
// across reconnects — the chain, not the broadcast, is the source of truth).
// The stream is filtered to the ACTIVE profile's cell (`?cell=<hex>`) when
// the wasm cell-id helper is available; receipts surface as a toolbar badge
// count plus the popup's recent-receipts list.
// ---------------------------------------------------------------------------

let receiptStreamAbort: AbortController | null = null;
let receiptStreamBackoffMs = 1000;
let receiptStreamTimer: ReturnType<typeof setTimeout> | null = null;
let recentReceipts: ReceiptEventSummary[] = [];
let receiptLastEventId: string | null = null;
let unseenReceiptCount = 0;
let recentReceiptsLoaded = false;

async function loadRecentReceipts(): Promise<void> {
  if (recentReceiptsLoaded) return;
  recentReceiptsLoaded = true;
  const stored = await chrome.storage.local.get(RECENT_RECEIPTS_KEY);
  const data = stored[RECENT_RECEIPTS_KEY] as {
    receipts?: ReceiptEventSummary[];
    lastEventId?: string | null;
    unseen?: number;
  } | undefined;
  if (data) {
    recentReceipts = Array.isArray(data.receipts) ? data.receipts : [];
    receiptLastEventId = data.lastEventId ?? null;
    unseenReceiptCount = data.unseen || 0;
  }
  updateReceiptBadge();
}

async function persistRecentReceipts(): Promise<void> {
  await chrome.storage.local.set({
    [RECENT_RECEIPTS_KEY]: {
      receipts: recentReceipts,
      lastEventId: receiptLastEventId,
      unseen: unseenReceiptCount,
    },
  });
}

function updateReceiptBadge(): void {
  try {
    chrome.action.setBadgeBackgroundColor({ color: "#a78bfa" });
    chrome.action.setBadgeText({ text: unseenReceiptCount > 0 ? String(unseenReceiptCount) : "" });
  } catch (_e) {
    // Badge API unavailable (e.g. headless test harness) — non-fatal.
  }
}

async function handleReceiptStreamEvent(data: string): Promise<void> {
  let raw: Record<string, unknown>;
  try {
    raw = JSON.parse(data) as Record<string, unknown>;
  } catch {
    return;
  }
  const summary: ReceiptEventSummary = {
    chainIndex: Number(raw.chain_index ?? 0),
    receiptHash: String(raw.receipt_hash ?? ""),
    turnHash: String(raw.turn_hash ?? ""),
    cells: Array.isArray(raw.cells) ? raw.cells.map(String) : [],
    kinds: Array.isArray(raw.kinds) ? raw.kinds.map(String) : [],
    height: Number(raw.height ?? 0),
    hasProof: !!raw.has_proof,
    proofStatus: typeof raw.proof_status === "string" ? raw.proof_status : undefined,
    finality: String(raw.finality ?? ""),
    timestamp: Number(raw.timestamp ?? 0),
    seenAt: Date.now(),
  };
  recentReceipts.unshift(summary);
  if (recentReceipts.length > RECENT_RECEIPTS_MAX) recentReceipts.length = RECENT_RECEIPTS_MAX;
  unseenReceiptCount++;
  updateReceiptBadge();
  await persistRecentReceipts();
  notifySubscribers("receipt", {
    hash: summary.receiptHash,
    turnHash: summary.turnHash,
    cells: summary.cells,
    kinds: summary.kinds,
    height: summary.height,
    hasProof: summary.hasProof,
    proofStatus: summary.proofStatus,
    finality: summary.finality,
  });
  pushActivity("turn_lifecycle", {
    phase: "committed",
    receipt_hash: summary.receiptHash,
    turn_hash: summary.turnHash,
    kinds: summary.kinds,
  }, { source: "node-sse" });
}

async function connectReceiptStream(): Promise<void> {
  if (receiptStreamAbort) return; // already running
  await loadRecentReceipts();

  const abort = new AbortController();
  receiptStreamAbort = abort;

  // Filter to the ACTIVE profile's cell when the wasm helper can derive it;
  // otherwise tail every receipt the node commits.
  let filter = "";
  try {
    await wasmReady;
    const cc = await loadState();
    const cellId = await clientCellIdHex(cc);
    if (cellId) filter = `?cell=${cellId}`;
  } catch (_e) {
    // No filter.
  }

  const url = nodeConfig.nodeUrl.replace(/\/$/, "") + "/api/events/stream" + filter;
  const headers: Record<string, string> = { Accept: "text/event-stream" };
  if (nodeConfig.devnetKey) headers["X-Devnet-Key"] = nodeConfig.devnetKey;
  if (receiptLastEventId !== null) headers["Last-Event-ID"] = receiptLastEventId;

  try {
    const resp = await fetch(url, { headers, signal: abort.signal });
    if (!resp.ok || !resp.body) throw new Error(`HTTP ${resp.status}`);
    const reader = resp.body.getReader();
    const decoder = new TextDecoder();
    const parser = createSseParser();
    for (;;) {
      const { done, value } = await reader.read();
      if (done) break;
      for (const ev of parser.feed(decoder.decode(value, { stream: true }))) {
        receiptStreamBackoffMs = 1000; // events flowing — reset backoff
        if (ev.id !== null) receiptLastEventId = ev.id;
        if (ev.event !== "receipt") continue;
        await handleReceiptStreamEvent(ev.data);
      }
    }
    throw new Error("receipt stream ended");
  } catch (_e) {
    if (receiptStreamAbort === abort) {
      receiptStreamAbort = null;
      scheduleReceiptStreamReconnect();
    }
  }
}

function scheduleReceiptStreamReconnect(): void {
  if (receiptStreamTimer !== null) return;
  const delay = receiptStreamBackoffMs;
  receiptStreamBackoffMs = Math.min(receiptStreamBackoffMs * 2, RECEIPT_STREAM_MAX_BACKOFF_MS);
  receiptStreamTimer = setTimeout(() => {
    receiptStreamTimer = null;
    connectReceiptStream();
  }, delay);
}

/** Tear down and reconnect (node config / active profile changed). */
function restartReceiptStream(): void {
  if (receiptStreamTimer !== null) {
    clearTimeout(receiptStreamTimer);
    receiptStreamTimer = null;
  }
  receiptStreamBackoffMs = 1000;
  const abort = receiptStreamAbort;
  receiptStreamAbort = null;
  if (abort) abort.abort();
  connectReceiptStream();
}

/** Popup read: the recent-receipts list; reading clears the unseen badge. */
async function getRecentReceipts(): Promise<{ receipts: ReceiptEventSummary[]; unseen: number }> {
  await loadRecentReceipts();
  const unseen = unseenReceiptCount;
  unseenReceiptCount = 0;
  updateReceiptBadge();
  await persistRecentReceipts();
  return { receipts: recentReceipts.slice(), unseen };
}

// ---------------------------------------------------------------------------
// WebSocket connection
// ---------------------------------------------------------------------------

let nodeWs: WebSocket | null = null;
let wsReconnectDelay = 1000;
let nodePublicKey: string | null = null;
let wsAuthenticated = false;

async function fetchNodePublicKey(): Promise<void> {
  try {
    const resp = await nodeRequest<{ public_key?: string }>(nodeConfig, "/api/node/status");
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

loadNodeConfig().then(() => {
  connectNodeWs();
  connectReceiptStream();
});
loadState();
startDiscoveryPolling();
startOutboxFlushLoop();

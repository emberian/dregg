/**
 * Page-injected script: defines `window.pyana` API for dapps.
 * Uses nonce-based event channels to prevent spoofing.
 */

import type {
  AuthorizeRequest,
  AuthorizeResult,
  MessageType,
  PageRequestMessage,
  StealthMetaAddress,
} from "./types";

// Retrieve the session nonce from the script tag's data attribute.
const currentScript = document.currentScript || document.querySelector("script[data-pyana-nonce]");
const SESSION_NONCE = (currentScript as HTMLElement | null)?.dataset?.pyanaNonce;

if (!SESSION_NONCE) {
  console.error("[pyana] Failed to initialize: missing session nonce.");
  throw new Error("pyana: injection integrity check failed");
}

// ---------------------------------------------------------------------------
// Request/response infrastructure
// ---------------------------------------------------------------------------

const pending = new Map<string, { resolve: (value: unknown) => void; reject: (error: Error) => void }>();
let idCounter = 0;

function sendMessage(type: MessageType, payload: Record<string, unknown> = {}): Promise<unknown> {
  return new Promise((resolve, reject) => {
    const id = `pyana_${Date.now()}_${idCounter++}`;
    pending.set(id, { resolve, reject });
    window.dispatchEvent(new CustomEvent(`pyana:request:${SESSION_NONCE}`, {
      detail: { type, id, ...payload } as PageRequestMessage,
    }));
    setTimeout(() => {
      if (pending.has(id)) {
        pending.delete(id);
        reject(new Error("Pyana: request timed out"));
      }
    }, 30000);
  });
}

window.addEventListener(`pyana:response:${SESSION_NONCE}`, ((event: CustomEvent) => {
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
}) as EventListener);

// ---------------------------------------------------------------------------
// Event system
// ---------------------------------------------------------------------------

type PyanaEvent = "ready" | "authorization" | "revoked" | "stealthNoteReceived" | "privateTransfer" | "intentFulfilled" | "privacyModeChanged";

const eventListeners = new Map<string, Set<(payload: unknown) => void>>();

function addListener(event: PyanaEvent, callback: (payload: unknown) => void): void {
  if (typeof callback !== "function") {
    throw new TypeError("pyana.on: callback must be a function");
  }
  const validEvents: PyanaEvent[] = ["ready", "authorization", "revoked", "stealthNoteReceived", "privateTransfer", "intentFulfilled", "privacyModeChanged"];
  if (!validEvents.includes(event)) {
    throw new Error(`pyana.on: unknown event "${event}". Valid: ${validEvents.join(", ")}`);
  }
  if (!eventListeners.has(event)) {
    eventListeners.set(event, new Set());
    sendMessage("pyana:subscribe", { event }).catch(() => {});
  }
  eventListeners.get(event)!.add(callback);
}

function removeListener(event: PyanaEvent, callback: (payload: unknown) => void): void {
  const listeners = eventListeners.get(event);
  if (listeners) {
    listeners.delete(callback);
  }
}

window.addEventListener(`pyana:event:${SESSION_NONCE}`, ((event: CustomEvent) => {
  const { eventName, payload } = event.detail || {};
  const listeners = eventListeners.get(eventName);
  if (listeners) {
    for (const cb of listeners) {
      try { cb(payload); } catch (e) { console.error("[pyana] event handler error:", e); }
    }
  }
}) as EventListener);

// ---------------------------------------------------------------------------
// Utility: ArrayBuffer <-> base64
// ---------------------------------------------------------------------------

function arrayBufferToBase64(buffer: ArrayBuffer | Uint8Array): string {
  const bytes = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer);
  let binary = "";
  for (let i = 0; i < bytes.length; i++) {
    binary += String.fromCharCode(bytes[i]);
  }
  return btoa(binary);
}

function base64ToArrayBuffer(base64: string): ArrayBuffer {
  const binary = atob(base64);
  const bytes = new Uint8Array(binary.length);
  for (let i = 0; i < binary.length; i++) {
    bytes[i] = binary.charCodeAt(i);
  }
  return bytes.buffer;
}

// ---------------------------------------------------------------------------
// Public API
// ---------------------------------------------------------------------------

export interface PyanaAPI {
  authorize(request: AuthorizeRequest): Promise<AuthorizeResult>;
  isConnected(): Promise<boolean>;
  canAuthorize(request: { action: string; resource: string }): Promise<boolean>;
  provision(tokenBytes: Uint8Array | Record<string, unknown>): Promise<{ accepted: boolean; tokenId?: string }>;
  postIntent(matchSpec: Record<string, unknown>, options?: Record<string, unknown>): Promise<{ intentId: string; expiry: number }>;
  getStealthAddress(): Promise<StealthMetaAddress>;
  postEncryptedIntent(matchSpec: Record<string, unknown>, options?: Record<string, unknown>): Promise<{ intentId: string; expiry: number; encrypted: boolean }>;
  privateTransfer(amount: number, assetType: string, recipientStealthMeta: StealthMetaAddress): Promise<{ success: boolean; turnId?: string; commitment?: number[] }>;
  createBearerCap(targetCellHex: string, action: string, expiry?: number): Promise<{ bearerTokenHex: string; targetCell: string; action: string }>;
  verifyBearerCap(bearerTokenHex: string, delegatorKeyHex: string, targetCellHex: string, action: string, expiry: number): Promise<{ valid: boolean; expired: boolean }>;
  createFromFactory(factoryVkHex: string, ownerPubkeyHex: string, initialBalance: number): Promise<{ childVk: string; paramHash: string; factoryVk: string }>;
  verifyProvenance(cellVkHex: string, knownFactoryVks: string[]): Promise<{ fromFactory: boolean; factoryVk: string | null }>;
  makeCellSovereign(cellIdHex: string): Promise<{ cellId: string; stateCommitment: string; mode: string }>;
  peerExchange(receiverCellHex: string, amount: number): Promise<{ exchangeId: string; proofCommitment: string }>;
  composeProofs(proofs: Array<{ proofJson: string; publicInputs?: number[] }>, mode: "and" | "or" | "chain" | "aggregate"): Promise<{ composedProof: string; mode: string; inputCount: number; valid: boolean }>;
  signTurn(turnSpec: { action: string; resource?: string; amount?: number; recipient?: string; metadata?: Record<string, unknown> }): Promise<{ turnId?: string; submitted: boolean; error?: string }>;
  queryBalance(): Promise<{ balance?: number; error?: string }>;
  getNodeConfig(): Promise<{ nodeUrl: string; wssUrl: string; wsUrl: string; devnetKey: string }>;
  setNodeConfig(config: Partial<{ nodeUrl: string; wssUrl: string; wsUrl: string; devnetKey: string }>): Promise<{ success: boolean; nodeUrl: string }>;
  shareCapability(cellId: string): Promise<{ uri: string; cellId: string; nodeId: string }>;
  acceptCapability(uri: string): Promise<{ refId: string; cellId: string; nodeId: string; permissions: string }>;
  createHandoff(cellId: string, recipientPk: string): Promise<{ certificateHash: string; cellId: string; recipientPk: string }>;
  mountService(path: string, opts: { sturdyRef: string; kind?: string; tags?: string[] }): Promise<{ path: string; version: number; kind: string }>;
  discoverServices(tags: string[]): Promise<{ results: unknown[] }>;
  resolvePath(path: string): Promise<Record<string, unknown>>;
  storageWrite(data: ArrayBuffer | Uint8Array): Promise<{ hash: string; size: number }>;
  storageRead(hash: string): Promise<{ hash: string; data: ArrayBuffer; size: number }>;
  storageQuota(): Promise<{ bytesStored: number; bytesLimit: number; computronsUsed: number; computronsRemaining: number; objectCount: number }>;
  federationStatus(): Promise<{ mode: string; height: number; peerCount: number; merkleRoot: string }>;
  proposeRoutes(routes: unknown[]): Promise<{ proposalId: string; submitted: boolean }>;
  voteOnProposal(proposalId: string, approve: boolean): Promise<{ accepted: boolean; proposalId: string }>;
  on(event: PyanaEvent, callback: (payload: unknown) => void): void;
  off(event: PyanaEvent, callback: (payload: unknown) => void): void;
}

const pyana: PyanaAPI = {
  authorize(request) {
    return sendMessage("pyana:authorize", { request }) as Promise<AuthorizeResult>;
  },

  isConnected() {
    return sendMessage("pyana:isConnected").then(() => true).catch(() => false);
  },

  canAuthorize(request) {
    return sendMessage("pyana:canAuthorize", { request }) as Promise<boolean>;
  },

  provision(tokenBytes) {
    let tokenData: Record<string, unknown>;
    if (tokenBytes instanceof Uint8Array) {
      try {
        tokenData = JSON.parse(new TextDecoder().decode(tokenBytes));
      } catch (_e) {
        return Promise.reject(new Error("pyana.provision: invalid token bytes"));
      }
    } else if (tokenBytes && typeof tokenBytes === "object") {
      tokenData = tokenBytes;
    } else {
      return Promise.reject(new Error("pyana.provision: tokenBytes must be Uint8Array or object"));
    }
    return sendMessage("pyana:provision", { tokenData }) as Promise<{ accepted: boolean; tokenId?: string }>;
  },

  postIntent(matchSpec, options) {
    return sendMessage("pyana:postIntent", { matchSpec, options }) as Promise<{ intentId: string; expiry: number }>;
  },

  getStealthAddress() {
    return sendMessage("pyana:getStealthAddress", {}) as Promise<StealthMetaAddress>;
  },

  postEncryptedIntent(matchSpec, options) {
    return sendMessage("pyana:postEncryptedIntent", { matchSpec, options }) as Promise<{ intentId: string; expiry: number; encrypted: boolean }>;
  },

  privateTransfer(amount, assetType, recipientStealthMeta) {
    return sendMessage("pyana:privateTransfer", { amount, assetType, recipientStealthMeta }) as Promise<{ success: boolean; turnId?: string; commitment?: number[] }>;
  },

  createBearerCap(targetCellHex, action, expiry) {
    return sendMessage("pyana:createBearerCap", { targetCellHex, action, expiry: expiry || 0 }) as Promise<{ bearerTokenHex: string; targetCell: string; action: string }>;
  },

  verifyBearerCap(bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry) {
    return sendMessage("pyana:verifyBearerCap", { bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry }) as Promise<{ valid: boolean; expired: boolean }>;
  },

  createFromFactory(factoryVkHex, ownerPubkeyHex, initialBalance) {
    return sendMessage("pyana:createFromFactory", { factoryVkHex, ownerPubkeyHex, initialBalance }) as Promise<{ childVk: string; paramHash: string; factoryVk: string }>;
  },

  verifyProvenance(cellVkHex, knownFactoryVks) {
    return sendMessage("pyana:verifyProvenance", { cellVkHex, knownFactoryVks }) as Promise<{ fromFactory: boolean; factoryVk: string | null }>;
  },

  makeCellSovereign(cellIdHex) {
    return sendMessage("pyana:makeCellSovereign", { cellIdHex }) as Promise<{ cellId: string; stateCommitment: string; mode: string }>;
  },

  peerExchange(receiverCellHex, amount) {
    return sendMessage("pyana:peerExchange", { receiverCellHex, amount }) as Promise<{ exchangeId: string; proofCommitment: string }>;
  },

  composeProofs(proofs, mode) {
    return sendMessage("pyana:composeProofs", { proofs, mode }) as Promise<{ composedProof: string; mode: string; inputCount: number; valid: boolean }>;
  },

  signTurn(turnSpec) {
    return sendMessage("pyana:signTurn", { turnSpec }) as Promise<{ turnId?: string; submitted: boolean; error?: string }>;
  },

  queryBalance() {
    return sendMessage("pyana:queryBalance", {}) as Promise<{ balance?: number; error?: string }>;
  },

  getNodeConfig() {
    return sendMessage("pyana:getNodeConfig", {}) as Promise<{ nodeUrl: string; wssUrl: string; wsUrl: string; devnetKey: string }>;
  },

  setNodeConfig(config) {
    return sendMessage("pyana:setNodeConfig", { config }) as Promise<{ success: boolean; nodeUrl: string }>;
  },

  shareCapability(cellId) {
    return sendMessage("pyana:shareCapability", { cellId }) as Promise<{ uri: string; cellId: string; nodeId: string }>;
  },

  acceptCapability(uri) {
    return sendMessage("pyana:acceptCapability", { uri }) as Promise<{ refId: string; cellId: string; nodeId: string; permissions: string }>;
  },

  createHandoff(cellId, recipientPk) {
    return sendMessage("pyana:createHandoff", { cellId, recipientPk }) as Promise<{ certificateHash: string; cellId: string; recipientPk: string }>;
  },

  mountService(path, opts) {
    return sendMessage("pyana:mountService", { path, ...opts }) as Promise<{ path: string; version: number; kind: string }>;
  },

  discoverServices(tags) {
    return sendMessage("pyana:discoverServices", { tags }) as Promise<{ results: unknown[] }>;
  },

  resolvePath(path) {
    return sendMessage("pyana:resolvePath", { path }) as Promise<Record<string, unknown>>;
  },

  storageWrite(data) {
    return sendMessage("pyana:storageWrite", { data: arrayBufferToBase64(data) }) as Promise<{ hash: string; size: number }>;
  },

  storageRead(hash) {
    return (sendMessage("pyana:storageRead", { hash }) as Promise<{ hash: string; data: string; size: number }>).then(result => {
      if (result && result.data) {
        return { ...result, data: base64ToArrayBuffer(result.data) };
      }
      return result as unknown as { hash: string; data: ArrayBuffer; size: number };
    });
  },

  storageQuota() {
    return sendMessage("pyana:storageQuota", {}) as Promise<{ bytesStored: number; bytesLimit: number; computronsUsed: number; computronsRemaining: number; objectCount: number }>;
  },

  federationStatus() {
    return sendMessage("pyana:federationStatus", {}) as Promise<{ mode: string; height: number; peerCount: number; merkleRoot: string }>;
  },

  proposeRoutes(routes) {
    return sendMessage("pyana:proposeRoutes", { routes }) as Promise<{ proposalId: string; submitted: boolean }>;
  },

  voteOnProposal(proposalId, approve) {
    return sendMessage("pyana:voteOnProposal", { proposalId, approve }) as Promise<{ accepted: boolean; proposalId: string }>;
  },

  on(event, callback) {
    addListener(event, callback);
  },

  off(event, callback) {
    removeListener(event, callback);
  },
};

Object.defineProperty(window, "pyana", {
  value: Object.freeze(pyana),
  writable: false,
  configurable: false,
});

window.dispatchEvent(new Event("pyana:ready"));

// Extend Window interface for TypeScript
declare global {
  interface Window {
    pyana: PyanaAPI;
  }
}

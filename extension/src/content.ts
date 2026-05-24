/**
 * Content script: bridges page.js (window.pyana) <-> background service worker.
 * Validates origins, checks allowlists, uses nonce-based event channels.
 */

import type { MessageType } from "./types";

// Generate a random nonce for this injection session to prevent event spoofing.
const SESSION_NONCE = crypto.randomUUID();

// Methods that any page origin can call without prior approval.
const UNRESTRICTED_METHODS = new Set<MessageType>([
  "pyana:isConnected",
  "pyana:canAuthorize",
  "pyana:subscribe",
  "pyana:discoverServices",
  "pyana:resolvePath",
  "pyana:storageQuota",
  "pyana:federationStatus",
]);

// Methods that require the origin to be in the user-approved allowlist.
const RESTRICTED_METHODS = new Set<MessageType>([
  "pyana:authorize",
  "pyana:provision",
  "pyana:postIntent",
  "pyana:signTurn",
  "pyana:queryBalance",
  "pyana:shareCapability",
  "pyana:acceptCapability",
  "pyana:createHandoff",
  "pyana:mountService",
  "pyana:storageWrite",
  "pyana:storageRead",
  "pyana:proposeRoutes",
  "pyana:voteOnProposal",
]);

// Inject page.js with the session nonce as a data attribute.
const script = document.createElement("script");
script.src = chrome.runtime.getURL("dist/page.js");
script.dataset.pyanaNonce = SESSION_NONCE;
(document.head || document.documentElement).appendChild(script);
script.onload = (): void => { script.remove(); };

/**
 * Check if the current page origin is allowed for a specific method.
 */
async function isOriginAllowed(origin: string, method: string): Promise<boolean> {
  try {
    const stored = await chrome.storage.local.get("pyana_allowed_origins");
    const allowlist = stored.pyana_allowed_origins || {};
    // P1-2: legacy array form is treated as no permission; user must re-prompt.
    if (Array.isArray(allowlist)) return false;
    const entry = allowlist[origin] as { methods: string[]; expires: number } | undefined;
    if (!entry) return false;
    if (entry.expires && entry.expires < Date.now()) return false;
    // No wildcard semantic — exact method match only.
    return entry.methods.includes(method);
  } catch {
    return false;
  }
}

/**
 * Request permission from the user for this origin to use restricted methods.
 */
async function requestOriginPermission(origin: string, method: string): Promise<boolean> {
  const response = await chrome.runtime.sendMessage({
    type: "pyana:requestOriginPermission",
    origin,
    method,
  });
  return response?.granted === true;
}

// Forward requests from page -> background (with security checks).
window.addEventListener(`pyana:request:${SESSION_NONCE}`, (async (event: Event): Promise<void> => {
  const customEvent = event as CustomEvent;
  // Only accept trusted events (not synthetically dispatched).
  if (!customEvent.isTrusted) return;

  const detail = customEvent.detail;
  if (!detail || !detail.type) return;

  const origin = window.location.origin;
  const messageType = detail.type as MessageType;

  // Check if this method is allowed for this origin (per-method allowlist).
  if (RESTRICTED_METHODS.has(messageType)) {
    const allowed = await isOriginAllowed(origin, messageType);
    if (!allowed) {
      const granted = await requestOriginPermission(origin, messageType);
      if (!granted) {
        window.dispatchEvent(new CustomEvent(`pyana:response:${SESSION_NONCE}`, {
          detail: { id: detail.id, error: "Origin not authorized for this method. User denied permission." },
        }));
        return;
      }
    }
  } else if (!UNRESTRICTED_METHODS.has(messageType)) {
    // Unknown or removed method -- reject.
    window.dispatchEvent(new CustomEvent(`pyana:response:${SESSION_NONCE}`, {
      detail: { id: detail.id, error: `Method "${messageType}" is not available from page context.` },
    }));
    return;
  }

  // Forward to background with origin metadata.
  const response = await chrome.runtime.sendMessage({
    ...detail,
    _origin: origin,
  });
  window.dispatchEvent(new CustomEvent(`pyana:response:${SESSION_NONCE}`, { detail: response }));
}) as EventListener);

// Forward event notifications from background -> page.
chrome.runtime.onMessage.addListener((
  message: { type: string; event?: string; payload?: unknown },
  _sender: chrome.runtime.MessageSender,
  sendResponse: (response: { ok: boolean }) => void,
): boolean => {
  if (message.type === "pyana:event") {
    window.dispatchEvent(new CustomEvent(`pyana:event:${SESSION_NONCE}`, {
      detail: { eventName: message.event, payload: message.payload },
    }));
    sendResponse({ ok: true });
  }
  return false;
});

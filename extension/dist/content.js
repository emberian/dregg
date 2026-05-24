"use strict";
(() => {
  // src/content.ts
  var SESSION_NONCE = crypto.randomUUID();
  var UNRESTRICTED_METHODS = /* @__PURE__ */ new Set([
    "pyana:isConnected",
    "pyana:canAuthorize",
    "pyana:subscribe",
    "pyana:discoverServices",
    "pyana:resolvePath",
    "pyana:storageQuota",
    "pyana:federationStatus"
  ]);
  var RESTRICTED_METHODS = /* @__PURE__ */ new Set([
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
    "pyana:voteOnProposal"
  ]);
  var script = document.createElement("script");
  script.src = chrome.runtime.getURL("dist/page.js");
  script.dataset.pyanaNonce = SESSION_NONCE;
  (document.head || document.documentElement).appendChild(script);
  script.onload = () => {
    script.remove();
  };
  async function isOriginAllowed(origin, method) {
    try {
      const stored = await chrome.storage.local.get("pyana_allowed_origins");
      const allowlist = stored.pyana_allowed_origins || {};
      if (Array.isArray(allowlist)) return false;
      const entry = allowlist[origin];
      if (!entry) return false;
      if (entry.expires && entry.expires < Date.now()) return false;
      return entry.methods.includes(method);
    } catch {
      return false;
    }
  }
  async function requestOriginPermission(origin, method) {
    const response = await chrome.runtime.sendMessage({
      type: "pyana:requestOriginPermission",
      origin,
      method
    });
    return response?.granted === true;
  }
  window.addEventListener(`pyana:request:${SESSION_NONCE}`, async (event) => {
    const customEvent = event;
    if (!customEvent.isTrusted) return;
    const detail = customEvent.detail;
    if (!detail || !detail.type) return;
    const origin = window.location.origin;
    const messageType = detail.type;
    if (RESTRICTED_METHODS.has(messageType)) {
      const allowed = await isOriginAllowed(origin, messageType);
      if (!allowed) {
        const granted = await requestOriginPermission(origin, messageType);
        if (!granted) {
          window.dispatchEvent(new CustomEvent(`pyana:response:${SESSION_NONCE}`, {
            detail: { id: detail.id, error: "Origin not authorized for this method. User denied permission." }
          }));
          return;
        }
      }
    } else if (!UNRESTRICTED_METHODS.has(messageType)) {
      window.dispatchEvent(new CustomEvent(`pyana:response:${SESSION_NONCE}`, {
        detail: { id: detail.id, error: `Method "${messageType}" is not available from page context.` }
      }));
      return;
    }
    const response = await chrome.runtime.sendMessage({
      ...detail,
      _origin: origin
    });
    window.dispatchEvent(new CustomEvent(`pyana:response:${SESSION_NONCE}`, { detail: response }));
  });
  chrome.runtime.onMessage.addListener((message, _sender, sendResponse) => {
    if (message.type === "pyana:event") {
      window.dispatchEvent(new CustomEvent(`pyana:event:${SESSION_NONCE}`, {
        detail: { eventName: message.event, payload: message.payload }
      }));
      sendResponse({ ok: true });
    }
    return false;
  });
})();

"use strict";
(() => {
  // src/content.ts
  var SESSION_NONCE = crypto.randomUUID();
  var UNRESTRICTED_METHODS = /* @__PURE__ */ new Set([
    "dregg:isConnected",
    "dregg:canAuthorize",
    "dregg:subscribe",
    "dregg:discoverServices",
    "dregg:resolvePath",
    "dregg:storageQuota",
    "dregg:federationStatus",
    "dregg:listKnownFederations"
  ]);
  var RESTRICTED_METHODS = /* @__PURE__ */ new Set([
    "dregg:authorize",
    "dregg:provision",
    "dregg:postIntent",
    "dregg:signTurn",
    "dregg:signTurnV3",
    "dregg:listOutbox",
    "dregg:flushOutbox",
    "dregg:dropOutboxEntry",
    "dregg:queryBalance",
    "dregg:shareCapability",
    "dregg:acceptCapability",
    "dregg:createHandoff",
    "dregg:mountService",
    "dregg:storageWrite",
    "dregg:storageRead",
    "dregg:proposeRoutes",
    "dregg:voteOnProposal",
    "dregg:registerFederation",
    "dregg:createCapTpDeliveredAuth"
  ]);
  var script = document.createElement("script");
  script.src = chrome.runtime.getURL("dist/page.js");
  script.dataset.dreggNonce = SESSION_NONCE;
  (document.head || document.documentElement).appendChild(script);
  script.onload = () => {
    script.remove();
  };
  async function isOriginAllowed(origin, method) {
    try {
      const stored = await chrome.storage.local.get("dregg_allowed_origins");
      const allowlist = stored.dregg_allowed_origins || {};
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
      type: "dregg:requestOriginPermission",
      origin,
      method
    });
    return response?.granted === true;
  }
  window.addEventListener(`dregg:request:${SESSION_NONCE}`, async (event) => {
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
          window.dispatchEvent(new CustomEvent(`dregg:response:${SESSION_NONCE}`, {
            detail: { id: detail.id, error: "Origin not authorized for this method. User denied permission." }
          }));
          return;
        }
      }
    } else if (!UNRESTRICTED_METHODS.has(messageType)) {
      window.dispatchEvent(new CustomEvent(`dregg:response:${SESSION_NONCE}`, {
        detail: { id: detail.id, error: `Method "${messageType}" is not available from page context.` }
      }));
      return;
    }
    const response = await chrome.runtime.sendMessage({
      ...detail,
      _origin: origin
    });
    window.dispatchEvent(new CustomEvent(`dregg:response:${SESSION_NONCE}`, { detail: response }));
  });
  chrome.runtime.onMessage.addListener((message, _sender, sendResponse) => {
    if (message.type === "dregg:event") {
      window.dispatchEvent(new CustomEvent(`dregg:event:${SESSION_NONCE}`, {
        detail: { eventName: message.event, payload: message.payload }
      }));
      sendResponse({ ok: true });
    }
    return false;
  });
})();

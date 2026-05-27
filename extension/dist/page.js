"use strict";
(() => {
  // src/page.ts
  var currentScript = document.currentScript || document.querySelector("script[data-dregg-nonce]");
  var SESSION_NONCE = currentScript?.dataset?.dreggNonce;
  if (!SESSION_NONCE) {
    console.error("[dregg] Failed to initialize: missing session nonce.");
    throw new Error("dregg: injection integrity check failed");
  }
  var pending = /* @__PURE__ */ new Map();
  var idCounter = 0;
  function sendMessage(type, payload = {}) {
    return new Promise((resolve, reject) => {
      const id = `dregg_${Date.now()}_${idCounter++}`;
      pending.set(id, { resolve, reject });
      window.dispatchEvent(new CustomEvent(`dregg:request:${SESSION_NONCE}`, {
        detail: { type, id, ...payload }
      }));
      setTimeout(() => {
        if (pending.has(id)) {
          pending.delete(id);
          reject(new Error("Dregg: request timed out"));
        }
      }, 3e4);
    });
  }
  window.addEventListener(`dregg:response:${SESSION_NONCE}`, (event) => {
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
  });
  var eventListeners = /* @__PURE__ */ new Map();
  function addListener(event, callback) {
    if (typeof callback !== "function") {
      throw new TypeError("dregg.on: callback must be a function");
    }
    const validEvents = [
      "ready",
      "authorization",
      "revoked",
      "stealthNoteReceived",
      "privateTransfer",
      "intentFulfilled",
      "privacyModeChanged",
      "receipt",
      "root",
      "intent",
      "note_announcement",
      "federation",
      "activity",
      "outbox"
    ];
    if (!validEvents.includes(event)) {
      throw new Error(`dregg.on: unknown event "${event}". Valid: ${validEvents.join(", ")}`);
    }
    if (!eventListeners.has(event)) {
      eventListeners.set(event, /* @__PURE__ */ new Set());
      sendMessage("dregg:subscribe", { event }).catch(() => {
      });
    }
    eventListeners.get(event).add(callback);
  }
  function removeListener(event, callback) {
    const listeners = eventListeners.get(event);
    if (listeners) {
      listeners.delete(callback);
    }
  }
  window.addEventListener(`dregg:event:${SESSION_NONCE}`, (event) => {
    const { eventName, payload } = event.detail || {};
    const listeners = eventListeners.get(eventName);
    if (listeners) {
      for (const cb of listeners) {
        try {
          cb(payload);
        } catch (e) {
          console.error("[dregg] event handler error:", e);
        }
      }
    }
  });
  function arrayBufferToBase64(buffer) {
    const bytes = buffer instanceof Uint8Array ? buffer : new Uint8Array(buffer);
    let binary = "";
    for (let i = 0; i < bytes.length; i++) {
      binary += String.fromCharCode(bytes[i]);
    }
    return btoa(binary);
  }
  function base64ToArrayBuffer(base64) {
    const binary = atob(base64);
    const bytes = new Uint8Array(binary.length);
    for (let i = 0; i < binary.length; i++) {
      bytes[i] = binary.charCodeAt(i);
    }
    return bytes.buffer;
  }
  var dregg = {
    authorize(request) {
      return sendMessage("dregg:authorize", { request });
    },
    isConnected() {
      return sendMessage("dregg:isConnected").then(() => true).catch(() => false);
    },
    canAuthorize(request) {
      return sendMessage("dregg:canAuthorize", { request });
    },
    provision(tokenBytes) {
      let tokenData;
      if (tokenBytes instanceof Uint8Array) {
        try {
          tokenData = JSON.parse(new TextDecoder().decode(tokenBytes));
        } catch (_e) {
          return Promise.reject(new Error("dregg.provision: invalid token bytes"));
        }
      } else if (tokenBytes && typeof tokenBytes === "object") {
        tokenData = tokenBytes;
      } else {
        return Promise.reject(new Error("dregg.provision: tokenBytes must be Uint8Array or object"));
      }
      return sendMessage("dregg:provision", { tokenData });
    },
    postIntent(matchSpec, options) {
      return sendMessage("dregg:postIntent", { matchSpec, options });
    },
    getStealthAddress() {
      return sendMessage("dregg:getStealthAddress", {});
    },
    postEncryptedIntent(matchSpec, options) {
      return sendMessage("dregg:postEncryptedIntent", { matchSpec, options });
    },
    privateTransfer(amount, assetType, recipientStealthMeta) {
      return sendMessage("dregg:privateTransfer", { amount, assetType, recipientStealthMeta });
    },
    createBearerCap(targetCellHex, action, expiry) {
      return sendMessage("dregg:createBearerCap", { targetCellHex, action, expiry: expiry || 0 });
    },
    verifyBearerCap(bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry) {
      return sendMessage("dregg:verifyBearerCap", { bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry });
    },
    createFromFactory(factoryVkHex, ownerPubkeyHex, initialBalance) {
      return sendMessage("dregg:createFromFactory", { factoryVkHex, ownerPubkeyHex, initialBalance });
    },
    verifyProvenance(cellVkHex, knownFactoryVks) {
      return sendMessage("dregg:verifyProvenance", { cellVkHex, knownFactoryVks });
    },
    makeCellSovereign(cellIdHex) {
      return sendMessage("dregg:makeCellSovereign", { cellIdHex });
    },
    peerExchange(receiverCellHex, amount) {
      return sendMessage("dregg:peerExchange", { receiverCellHex, amount });
    },
    composeProofs(proofs, mode) {
      return sendMessage("dregg:composeProofs", { proofs, mode });
    },
    signTurn(turnSpec) {
      return sendMessage("dregg:signTurn", { turnSpec });
    },
    queryBalance() {
      return sendMessage("dregg:queryBalance", {});
    },
    shareCapability(cellId) {
      return sendMessage("dregg:shareCapability", { cellId });
    },
    acceptCapability(uri) {
      return sendMessage("dregg:acceptCapability", { uri });
    },
    createHandoff(cellId, recipientPk) {
      return sendMessage("dregg:createHandoff", { cellId, recipientPk });
    },
    mountService(path, opts) {
      return sendMessage("dregg:mountService", { path, ...opts });
    },
    discoverServices(tags) {
      return sendMessage("dregg:discoverServices", { tags });
    },
    resolvePath(path) {
      return sendMessage("dregg:resolvePath", { path });
    },
    storageWrite(data) {
      return sendMessage("dregg:storageWrite", { data: arrayBufferToBase64(data) });
    },
    storageRead(hash) {
      return sendMessage("dregg:storageRead", { hash }).then((result) => {
        if (result && result.data) {
          return { ...result, data: base64ToArrayBuffer(result.data) };
        }
        return result;
      });
    },
    storageQuota() {
      return sendMessage("dregg:storageQuota", {});
    },
    federationStatus() {
      return sendMessage("dregg:federationStatus", {});
    },
    proposeRoutes(routes) {
      return sendMessage("dregg:proposeRoutes", { routes });
    },
    voteOnProposal(proposalId, approve) {
      return sendMessage("dregg:voteOnProposal", { proposalId, approve });
    },
    signTurnV3(turnBytes) {
      return sendMessage("dregg:signTurnV3", { turnBytes: Array.from(turnBytes) });
    },
    listOutbox() {
      return sendMessage("dregg:listOutbox", {});
    },
    flushOutbox() {
      return sendMessage("dregg:flushOutbox", {});
    },
    dropOutboxEntry(id) {
      return sendMessage("dregg:dropOutboxEntry", { outboxId: id });
    },
    registerFederation(federationId, name, committeePubkeys) {
      return sendMessage("dregg:registerFederation", { federationId, name, committeePubkeys });
    },
    listKnownFederations() {
      return sendMessage("dregg:listKnownFederations", {});
    },
    getActivityFeed() {
      return sendMessage("dregg:getActivityFeed", {});
    },
    createCapTpDeliveredAuth({ handoffCertB58, introducerPk, senderPk }) {
      return sendMessage("dregg:createCapTpDeliveredAuth", { handoffCertB58, introducerPk, senderPk });
    },
    on(event, callback) {
      addListener(event, callback);
    },
    off(event, callback) {
      removeListener(event, callback);
    }
  };
  Object.defineProperty(window, "dregg", {
    value: Object.freeze(dregg),
    writable: false,
    configurable: false
  });
  window.dispatchEvent(new Event("dregg:ready"));
})();

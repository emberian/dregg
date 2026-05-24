"use strict";
(() => {
  // src/page.ts
  var currentScript = document.currentScript || document.querySelector("script[data-pyana-nonce]");
  var SESSION_NONCE = currentScript?.dataset?.pyanaNonce;
  if (!SESSION_NONCE) {
    console.error("[pyana] Failed to initialize: missing session nonce.");
    throw new Error("pyana: injection integrity check failed");
  }
  var pending = /* @__PURE__ */ new Map();
  var idCounter = 0;
  function sendMessage(type, payload = {}) {
    return new Promise((resolve, reject) => {
      const id = `pyana_${Date.now()}_${idCounter++}`;
      pending.set(id, { resolve, reject });
      window.dispatchEvent(new CustomEvent(`pyana:request:${SESSION_NONCE}`, {
        detail: { type, id, ...payload }
      }));
      setTimeout(() => {
        if (pending.has(id)) {
          pending.delete(id);
          reject(new Error("Pyana: request timed out"));
        }
      }, 3e4);
    });
  }
  window.addEventListener(`pyana:response:${SESSION_NONCE}`, (event) => {
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
      throw new TypeError("pyana.on: callback must be a function");
    }
    const validEvents = ["ready", "authorization", "revoked", "stealthNoteReceived", "privateTransfer", "intentFulfilled", "privacyModeChanged"];
    if (!validEvents.includes(event)) {
      throw new Error(`pyana.on: unknown event "${event}". Valid: ${validEvents.join(", ")}`);
    }
    if (!eventListeners.has(event)) {
      eventListeners.set(event, /* @__PURE__ */ new Set());
      sendMessage("pyana:subscribe", { event }).catch(() => {
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
  window.addEventListener(`pyana:event:${SESSION_NONCE}`, (event) => {
    const { eventName, payload } = event.detail || {};
    const listeners = eventListeners.get(eventName);
    if (listeners) {
      for (const cb of listeners) {
        try {
          cb(payload);
        } catch (e) {
          console.error("[pyana] event handler error:", e);
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
  var pyana = {
    authorize(request) {
      return sendMessage("pyana:authorize", { request });
    },
    isConnected() {
      return sendMessage("pyana:isConnected").then(() => true).catch(() => false);
    },
    canAuthorize(request) {
      return sendMessage("pyana:canAuthorize", { request });
    },
    provision(tokenBytes) {
      let tokenData;
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
      return sendMessage("pyana:provision", { tokenData });
    },
    postIntent(matchSpec, options) {
      return sendMessage("pyana:postIntent", { matchSpec, options });
    },
    getStealthAddress() {
      return sendMessage("pyana:getStealthAddress", {});
    },
    postEncryptedIntent(matchSpec, options) {
      return sendMessage("pyana:postEncryptedIntent", { matchSpec, options });
    },
    privateTransfer(amount, assetType, recipientStealthMeta) {
      return sendMessage("pyana:privateTransfer", { amount, assetType, recipientStealthMeta });
    },
    createBearerCap(targetCellHex, action, expiry) {
      return sendMessage("pyana:createBearerCap", { targetCellHex, action, expiry: expiry || 0 });
    },
    verifyBearerCap(bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry) {
      return sendMessage("pyana:verifyBearerCap", { bearerTokenHex, delegatorKeyHex, targetCellHex, action, expiry });
    },
    createFromFactory(factoryVkHex, ownerPubkeyHex, initialBalance) {
      return sendMessage("pyana:createFromFactory", { factoryVkHex, ownerPubkeyHex, initialBalance });
    },
    verifyProvenance(cellVkHex, knownFactoryVks) {
      return sendMessage("pyana:verifyProvenance", { cellVkHex, knownFactoryVks });
    },
    makeCellSovereign(cellIdHex) {
      return sendMessage("pyana:makeCellSovereign", { cellIdHex });
    },
    peerExchange(receiverCellHex, amount) {
      return sendMessage("pyana:peerExchange", { receiverCellHex, amount });
    },
    composeProofs(proofs, mode) {
      return sendMessage("pyana:composeProofs", { proofs, mode });
    },
    signTurn(turnSpec) {
      return sendMessage("pyana:signTurn", { turnSpec });
    },
    queryBalance() {
      return sendMessage("pyana:queryBalance", {});
    },
    getNodeConfig() {
      return sendMessage("pyana:getNodeConfig", {});
    },
    setNodeConfig(config) {
      return sendMessage("pyana:setNodeConfig", { config });
    },
    shareCapability(cellId) {
      return sendMessage("pyana:shareCapability", { cellId });
    },
    acceptCapability(uri) {
      return sendMessage("pyana:acceptCapability", { uri });
    },
    createHandoff(cellId, recipientPk) {
      return sendMessage("pyana:createHandoff", { cellId, recipientPk });
    },
    mountService(path, opts) {
      return sendMessage("pyana:mountService", { path, ...opts });
    },
    discoverServices(tags) {
      return sendMessage("pyana:discoverServices", { tags });
    },
    resolvePath(path) {
      return sendMessage("pyana:resolvePath", { path });
    },
    storageWrite(data) {
      return sendMessage("pyana:storageWrite", { data: arrayBufferToBase64(data) });
    },
    storageRead(hash) {
      return sendMessage("pyana:storageRead", { hash }).then((result) => {
        if (result && result.data) {
          return { ...result, data: base64ToArrayBuffer(result.data) };
        }
        return result;
      });
    },
    storageQuota() {
      return sendMessage("pyana:storageQuota", {});
    },
    federationStatus() {
      return sendMessage("pyana:federationStatus", {});
    },
    proposeRoutes(routes) {
      return sendMessage("pyana:proposeRoutes", { routes });
    },
    voteOnProposal(proposalId, approve) {
      return sendMessage("pyana:voteOnProposal", { proposalId, approve });
    },
    on(event, callback) {
      addListener(event, callback);
    },
    off(event, callback) {
      removeListener(event, callback);
    }
  };
  Object.defineProperty(window, "pyana", {
    value: Object.freeze(pyana),
    writable: false,
    configurable: false
  });
  window.dispatchEvent(new Event("pyana:ready"));
})();

"use strict";
(() => {
  // src/popup-script.ts
  var statusDot = document.getElementById("statusDot");
  var statusText = document.getElementById("statusText");
  var tokenCount = document.getElementById("tokenCount");
  var chainLength = document.getElementById("chainLength");
  var logContainer = document.getElementById("logContainer");
  var lockBtn = document.getElementById("lockBtn");
  var backupBtn = document.getElementById("backupBtn");
  var recoverBtn = document.getElementById("recoverBtn");
  var managePermsBtn = document.getElementById("managePermsBtn");
  var passphraseSection = document.getElementById("passphraseSection");
  var passphraseInput = document.getElementById("passphraseInput");
  var passphraseSetupSection = document.getElementById("passphraseSetupSection");
  var newPassphraseInput = document.getElementById("newPassphraseInput");
  var confirmPassphraseInput = document.getElementById("confirmPassphraseInput");
  var setPassphraseBtn = document.getElementById("setPassphraseBtn");
  var mnemonicDisplay = document.getElementById("mnemonicDisplay");
  var mnemonicWarning = document.getElementById("mnemonicWarning");
  var permissionsSection = document.getElementById("permissionsSection");
  var permissionsContainer = document.getElementById("permissionsContainer");
  var settingsBtn = document.getElementById("settingsBtn");
  var intentsBtn = document.getElementById("intentsBtn");
  var intentsSection = document.getElementById("intentsSection");
  var intentsContainer = document.getElementById("intentsContainer");
  async function sendMessage(type, extra = {}) {
    const id = `popup_${Date.now()}`;
    const response = await chrome.runtime.sendMessage({ type, id, ...extra });
    return response?.result;
  }
  function escapeHtml(str) {
    return String(str).replace(/&/g, "&amp;").replace(/</g, "&lt;").replace(/>/g, "&gt;").replace(/"/g, "&quot;");
  }
  async function refresh() {
    const state = await sendMessage("pyana:getState");
    if (!state) return;
    if (state.locked) {
      statusDot.classList.add("locked");
      statusText.textContent = "Locked";
      lockBtn.textContent = "Unlock Cipherclerk";
      lockBtn.classList.add("locked");
      passphraseSection.classList.remove("hidden");
      passphraseSetupSection.classList.add("hidden");
      backupBtn.style.display = "none";
      mnemonicDisplay.style.display = "none";
      mnemonicWarning.style.display = "none";
      permissionsSection.style.display = "none";
    } else {
      statusDot.classList.remove("locked");
      statusText.textContent = "Connected";
      lockBtn.textContent = "Lock Cipherclerk";
      lockBtn.classList.remove("locked");
      passphraseSection.classList.add("hidden");
      backupBtn.style.display = state.hasMnemonic ? "block" : "none";
      if (state.needsPassphraseSetup) {
        passphraseSetupSection.classList.remove("hidden");
      } else {
        passphraseSetupSection.classList.add("hidden");
      }
    }
    tokenCount.textContent = String(state.tokenCount);
    chainLength.textContent = String(state.chainLength);
  }
  async function loadLog() {
    const stored = await chrome.storage.local.get("pyana_cipherclerk");
    const cc = stored["pyana_cipherclerk"];
    if (!cc || !cc.log || cc.log.length === 0) {
      logContainer.innerHTML = '<div class="empty">No recent authorizations</div>';
      return;
    }
    const entries = cc.log.slice(-5).reverse();
    logContainer.innerHTML = entries.map((entry) => {
      const time = new Date(entry.timestamp).toLocaleTimeString();
      const icon = entry.allowed ? "&#x2713;" : "&#x2717;";
      return `<div class="log-entry"><span>${icon} ${escapeHtml(entry.action)} on ${escapeHtml(entry.resource)}</span><div class="time">${escapeHtml(time)}</div></div>`;
    }).join("");
  }
  lockBtn.addEventListener("click", async () => {
    const state = await sendMessage("pyana:getState");
    if (!state) return;
    if (state.locked) {
      const passphrase = passphraseInput.value;
      const result = await sendMessage("pyana:unlock", { passphrase });
      if (result && !result.success) {
        passphraseInput.style.borderColor = "#f87171";
        passphraseInput.value = "";
        passphraseInput.placeholder = "Invalid passphrase - try again";
        return;
      }
      passphraseInput.value = "";
      passphraseInput.style.borderColor = "";
      passphraseInput.placeholder = "Enter passphrase to unlock";
    } else {
      await sendMessage("pyana:lock");
    }
    await refresh();
  });
  setPassphraseBtn.addEventListener("click", async () => {
    const newPass = newPassphraseInput.value;
    const confirmPass = confirmPassphraseInput.value;
    if (!newPass) {
      newPassphraseInput.style.borderColor = "#f87171";
      newPassphraseInput.placeholder = "Passphrase is required";
      return;
    }
    if (newPass !== confirmPass) {
      confirmPassphraseInput.style.borderColor = "#f87171";
      confirmPassphraseInput.value = "";
      confirmPassphraseInput.placeholder = "Passphrases do not match";
      return;
    }
    await sendMessage("pyana:setPassphrase", { passphrase: newPass });
    newPassphraseInput.value = "";
    confirmPassphraseInput.value = "";
    newPassphraseInput.style.borderColor = "";
    confirmPassphraseInput.style.borderColor = "";
    passphraseSetupSection.classList.add("hidden");
    await refresh();
  });
  managePermsBtn.addEventListener("click", async () => {
    if (permissionsSection.style.display === "none") {
      permissionsSection.style.display = "block";
      managePermsBtn.textContent = "Hide Permissions";
      await loadPermissions();
    } else {
      permissionsSection.style.display = "none";
      managePermsBtn.textContent = "Manage Permissions";
    }
  });
  async function loadPermissions() {
    const perms = await sendMessage("pyana:getOriginPermissions");
    if (!perms || perms.length === 0) {
      permissionsContainer.innerHTML = '<div class="empty">No origins approved</div>';
      return;
    }
    permissionsContainer.innerHTML = perms.map((p) => {
      const expiresIn = p.expiresIn ? Math.round(p.expiresIn / 6e4) : 0;
      const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
      return `<div class="log-entry" style="display:flex;justify-content:space-between;align-items:center;">
      <div>
        <div style="font-size:11px;color:#fbbf24;word-break:break-all;">${escapeHtml(p.origin)}</div>
        <div class="time">${escapeHtml(p.methods.join(", "))} - expires in ${expiresStr}</div>
      </div>
      <button class="revoke-btn" data-origin="${escapeHtml(p.origin)}" style="flex-shrink:0;padding:4px 8px;font-size:11px;background:#7f1d1d;color:#fca5a5;border:none;border-radius:4px;cursor:pointer;">Revoke</button>
    </div>`;
    }).join("");
    permissionsContainer.querySelectorAll(".revoke-btn").forEach((btn) => {
      btn.addEventListener("click", async () => {
        await sendMessage("pyana:revokeOriginPermission", { origin: btn.dataset.origin });
        await loadPermissions();
      });
    });
  }
  backupBtn.addEventListener("click", async () => {
    const state = await sendMessage("pyana:getState");
    if (state && state.locked) {
      alert("Unlock your cipherclerk first to view the recovery phrase.");
      return;
    }
    const mnemonic = await sendMessage("pyana:getMnemonic");
    if (!mnemonic) {
      alert("No recovery phrase available for this cipherclerk.");
      return;
    }
    if (mnemonicDisplay.style.display === "block") {
      mnemonicDisplay.style.display = "none";
      mnemonicWarning.style.display = "none";
      backupBtn.textContent = "Backup (Show Recovery Phrase)";
    } else {
      const words = mnemonic.split(" ");
      mnemonicDisplay.innerHTML = words.map(
        (w, i) => `<span>${String(i + 1).padStart(2, "0")}. ${w}</span>`
      ).join("&nbsp;&nbsp;");
      mnemonicDisplay.style.display = "block";
      mnemonicWarning.style.display = "block";
      backupBtn.textContent = "Hide Recovery Phrase";
    }
  });
  recoverBtn.addEventListener("click", () => {
    chrome.tabs.create({ url: chrome.runtime.getURL("recovery.html") });
  });
  settingsBtn.addEventListener("click", () => {
    chrome.tabs.create({ url: chrome.runtime.getURL("settings.html") });
  });
  intentsBtn.addEventListener("click", async () => {
    if (intentsSection.style.display === "none") {
      intentsSection.style.display = "block";
      intentsBtn.textContent = "Hide Intents";
      await loadFulfillableIntents();
    } else {
      intentsSection.style.display = "none";
      intentsBtn.textContent = "Fulfill Intents";
    }
  });
  async function loadFulfillableIntents() {
    const intents = await sendMessage("pyana:getFulfillableIntents");
    if (!intents || intents.length === 0) {
      intentsContainer.innerHTML = '<div class="empty">No fulfillable intents available</div>';
      return;
    }
    intentsContainer.innerHTML = intents.map((item) => {
      const actions = item.grantedActions ? item.grantedActions.join(", ") : "any";
      const expiresIn = Math.max(0, Math.round((item.expiry - Date.now()) / 6e4));
      const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
      const shortId = item.intentId.slice(0, 12) + "...";
      return `<div class="log-entry" style="display:flex;justify-content:space-between;align-items:center;">
      <div>
        <div style="font-size:11px;color:#a78bfa;word-break:break-all;" title="${escapeHtml(item.intentId)}">${escapeHtml(shortId)}</div>
        <div class="time">${escapeHtml(actions)} on ${escapeHtml(item.resource)} - expires in ${expiresStr}</div>
      </div>
      <button class="fulfill-btn" data-intent-id="${escapeHtml(item.intentId)}" data-token-id="${escapeHtml(item.matchedTokenId)}" style="flex-shrink:0;padding:4px 8px;font-size:11px;background:#065f46;color:#6ee7b7;border:none;border-radius:4px;cursor:pointer;">Fulfill</button>
    </div>`;
    }).join("");
    intentsContainer.querySelectorAll(".fulfill-btn").forEach((btn) => {
      btn.addEventListener("click", async () => {
        const button = btn;
        button.disabled = true;
        button.textContent = "...";
        const result = await sendMessage("pyana:fulfillIntent", {
          intentId: button.dataset.intentId,
          tokenId: button.dataset.tokenId
        });
        if (result && result.fulfilled) {
          button.textContent = "Done";
          button.style.background = "#064e3b";
          setTimeout(() => loadFulfillableIntents(), 1e3);
        } else {
          button.textContent = "Failed";
          button.style.background = "#7f1d1d";
          button.style.color = "#fca5a5";
          button.disabled = false;
          setTimeout(() => {
            button.textContent = "Fulfill";
            button.style.background = "#065f46";
            button.style.color = "#6ee7b7";
          }, 3e3);
        }
      });
    });
  }
  var tabButtons = document.querySelectorAll(".tab-btn");
  var tabContents = document.querySelectorAll(".tab-content");
  tabButtons.forEach((btn) => {
    btn.addEventListener("click", () => {
      const tabId = btn.dataset.tab;
      tabButtons.forEach((b) => b.classList.remove("active"));
      tabContents.forEach((c) => c.classList.remove("active"));
      btn.classList.add("active");
      document.getElementById(`tab-${tabId}`)?.classList.add("active");
      if (tabId === "capabilities") loadLiveRefs();
      if (tabId === "directory") loadDirectory();
      if (tabId === "storage") loadStorageQuota();
    });
  });
  var liveRefsContainer = document.getElementById("liveRefsContainer");
  var acceptUriInput = document.getElementById("acceptUriInput");
  var acceptCapBtn = document.getElementById("acceptCapBtn");
  var shareCellInput = document.getElementById("shareCellInput");
  var shareCapBtn = document.getElementById("shareCapBtn");
  var shareResult = document.getElementById("shareResult");
  var shareResultUri = document.getElementById("shareResultUri");
  var copyUriBtn = document.getElementById("copyUriBtn");
  async function loadLiveRefs() {
    const refs = await sendMessage("pyana:getLiveRefs");
    if (!refs || refs.length === 0) {
      liveRefsContainer.innerHTML = '<div class="empty">No live references held</div>';
      return;
    }
    liveRefsContainer.innerHTML = refs.map((r) => {
      const shortCell = r.cellId ? r.cellId.slice(0, 12) + "..." + r.cellId.slice(-4) : "?";
      const age = Math.round((Date.now() - r.createdAt) / 6e4);
      const ageStr = age > 60 ? `${Math.round(age / 60)}h ago` : `${age}m ago`;
      return `<div class="ref-item">
      <div class="ref-cell">${escapeHtml(shortCell)}</div>
      <div class="ref-meta">Node: ${escapeHtml(r.nodeId || "?")} | ${ageStr}</div>
      <button class="small-btn danger drop-ref-btn" data-ref-id="${escapeHtml(r.refId)}" style="margin-top: 4px;">Drop</button>
    </div>`;
    }).join("");
    liveRefsContainer.querySelectorAll(".drop-ref-btn").forEach((btn) => {
      btn.addEventListener("click", async () => {
        await sendMessage("pyana:dropLiveRef", { refId: btn.dataset.refId });
        await loadLiveRefs();
      });
    });
  }
  acceptCapBtn.addEventListener("click", async () => {
    const uri = acceptUriInput.value.trim();
    if (!uri) return;
    acceptCapBtn.textContent = "...";
    acceptCapBtn.disabled = true;
    const result = await sendMessage("pyana:acceptCapability", { uri });
    if (result && !result.error) {
      acceptUriInput.value = "";
      acceptCapBtn.textContent = "Accepted!";
      setTimeout(() => {
        acceptCapBtn.textContent = "Accept Capability";
        acceptCapBtn.disabled = false;
      }, 2e3);
      await loadLiveRefs();
    } else {
      acceptCapBtn.textContent = result?.error || "Failed";
      setTimeout(() => {
        acceptCapBtn.textContent = "Accept Capability";
        acceptCapBtn.disabled = false;
      }, 3e3);
    }
  });
  shareCapBtn.addEventListener("click", async () => {
    const cellId = shareCellInput.value.trim();
    if (!cellId || !/^[0-9a-fA-F]{64}$/.test(cellId)) {
      shareCellInput.style.borderColor = "#f87171";
      shareCellInput.placeholder = "Enter valid 64-char hex cell ID";
      return;
    }
    shareCellInput.style.borderColor = "";
    shareCapBtn.textContent = "...";
    shareCapBtn.disabled = true;
    const result = await sendMessage("pyana:shareCapability", { cellId });
    shareCapBtn.textContent = "Share as URI";
    shareCapBtn.disabled = false;
    if (result && result.uri) {
      shareResultUri.textContent = result.uri;
      shareResult.style.display = "block";
    } else {
      shareResultUri.textContent = result?.error || "Failed to generate URI";
      shareResult.style.display = "block";
    }
  });
  copyUriBtn.addEventListener("click", () => {
    const uri = shareResultUri.textContent || "";
    navigator.clipboard.writeText(uri).then(() => {
      copyUriBtn.textContent = "Copied!";
      setTimeout(() => {
        copyUriBtn.textContent = "Copy URI";
      }, 2e3);
    });
  });
  var directoryContainer = document.getElementById("directoryContainer");
  var discoverTagsInput = document.getElementById("discoverTagsInput");
  var discoverBtn = document.getElementById("discoverBtn");
  var discoveryResults = document.getElementById("discoveryResults");
  async function loadDirectory() {
    const result = await sendMessage("pyana:resolvePath", { path: "/" });
    if (result && result.entries) {
      const entries = result.entries || [];
      if (entries.length === 0) {
        directoryContainer.innerHTML = '<div class="empty">No services mounted</div>';
      } else {
        directoryContainer.innerHTML = entries.map((e) => {
          return `<div class="dir-item">
          <div class="dir-path">${escapeHtml(e.name || e.path || "?")}</div>
          <div class="dir-kind">${escapeHtml(e.kind || "-")} | v${e.version || 0}</div>
        </div>`;
        }).join("");
      }
    } else {
      directoryContainer.innerHTML = '<div class="empty">Could not load directory</div>';
    }
  }
  discoverBtn.addEventListener("click", async () => {
    const tagsStr = discoverTagsInput.value.trim();
    const tags = tagsStr ? tagsStr.split(",").map((t) => t.trim()).filter(Boolean) : [];
    discoverBtn.textContent = "...";
    discoverBtn.disabled = true;
    const result = await sendMessage("pyana:discoverServices", { tags });
    discoverBtn.textContent = "Search";
    discoverBtn.disabled = false;
    if (result && result.results && result.results.length > 0) {
      discoveryResults.innerHTML = result.results.map((r) => {
        return `<div class="dir-item">
        <div class="dir-path">${escapeHtml(r.path || r.name || "?")}</div>
        <div class="dir-kind">${escapeHtml(r.kind || "-")}</div>
      </div>`;
      }).join("");
    } else {
      discoveryResults.innerHTML = '<div class="empty">No results found</div>';
    }
  });
  var quotaBytesStored = document.getElementById("quotaBytesStored");
  var quotaBytesLimit = document.getElementById("quotaBytesLimit");
  var quotaBarFill = document.getElementById("quotaBarFill");
  var quotaObjectCount = document.getElementById("quotaObjectCount");
  var quotaComputrons = document.getElementById("quotaComputrons");
  var refreshQuotaBtn = document.getElementById("refreshQuotaBtn");
  function formatBytes(bytes) {
    if (bytes === 0) return "0 B";
    const units = ["B", "KB", "MB", "GB"];
    const i = Math.floor(Math.log(bytes) / Math.log(1024));
    return `${(bytes / Math.pow(1024, i)).toFixed(1)} ${units[i]}`;
  }
  async function loadStorageQuota() {
    const result = await sendMessage("pyana:storageQuota", {});
    if (result && !result.error) {
      quotaBytesStored.textContent = formatBytes(result.bytesStored || 0);
      quotaBytesLimit.textContent = formatBytes(result.bytesLimit || 0);
      quotaObjectCount.textContent = String(result.objectCount || 0);
      quotaComputrons.textContent = String(result.computronsRemaining || 0);
      const pct = result.bytesLimit > 0 ? Math.round(result.bytesStored / result.bytesLimit * 100) : 0;
      quotaBarFill.style.width = `${Math.min(pct, 100)}%`;
      if (pct > 90) quotaBarFill.style.background = "#f87171";
    } else {
      quotaBytesStored.textContent = "--";
      quotaBytesLimit.textContent = "--";
      quotaObjectCount.textContent = "--";
      quotaComputrons.textContent = "--";
    }
  }
  refreshQuotaBtn.addEventListener("click", loadStorageQuota);
  refresh();
  loadLog();
})();

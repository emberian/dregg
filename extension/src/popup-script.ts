/**
 * Popup script for the Dragon's Egg cipherclerk extension UI.
 * Communicates with the background service worker via chrome.runtime.sendMessage.
 */

import type { CipherclerkState, OriginPermissionDisplay, ProfileInfo, ReceiptEventSummary } from "./types";

// ---------------------------------------------------------------------------
// DOM Elements
// ---------------------------------------------------------------------------

const statusDot = document.getElementById("statusDot")!;
const statusText = document.getElementById("statusText")!;
const wasmError = document.getElementById("wasmError") as HTMLElement;
const tokenCount = document.getElementById("tokenCount")!;
const chainLength = document.getElementById("chainLength")!;
const logContainer = document.getElementById("logContainer")!;
const lockBtn = document.getElementById("lockBtn")!;
const backupBtn = document.getElementById("backupBtn")!;
const recoverBtn = document.getElementById("recoverBtn")!;
const managePermsBtn = document.getElementById("managePermsBtn")!;
const passphraseSection = document.getElementById("passphraseSection")!;
const passphraseInput = document.getElementById("passphraseInput") as HTMLInputElement;
const passphraseSetupSection = document.getElementById("passphraseSetupSection")!;
const newPassphraseInput = document.getElementById("newPassphraseInput") as HTMLInputElement;
const confirmPassphraseInput = document.getElementById("confirmPassphraseInput") as HTMLInputElement;
const setPassphraseBtn = document.getElementById("setPassphraseBtn")!;
const mnemonicDisplay = document.getElementById("mnemonicDisplay")!;
const mnemonicWarning = document.getElementById("mnemonicWarning")!;
const permissionsSection = document.getElementById("permissionsSection")!;
const permissionsContainer = document.getElementById("permissionsContainer")!;
const settingsBtn = document.getElementById("settingsBtn")!;
const intentsBtn = document.getElementById("intentsBtn")!;
const intentsSection = document.getElementById("intentsSection")!;
const intentsContainer = document.getElementById("intentsContainer")!;
const profileSelect = document.getElementById("profileSelect") as HTMLSelectElement;
const profilePubkey = document.getElementById("profilePubkey")!;
const newProfileName = document.getElementById("newProfileName") as HTMLInputElement;
const createProfileBtn = document.getElementById("createProfileBtn") as HTMLButtonElement;
const profileError = document.getElementById("profileError")!;
const receiptsContainer = document.getElementById("receiptsContainer")!;

// Onboarding (first-run) elements.
const onboardingSection = document.getElementById("onboardingSection")!;
const tabsNav = document.getElementById("tabsNav")!;
const onbStep1 = document.getElementById("onbStep1")!;
const onbStep2 = document.getElementById("onbStep2")!;
const onbPass = document.getElementById("onbPass") as HTMLInputElement;
const onbPassConfirm = document.getElementById("onbPassConfirm") as HTMLInputElement;
const onbNextBtn = document.getElementById("onbNextBtn") as HTMLButtonElement;
const onbErr1 = document.getElementById("onbErr1")!;
const onbMnemonic = document.getElementById("onbMnemonic")!;
const onbConfirm = document.getElementById("onbConfirm") as HTMLTextAreaElement;
const onbCreateBtn = document.getElementById("onbCreateBtn") as HTMLButtonElement;
const onbBackBtn = document.getElementById("onbBackBtn") as HTMLButtonElement;
const onbErr2 = document.getElementById("onbErr2")!;

// ---------------------------------------------------------------------------
// Helpers
// ---------------------------------------------------------------------------

async function sendMessage<T = unknown>(type: string, extra: Record<string, unknown> = {}): Promise<T | undefined> {
  const id = `popup_${Date.now()}`;
  const response = await chrome.runtime.sendMessage({ type, id, ...extra });
  return response?.result as T | undefined;
}

// Safe DOM construction. Every rendered value reaches the DOM through
// `textContent` (never `innerHTML`), so dynamic data — balances, cell IDs,
// origins, node responses, recovery words — can never be parsed as markup.
// This is a key-handling wallet: no string ever becomes HTML.
interface ElProps {
  className?: string;
  textContent?: string;
  title?: string;
  cssText?: string;
}

function makeEl<K extends keyof HTMLElementTagNameMap>(
  tag: K,
  props: ElProps = {},
  children: Node[] = [],
): HTMLElementTagNameMap[K] {
  const node = document.createElement(tag);
  if (props.className !== undefined) node.className = props.className;
  if (props.textContent !== undefined) node.textContent = props.textContent;
  if (props.title !== undefined) node.title = props.title;
  if (props.cssText !== undefined) node.style.cssText = props.cssText;
  for (const c of children) node.appendChild(c);
  return node;
}

// Render the standard "<div class='empty'>…</div>" placeholder via DOM.
function renderEmpty(container: Element, text: string): void {
  container.replaceChildren(makeEl("div", { className: "empty", textContent: text }));
}

// Build a fragment from a mix of text and nodes (text becomes text nodes).
function frag(...parts: Array<Node | string>): DocumentFragment {
  const f = document.createDocumentFragment();
  f.append(...parts);
  return f;
}

// ---------------------------------------------------------------------------
// Refresh state
// ---------------------------------------------------------------------------

async function refresh(): Promise<void> {
  const state = await sendMessage<CipherclerkState>("dregg:getState");
  if (!state) return;

  // Surface WASM load failures: every signing / proof / key-derivation
  // operation depends on the WASM crypto module, so make the failure visible
  // rather than letting the user hit cryptic per-operation errors.
  if (wasmError) {
    if (state.wasmReady === false) {
      wasmError.textContent = state.wasmError
        ? `Cryptographic module failed to load: ${state.wasmError}. Cipherclerk operations requiring proofs or key derivation are unavailable.`
        : "Cryptographic module failed to load. Cipherclerk operations requiring proof generation or key derivation are unavailable. Ensure your browser supports WebAssembly.";
      wasmError.style.display = "block";
    } else {
      wasmError.style.display = "none";
    }
  }

  // First-run onboarding: no wallet exists yet. Force passphrase + recovery
  // backup before anything else is shown.
  if (state.uninitialized) {
    onboardingSection.classList.remove("hidden");
    tabsNav.style.display = "none";
    document.querySelectorAll(".tab-content").forEach(c => ((c as HTMLElement).style.display = "none"));
    statusDot.classList.add("locked");
    statusText.textContent = "Setup required";
    return;
  }
  onboardingSection.classList.add("hidden");
  tabsNav.style.display = "";
  // Clear the inline overrides so the CSS rules (only .active shows) apply.
  document.querySelectorAll(".tab-content").forEach(c => ((c as HTMLElement).style.display = ""));

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

// ---------------------------------------------------------------------------
// Log
// ---------------------------------------------------------------------------

interface LogEntryDisplay {
  action: string;
  resource: string;
  allowed: boolean;
  timestamp: number;
}

async function loadLog(): Promise<void> {
  // The activity log lives in the encrypted, in-memory cipherclerk state — the
  // plaintext `dregg_cipherclerk` storage key is removed after migration, so it
  // must be fetched via the background `dregg:getLog` message (returns [] while
  // locked). `getLog` already returns newest-first.
  const log = await sendMessage<LogEntryDisplay[]>("dregg:getLog");
  if (!log || log.length === 0) {
    renderEmpty(logContainer, "No recent authorizations");
    return;
  }
  const entries = log.slice(0, 5);
  logContainer.replaceChildren(...entries.map(entry => {
    const time = new Date(entry.timestamp).toLocaleTimeString();
    const icon = entry.allowed ? "✓" : "✗";
    const label = makeEl("span", { textContent: `${icon} ${entry.action} on ${entry.resource}` });
    const timeDiv = makeEl("div", { className: "time", textContent: time });
    return makeEl("div", { className: "log-entry" }, [label, timeDiv]);
  }));
}

// ---------------------------------------------------------------------------
// Identity profiles (mirrors `dregg id create / list / use`)
// ---------------------------------------------------------------------------

function showProfileError(text: string): void {
  profileError.textContent = text;
  profileError.style.display = text ? "block" : "none";
}

function renderProfiles(profiles: ProfileInfo[]): void {
  profileSelect.replaceChildren();
  if (!profiles || profiles.length === 0) {
    const opt = document.createElement("option");
    opt.value = "";
    opt.textContent = "--";
    profileSelect.appendChild(opt);
    profilePubkey.textContent = "";
    return;
  }
  for (const p of profiles) {
    const opt = document.createElement("option");
    opt.value = p.name;
    opt.textContent = p.active ? `${p.name} (active)` : p.name;
    if (p.active) opt.selected = true;
    profileSelect.appendChild(opt);
  }
  const active = profiles.find(p => p.active);
  profilePubkey.textContent = active ? active.publicKeyHex : "";
}

async function loadProfiles(): Promise<void> {
  const profiles = await sendMessage<ProfileInfo[]>("dregg:listProfiles");
  renderProfiles(profiles || []);
}

profileSelect.addEventListener("change", async () => {
  const name = profileSelect.value;
  if (!name) return;
  showProfileError("");
  const result = await sendMessage<{ active?: string; error?: string }>("dregg:useProfile", { name });
  if (result?.error) {
    showProfileError(result.error);
  }
  await loadProfiles();
  await loadReceipts();
  await loadLoginStatus();
});

createProfileBtn.addEventListener("click", async () => {
  const name = newProfileName.value.trim();
  if (!name) return;
  showProfileError("");
  createProfileBtn.disabled = true;
  const result = await sendMessage<{ created?: ProfileInfo; error?: string }>("dregg:createProfile", { name });
  createProfileBtn.disabled = false;
  if (result?.error) {
    showProfileError(result.error);
    return;
  }
  newProfileName.value = "";
  await loadProfiles();
});

// ---------------------------------------------------------------------------
// Cap-account login (challenge -> sign -> session). Log the wallet into the
// live cloud with the active profile's key. No username, no password.
// ---------------------------------------------------------------------------

interface LoginStatus {
  loggedIn: boolean;
  subject: string | null;
  accountId: string | null;
  profile: string | null;
  cloudUrl: string;
  expiresAt: number;
  expired: boolean;
}

const loginCloudUrl = document.getElementById("loginCloudUrl")!;
const loginLoggedOut = document.getElementById("loginLoggedOut")!;
const loginLoggedIn = document.getElementById("loginLoggedIn")!;
const loginBtn = document.getElementById("loginBtn") as HTMLButtonElement;
const logoutBtn = document.getElementById("logoutBtn") as HTMLButtonElement;
const loginSubject = document.getElementById("loginSubject")!;
const loginProfile = document.getElementById("loginProfile")!;
const loginError = document.getElementById("loginError")!;

function showLoginError(text: string): void {
  loginError.textContent = text;
  loginError.style.display = text ? "block" : "none";
}

function renderLoginStatus(status: LoginStatus | undefined): void {
  if (!status) return;
  loginCloudUrl.textContent = status.cloudUrl || "(unset)";
  if (status.loggedIn) {
    loginLoggedOut.classList.add("hidden");
    loginLoggedIn.classList.remove("hidden");
    loginSubject.textContent = status.subject || "(unknown)";
    const expires = status.expiresAt > 0
      ? ` · expires ${new Date(status.expiresAt * 1000).toLocaleString()}`
      : "";
    loginProfile.textContent = `profile: ${status.profile || "?"}${expires}`;
  } else {
    loginLoggedIn.classList.add("hidden");
    loginLoggedOut.classList.remove("hidden");
    if (status.expired) showLoginError("Session expired — log in again.");
  }
}

async function loadLoginStatus(): Promise<void> {
  const status = await sendMessage<LoginStatus>("dregg:getLoginStatus");
  renderLoginStatus(status);
}

loginBtn.addEventListener("click", async () => {
  showLoginError("");
  loginBtn.disabled = true;
  loginBtn.textContent = "Signing challenge...";
  const result = await sendMessage<LoginStatus & { error?: string }>("dregg:capLogin");
  loginBtn.disabled = false;
  loginBtn.textContent = "Log in to the dregg network";
  if (!result || result.error) {
    showLoginError(result?.error || "Login failed.");
    return;
  }
  renderLoginStatus(result);
});

logoutBtn.addEventListener("click", async () => {
  logoutBtn.disabled = true;
  const result = await sendMessage<LoginStatus>("dregg:capLogout");
  logoutBtn.disabled = false;
  renderLoginStatus(result);
});

// ---------------------------------------------------------------------------
// Recent receipts (node SSE /api/events/stream; reading clears the badge)
// ---------------------------------------------------------------------------

async function loadReceipts(): Promise<void> {
  const result = await sendMessage<{ receipts: ReceiptEventSummary[]; unseen: number }>("dregg:getRecentReceipts");
  const receipts = result?.receipts || [];
  if (receipts.length === 0) {
    renderEmpty(receiptsContainer, "No receipts observed yet");
    return;
  }
  receiptsContainer.replaceChildren(...receipts.slice(0, 8).map(r => {
    const short = r.receiptHash ? r.receiptHash.slice(0, 12) + "..." : "?";
    const kinds = r.kinds && r.kinds.length > 0 ? r.kinds.join(", ") : "(no effect summary)";
    const time = r.timestamp ? new Date(r.timestamp * 1000).toLocaleTimeString() : "";
    const proof = r.hasProof ? " ✓proof" : "";
    const hashSpan = makeEl("span", {
      cssText: "font-family:monospace;color:#a78bfa;",
      title: r.receiptHash || "",
      textContent: short,
    });
    const kindsSpan = makeEl("span", { cssText: "font-size:11px;", textContent: ` ${kinds}${proof}` });
    const timeDiv = makeEl("div", {
      className: "time",
      textContent: `${r.finality || ""} · h${r.height} · ${time}`,
    });
    return makeEl("div", { className: "log-entry" }, [hashSpan, kindsSpan, timeDiv]);
  }));
}

// ---------------------------------------------------------------------------
// Lock / Unlock
// ---------------------------------------------------------------------------

lockBtn.addEventListener("click", async () => {
  const state = await sendMessage<CipherclerkState>("dregg:getState");
  if (!state) return;

  if (state.locked) {
    const passphrase = passphraseInput.value;
    const result = await sendMessage<{ success: boolean }>("dregg:unlock", { passphrase });
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
    await sendMessage("dregg:lock");
  }
  await refresh();
  await loadLog();
  await loadProfiles();
  await loadReceipts();
  await loadLoginStatus();
});

// ---------------------------------------------------------------------------
// Passphrase setup
// ---------------------------------------------------------------------------

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
  await sendMessage("dregg:setPassphrase", { passphrase: newPass });
  newPassphraseInput.value = "";
  confirmPassphraseInput.value = "";
  newPassphraseInput.style.borderColor = "";
  confirmPassphraseInput.style.borderColor = "";
  passphraseSetupSection.classList.add("hidden");
  await refresh();
});

// ---------------------------------------------------------------------------
// First-run onboarding
// ---------------------------------------------------------------------------

let onboardingPass = "";

function showOnbErr(el: HTMLElement, text: string): void {
  el.textContent = text;
  el.style.display = text ? "block" : "none";
}

onbNextBtn.addEventListener("click", async () => {
  showOnbErr(onbErr1, "");
  const pass = onbPass.value;
  const confirm = onbPassConfirm.value;
  if (!pass || pass.length < 8) {
    showOnbErr(onbErr1, "Passphrase must be at least 8 characters.");
    return;
  }
  if (pass !== confirm) {
    showOnbErr(onbErr1, "Passphrases do not match.");
    return;
  }
  onbNextBtn.disabled = true;
  const result = await sendMessage<{ mnemonic?: string; error?: string }>("dregg:beginOnboarding");
  onbNextBtn.disabled = false;
  if (!result || result.error || !result.mnemonic) {
    showOnbErr(onbErr1, result?.error || "Could not start onboarding.");
    return;
  }
  onboardingPass = pass;
  const words = result.mnemonic.split(" ");
  onbMnemonic.textContent = "";
  words.forEach((w, i) => {
    const span = document.createElement("span");
    span.textContent = `${String(i + 1).padStart(2, "0")}. ${w}`;
    onbMnemonic.appendChild(span);
    onbMnemonic.appendChild(document.createTextNode("  "));
  });
  onbStep1.classList.add("hidden");
  onbStep2.classList.remove("hidden");
});

onbBackBtn.addEventListener("click", () => {
  // Return to step 1. The candidate phrase stays in the background until
  // completeOnboarding (or it is discarded when a fresh beginOnboarding runs).
  onbStep2.classList.add("hidden");
  onbStep1.classList.remove("hidden");
  onbConfirm.value = "";
  showOnbErr(onbErr2, "");
});

onbCreateBtn.addEventListener("click", async () => {
  showOnbErr(onbErr2, "");
  if (!onbConfirm.value.trim()) {
    showOnbErr(onbErr2, "Re-type your recovery phrase to confirm you backed it up.");
    return;
  }
  onbCreateBtn.disabled = true;
  onbCreateBtn.textContent = "Creating...";
  const result = await sendMessage<{ success: boolean; error?: string }>("dregg:completeOnboarding", {
    passphrase: onboardingPass,
    confirmMnemonic: onbConfirm.value,
  });
  onbCreateBtn.disabled = false;
  onbCreateBtn.textContent = "Create wallet";
  if (!result || !result.success) {
    showOnbErr(onbErr2, result?.error || "Could not create wallet.");
    return;
  }
  // Wallet created + unlocked. Wipe the in-memory passphrase + confirmation.
  onboardingPass = "";
  onbPass.value = "";
  onbPassConfirm.value = "";
  onbConfirm.value = "";
  onbMnemonic.textContent = "";
  onbStep2.classList.add("hidden");
  onbStep1.classList.remove("hidden");
  await refresh();
  await loadLog();
  await loadProfiles();
  await loadReceipts();
});

// ---------------------------------------------------------------------------
// Permissions management
// ---------------------------------------------------------------------------

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

async function loadPermissions(): Promise<void> {
  const perms = await sendMessage<OriginPermissionDisplay[]>("dregg:getOriginPermissions");
  if (!perms || perms.length === 0) {
    renderEmpty(permissionsContainer, "No origins approved");
    return;
  }
  permissionsContainer.replaceChildren(...perms.map(p => {
    const expiresIn = p.expiresIn ? Math.round(p.expiresIn / 60000) : 0;
    const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
    const originDiv = makeEl("div", {
      cssText: "font-size:11px;color:#fbbf24;word-break:break-all;",
      textContent: p.origin,
    });
    const metaDiv = makeEl("div", {
      className: "time",
      textContent: `${p.methods.join(", ")} - expires in ${expiresStr}`,
    });
    const info = makeEl("div", {}, [originDiv, metaDiv]);
    const revokeBtn = makeEl("button", {
      className: "revoke-btn",
      cssText: "flex-shrink:0;padding:4px 8px;font-size:11px;background:#7f1d1d;color:#fca5a5;border:none;border-radius:4px;cursor:pointer;",
      textContent: "Revoke",
    });
    revokeBtn.dataset.origin = p.origin;
    revokeBtn.addEventListener("click", async () => {
      await sendMessage("dregg:revokeOriginPermission", { origin: p.origin });
      await loadPermissions();
    });
    return makeEl(
      "div",
      { className: "log-entry", cssText: "display:flex;justify-content:space-between;align-items:center;" },
      [info, revokeBtn],
    );
  }));
}

// ---------------------------------------------------------------------------
// Backup / Recovery
// ---------------------------------------------------------------------------

backupBtn.addEventListener("click", async () => {
  const state = await sendMessage<CipherclerkState>("dregg:getState");
  if (state && state.locked) {
    alert("Unlock your cipherclerk first to view the recovery phrase.");
    return;
  }
  const mnemonic = await sendMessage<string>("dregg:getMnemonic");
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
    const nodes: Node[] = [];
    words.forEach((w, i) => {
      // Preserve the original "&nbsp;&nbsp;" separator between words.
      if (i > 0) nodes.push(document.createTextNode("  "));
      nodes.push(makeEl("span", { textContent: `${String(i + 1).padStart(2, "0")}. ${w}` }));
    });
    mnemonicDisplay.replaceChildren(...nodes);
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

// ---------------------------------------------------------------------------
// Intents
// ---------------------------------------------------------------------------

interface FulfillableIntent {
  intentId: string;
  grantedActions: string[];
  resource: string;
  expiry: number;
  matchedTokenId: string;
}

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

async function loadFulfillableIntents(): Promise<void> {
  const intents = await sendMessage<FulfillableIntent[]>("dregg:getFulfillableIntents");
  if (!intents || intents.length === 0) {
    renderEmpty(intentsContainer, "No fulfillable intents available");
    return;
  }
  intentsContainer.replaceChildren(...intents.map(item => {
    const actions = item.grantedActions ? item.grantedActions.join(", ") : "any";
    const expiresIn = Math.max(0, Math.round((item.expiry - Date.now()) / 60000));
    const expiresStr = expiresIn > 60 ? `${Math.round(expiresIn / 60)}h` : `${expiresIn}m`;
    const shortId = item.intentId.slice(0, 12) + "...";
    const idDiv = makeEl("div", {
      cssText: "font-size:11px;color:#a78bfa;word-break:break-all;",
      title: item.intentId,
      textContent: shortId,
    });
    const metaDiv = makeEl("div", {
      className: "time",
      textContent: `${actions} on ${item.resource} - expires in ${expiresStr}`,
    });
    const info = makeEl("div", {}, [idDiv, metaDiv]);
    const button = makeEl("button", {
      className: "fulfill-btn",
      cssText: "flex-shrink:0;padding:4px 8px;font-size:11px;background:#065f46;color:#6ee7b7;border:none;border-radius:4px;cursor:pointer;",
      textContent: "Fulfill",
    });
    button.dataset.intentId = item.intentId;
    button.dataset.tokenId = item.matchedTokenId;
    button.addEventListener("click", async () => {
      button.disabled = true;
      button.textContent = "...";
      const result = await sendMessage<{ fulfilled?: boolean }>("dregg:fulfillIntent", {
        intentId: button.dataset.intentId,
        tokenId: button.dataset.tokenId,
      });
      if (result && result.fulfilled) {
        button.textContent = "Done";
        button.style.background = "#064e3b";
        setTimeout(() => loadFulfillableIntents(), 1000);
      } else {
        button.textContent = "Failed";
        button.style.background = "#7f1d1d";
        button.style.color = "#fca5a5";
        button.disabled = false;
        setTimeout(() => {
          button.textContent = "Fulfill";
          button.style.background = "#065f46";
          button.style.color = "#6ee7b7";
        }, 3000);
      }
    });
    return makeEl(
      "div",
      { className: "log-entry", cssText: "display:flex;justify-content:space-between;align-items:center;" },
      [info, button],
    );
  }));
}

// ---------------------------------------------------------------------------
// Tab navigation
// ---------------------------------------------------------------------------

const tabButtons = document.querySelectorAll(".tab-btn");
const tabContents = document.querySelectorAll(".tab-content");

tabButtons.forEach(btn => {
  btn.addEventListener("click", () => {
    const tabId = (btn as HTMLElement).dataset.tab;
    tabButtons.forEach(b => b.classList.remove("active"));
    tabContents.forEach(c => c.classList.remove("active"));
    btn.classList.add("active");
    document.getElementById(`tab-${tabId}`)?.classList.add("active");

    if (tabId === "account") loadAccount();
    if (tabId === "capabilities") loadLiveRefs();
    if (tabId === "directory") loadDirectory();
    if (tabId === "storage") loadStorageQuota();
  });
});

// ---------------------------------------------------------------------------
// Account / Devnet tab
//
// Routes through the node's REAL verified executor via the background
// node-API handlers. JSON turns submitted here are signed by the node
// operator's cipherclerk (the node ignores the body agent — confused-deputy
// hardening), so this surfaces the operator's agent cell: the identity whose
// turns actually commit on the devnet node the extension is pointed at.
// ---------------------------------------------------------------------------

const acctNodeUrl = document.getElementById("acctNodeUrl")!;
const acctUnlocked = document.getElementById("acctUnlocked")!;
const acctCell = document.getElementById("acctCell")!;
const acctBalance = document.getElementById("acctBalance")!;
const acctNonce = document.getElementById("acctNonce")!;
const acctRefreshBtn = document.getElementById("acctRefreshBtn") as HTMLButtonElement;
const acctFaucetBtn = document.getElementById("acctFaucetBtn") as HTMLButtonElement;
const acctSendTo = document.getElementById("acctSendTo") as HTMLInputElement;
const acctSendAmount = document.getElementById("acctSendAmount") as HTMLInputElement;
const acctSendBtn = document.getElementById("acctSendBtn") as HTMLButtonElement;
const acctResult = document.getElementById("acctResult") as HTMLElement;

interface NodeIdentity {
  publicKey: string;
  agentCell: string;
  unlocked: boolean;
  agentBalance: number | null;
  agentNonce: number | null;
  error?: string;
}

let cachedIdentity: NodeIdentity | null = null;

function showAcctResult(content: Node | string, color: string): void {
  acctResult.replaceChildren(content);
  acctResult.style.color = color;
  acctResult.style.display = "block";
}

async function loadAccount(): Promise<void> {
  const cfg = await sendMessage<{ nodeUrl?: string }>("dregg:getNodeConfig");
  acctNodeUrl.textContent = cfg?.nodeUrl || "(unset)";

  const id = await sendMessage<NodeIdentity>("dregg:nodeIdentity");
  cachedIdentity = id ?? null;
  if (!id || id.error || !id.agentCell) {
    acctUnlocked.textContent = "offline";
    acctCell.textContent = id?.error ? `Node unreachable: ${id.error}` : "--";
    acctBalance.textContent = "--";
    acctNonce.textContent = "--";
    return;
  }
  acctUnlocked.textContent = id.unlocked ? "unlocked" : "locked (set passphrase on node)";
  acctCell.textContent = id.agentCell;
  acctBalance.textContent = id.agentBalance == null ? "0 (cell not materialized)" : String(id.agentBalance);
  acctNonce.textContent = id.agentNonce == null ? "0" : String(id.agentNonce);
}

acctRefreshBtn.addEventListener("click", loadAccount);

acctFaucetBtn.addEventListener("click", async () => {
  if (!cachedIdentity?.agentCell) {
    showAcctResult("Load the account first (node unreachable).", "#f87171");
    return;
  }
  acctFaucetBtn.disabled = true;
  acctFaucetBtn.textContent = "Funding...";
  // Pass the operator pubkey so the cell is materialized with a real key —
  // otherwise later operator-signed turns fail Ed25519 verification.
  const result = await sendMessage<{ success: boolean; amount?: number; error?: string }>("dregg:faucetFund", {
    cellId: cachedIdentity.agentCell,
    amount: 1000,
    publicKey: cachedIdentity.publicKey,
  });
  acctFaucetBtn.disabled = false;
  acctFaucetBtn.textContent = "Faucet: fund 1000 DEC";
  if (result?.success) {
    showAcctResult(`Funded ${result.amount ?? 0} DEC.`, "#6ee7b7");
    setTimeout(loadAccount, 1500);
  } else {
    showAcctResult(`Faucet failed: ${result?.error || "unknown"}`, "#f87171");
  }
});

acctSendBtn.addEventListener("click", async () => {
  if (!cachedIdentity?.agentCell) {
    showAcctResult("Load the account first (node unreachable).", "#f87171");
    return;
  }
  const to = acctSendTo.value.trim();
  const amount = parseInt(acctSendAmount.value, 10);
  if (!/^[0-9a-fA-F]{64}$/.test(to)) {
    showAcctResult("Recipient must be a 64-char hex cell ID.", "#f87171");
    return;
  }
  if (!Number.isFinite(amount) || amount <= 0) {
    showAcctResult("Amount must be a positive integer.", "#f87171");
    return;
  }
  acctSendBtn.disabled = true;
  acctSendBtn.textContent = "Submitting...";
  // fee is the computron budget; a single transfer needs ~300, use 500 headroom.
  const nonce = cachedIdentity.agentNonce == null ? 0 : cachedIdentity.agentNonce;
  const result = await sendMessage<{
    accepted: boolean;
    turnHash?: string;
    proofStatus?: string;
    witnessCount?: number;
    error?: string;
  }>("dregg:submitJsonTurn", {
    spec: {
      agent: cachedIdentity.agentCell,
      nonce,
      fee: 500,
      memo: "extension transfer",
      effects: [{ kind: "transfer", to, amount }],
    },
  });
  acctSendBtn.disabled = false;
  acctSendBtn.textContent = "Operator Send";
  if (result?.accepted && result.turnHash) {
    const short = result.turnHash.slice(0, 16);
    const code = makeEl("code", { textContent: `${short}...` });
    showAcctResult(
      frag(
        "Committed turn ",
        code,
        ` (${result.proofStatus || "?"}, ${result.witnessCount ?? 0} witness).`,
      ),
      "#6ee7b7",
    );
    acctSendTo.value = "";
    acctSendAmount.value = "";
    setTimeout(loadAccount, 1500);
  } else {
    showAcctResult(`Rejected: ${result?.error || "unknown error"}`, "#f87171");
  }
});

// ---------------------------------------------------------------------------
// Capabilities tab
// ---------------------------------------------------------------------------

const liveRefsContainer = document.getElementById("liveRefsContainer")!;
const acceptUriInput = document.getElementById("acceptUriInput") as HTMLInputElement;
const acceptCapBtn = document.getElementById("acceptCapBtn")!;
const shareCellInput = document.getElementById("shareCellInput") as HTMLInputElement;
const shareCapBtn = document.getElementById("shareCapBtn")!;
const shareResult = document.getElementById("shareResult")!;
const shareResultUri = document.getElementById("shareResultUri")!;
const copyUriBtn = document.getElementById("copyUriBtn")!;

interface LiveRefDisplay {
  refId: string;
  cellId: string;
  nodeId: string;
  createdAt: number;
}

async function loadLiveRefs(): Promise<void> {
  const refs = await sendMessage<LiveRefDisplay[]>("dregg:getLiveRefs");
  if (!refs || refs.length === 0) {
    renderEmpty(liveRefsContainer, "No live references held");
    return;
  }
  liveRefsContainer.replaceChildren(...refs.map(r => {
    const shortCell = r.cellId ? (r.cellId.slice(0, 12) + "..." + r.cellId.slice(-4)) : "?";
    const age = Math.round((Date.now() - r.createdAt) / 60000);
    const ageStr = age > 60 ? `${Math.round(age / 60)}h ago` : `${age}m ago`;
    const cellDiv = makeEl("div", { className: "ref-cell", textContent: shortCell });
    const metaDiv = makeEl("div", { className: "ref-meta", textContent: `Node: ${r.nodeId || "?"} | ${ageStr}` });
    const dropBtn = makeEl("button", {
      className: "small-btn danger drop-ref-btn",
      cssText: "margin-top: 4px;",
      textContent: "Drop",
    });
    dropBtn.dataset.refId = r.refId;
    dropBtn.addEventListener("click", async () => {
      await sendMessage("dregg:dropLiveRef", { refId: r.refId });
      await loadLiveRefs();
    });
    return makeEl("div", { className: "ref-item" }, [cellDiv, metaDiv, dropBtn]);
  }));
}

// Powerbox: grant an ATTENUATED bearer capability to a target cell, scoped to
// one action + expiry. The wasm `create_bearer_cap` primitive binds the grant
// to (delegator key, target cell, action, expiry); it can only be narrowed
// further, never amplified — the no-amplify story made visible.
const grantCellInput = document.getElementById("grantCellInput") as HTMLInputElement;
const grantActionInput = document.getElementById("grantActionInput") as HTMLInputElement;
const grantExpiryInput = document.getElementById("grantExpiryInput") as HTMLInputElement;
const grantCapBtn = document.getElementById("grantCapBtn") as HTMLButtonElement;
const grantError = document.getElementById("grantError")!;
const grantResult = document.getElementById("grantResult")!;
const grantResultToken = document.getElementById("grantResultToken")!;
const grantResultScope = document.getElementById("grantResultScope")!;
const copyGrantBtn = document.getElementById("copyGrantBtn")!;

function showGrantError(text: string): void {
  grantError.textContent = text;
  grantError.style.display = text ? "block" : "none";
}

grantCapBtn.addEventListener("click", async () => {
  showGrantError("");
  grantResult.style.display = "none";
  const targetCellHex = grantCellInput.value.trim();
  const action = grantActionInput.value.trim();
  if (!/^[0-9a-fA-F]{64}$/.test(targetCellHex)) {
    showGrantError("Target cell must be a 64-char hex cell ID.");
    return;
  }
  if (!action) {
    showGrantError("Enter the action to grant (e.g. read, transfer).");
    return;
  }
  const minutes = parseInt(grantExpiryInput.value, 10);
  // Bearer-cap expiry is a Unix-seconds deadline; 0 = no expiry.
  const expiry = Number.isFinite(minutes) && minutes > 0
    ? Math.floor(Date.now() / 1000) + minutes * 60
    : 0;
  grantCapBtn.disabled = true;
  grantCapBtn.textContent = "Granting...";
  const result = await sendMessage<{ bearerTokenHex?: string; targetCell?: string; action?: string; error?: string }>(
    "dregg:createBearerCap",
    { targetCellHex, action, expiry },
  );
  grantCapBtn.disabled = false;
  grantCapBtn.textContent = "Grant attenuated capability";
  if (!result || result.error || !result.bearerTokenHex) {
    showGrantError(result?.error || "Could not create the grant (wallet locked?).");
    return;
  }
  grantResultToken.textContent = `dregg-cap:${result.bearerTokenHex}`;
  const scope = expiry > 0
    ? `action "${action}" · expires ${new Date(expiry * 1000).toLocaleString()}`
    : `action "${action}" · no expiry`;
  grantResultScope.textContent = scope;
  grantResult.style.display = "block";
});

copyGrantBtn.addEventListener("click", () => {
  const token = grantResultToken.textContent || "";
  navigator.clipboard.writeText(token).then(() => {
    copyGrantBtn.textContent = "Copied!";
    setTimeout(() => { copyGrantBtn.textContent = "Copy token"; }, 2000);
  });
});

acceptCapBtn.addEventListener("click", async () => {
  const uri = acceptUriInput.value.trim();
  if (!uri) return;
  acceptCapBtn.textContent = "...";
  (acceptCapBtn as HTMLButtonElement).disabled = true;
  const result = await sendMessage<{ error?: string }>("dregg:acceptCapability", { uri });
  if (result && !result.error) {
    acceptUriInput.value = "";
    acceptCapBtn.textContent = "Accepted!";
    setTimeout(() => {
      acceptCapBtn.textContent = "Accept Capability";
      (acceptCapBtn as HTMLButtonElement).disabled = false;
    }, 2000);
    await loadLiveRefs();
  } else {
    acceptCapBtn.textContent = result?.error || "Failed";
    setTimeout(() => {
      acceptCapBtn.textContent = "Accept Capability";
      (acceptCapBtn as HTMLButtonElement).disabled = false;
    }, 3000);
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
  (shareCapBtn as HTMLButtonElement).disabled = true;
  const result = await sendMessage<{ uri?: string; error?: string }>("dregg:shareCapability", { cellId });
  shareCapBtn.textContent = "Share as URI";
  (shareCapBtn as HTMLButtonElement).disabled = false;
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
    setTimeout(() => { copyUriBtn.textContent = "Copy URI"; }, 2000);
  });
});

// ---------------------------------------------------------------------------
// Directory tab
// ---------------------------------------------------------------------------

const directoryContainer = document.getElementById("directoryContainer")!;
const discoverTagsInput = document.getElementById("discoverTagsInput") as HTMLInputElement;
const discoverBtn = document.getElementById("discoverBtn")!;
const discoveryResults = document.getElementById("discoveryResults")!;

async function loadDirectory(): Promise<void> {
  const result = await sendMessage<{ entries?: Array<{ name?: string; path?: string; kind?: string; version?: number }> }>("dregg:resolvePath", { path: "/" });
  if (result && result.entries) {
    const entries = result.entries || [];
    if (entries.length === 0) {
      renderEmpty(directoryContainer, "No services mounted");
    } else {
      directoryContainer.replaceChildren(...entries.map(e => {
        const pathDiv = makeEl("div", { className: "dir-path", textContent: e.name || e.path || "?" });
        const kindDiv = makeEl("div", { className: "dir-kind", textContent: `${e.kind || "-"} | v${e.version || 0}` });
        return makeEl("div", { className: "dir-item" }, [pathDiv, kindDiv]);
      }));
    }
  } else {
    renderEmpty(directoryContainer, "Could not load directory");
  }
}

discoverBtn.addEventListener("click", async () => {
  const tagsStr = discoverTagsInput.value.trim();
  const tags = tagsStr ? tagsStr.split(",").map(t => t.trim()).filter(Boolean) : [];
  discoverBtn.textContent = "...";
  (discoverBtn as HTMLButtonElement).disabled = true;
  const result = await sendMessage<{ results?: Array<{ path?: string; name?: string; kind?: string }> }>("dregg:discoverServices", { tags });
  discoverBtn.textContent = "Search";
  (discoverBtn as HTMLButtonElement).disabled = false;

  if (result && result.results && result.results.length > 0) {
    discoveryResults.replaceChildren(...result.results.map(r => {
      const pathDiv = makeEl("div", { className: "dir-path", textContent: r.path || r.name || "?" });
      const kindDiv = makeEl("div", { className: "dir-kind", textContent: r.kind || "-" });
      return makeEl("div", { className: "dir-item" }, [pathDiv, kindDiv]);
    }));
  } else {
    renderEmpty(discoveryResults, "No results found");
  }
});

// ---------------------------------------------------------------------------
// Storage tab
// ---------------------------------------------------------------------------

const quotaBytesStored = document.getElementById("quotaBytesStored")!;
const quotaBytesLimit = document.getElementById("quotaBytesLimit")!;
const quotaBarFill = document.getElementById("quotaBarFill") as HTMLElement;
const quotaObjectCount = document.getElementById("quotaObjectCount")!;
const quotaComputrons = document.getElementById("quotaComputrons")!;
const refreshQuotaBtn = document.getElementById("refreshQuotaBtn")!;

function formatBytes(bytes: number): string {
  if (bytes === 0) return "0 B";
  const units = ["B", "KB", "MB", "GB"];
  const i = Math.floor(Math.log(bytes) / Math.log(1024));
  return `${(bytes / Math.pow(1024, i)).toFixed(1)} ${units[i]}`;
}

interface StorageQuotaDisplay {
  bytesStored: number;
  bytesLimit: number;
  objectCount: number;
  computronsRemaining: number;
  error?: string;
}

async function loadStorageQuota(): Promise<void> {
  const result = await sendMessage<StorageQuotaDisplay>("dregg:storageQuota", {});
  if (result && !result.error) {
    quotaBytesStored.textContent = formatBytes(result.bytesStored || 0);
    quotaBytesLimit.textContent = formatBytes(result.bytesLimit || 0);
    quotaObjectCount.textContent = String(result.objectCount || 0);
    quotaComputrons.textContent = String(result.computronsRemaining || 0);
    const pct = result.bytesLimit > 0
      ? Math.round((result.bytesStored / result.bytesLimit) * 100)
      : 0;
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

// ---------------------------------------------------------------------------
// Initialize
// ---------------------------------------------------------------------------

refresh();
loadLog();
loadProfiles();
loadReceipts();
loadLoginStatus();

# Extension Security Audit — `extension/`

**Verdict:** **CRITICAL**

## Summary

The extension's high-level architecture is reasonable: a nonce-bound page<->content event channel, an origin-gated method allowlist, a per-method origin permission system with expiry, and an encrypted-state model using PBKDF2-SHA256 (600k iterations) + AES-256-GCM. The page-side surface is largely correct: events are checked with `isTrusted`, `_origin` is overwritten with the trusted `window.location.origin` after spreading attacker `detail` (so origin spoofing from a page is blocked), and `window.pyana` is frozen with a non-configurable property.

However, the user-approval popups (provision, intent-confirm, disclosure-picker, origin-permission) all use a pattern of `chrome.windows.create()` + a global `chrome.runtime.onMessage.addListener` that **does not validate the sender** of the decision message. Because `chrome.runtime.onMessage` dispatches to *every* registered listener, a malicious page's content script can forge any decision message (`pyana:provisionDecision`, `pyana:intentConfirmation`, `pyana:disclosureDecision`, `pyana:originPermissionDecision`) while a real popup is open — silently auto-approving the user's review and granting blanket capabilities. This is a clean approval-drift exploit equivalent to wallet compromise on any visited site.

Additional serious findings: passphrase-less first-run wallets are encrypted under an internal key stored in `chrome.storage.session` (i.e. effectively unencrypted at rest until the user sets a passphrase, with `needsPassphraseSetup` never enforced); user PII (token facts including email/userId/org) is passed in popup URLs (visible to extension-API observers and chrome:// internals); WASM has a JS fallback BIP-39 path; legacy `.js` files in the repo root are still referenced by `build.sh` packaging and `popup.html` style; CSP is reasonable but the manifest content_scripts use `<all_urls>` and WAR is also `<all_urls>` so any web page can frame extension HTML.

## P0 — Critical

### P0-1. Forged user-confirmation messages bypass every approval popup
**Files:**
- `src/background.ts:961-997` (disclosure-picker listener)
- `src/background.ts:1090-1125` (provisionToken listener)
- `src/background.ts:1133-1164` (intent-confirmation listener)
- `src/background.ts:1637-1672` (origin-permission listener)

**Attack.** Each of these functions opens a popup window then calls `chrome.runtime.onMessage.addListener(listener)` where `listener` only checks `message.type` and never inspects `sender`. `chrome.runtime.onMessage` delivers to *all* listeners regardless of what the main router at line 2086 returns. A malicious content script on any page in the user's session can race the user by calling
```
chrome.runtime.sendMessage({ type: "pyana:provisionDecision", accepted: true, tokenData })
chrome.runtime.sendMessage({ type: "pyana:disclosureDecision", authorized: true, level: "full" })
chrome.runtime.sendMessage({ type: "pyana:originPermissionDecision", granted: true })
chrome.runtime.sendMessage({ type: "pyana:intentConfirmation", confirmed: true })
```
while a popup is open. The inner listener accepts the forged message and resolves the promise as if the user clicked Approve. This is exploitable any time another page (even a benign one) triggers a confirmation: the attacker site can simply spam the four message types continuously, and the next time *any* popup opens, it auto-approves.

The check at line 2092 (`isContentScript(sender) && !PAGE_ALLOWED_METHODS.has(msgType)`) rejects these in the *main* router but does not stop the inner listener from firing.

**Fix.** In every inner listener, validate `sender.url?.startsWith(\`chrome-extension://${chrome.runtime.id}/\`)` and the specific popup URL (or correlate by `sender.tab?.windowId === win.id`). Better: route decisions through a dedicated extension-popup-only handler that stores the pending request id, and require the popup to echo that id back.

### P0-2. User PII leaked to URL query parameters in popup windows
**Files:**
- `src/background.ts:965-971` (disclosure-picker URL embeds full `tokenFacts` including email/userId/org)
- `src/background.ts:1093` (provision.html URL embeds the full token JSON)
- `src/background.ts:1136-1138` (confirm-intent embeds full matchSpec/options)

**Attack.** Token facts include `email`, `userId`, `org`, `organization` (see `extractTokenFacts` at lines 927-958). These end up in `chrome-extension://<id>/disclosure-picker.html?facts=...`. Such URLs are visible to other extensions with the `tabs` permission, appear in chrome's session history & devtools, and are written to the popup's `document.referrer`/`window.name`. They are also not cleared from memory after the popup closes.

**Fix.** Pass an opaque request-id in the URL and have the popup fetch the details via `chrome.runtime.sendMessage({ type: "pyana:getPendingDecision", id })`. Keep PII out of URLs.

## P1 — High

### P1-1. Wallet ships with a default "internal key" that is not derived from any user secret
**File:** `src/background.ts:219-229, 413-488, 519-531, 533-574`

On first run `loadState()` creates a mnemonic and a keypair, then encrypts state under `getInternalEncryptionKey()` — a 32-byte random value stored *in clear text* in `chrome.storage.session` (line 226 — `chrome.storage.session.set({ _internalKey: key })`). `chrome.storage.session` is **not** encrypted at rest in all browsers (Firefox in particular persists session storage; Chrome stores in unencrypted browser profile until restart). Until the user explicitly sets a passphrase the wallet is effectively unencrypted; `needsPassphraseSetup` is set but never *enforced* anywhere — the user is never blocked from signing turns or exporting capabilities while in this state. `getMnemonic()` and `signTurn()` work without a real passphrase.

**Fix.** Block sensitive ops while `needsPassphraseSetup === true` (or require ephemeral re-derivation). Treat the internal key as a true ephemeral session secret stored only in JS memory, not in `chrome.storage.session`.

### P1-2. Origin permission check has TOCTOU + wildcard pitfalls
**File:** `src/content.ts:49-63, 90-100`

`isOriginAllowed` reads `chrome.storage.local` synchronously each call, so a freshly added permission is immediately effective. But `allowlist[origin].methods.includes("*")` means a one-time `*` grant (e.g. from migration code at `background.ts:671`, `methods: ["*"]`) silently authorizes *every* restricted method including `signTurn` and `proposeRoutes`. The migration path at line 668-675 unconditionally upgrades any legacy array-form allowlist entry into `methods: ["*"]`. If the user had any prior approval, they get blanket permission post-update.

**Fix.** Drop the `*` wildcard from the methods list semantics; migrate by clearing the legacy allowlist and re-prompting per method.

### P1-3. WebSocket auth handshake accepts unsigned messages when node pubkey unknown
**File:** `src/background.ts:2200-2218`

If `nodePublicKey` is null (the `/status` fetch failed), `auth_response` skips signature validation and marks the socket `wsAuthenticated = true`. A network attacker that can MITM the WS endpoint (e.g. via the `ws://localhost:8420/ws` fallback, line 2160-2161) can feed forged `revocation` messages that quietly remove tokens (line 2227-2231), or forged `receipt` messages that pollute the local receipt chain (line 2236-2240). The plaintext `ws://` fallback for localhost is reachable on a multi-user machine.

**Fix.** Fail closed when `nodePublicKey` is unknown. Remove the `ws://` plaintext fallback for non-loopback or require the node pubkey to be pinned in settings.

### P1-4. Settings page accepts arbitrary node URLs without confirmation
**File:** `settings-script.js:34-73`; `src/background.ts:1973-1977`

`setNodeConfig` is restricted to `isExtensionPopup`, but `settings.html` is opened via `chrome.tabs.create` and is itself an extension page so the check passes. A user who navigates to a phishing site that exploits a separate vuln (or who is socially-engineered into pasting a URL) can silently redirect *all* turn submissions, balance queries, sturdy-ref exchanges, etc. through an attacker-controlled node — which then sees plaintext capability secrets (see `shareCapability` returning `pyana://<node>/<cell>/<secret>` at `background.ts:1310`).

**Fix.** When the node URL changes, force a confirmation modal that shows the old vs new host, and revoke all live refs / clear receipt chain. Consider pinning the node pubkey alongside the URL so the WS handshake fails on switch.

### P1-5. Rate limit is per-origin but keyed on attacker-controlled `_origin`
**File:** `src/background.ts:196-213, 1714-1721`

`checkRateLimit(origin)` uses the `origin` derived from `message._origin || sender.tab.url`. Although `_origin` is overwritten by the content script in the normal flow, an attacker with even minimal control over `sender.tab.url` (e.g. via repeated page navigation) can rotate the origin string and never hit the 5-call/minute cap. Also `chrome.storage.session.get` is async — concurrent requests race past the limit before `set` lands.

**Fix.** Use atomic in-memory counters keyed off `sender.tab.id`+origin, not URL-derived strings.

## P2 — Medium

### P2-1. Legacy duplicate scripts in repo root are shipped
**File:** `build.sh:120-141`, `extension/legacy/*`, `extension/*.js`

`build.sh` packages root `.js` files (background.js, content.js, page.js, popup-script.js) — but the manifest now points to `dist/`. The result is that the package contains two copies of every script; if a future manifest typo or chrome update prefers a different path the old vulnerable version (in legacy/) could be loaded. `extension/legacy/background.js` is the pre-TS version (127kb) and not audited.

**Fix.** Remove `legacy/` and the root `.js` from packaging. Only ship `dist/`.

### P2-2. Sourcemaps shipped to production
**File:** `build.mjs:15` (`sourcemap: true`)

`dist/*.js.map` exposes full source structure including internal symbol names useful for crafting forged messages. Sourcemaps are not packaged by `build.sh` directly, but they are present in the unpacked extension load path. Web-accessible-resources is `dist/page.js` only, so they are not page-readable, but they leak via devtools to anyone inspecting the extension.

**Fix.** `sourcemap: false` for production builds.

### P2-3. `innerHTML` interpolation with `escapeHtml` is correct but fragile
**File:** `src/popup-script.ts:109-113, 187-200, 274-289, 363-...`

All places escape values, but values like `entry.action`, `p.methods.join(", ")`, `item.intentId` come from `chrome.storage.local`, which is set by message handlers that accept arbitrary strings from the network/page. One missed `escapeHtml()` or a future refactor creates XSS in the popup with full extension privileges.

**Fix.** Use `textContent` + DOM construction (the project already uses it elsewhere).

### P2-4. `pasteBtn` on recovery page reads mnemonic from system clipboard
**File:** `recovery.js:78-92`

A 24-word phrase is left on the system clipboard. Combined with other extensions' clipboard listeners or paste history on macOS, this leaks the master secret. Should warn the user, and call `navigator.clipboard.writeText("")` after paste.

### P2-5. `confirm-intent.html` shows JSON.stringify without origin context
**File:** `confirm-intent.html:82-99`, `confirm-intent-script.js`

The popup tells the user "A page wants to broadcast an intent" but never displays *which* page (origin not passed in URL). The user has no way to distinguish a confirmation from `bank.com` vs `evil.com`.

**Fix.** Pass `origin` to confirm-intent.html and display prominently.

### P2-6. Manifest content_scripts and WAR match `<all_urls>`
**File:** `manifest.json:11, 17`

Page.js is injected into every page. WAR is also `<all_urls>` so any web page can frame `chrome-extension://<id>/...` HTML and attempt clickjacking on share-capability/disclosure-picker. None of the popup HTML defines `frame-ancestors 'none'`.

**Fix.** Add `frame-ancestors 'none'` to the popup CSP, or use `web_accessible_resources` only for page.js and constrain matches.

## P3 — Low

- **`disclosure-picker.js:341`** assigns `previewEl.innerHTML = html` where `html` is built from token fact values via template literals without escaping (`${formatFactValue(fact.key, fact.value)}` and `${thresholdStr}`). `fact.value` comes from `tokenFacts` (URL-passed; user-approved token data). Low because the popup only runs in extension context and values originate from already-trusted tokens, but inconsistent with rest of file.
- **`background.ts:741-754`** — `generateProof` derives "depth" from a 32-bit XOR-folded hash of the witness; this is a demo proof, not real binding. The naming `generate_demo_stark_proof` is honest but the call site in `authorize()` returns this as if it were the security artifact (line 828: `result.proof = Array.from(proof)`). Callers may believe this is a real ZK proof.
- **`background.ts:1186-1206`** — `computeIntentId` JS fallback uses SHA-256 only over a subset of fields (excludes `creator`, `proof_of_stake`); WASM and JS hash domains differ, allowing intent-id collisions across modes.
- **`background.ts:1336`** — `liveRef.permissions: resp.data?.permissions || "full"` — if the node omits the field, the extension assumes **full** access. Should default to `"none"` or refuse.
- **`background.ts:2050`** — `compose_proofs` mode default is `"and"` — but the caller-controlled `message.mode` is passed without validation against the small enum `"and"|"or"|"chain"|"aggregate"`.
- **`recovery.js:42`** — `/^[a-z]{3,8}$/` validates input but real BIP-39 words are 3-8 letters with a specific set; the JS validation in `background.ts:validateMnemonic` is correct but `recovery.js` does no checksum check before enabling the button (cosmetic, but misleads users).
- **No CSP for individual popup HTML** — relies on the global `extension_pages` CSP. All popups load `script src="..."` correctly, no inline scripts. Good.

## Permission model summary

| Setting | Value | Notes |
|---|---|---|
| `manifest_version` | 3 | Good. |
| `permissions` | `storage`, `activeTab`, `contextMenus` | Minimal. |
| `host_permissions` | (none) | Good — no `<all_urls>` host permission. |
| `content_scripts.matches` | `<all_urls>` | Page.js injected everywhere. Defensible for a wallet. |
| `web_accessible_resources.resources` | `dist/page.js`, `bip39_english.txt`, `pyana_wasm.js`, `pyana_wasm_bg.wasm` | `bip39_english.txt` exposed unnecessarily; can be fetched only by background. |
| `web_accessible_resources.matches` | `<all_urls>` | Means any page can frame extension HTML (only HTML files are framable via direct nav, not WAR list, but extension pages are still openable). |
| `content_security_policy.extension_pages` | `script-src 'self' 'wasm-unsafe-eval'; object-src 'self'` | No `unsafe-inline`. Good. Missing `frame-ancestors`. |

## Message-passing summary

| Route | Method | What is validated |
|---|---|---|
| page -> content (postMessage / CustomEvent) | `pyana:request:<NONCE>` | `event.isTrusted`, nonce in event name |
| content -> background (`chrome.runtime.sendMessage`) | `_origin` set by content script, overrides page-supplied | `_origin` overwritten via spread |
| background main router | `PAGE_ALLOWED_METHODS`, `POPUP_ONLY_METHODS`, `isContentScript()`, `isExtensionPopup()` | OK for main dispatch |
| background inner listeners (`provisionDecision`, `intentConfirmation`, `disclosureDecision`, `originPermissionDecision`) | **Only message.type checked** | **No sender validation — P0** |
| background -> tab (`chrome.tabs.sendMessage`) | tab id from subscriber set | OK |
| WS message in | `validateNodeMessage` signs-or-skips when no pubkey | Fails open — P1 |

## Confirmation-flow summary

| Flow | What user sees | What is signed/executed | Identical? |
|---|---|---|---|
| `provision` | Issuer, resource, actions, expiry (provision.html) | `tokenData` from URL param JSON | **Yes**, except: actions are escaped, but server could send `actions: ["*"]` and warning text shown. Decision message is forge-able (P0-1). |
| `confirm-intent` | action, JSON.stringify(spec), options | matchSpec + options sent unchanged to node WS | Yes, but no origin shown (P2-5). Decision forge-able. |
| `disclosure-picker` | origin, action, resource, fact picker | mode + disclosedFacts + predicateFacts | Yes. Decision forge-able. URL leaks PII (P0-2). |
| `origin-permission` | origin + method | adds `{methods: [method], expires: +24h}` | Yes. Decision forge-able. |
| `share-capability` (context-menu) | URI + QR placeholder | URI displayed for copy; no further action | Read-only — OK. |
| `signTurn` (page-initiated) | **No popup** — directly signs and submits if origin allowed | turn payload signed with `wallet.secretKey` | **Asymmetry: signTurn requires only origin permission, no per-turn UI confirmation.** A site with one-time `pyana:signTurn` grant can sign arbitrary turns silently for 24h. |

## Open questions

1. Is `extension/legacy/` actively loaded anywhere, or is it just historical? Confirm `build.sh` should not be packaging it (it currently does because it loads root-level `.js` files which are duplicates of legacy).
2. Should `pyana:signTurn` require per-call user confirmation? Currently it only requires the origin to be allowlisted — that's the highest-impact wallet operation with zero per-action UI.
3. Is the `chrome.storage.session._internalKey` design intentional (i.e. is the threat model "a thief who reads disk but not running memory")? If so, document it; if not, fix P1-1.
4. What is the production node pubkey distribution strategy? Today the extension fetches `/status` to learn it — TOFU. A pinned key would close P1-3.
5. The `pyana://<node>/<cell>/<secret>` URI exposes a bearer secret in cleartext. Is this intended? If so, how is it transported between users (clipboard / URL / QR)?
6. Should the popups (provision/confirm-intent/disclosure/origin-permission) be migrated to use `chrome.runtime.connect` with port-based messaging instead of broadcast `sendMessage`? That alone resolves P0-1 because ports are 1:1.

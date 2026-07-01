# Notes to Reviewer — Dragon's Egg Cipherclerk

This is the paste-ready text for the **"Notes to reviewer"** field of the AMO and
Chrome Web Store submissions. It tells the reviewer what the extension is, how to
test it without any account, where the source is, and where the privacy policy
lives. Two short paste blocks follow — one for the test/how-to, one source-build
pointer — plus a checklist of what to attach.

---

## Paste block — Notes to reviewer

```
WHAT IT IS
Dragon's Egg Cipherclerk is a self-custody signing wallet ("cipherclerk") for
the dregg network. It generates and stores signing keys on-device, shows a
human-readable confirmation for every transaction before signing, and talks only
to the dregg node the user configures. It is the wallet equivalent of MetaMask
for the dregg protocol.

NO MANDATORY ACCOUNT — IT IS SELF-CUSTODY
There is no sign-up, no username, and no password to give you. The wallet is
created locally on first run. An OPTIONAL cap-account login lets the user sign
into the dregg network by proving they hold a key (a one-time challenge is
signed on-device); it is pseudonymous, requires no personal data, and is not
needed to evaluate the wallet. To test:

1. Install the extension and click the toolbar icon to open the popup.
2. Onboarding runs automatically. You will be asked to:
   a. set a passphrase (>= 8 characters) — this encrypts the wallet at rest;
   b. write down the displayed recovery phrase and re-type it to confirm the
      backup. A key is generated only after this step.
3. The wallet is now unlocked and shows your address/profile. By default it
   points at the dregg devnet over TLS (https/wss devnet.dregg.fg-goose.online)
   — no configuration needed to see the UI work.
4. Optional, to exercise signing end-to-end: open the Settings page (toolbar
   popup -> Settings) to view/adjust the node endpoint. Any signing or
   authorization request surfaces a confirmation popup that decodes the
   transaction into plain-language prose; the signature is released only when you
   click approve.
5. Lock/unlock: locking wipes the in-memory key; unlocking requires the
   passphrase from step 2a. (Keep the recovery phrase from step 2b — it is the
   only way to restore the wallet.)
6. Optional cap-account login: the Cipherclerk tab has a "Cloud Session" section
   with a "Log in to the dregg network" button. Clicking it fetches a one-time
   challenge from the cloud, signs it with the active profile's key, and shows
   the signed-in cap-account (dregg:…); "Log out" drops the session. It needs a
   reachable cloud endpoint; without one it simply reports the connection error.
   The exact request/response contract is documented in LOGIN-CONTRACT.md and
   covered by the unit test in test/login.test.mjs (a stub-cloud handshake), so
   the flow is verifiable without a live server.

You do not need funds or a live counterparty to evaluate the security model: the
key generation, encryption-at-rest, lock/unlock, and the signing-confirmation UI
are all exercisable on a fresh install.

PRIVACY / DATA
Keys never leave the device. No analytics, no telemetry, no third-party services.
The only network connection is to the dregg node the user configures. Full
policy: <PRIVACY_POLICY_URL>  (text: extension/PRIVACY.md in the source).

SOURCE & REPRODUCIBLE BUILD
This package contains a compiled WebAssembly binary (dregg_wasm_bg.wasm) and
bundled JavaScript (dist/*.js). Both are generated at build time from source — no
code is fetched or evaluated at runtime. The exact toolchain versions and the
step-by-step commands to reproduce every artifact from source are in
SOURCE-SUBMISSION.md (included in the submitted source archive). Public source
repository: <SOURCE_REPO_URL>.

CONTACT
dregg-cipherclerk@fg-goose.online
```

---

## Before submitting — fill in / attach

- Replace `<PRIVACY_POLICY_URL>` with the **hosted** URL of `PRIVACY.md` (both
  stores want a reachable privacy-policy URL, not a file path). The text is in
  `extension/PRIVACY.md`.
- Replace `<SOURCE_REPO_URL>` with the public repository URL.
- **AMO:** upload the source archive (so `SOURCE-SUBMISSION.md`, `wasm/`, and
  `extension/src/` are available to the reviewer) — required because the package
  ships a compiled wasm + bundled JS.
- **Chrome:** paste the Notes block; if asked for source during review, point to
  the same repo and `SOURCE-SUBMISSION.md`.
- Attach the listing screenshots and the 128×128 store icon.

## One-line permission justifications (for the store listing's permission prompt)

- `storage` — store the encrypted wallet on your device.
- `activeTab` — open the wallet's own pages and deliver receipt notifications to
  the active tab.
- `contextMenus` — the "Share capability…" right-click action.
- `alarms` — retry queued submissions while the background worker is asleep.
- host access to the configured dregg node — submit signed transactions and
  receive receipts (TLS only); localhost is an opt-in developer toggle.
- content script on all sites — inject the `window.dregg` provider so dApps can
  *request* an authorization (it cannot read keys or sign without your approval).

# Store Listing — Dragon's Egg Cipherclerk

Ready-to-paste copy and assets for the **Chrome Web Store** and **Firefox AMO**
listings. Everything here matches what the code actually does (see
`PRIVACY.md` and `STORE-READINESS-REVIEW.md`). Version **0.1.0 (alpha)**.

The privacy-policy URL to enter in both consoles:
`https://github.com/emberian/dregg/blob/main/extension/PRIVACY.md`

---

## Name

```
Dragon's Egg Cipherclerk
```

## Short description / summary

**Chrome Web Store** — short description (max 132 chars). Use this (115 chars):

```
A self-custody signing clerk for dregg. See exactly what you sign — no blind signing. Keys never leave your device.
```

**Firefox AMO** — summary (max 250 chars). Use this (242 chars):

```
A self-custody signing clerk for the dregg network. Every transaction is decoded into a faithful, effect-by-effect reading before you approve it — no blind signing. Named identities, capability tokens, ZK disclosure. Keys stay on your device.
```

---

## Detailed description

Paste into both stores (plain text; both render light markdown-ish formatting —
the headings and bullets below survive as readable text):

```
Dragon's Egg Cipherclerk is a self-custody signing wallet — a "cipherclerk" —
for the dregg network (https://dregg.net). It holds your signing identities,
shows you exactly what every transaction does before it signs, submits the
signed transaction to the dregg node you choose, and shows you the receipts as
they commit.

AUTHORIZATION-FIRST — SEE EXACTLY WHAT YOU SIGN
This wallet never signs blind. When a site asks the clerk to sign a "turn" (a
dregg transaction), it decodes the turn and renders a faithful, effect-by-effect
reading in plain language — "transfer 25 computrons from cell … to cell …",
"attenuate capability …", and so on — bound to the exact transaction hash the
node will verify. You see precisely what your key authorizes, and your signature
is released only when you explicitly approve. Anything the clerk cannot read is
shown as UNKNOWN with a do-not-sign-blind warning; it is never quietly hidden.

YOUR KEYS, ON YOUR DEVICE
First-run setup is guided and required: you set a passphrase and back up your
24-word recovery phrase before any key is created. Signing keys are generated and
stored only on your device, encrypted at rest with AES-256-GCM under a key
derived from your passphrase (PBKDF2-SHA256, 600,000 iterations). The decrypted
key exists only in the extension's background memory while unlocked, and is wiped
on lock or timeout. Keys and recovery phrases are never exposed to web pages and
never leave your device.

BRING YOUR OWN IDENTITY
An identity is a name you chose, not a hex key you pasted. Create and switch
between named profiles, each with its own Ed25519 key. Recovery uses standard
BIP39, and key derivation matches the dregg CLI and SDK, so a profile is portable
across tools.

LOG IN WITH YOUR WALLET — NO PASSWORD
Log into the live dregg network with a profile instead of a username and
password. The clerk fetches a one-time challenge from the cloud, signs it with
your selected key on-device, and holds the returned session — you are signed in
as a pseudonymous cap-account (dregg:…) derived from your key. Your key never
leaves the device, there is nothing to phish, and logging out drops the session.

RECEIPTS AND CAPABILITIES
The clerk tails the node's receipt stream and surfaces committed receipts —
transaction hash, effect kinds, finality, proof status — with a toolbar badge.
It holds capability tokens (attenuable, expiring grants), lets you accept and
share scoped capabilities, and evaluates authorization against the tokens you
hold. A powerbox grant ceremony lets you hand a site or app a NARROWED bearer
capability — bounded to one action, one cell, and an expiry you choose — that
can only ever be attenuated further, never amplified.

PRIVACY — PROVE IT WITHOUT REVEALING IT
Selective disclosure lets you respond to an authorization request three ways:
share a full token, reveal only the facts you choose, or prove authorization in
zero knowledge using range predicate proofs (Bulletproofs) — so the verifier
learns only allow or deny.

WHAT IT TALKS TO
The only network connection is to the dregg node you configure (a TLS dregg
devnet endpoint by default). There is no analytics, no telemetry, and no
tracking. Nothing is sent to us or any third party. See the privacy policy for
the full data story.

HONEST ALPHA
This is version 0.1.0, an early alpha for the dregg network. The signing security
model (no blind signing, keys never leave the device) is the core of the wallet
and is the part we have built and reviewed most carefully. Some experimental
surfaces (federation, CapTP handoff) are still maturing, and STARK membership
proof composition is intentionally disabled until its hash is collision-resistant
(range predicate proofs are unaffected). Use accordingly, and always keep your
recovery phrase backed up.

dregg: https://dregg.net
Privacy policy: https://github.com/emberian/dregg/blob/main/extension/PRIVACY.md
```

---

## Category and tags

| Field | Chrome Web Store | Firefox AMO |
|-------|------------------|-------------|
| Category | **Developer Tools** (primary). Productivity is an acceptable alternative; Developer Tools fits the dregg/DreggNet audience better. | **Other** or **Privacy & Security** (AMO has no dedicated wallet/web3 category) |
| Tags / keywords | dregg, wallet, signing, capability, self-custody, Ed25519, zero-knowledge | dregg, wallet, signing, capabilities, zero-knowledge, self-custody |
| Language | English | English |

---

## Per-permission justification (for the Chrome review form)

One honest line per permission. Paste each next to the matching permission in
the Chrome "Privacy practices" → permission-justification fields; AMO asks the
same in free text on submission.

| Permission | Justification |
|------------|---------------|
| `storage` | Stores the user's encrypted keys, identity profiles, capability tokens, observed receipts, per-origin permission grants, and node configuration locally. Nothing is uploaded. |
| `activeTab` | Associates an authorization or signing request with the page the user is currently interacting with, on user action. |
| `contextMenus` | Adds a "Share capability…" right-click action so a user can share a selected dregg cell ID as a capability URI. |
| `alarms` | Wakes the MV3 service worker on a short interval to flush the durable outbox (retry submitting signed transactions that were queued while offline). |
| `host_permissions`: `https://devnet.dregg.fg-goose.online/*`, `wss://devnet.dregg.fg-goose.online/*` | The default dregg node endpoint. Used to submit signed transactions, read public chain data (balances, status, directory, capability resolution), and subscribe to the node's receipt/event streams. The user can change this endpoint in settings. |
| `optional_host_permissions`: `http://localhost:8420/*`, `ws://localhost:8420/*`, `http://127.0.0.1:8420/*`, `ws://127.0.0.1:8420/*` | Optional, not granted by default. Requested only if a developer points the wallet at a local dregg node. |
| Content script on `<all_urls>` | Injects the `window.dregg` provider into pages so dApps can request authorizations, the same model as MetaMask's `window.ethereum`. The provider exposes no key-reading method; every signing/authorization request is gated by an explicit confirmation prompt. |
| `web_accessible_resources` (`dist/page.js`, `dregg_wasm.js`, `dregg_wasm_bg.wasm`, `bip39_english.txt`) | Resources the in-page provider loads in page context (the provider script, the bundled WASM crypto module, and the BIP39 wordlist). The WASM is bundled, never fetched remotely. |
| Remote code | None. No remote code is loaded or executed; the WASM module ships inside the package (CSP `script-src 'self' 'wasm-unsafe-eval'`). |

---

## Data-handling / privacy declaration

### Chrome Web Store — "Privacy practices" answers

- **Single purpose**: A self-custody signing wallet (cipherclerk) for the dregg
  network: it holds the user's signing identities, shows a faithful reading of
  each transaction before signing, submits signed transactions to the user's
  configured dregg node, and displays the resulting receipts.
- **Does this item collect or use … user data?** Yes — but only data the user
  provides for the extension's own function, stored locally. Answer the data-type
  checklist as:
  - Personally identifiable information: **No**
  - Health information: **No**
  - Financial and payment information: **No** (the wallet holds signing keys for
    a peer-to-peer network; it does not collect payment-card or bank data)
  - Authentication information: **Yes** — signing keys and the recovery phrase,
    stored locally and encrypted at rest; never transmitted.
  - Personal communications, location, web history, user activity, website
    content: **No**
- **Are you using/transferring data for purposes unrelated to the single
  purpose?** No.
- **Are you selling data to third parties?** No.
- **Are you using/transferring data to determine creditworthiness or for
  lending?** No.
- **Data usage compliance certifications**: check all three boxes:
  - I do not sell or transfer user data to third parties, outside of the
    approved use cases.
  - I do not use or transfer user data for purposes unrelated to my item's
    single purpose.
  - I do not use or transfer user data to determine creditworthiness or for
    lending purposes.
- **Privacy policy URL**:
  `https://github.com/emberian/dregg/blob/main/extension/PRIVACY.md`

### Firefox AMO — data-collection disclosure

- **Does this add-on collect/transmit user data?** It transmits only what the
  user explicitly initiates, and only to the dregg node the user configures:
  signed transactions the user approves, read requests for public chain data, and
  a subscription to that node's receipt stream filtered by the user's cell id.
- **No data is sent to the developer or any third party.** No analytics, no
  telemetry, no tracking, no ad networks, no third-party SDKs.
- **Keys never leave the device.** Signing keys and the recovery phrase are
  stored locally, encrypted at rest (AES-256-GCM, PBKDF2-SHA256 600k), and are
  never transmitted.
- **Privacy policy URL**:
  `https://github.com/emberian/dregg/blob/main/extension/PRIVACY.md`

---

## What to upload where

### Chrome Web Store

1. **Package**: `extension/dist/dregg-cipherclerk-chrome.zip`
2. **Store icon**: `extension/icons/icon-128.png` (128×128)
3. **Screenshots** (1280×800 PNG — upload at least three; order them so the hero
   is first):
   - `extension/store-assets/01-signing-authorization.png`  ← hero (see exactly what you sign)
   - `extension/store-assets/02-onboarding.png`
   - `extension/store-assets/03-identity-receipts.png`
   - `extension/store-assets/04-capabilities.png`
   - `extension/store-assets/05-zk-disclosure.png`
   - *(planned, regenerate via `make-screenshots.mjs`)* `06-cloud-login.png` — the
     Cloud Session panel, signed in as a `dregg:…` cap-account (no password shown).
   - *(planned)* `07-powerbox-grant.png` — the powerbox granting a narrowed,
     action-scoped, expiring capability with the "cannot be amplified" note.
4. **Name / short description / detailed description**: paste from the sections above.
5. **Category**: Developer Tools. **Privacy policy URL**: as above. Fill the
   per-permission justifications and the Privacy-practices answers from above.

### Firefox AMO

1. **Package**: `extension/dist/dregg-cipherclerk-firefox.xpi`
2. **Screenshots**: the same five 1280×800 PNGs from `extension/store-assets/`.
   (AMO accepts these sizes; the hero shot first.)
3. **Summary / description**: paste the AMO summary and the detailed description
   from above.
4. **Category**: Other (or Privacy & Security). **Privacy policy URL**: as above.
   Paste the AMO data-collection disclosure when prompted.

### Notes

- The icon and screenshots are committed under `extension/`. The screenshots are
  honestly **rendered** captures of the shipped popup/confirmation HTML with
  representative example data (no live node, no real keys); regenerate them with
  `node store-assets/make-screenshots.mjs`.
- The `*-raw.png` files in `store-assets/` are the bare UI captures (unframed),
  kept for reuse as small tiles; do not upload these as the primary screenshots.
- Rebuild the packages before upload if `src/` or the WASM changed:
  `./build.sh && ./build.sh package` (both must exit 0).

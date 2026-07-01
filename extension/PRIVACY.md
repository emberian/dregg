# Privacy Policy — Dragon's Egg Cipherclerk

Last updated: 2026-06-28

Dragon's Egg Cipherclerk is a self-custody signing wallet for the dregg
network. This policy describes exactly what data the extension handles. It is
written to match what the code actually does.

## Summary

- Your keys never leave your device.
- There is no analytics, no telemetry, and no tracking.
- We do not collect, sell, or share any personal information.
- The only network connection is to the dregg node you configure.

## What is stored, and where

All wallet data is stored locally in your browser's extension storage
(`chrome.storage.local`). Nothing is uploaded to us or to any third party.

Stored locally:

- Your signing key material (Ed25519 keypairs and the BIP39 recovery phrase),
  always **encrypted at rest** with AES-256-GCM under a key derived from your
  passphrase via PBKDF2-SHA256 (600,000 iterations). A passphrase and a
  recovery-phrase backup are required during setup; the wallet is never left
  unencrypted.
- Identity profile names and their public keys.
- Capability tokens, recently observed receipts, an activity log, per-origin
  permission grants, and your node endpoint configuration.
- If you log into the dregg network, the returned **session token** — a
  revocable, expiring bearer token, not a password — is held in the browser's
  in-memory session storage (cleared when the browser closes) where available,
  or local extension storage otherwise. The cap-account you sign in as is a
  pseudonymous identifier derived from your public key; there is no email,
  username, or password involved.

The decrypted private key exists only in the background service worker's memory
while the wallet is unlocked, and is wiped on lock or timeout. It is never
exposed to web pages or content scripts.

## What is sent over the network

The extension connects only to the dregg node you configure (by default, the
dregg devnet over TLS). It never contacts any other server, and it never sends
your private keys or recovery phrase anywhere.

When you use the wallet, the following may be sent to your configured node:

- Signed turns you explicitly approve (the cryptographic transactions you
  authorize in the signing confirmation prompt).
- Read requests for public chain data (balances, node status, directory
  listings, capability resolution).
- A subscription to the node's receipt event stream, filtered by your cell id,
  so the wallet can show receipts relevant to you.
- If you choose to log in, a login handshake with the cloud control plane: your
  public key, a one-time challenge signed by your key, and (on logout) the
  session token. Your private key is never sent — only a signature over the
  challenge. The cloud login URL defaults to your configured node host and can
  be pointed elsewhere in settings.

You can change or remove the node endpoint at any time in the extension's node
settings. Connecting to a local development node is an explicit, optional
permission that is not granted by default.

## Web page access

Like other wallets (e.g. MetaMask's `window.ethereum`), the extension injects a
`window.dregg` provider into pages so dApps can request authorizations. This
provider exposes **no** key-reading method. Web pages cannot read your keys,
and any signing or authorization request is gated by an explicit, per-action
confirmation prompt that you must approve.

## Third parties

None. There are no third-party services, SDKs, analytics, or ad networks in the
extension.

## Data deletion

Removing the extension, or clearing its storage, deletes all locally stored
data. Because your keys are stored only on your device, make sure you have
backed up your recovery phrase before removing the extension — it is the only
way to restore your wallet.

## Contact

Questions: dregg-cipherclerk@fg-goose.online

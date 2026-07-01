# Cap-account login contract (client side)

The wallet logs into the live dregg network by **proving it holds a key**, not
by presenting a username and password. This is the challenge–response floor of
the deos login manager (`docs/deos/SESSION-LOGIN.md` §2.1) reached over HTTP:
the cloud issues a nonce, the wallet signs it with the selected profile's
Ed25519 key, and the cloud returns a session.

This document is the **client half** of the contract, so the cap-auth lane's
webauth control plane can implement the matching server half. The wallet does
**not** reimplement the server: it never derives the account id itself, never
mints the session, and reads the server's response fields liberally so a small
naming drift is a config note, not a break.

The pure wire-shaping + validation lives in `src/login.ts`; the two impure
steps (the `fetch` and the Ed25519 signature) live in `src/background.ts`
(`capLogin` / `capLogout` / `getLoginStatus`). Golden teeth: `test/login.test.mjs`.

## Endpoints

All three are on the **cloud base URL** — `cloudUrl` from node settings, or the
node host itself when that is blank (`cloudBaseUrl(nodeUrl, cloudUrl)`).

| Step | Method + path | Auth |
| --- | --- | --- |
| Challenge | `POST {cloud}/auth/challenge` | none |
| Login | `POST {cloud}/auth/login` | none (the signature is the proof) |
| Logout | `POST {cloud}/auth/logout` | `Authorization: Bearer <session_token>` |

## 1. Challenge

Request:

```json
POST /auth/challenge
{ "public_key": "<hex32>" }
```

Response (`200`):

```json
{ "challenge": "<opaque string>", "expires_at": 1750000000 }
```

- `challenge` is a server-authored opaque string. The server binds whatever it
  needs into it (a random nonce, the pubkey, an expiry, the login domain); the
  client never parses it — it signs the exact UTF-8 bytes.
- `nonce` is accepted as an alias for `challenge`.
- `expires_at` (unix seconds) is optional / advisory to the client.

## 2. Sign

The client signs the raw UTF-8 bytes of `challenge` with the selected profile's
Ed25519 secret key — the same key that signs turns (`AgentWallet`). No client-side
hashing (Ed25519 hashes internally). Output is a 64-byte signature, hex-encoded.

The server verifies `Ed25519_verify(public_key, utf8(challenge), signature)`.

## 3. Login

Request:

```json
POST /auth/login
{
  "public_key": "<hex32>",
  "challenge":  "<the exact string from step 1>",
  "signature":  "<hex64>",
  "profile":    "<name>"
}
```

Response (`200`):

```json
{
  "session_token": "<opaque bearer>",
  "subject":       "dregg:<accountIdHex>",
  "account_id":    "<accountIdHex>",
  "expires_at":    1750000000
}
```

- The server recomputes the account id as
  `CellId::derive_raw(public_key, ACCOUNT_ROOT_TOKEN)` — the account-identity
  weld pinned by `sdk/tests/dreggnet_account_identity_e2e.rs`, where
  `ACCOUNT_ROOT_TOKEN = blake3("<account-identity label>:v1")`. So the subject
  the cloud reports **is** the substrate identity cell. The wallet displays
  `subject` verbatim; it does not derive the account id.
- Aliases read by the client: `session_token` ← `sessionToken` / `token`;
  `account_id` ← `accountId`; `expires_at` ← `expiresAt`.
- If `subject` is absent the client synthesizes `dregg:<account_id>`, and if
  that is also absent, `dregg:<pubkey-prefix>` — but a real deployment SHOULD
  return `subject`.

The wallet stores the session (token + subject + account id + expiry + bound
pubkey + profile + cloud URL) in **memory-only** `chrome.storage.session` where
available (cleared on browser close), falling back to local storage otherwise.
The token is a revocable, expiring bearer secret — never the private key.

## 4. Authenticated calls & logout

Authenticated cloud calls present `Authorization: Bearer <session_token>`.
Logout is best-effort: the client `POST`s `/auth/logout` with the bearer header,
then discards the local session regardless of the server's response (a network
failure must not strand a locked-out user). At n=1 the server-side session cap
goes dark; locally there is simply no token left to present.

## Host-permission note

The default cloud host is the configured node host, which the manifest already
grants (`host_permissions`). Pointing `cloudUrl` at a **different** host would
require that host to be covered by an (optional) host permission for the
service-worker `fetch` to succeed. The same-host default needs no new permission.

## Error handling

Every failure is surfaced as a plain `{ error }` to the popup: an unreachable
cloud, a missing challenge, a signing failure, a rejected signature, or a
missing session token. The wallet never silently treats a failed login as
success, and an expired stored session is dropped and reported as "log in again".

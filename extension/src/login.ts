/**
 * Cap-account login — the pure client-side contract for logging the wallet into
 * the live dregg cloud (the console / attach control plane).
 *
 * This module holds ONLY the wire-shaping and validation of the login handshake
 * — no `chrome`, no `wasm`, no key material — so it is unit-testable with plain
 * `node --test`. The background worker owns the two impure steps: the actual
 * `fetch` and the Ed25519 signature of the challenge with the selected profile's
 * key.
 *
 * ## The contract (challenge → sign → session)
 *
 * A cap-account is a *pseudonymous* identity: a key you hold, not a username +
 * password. Login proves possession of that key against a server-issued nonce —
 * exactly the challenge–response floor of the deos login manager
 * (`docs/deos/SESSION-LOGIN.md` §2.1: "the manager issues a random nonce; the
 * principal signs it with the secret half of `pubkey`; the manager verifies the
 * signature against `pubkey`").
 *
 * Client ⇄ cloud, three round-trips:
 *
 *   1. `POST {cloud}/auth/challenge`  body `{ "public_key": "<hex32>" }`
 *        → `200 { "challenge": "<opaque string>", "expires_at": <unix secs> }`
 *      The `challenge` is an opaque, server-authored string (it binds the nonce,
 *      the pubkey, an expiry, and the login domain — the client never has to
 *      parse it). `nonce` is accepted as an alias for `challenge`.
 *
 *   2. Client signs the raw UTF-8 bytes of `challenge` with the selected
 *      profile's Ed25519 secret key (`AgentWallet` key; the same key that signs
 *      turns). No hashing on the client — Ed25519 hashes internally.
 *
 *   3. `POST {cloud}/auth/login`  body
 *        `{ "public_key": "<hex32>", "challenge": "<the string>",
 *           "signature": "<hex64>", "profile": "<name>" }`
 *        → `200 { "session_token": "<opaque>", "subject": "dregg:<hex>",
 *                 "account_id": "<hex>", "expires_at": <unix secs> }`
 *      The server recomputes the account id as
 *      `CellId::derive_raw(public_key, ACCOUNT_ROOT_TOKEN)` (the account-identity
 *      weld — `sdk/tests/dreggnet_account_identity_e2e.rs`), so the subject the
 *      cloud reports IS the substrate identity cell. The client displays what
 *      the server returns; it does not derive the account id itself.
 *
 * Logout is `POST {cloud}/auth/logout` with `Authorization: Bearer <token>`,
 * then the local session is discarded. At n=1 the session cap goes dark on the
 * server; locally there is simply no token to present.
 *
 * The verb "reimplement the server" is deliberately NOT done here: this is the
 * client half against the cap-auth lane's contract. Field names are read
 * liberally (snake_case, common aliases) so a small server-side naming drift is
 * a config note, not a break.
 */

/** Path of the challenge endpoint on the cloud base. */
export const AUTH_CHALLENGE_PATH = "/auth/challenge";
/** Path of the login (signed-challenge) endpoint on the cloud base. */
export const AUTH_LOGIN_PATH = "/auth/login";
/** Path of the logout endpoint on the cloud base. */
export const AUTH_LOGOUT_PATH = "/auth/logout";

/** A server-issued challenge, normalized. */
export interface CapLoginChallenge {
  /** The opaque string to sign, verbatim. */
  challenge: string;
  /** Unix seconds after which the challenge is stale (0 = unknown). */
  expiresAt: number;
}

/** A held cap-account session (stored locally; the token is a bearer secret). */
export interface CapLoginSession {
  /** Bearer session token presented on authenticated cloud calls. */
  token: string;
  /** Display subject the server reports, e.g. `dregg:<accountIdHex>`. */
  subject: string;
  /** The account id (identity-cell hex) the server derived, if provided. */
  accountId: string;
  /** Hex public key the session is bound to. */
  publicKeyHex: string;
  /** Name of the profile used to log in. */
  profile: string;
  /** Cloud base URL the session was minted against. */
  cloudUrl: string;
  /** Unix seconds the session expires (0 = server did not say). */
  expiresAt: number;
  /** Unix ms the client recorded the login. */
  loggedInAt: number;
}

/** Public login status handed to the popup. */
export interface CapLoginStatus {
  loggedIn: boolean;
  subject: string | null;
  accountId: string | null;
  profile: string | null;
  cloudUrl: string;
  expiresAt: number;
  /** True when a stored session exists but has passed its expiry. */
  expired: boolean;
}

// --------------------------------------------------------------------------
// Pure hex / utf8 helpers (no Buffer, no chrome)
// --------------------------------------------------------------------------

/** Lowercase hex of a byte array. */
export function bytesToHex(bytes: ArrayLike<number>): string {
  let s = "";
  for (let i = 0; i < bytes.length; i++) s += (bytes[i] & 0xff).toString(16).padStart(2, "0");
  return s;
}

/** UTF-8 encode a string to bytes. */
export function utf8Bytes(s: string): Uint8Array {
  return new TextEncoder().encode(s);
}

/** True iff a string is exactly `len` hex characters. */
export function isHex(s: unknown, len?: number): boolean {
  if (typeof s !== "string") return false;
  if (len !== undefined && s.length !== len) return false;
  return /^[0-9a-fA-F]*$/.test(s) && s.length > 0;
}

// --------------------------------------------------------------------------
// Cloud base URL selection
// --------------------------------------------------------------------------

/**
 * The cloud base URL the login handshake targets. A deployment may run the
 * webauth control plane on the same host as the node (the default) or a
 * separate one (`cloudUrl` override). Trailing slash stripped.
 */
export function cloudBaseUrl(nodeUrl: string, cloudUrl?: string | null): string {
  const base = (cloudUrl && cloudUrl.trim()) ? cloudUrl.trim() : nodeUrl;
  return base.replace(/\/+$/, "");
}

// --------------------------------------------------------------------------
// Request bodies
// --------------------------------------------------------------------------

/** Body for `POST /auth/challenge`. */
export function challengeRequestBody(publicKeyHex: string): { public_key: string } {
  return { public_key: publicKeyHex };
}

/** Body for `POST /auth/login`. */
export function loginRequestBody(
  publicKeyHex: string,
  challenge: string,
  signatureHex: string,
  profile: string,
): { public_key: string; challenge: string; signature: string; profile: string } {
  return { public_key: publicKeyHex, challenge, signature: signatureHex, profile };
}

// --------------------------------------------------------------------------
// Response parsing / validation
// --------------------------------------------------------------------------

type Json = Record<string, unknown> | null | undefined;

function str(o: Json, ...keys: string[]): string | null {
  if (!o) return null;
  for (const k of keys) {
    const v = (o as Record<string, unknown>)[k];
    if (typeof v === "string" && v.length > 0) return v;
  }
  return null;
}

function num(o: Json, ...keys: string[]): number {
  if (!o) return 0;
  for (const k of keys) {
    const v = (o as Record<string, unknown>)[k];
    if (typeof v === "number" && Number.isFinite(v)) return v;
  }
  return 0;
}

/** Normalize a `/auth/challenge` response. */
export function parseChallengeResponse(data: Json): CapLoginChallenge | { error: string } {
  const challenge = str(data, "challenge", "nonce");
  if (!challenge) return { error: "cloud did not return a challenge" };
  return { challenge, expiresAt: num(data, "expires_at", "expiresAt") };
}

/** Normalize a `/auth/login` response into a held session. */
export function parseLoginResponse(
  data: Json,
  bound: { publicKeyHex: string; cloudUrl: string; profile: string; nowMs: number },
): CapLoginSession | { error: string } {
  const token = str(data, "session_token", "sessionToken", "token");
  if (!token) return { error: "cloud login did not return a session token" };
  const accountId = str(data, "account_id", "accountId") || "";
  const subject = str(data, "subject") || (accountId ? `dregg:${accountId}` : `dregg:${bound.publicKeyHex.slice(0, 16)}`);
  return {
    token,
    subject,
    accountId,
    publicKeyHex: bound.publicKeyHex,
    profile: bound.profile,
    cloudUrl: bound.cloudUrl,
    expiresAt: num(data, "expires_at", "expiresAt"),
    loggedInAt: bound.nowMs,
  };
}

/** True iff a session has passed its (nonzero) expiry. */
export function sessionIsExpired(session: CapLoginSession | null, nowSec: number): boolean {
  if (!session) return false;
  return session.expiresAt > 0 && nowSec >= session.expiresAt;
}

/** Derive the public status the popup renders from a stored session. */
export function statusFromSession(
  session: CapLoginSession | null,
  cloudUrl: string,
  nowSec: number,
): CapLoginStatus {
  const expired = sessionIsExpired(session, nowSec);
  const live = !!session && !expired;
  return {
    loggedIn: live,
    subject: live ? session!.subject : null,
    accountId: live ? session!.accountId : null,
    profile: live ? session!.profile : null,
    cloudUrl,
    expiresAt: session?.expiresAt ?? 0,
    expired,
  };
}

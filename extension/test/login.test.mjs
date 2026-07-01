// Cap-account login contract — the pure wire-shaping + validation of the
// challenge -> sign -> session handshake. These teeth pin the CLIENT half of
// the contract against a stub cloud (no chrome, no wasm): the request bodies
// are shaped correctly, the responses parse liberally (snake_case + aliases),
// a missing token/challenge is rejected, the subject falls back sanely, and
// session expiry is honored.
import { test } from 'node:test';
import assert from 'node:assert/strict';
import {
  AUTH_CHALLENGE_PATH,
  AUTH_LOGIN_PATH,
  AUTH_LOGOUT_PATH,
  bytesToHex,
  cloudBaseUrl,
  challengeRequestBody,
  loginRequestBody,
  parseChallengeResponse,
  parseLoginResponse,
  sessionIsExpired,
  statusFromSession,
} from './.build/login.mjs';

const PUBKEY = 'aa'.repeat(32);
const ACCOUNT = 'bb'.repeat(32);

test('endpoint paths are the agreed contract', () => {
  assert.equal(AUTH_CHALLENGE_PATH, '/auth/challenge');
  assert.equal(AUTH_LOGIN_PATH, '/auth/login');
  assert.equal(AUTH_LOGOUT_PATH, '/auth/logout');
});

test('bytesToHex is lowercase, zero-padded, byte-masked', () => {
  assert.equal(bytesToHex([0, 15, 255, 16]), '000fff10');
  assert.equal(bytesToHex(new Uint8Array([1, 2, 3])), '010203');
});

test('cloudBaseUrl prefers cloudUrl, falls back to node, strips trailing slash', () => {
  assert.equal(cloudBaseUrl('https://node.example/', ''), 'https://node.example');
  assert.equal(cloudBaseUrl('https://node.example', 'https://cloud.example//'), 'https://cloud.example');
  assert.equal(cloudBaseUrl('https://node.example', null), 'https://node.example');
  assert.equal(cloudBaseUrl('https://node.example', '   '), 'https://node.example');
});

test('request bodies carry exactly the contract fields', () => {
  assert.deepEqual(challengeRequestBody(PUBKEY), { public_key: PUBKEY });
  assert.deepEqual(
    loginRequestBody(PUBKEY, 'the-challenge', 'cc'.repeat(64), 'default'),
    { public_key: PUBKEY, challenge: 'the-challenge', signature: 'cc'.repeat(64), profile: 'default' },
  );
});

test('parseChallengeResponse accepts `challenge` and the `nonce` alias', () => {
  assert.deepEqual(parseChallengeResponse({ challenge: 'x', expires_at: 100 }), { challenge: 'x', expiresAt: 100 });
  assert.deepEqual(parseChallengeResponse({ nonce: 'y' }), { challenge: 'y', expiresAt: 0 });
});

test('parseChallengeResponse rejects a response with no challenge', () => {
  assert.ok('error' in parseChallengeResponse({}));
  assert.ok('error' in parseChallengeResponse(null));
});

test('parseLoginResponse builds a session and honors the server subject', () => {
  const s = parseLoginResponse(
    { session_token: 'tok', subject: `dregg:${ACCOUNT}`, account_id: ACCOUNT, expires_at: 5000 },
    { publicKeyHex: PUBKEY, cloudUrl: 'https://cloud.example', profile: 'default', nowMs: 1234 },
  );
  assert.ok(!('error' in s));
  assert.equal(s.token, 'tok');
  assert.equal(s.subject, `dregg:${ACCOUNT}`);
  assert.equal(s.accountId, ACCOUNT);
  assert.equal(s.publicKeyHex, PUBKEY);
  assert.equal(s.profile, 'default');
  assert.equal(s.cloudUrl, 'https://cloud.example');
  assert.equal(s.expiresAt, 5000);
  assert.equal(s.loggedInAt, 1234);
});

test('parseLoginResponse synthesizes a subject from account_id when absent', () => {
  const s = parseLoginResponse(
    { token: 'tok', account_id: ACCOUNT },
    { publicKeyHex: PUBKEY, cloudUrl: 'https://c', profile: 'p', nowMs: 0 },
  );
  assert.equal(s.subject, `dregg:${ACCOUNT}`);
});

test('parseLoginResponse falls back to a pubkey-prefix subject with no account_id', () => {
  const s = parseLoginResponse(
    { session_token: 'tok' },
    { publicKeyHex: PUBKEY, cloudUrl: 'https://c', profile: 'p', nowMs: 0 },
  );
  assert.equal(s.subject, `dregg:${PUBKEY.slice(0, 16)}`);
});

test('parseLoginResponse rejects a response with no session token', () => {
  const r = parseLoginResponse({ subject: 'dregg:x' }, { publicKeyHex: PUBKEY, cloudUrl: 'c', profile: 'p', nowMs: 0 });
  assert.ok('error' in r);
});

test('sessionIsExpired honors a nonzero expiry only', () => {
  assert.equal(sessionIsExpired(null, 100), false);
  assert.equal(sessionIsExpired({ expiresAt: 0 }, 10_000_000), false); // 0 = no expiry
  assert.equal(sessionIsExpired({ expiresAt: 100 }, 99), false);
  assert.equal(sessionIsExpired({ expiresAt: 100 }, 100), true);
  assert.equal(sessionIsExpired({ expiresAt: 100 }, 101), true);
});

test('statusFromSession reflects live / expired / logged-out', () => {
  const live = { token: 't', subject: 'dregg:x', accountId: 'x', publicKeyHex: PUBKEY, profile: 'default', cloudUrl: 'c', expiresAt: 5000, loggedInAt: 0 };
  const now = statusFromSession(live, 'c', 100);
  assert.equal(now.loggedIn, true);
  assert.equal(now.subject, 'dregg:x');
  assert.equal(now.profile, 'default');
  assert.equal(now.expired, false);

  const expired = statusFromSession({ ...live, expiresAt: 50 }, 'c', 100);
  assert.equal(expired.loggedIn, false);
  assert.equal(expired.subject, null);
  assert.equal(expired.expired, true);

  const out = statusFromSession(null, 'c', 100);
  assert.equal(out.loggedIn, false);
  assert.equal(out.subject, null);
  assert.equal(out.expired, false);
});

// A documented manual end-to-end against a stub cloud: the exact shape the
// background worker drives. This exercises the full client contract (fetch is
// stubbed; the signature is a fixed 64-byte stand-in) so the wire is proven
// without a live server.
test('full client handshake against a stub cloud (documented manual flow)', () => {
  const cloud = cloudBaseUrl('https://node.example', '');

  // 1. Client asks for a challenge.
  const chReq = challengeRequestBody(PUBKEY);
  assert.deepEqual(chReq, { public_key: PUBKEY });

  // Stub cloud responds with a nonce-bearing challenge.
  const chResp = { challenge: `login:${cloud}:nonce-deadbeef`, expires_at: 2_000 };
  const ch = parseChallengeResponse(chResp);
  assert.ok(!('error' in ch));

  // 2. Client signs the challenge bytes (stubbed 64-byte signature).
  const signatureHex = bytesToHex(new Uint8Array(64).fill(7));
  assert.equal(signatureHex.length, 128);

  // 3. Client posts the signed challenge.
  const loginReq = loginRequestBody(PUBKEY, ch.challenge, signatureHex, 'default');
  assert.equal(loginReq.challenge, ch.challenge);
  assert.equal(loginReq.signature, signatureHex);

  // Stub cloud verifies and mints a session bound to the derived account id.
  const loginResp = { session_token: 'sess-xyz', subject: `dregg:${ACCOUNT}`, account_id: ACCOUNT, expires_at: 100_000 };
  const session = parseLoginResponse(loginResp, { publicKeyHex: PUBKEY, cloudUrl: cloud, profile: 'default', nowMs: 1 });
  assert.ok(!('error' in session));

  // 4. The held session is live.
  const status = statusFromSession(session, cloud, 10);
  assert.equal(status.loggedIn, true);
  assert.equal(status.subject, `dregg:${ACCOUNT}`);
});

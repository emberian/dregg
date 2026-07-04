# AUTH-DEPLOY — the request-authentication gate on the deployed serve path

`Reactor/AuthDeploy.lean` folds a real request-authentication gate onto the same
deployed serve path the orb binary runs. A route marked **protected** now
requires authentication, and the decision is the REAL `Jwt.authenticate`
(RFC 7515/7519) — the validated, key-pinned JWT machine — not a stub. On a
failure it emits a serializer-built **401**; the route handler body is never
reached.

## Where this sits on the deployed path

The deployed orb runs `Arena.Orb.main → Reactor.Deploy.deployStepGuarded →
serveGuarded`. On a bare dispatch, `serveGuarded` runs `guardOne`: the REAL
Policy admission and the REAL Safety traversal decode, emitting a 403/404 on
refusal and the normal `deployResp` otherwise.

This file layers one more gate in the **same shape**, over the **same**
`deploySubs` / `deployResp` / `guardOne` machinery:

- `authGuardOne input req` wraps `Deploy.guardOne`. On a protected route it runs
  `Jwt.authenticate deployJwtCfg` on the request's `Authorization` header:
  - a `reject` (no token, bad signature, alg confusion, expiry, claim mismatch)
    → `serialize unauthorized401`;
  - an `admit` → defer to `Deploy.guardOne` (Policy/Safety + `deployResp`).
  - an unprotected route defers to `Deploy.guardOne` unchanged.
- `serveAuthGuarded input` is `Deploy.serveGuarded` with `authGuardOne` on the
  dispatch arm: byte-identical on the FSM-send path and on unprotected routes,
  so it only ever ADDS the 401 branch to the bytes the deployed serve emits.
- `deployStepAuthGuarded` re-exports the same observation-state advance
  (`Metrics.inc`, `Tap.step`, `Trace` id) so a `main` repointed to the auth gate
  runs exactly this.

`serveAuthGuarded_unprotected` proves `serveAuthGuarded input =
Deploy.serveGuarded input` on any unprotected dispatch — the gate is a strict
extension of the deployed serve, not a sibling.

## The seam theorems (over the served bytes)

- **`deployed_auth_401`** — a dispatched protected request whose REAL
  `Jwt.authenticate` does not admit yields EXACTLY `serialize unauthorized401`
  (status 401, fixed body). Never a 200, never the handler body.
- **`deployed_auth_alg_confusion`** — a dispatched protected request whose parsed
  token is algorithm-confused (`alg = none`, or `alg ≠` the selected key's own
  algorithm) is rejected on the deployed path → the 401 bytes. This transports
  `Jwt.jwt_alg_confusion_safe`:
  - `deployJwt_admit_no_confusion` is the direct transport (an admit forces a
    non-confused token: `alg ≠ none ∧ alg = key.alg`);
  - `authenticate_alg_confused_rejects` drives the reject arm through
    `Jwt.afterKey`.

### Concrete drivers of the reject condition

- `deployJwt_noToken` — a protected request with no `Authorization` header is
  rejected `noToken` by the REAL extraction over the deployed `[bearer]` source.
- `deployJwt_admit_good_sig` / `deployJwt_badsig_rejects` — transport of
  `jwt_rejects_bad_sig`: a `verify`-rejected signature is never admitted, so it
  rejects.

### The gate genuinely branches — kernel `decide`, no reactor

Literal `Jwt.afterKey` executions (no strings, so the kernel reduces them):

- `afterKey_none_rejects` — `alg = none` → `reject algNone`;
- `afterKey_rs_rejects` — RS256 header over the HS256 key → `reject algMismatch`;
- `afterKey_hs_admits` — a well-formed HS256 token with a matching signature →
  `admit []` (the admit arm is genuinely reachable — the gate is not
  reject-all).

Plus `protected_admin` / `unprotected_health`: the `/admin` surface is protected,
`/health` is not.

## The deployed JWT config

`deployJwtCfg` fills the `Jwt.Config` crypto/decode boundaries with concrete
total functions (one pinned HS256 key `k1`; `bearer` source; a `sigValid`
stand-in that accepts when the signature equals the signing input, so both arms
are reachable). Every `jwt_*` control-flow theorem quantifies over ALL configs,
so this concrete choice weakens no gate: the verification algorithm is pinned to
the key, never taken from the token.

## Section B — the Basic gate (RFC 7617)

The same construction for the `Basic` scheme via the REAL
`BasicAuth.authenticate`: `serveBasicAuthGuarded`, and
`deployed_basic_401` — a dispatched protected request whose `authenticate`
challenges yields the serializer-built 401 with the realm challenge.
`deployBasic_noCreds` (concrete, via `basic_no_creds_challenges`) and
`deployBasic_admit_good_cred` (transport of `basic_rejects_bad_cred`) back it.

## Build / axioms

`lake build Reactor.AuthDeploy` is green. Zero sorries. `#print axioms` for the
two seam theorems (`deployed_auth_401`, `deployed_auth_alg_confusion`) reports
`[propext, Classical.choice, Quot.sound]` — the permitted set. The deployed spine
(`Reactor.Deploy`, `Reactor.Serve`, `Reactor.App`, `Reactor.Config`,
`Reactor.Bridge`, `Reactor.H2Ingress`, `Arena.Orb`) builds green alongside it.

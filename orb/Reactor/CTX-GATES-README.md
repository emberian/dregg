# CTX-GATES — all ten byte-driving stages composed into the deployed orb

`deployStagesFull2` (section **(7)** of `Reactor/Deploy.lean`) composes **all
ten** byte-driving stages into the deployed serve, and `main` runs it via
`deployStepFull2`. The ten stages are each built and unit-proven in
`Reactor/Stage/*.lean`; composing them into the served path is what lets their
gates fire on a real orb run.

The earlier `deployStagesFull` (run via `deployStepFull`) composes only **two**
safe transforms — `securityheadersStage` and `headerStage` — onto the
traversal/policy gates. `deployStages` / `servePipeline` / `serveGuarded` and
`deployStagesFull` (section (6)) remain in place — `deployStagesFull2` is purely
additive.

## The composed list (`Reactor.Deploy.deployStagesFull2`)

Request-phase order (gates first, then the handler-side transforms):

| # | stage | kind | real decision | deployed config (production-safe) |
|---|-------|------|---------------|-----------------------------------|
| 1 | `jwtAdminStage` | GATE 401 | `Jwt.authenticate` | only on `/admin*`; other paths pass |
| 2 | `ipfilterPermissiveStage` | GATE 403 | `IpFilter.permits` | `defaultDeny := false`; no peer addr ⇒ admit |
| 3 | `rateHighStage` | GATE 429 | `Rate.tryAdmit` | full high-cap bucket ⇒ admit |
| 4 | `cacheEmptyStage` | GATE (serve stored) | `Cache.Store.get?`/`isFresh` | empty store ⇒ always miss |
| 5 | `redirectStage` | GATE 3xx | `Redirect.redirect` | verbatim; only its `/old` target |
| 6 | `traversalStage` | GATE 404 | `Route.Path.decodeSegs` | verbatim (existing) |
| 7 | `policyStage` | GATE 403 | `Policy.serveDecision` | verbatim (existing) |
| 8 | `headerRewriteStage` | transform | `Header.run` | verbatim: Server / x-upstream / x-corr |
| 9 | `deployCorsStage` | transform | `Cors.acaoValue` | re-cased to canonical lowercase `origin` |
| 10 | `gzipStage` | transform | `Gzip.gzipStored` | verbatim |
| 11 | `htmlrewriteStage` | transform | `HtmlRewrite.tokenize` | verbatim |
| 12 | `securityheadersStage` | transform | `SecurityHeaders.render` | verbatim (existing) |
| 13 | `headerStage` | transform | `Header.run` | verbatim (existing) |

The five new gates run **first** (request phase, in list order), so a refused
request emits its pristine gate response with **none** of the transforms. On the
admitted arm the response phase runs in reverse (the onion): `headerStage`
innermost, then security headers, then the markup rewrite, then gzip (compresses
the rewritten body), then CORS, and `headerRewriteStage` outermost (its hop-strip
keeps every non-hop header the inner transforms added — `deployProg_preserves_field`).

### Why several gates are re-wired rather than dropped in verbatim

The unit stages in `Reactor/Stage/*` are configured for their non-vacuity
*witnesses*: `jwtStage` rejects **every** request; `rateStage` / `ipfilterStage`
fail **closed**; `cacheStage` is **warm** on `GET /`. Dropped in verbatim they would
401/429/403 or spuriously cache `/health`. Each is therefore wired
production-safe here while still routing through the **real** library decision
(same `Jwt.authenticate` / `IpFilter.permits` / `Rate.tryAdmit` /
`Cache.Store.get?`). `deployCorsStage` re-wires `Cors.acaoValue` to read the arena's
**canonical lowercase** `origin` header — the unit `corsStage` looked up `Origin`,
which the HTTP/1.1 parser lowercases, so it could never fire on the deployed path.

`Reactor.Stage.IpFilter` sits *above* `Deploy` in the import graph (via
`Reactor.Bridge → Reactor.Deploy`), so importing it would cycle; the permissive
ip-filter gate is wired over the base `IpFilter` library directly.

### Build note

Composing the real Jwt gate pulls `Crypto` (HACL*/EverCrypt `@[extern]`
primitives — `ed25519Verify` et al.) into the `orb` binary, so its `moreLinkArgs`
in `lakefile.toml` now link `ffi/crypto_shim.o` + `libevercrypt.a` — the same recipe
`crypto-selftest` uses. The deployed JWT config routes around the crypto (its verify
boundaries are pure stubs), but the Jwt object references the extern symbols, so the
link needs them. No unverified C crosses the seam.

## Theorems (`lake build orb` green, zero sorries)

`#print axioms` footprint of each is `{propext, Classical.choice, Quot.sound}`:

* `deployStepFull2_serves` — what `main` writes is definitionally `servePipelineFull2` (total).
* `full2_admin_gate` — for any `/admin*` request the real `Jwt.authenticate` rejects,
  the built response of the **whole** `deployStagesFull2` fold is exactly the `401`
  (the gate short-circuits the handler and every later stage).
* `full2_admin_serves_401` / `full2_admin_status_401` — the non-vacuous witness: the
  concrete credential-less `GET /admin` context serves the `401` through the full fold,
  off the genuine FSM (`adminNoAuth_rejects : decision = reject .noToken` by `rfl`).
* `servePipelineFull2_admin_401` — the seam lifted to the bytes `main` writes: an
  `/admin`-no-token **dispatch** makes `servePipelineFull2 input = serialize unauthorized`.
* `rateHigh_always_admits` — the high-limit bucket admits (real `Rate.tryAdmit`, `decide`).

## The real orb run — gates firing (proof the stages byte-drive)

Binary: `.lake/build/bin/orb` (sans-IO core: request bytes on stdin → response on
stdout). Exact observed output:

### (a) `GET /health` → 200 (all stages compose; still works)

```
$ printf 'GET /health HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 200 OK
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
X-Frame-Options: DENY
X-Content-Type-Options: nosniff
Referrer-Policy: no-referrer
Server: drorb
x-upstream: 1572395042
x-corr: 71.69.84.32.47.104.101.97.108.116.104. ...
Content-Length: 2

ok
```

### (b) `GET /admin` with NO Authorization → 401 (the JWT gate fires)

The response is **pristine** — no security headers, no `x-upstream`/`x-corr` — proving
the jwt gate short-circuited **first**, skipping the handler and every transform.

```
$ printf 'GET /admin HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 401 Unauthorized
WWW-Authenticate: Bearer
Content-Length: 31

invalid or missing bearer token
```

### (c) `Accept-Encoding: gzip` → gzipped body + `Content-Encoding: gzip` (the gzip transform fires)

Note: `GET /something` (the literal example) is instead **403 Forbidden — "policy:
undeclared surface"**: the policy gate (outer) refuses the undeclared surface before
gzip runs — itself a demonstration that the gates compose in order. gzip is therefore
shown on a **policy-admitted** path.

```
$ printf 'GET /static/app.js HTTP/1.1\r\nHost: x\r\nAccept-Encoding: gzip\r\n\r\n' | orb
HTTP/1.1 200 OK
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
...
Content-Encoding: gzip
Server: drorb
...
Content-Length: 28

<body is the RFC-1952 gzip container>
```

Hexdump of the body region — the RFC-1952 magic `1f 8b 08 00` then a DEFLATE stored
block wrapping the plaintext `asset` and the CRC-32/size trailer:

```
000001e0: 0d0a 0d0a 1f8b 0800 0000 0000 00ff 0105  ................
000001f0: 00fa ff61 7373 6574 5c5a af02 0500 0000  ...asset\Z......
```

Control — **without** `Accept-Encoding`, the same path serves **plain** bytes, no
`Content-Encoding`, `Content-Length: 5` (`asset`) — so the gzip change is the header's
doing, not the handler's:

```
$ printf 'GET /static/app.js HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 200 OK
...
Server: drorb
...
Content-Length: 5

asset
```

### (d) request with an `Origin` header → `Access-Control-Allow-Origin` (the CORS transform fires)

```
$ printf 'GET /health HTTP/1.1\r\nHost: x\r\nOrigin: https://app.example.com\r\n\r\n' | orb
HTTP/1.1 200 OK
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
X-Frame-Options: DENY
X-Content-Type-Options: nosniff
Referrer-Policy: no-referrer
Access-Control-Allow-Origin: https://app.example.com
Server: drorb
x-upstream: 1572395042
x-corr: ...
```

The real `Cors.acaoValue` over `corsPolicy` grants the allowed origin; an
off-allowlist origin adds nothing (`Cors.cors_no_leak`).

## Files

* `Reactor/Deploy.lean` — section (7): the ten-stage list, the production-safe gate
  wrappers, `servePipelineFull2` / `deployStepFull2`, and the JWT gate seams.
* `Arena/Orb.lean` — `main` repointed to `deployStepFull2` (h2c fork preserved:
  `hasH2Preface → serveIngress`, else `deployStepFull2`).
* `lakefile.toml` — `orb` exe links the crypto shim (required by the composed Jwt gate).

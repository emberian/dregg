# MIDDLEWARE-DEPLOY — the real middleware chain on the deployed response

`Reactor/MiddlewareDeploy.lean` folds the response-security middleware onto the
bytes the deployed serve writes. It connects three already-verified single-file
libraries — `Middleware`, `SecurityHeaders` (RFC 6797 HSTS), `Cors` (WHATWG
Fetch) — onto `Reactor.Deploy.serveFull`, the function `main`'s serve runs on a
dispatch.

## The bar and how this meets it

The connected path is:

```
Arena/Orb.lean main
  → Reactor.Deploy.deployStepGuarded
  → serveGuarded / serveFull
  → serialize (Deploy.deployResp input)      -- the response bytes on a dispatch
```

`serveFull` on a dispatch emits `serialize (deployResp input)` — the application
response passed through the real `Header.run` rewrite. This file runs the REAL
`Middleware.run` chain over *that* response's headers and states its seam
theorems over the result.

## What is wired

* `deploySecPolicy` — a `SecurityHeaders.Policy` carrying an HSTS member
  (`max-age = 31536000`, `includeSubDomains`, RFC 6797). `SecurityHeaders.render`
  emits its `Strict-Transport-Security` field.
* `deployCorsPolicy` — a `Cors.Policy` with an exact-match origin allowlist
  (`https://app.example.com`), no wildcard, credentials off.
* `secMw` / `corsMw o` — two `Middleware.Mw` layers: each leaves the request
  alone and prepends its header contribution to the response.
* `deployChain o = [secMw, corsMw o]` — security on the **outside**, CORS inside.
* `deployMwHeaders input o = Middleware.run (deployChain o) (fun _ => baseHeaders input) ()`
  — the real onion run, where `baseHeaders input` is the `String` (Latin-1) view
  of the deployed response's headers.

`deployMwHeaders_expand` proves the run equals
`SecurityHeaders.render deploySecPolicy ++ (Cors.actualResponse deployCorsPolicy o ++ baseHeaders input)`
using only the framework's `Middleware.run_cons` (twice) and
`Middleware.chain_identity` — so the ordering is the onion law's, not ad hoc: the
security layer's `onResp` runs last and its headers land at the front.

## Seam theorems

* **`deployed_security_headers`** — the deployed middleware headers carry the real
  `SecurityHeaders` output: `(deployMwHeaders input o).lookup
  "Strict-Transport-Security" = some (hstsRender deployHsts)`. HSTS is present on
  the deployed path. Proof: `deployMwHeaders_expand` + `List.lookup_append` +
  `SecurityHeaders.render_hsts_present` (the security layer is at the front, so
  the lookup reads it).

* **`deployed_cors_no_leak`** — a disallowed origin never gets ACAO. For an origin
  off the allowlist the CORS layer contributes `[]` (`cors_layer_empty`, from
  `Cors.actualResponse` collapsing when the ACAO value is `none`), so the deployed
  headers are byte-identical to the no-CORS response, and the CORS decision itself
  has `hasAcao = false` (`Cors.cors_no_leak_actual`).

* **`deployed_cors_no_leak_full`** — the *whole* deployed header set has
  `hasAcao = false` for a disallowed origin, under the side condition
  `(baseHeaders input).lookup "Access-Control-Allow-Origin" = none`. That side
  condition holds on the deployed path: `deployProg` only stamps
  `Server`/`x-upstream`/`x-corr` and strips hop-by-hop headers — it never emits a
  CORS header. The security layer carries no ACAO either (`sec_no_acao`).

* **`deployed_cors_grants`** — an allowed origin *does* get ACAO
  (`Cors.cors_actual_grants`). The gate genuinely branches; it is not a constant.

* **`deployed_mw_over_serveFull`** — on a dispatch, `serveFull input =
  serialize (deployResp input)` and `baseHeaders input` is the `String` view of
  that response's headers. So the seams above range over the headers the deployed
  serve actually writes, not a bespoke response.

Concrete `decide`/`#guard` checks (`origin_allowed_app`, `origin_denied_evil`,
`acao_echoes_app`, `acao_none_evil`, `hsts_wellformed_deploy`) execute the real
decisions on the deployed policies so the branch is a mechanism, not three names
for one output.

## Build / axioms

* `lake build Reactor` is green; `Reactor.lean` imports `Reactor.MiddlewareDeploy`.
* Zero `sorry`. Every seam theorem's `#print axioms` is a subset of
  `{propext, Quot.sound, Classical.choice}` (`acao_echoes_app` uses none;
  `hsts_wellformed_deploy` uses only `propext`).

## Boundary / UNCLOSED

* **`String`↔`Bytes` header boundary.** The seams are stated at the `String`-keyed
  header level — the native type of the `SecurityHeaders` / `Cors` models — over
  the Latin-1 view `Deploy.latin1B` of the response's byte headers. That view is
  proof-inert here (the seams only compare and look up header *names*). Folding the
  augmented header block back to wire bytes, so the literal bytes `main` writes
  contain the middleware headers rather than the `String` view of the response
  those bytes serialize, is left as a boundary.
* **Gate arms.** `main` runs `serveGuarded`, whose Policy/Safety arms emit fixed
  serializer bodies. `deployed_mw_over_serveFull` is over `serveFull` (the admit
  arm's payload); the 403/404 gate responses are out of scope for the header fold.
* The CORS model is the allow/deny decision only (preflight caching, `Vary:
  Origin`, safelist classification are the model's own boundaries); HSTS carries
  `max-age` as a `Nat` (directive-value ABNF is the model's boundary).

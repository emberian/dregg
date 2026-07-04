# BYTE-DRIVING COMPLETE — all deployed stages drive the served bytes

`main` (`Arena/Orb.lean`) runs `Reactor.Deploy.deployStepFull2`, whose response
component is `servePipelineFull2` — `serialize` of the built fold over
`Reactor.Deploy.deployStagesFull2` (13 stages: 7 request-phase gates + 6 response
transforms). This note records the live orb transcript showing the stages driving
bytes, and the verified seams that prove the two transforms (gzip,
cors) fire through the *composed* ten-stage fold — not just in isolation.

Toolchain: Lean 4 v4.17.0, `lake build orb` green (178/178). Binary:
`.lake/build/bin/orb` (sans-IO core: request bytes on stdin → response on stdout).

---

## gzip and cors fire on the deployed orb

gzip and cors fire on the deployed orb. Two design points make this work:

1. **`ctxOf` carries the REAL parsed request headers.** `ctxOf input` builds its
   `Ctx.req` from `dispatchReqOf (deploySubs input)`, and the dispatched request is
   the arena parser's output: `Reactor.Config.protoReqOf` fills
   `Proto.Request.headers` byte-for-byte from the resolved arena entries
   (`h1Parse_complete_content`). So `c.req.headers` seen by the stages is the
   client's real header set — not empty. `acceptsGzip` (scans `accept-encoding`)
   and `corsOriginOf` (reads the canonical lowercase `origin`) therefore see the
   incoming values.
2. **`deployCorsStage` reads the arena's canonical lowercase `origin`.** The
   HTTP/1.1 arena parser lowercases header names; the unit `corsStage` looked up
   `Origin` (mixed case) and so could never match. `deployCorsStage`
   (`Reactor/Deploy.lean` §7b) reads `corsOriginNameLower = "origin"`, so the real
   `Cors.acaoValue` decision fires on the deployed path.

This is verified empirically below, together with the proof-layer seams.

---

## LIVE TRANSCRIPT — the flagship case (gzip + cors both fire)

Request (stdin):

```
GET /health HTTP/1.1
Host: x
Accept-Encoding: gzip
Origin: https://app.example.com
```

Response (stdout), headers verbatim:

```
HTTP/1.1 200 OK
Strict-Transport-Security: max-age=31536000; includeSubDomains; preload
X-Frame-Options: DENY
X-Content-Type-Options: nosniff
Referrer-Policy: no-referrer
Content-Encoding: gzip
Access-Control-Allow-Origin: https://app.example.com
Server: drorb
x-upstream: 1572395042
x-corr: 71.69.84.32.47.104.101.…      (Trace-assigned correlation id)
Content-Length: 25
```

Body (25 bytes), hex head: `1f 8b 08 00 00 00 00 00 00 ff 01 02 00 fd ff 6f …`
— `1f 8b` is the RFC 1952 gzip magic, `08` = DEFLATE; the body IS
`Gzip.gzipStored` of the `/health` payload (`6f6b` = "ok"), not the plaintext.
stderr: `orb: reactor.requests=1 corrs=1` (REAL `Metrics` counter).

**Both target headers observed:**
- `GET` with `Accept-Encoding: gzip` → `Content-Encoding: gzip` + a real gzip body.
- `GET` with `Origin: https://app.example.com` (allowed) → `Access-Control-Allow-Origin: https://app.example.com`.

And the security headers (HSTS + companions), the deploy header rewrite
(`Server: drorb`, `x-upstream:` the REAL proxy/DNS-chosen backend, `x-corr:` the
REAL Trace id) all survive the outer rewrite intact.

---

## FULL STAGE MATRIX — every gate and transform, on the live orb

| Request | Status | Byte effect observed | Driving stage |
|---|---|---|---|
| `GET /health` + `Accept-Encoding: gzip` + allowed `Origin` | 200 | `Content-Encoding: gzip` + gzip body (`1f8b08…`); `Access-Control-Allow-Origin: https://app.example.com`; HSTS set; `Server`/`x-upstream`/`x-corr` | **gzip**, **cors**, security-headers, header-rewrite |
| `GET /health` (no `Accept-Encoding`, no `Origin`) | 200 | body `6f6b` ("ok") plaintext; NO `Content-Encoding`; NO ACAO | gzip/cors correctly quiescent (no false fire) |
| `GET /health` + `Origin: https://evil.example.com` (disallowed) | 200 | NO `Access-Control-Allow-Origin` | **cors** no-leak (real `Cors.originAllowed` denies) |
| `GET /admin` (no bearer) | **401** | `WWW-Authenticate: Bearer`; body "invalid or missing…" | **jwt-admin** (real `Jwt.authenticate`) |
| `GET /old` | **308** | `Location: https://new.example/old` | **redirect** |
| `GET /nope` | **403** | body "policy: undeclared surface" | **policy** (real `Policy.serveDecision`) |
| `GET /../../etc/passwd` | **404** | body "traversal blocked" | **traversal** (real `Route.Path.decodeSegs`) |

The remaining three composed gates run their REAL library decision and **admit /
pass** on this peerless stdin input, which is the production-safe wiring:

- **ipfilter** — no `client.ip` attribute is stashed on the stdin model, so
  `IpFilter.permits` has nothing to reject; the stage admits. Its 403 reject arm
  (deny-precedence over `deployIpRuleset`) is unit-proven in
  `Reactor/Stage/IpFilter`/`WireIpFilter` and fires when a blocked address is
  present.
- **rate** — the high-limit bucket (`rateFullBucket`) always yields a token, so
  `Rate.tryAdmit` admits; the 429 arm is unit-proven in `Reactor/Stage/Rate` on an
  empty bucket.
- **cache** — the empty-start store misses on every request (`Cache.Store.get?`
  over `entries := []`), so it passes through; the warm-hit arm is unit-proven in
  `Reactor/Stage/Cache`.

The eighth transform, **htmlrewrite**, is a lossless streaming rewrite
(`HtmlRewrite.roundtrip`), so on these bodies it passes the bytes through
unchanged; its load-bearing property is chunk-boundary safety
(`deploy_transforms_applied`).

---

## Verified seams — gzip and cors byte-drive through the composed fold

The composed-list (`deployStagesFull2`) byte-driving seams live in
`Reactor/Deploy.lean` §7g, all axiom-clean (`{propext, Classical.choice,
Quot.sound}` only; no `sorry`, no `native_decide`). Alongside the JWT gate's
composed seam (`full2_admin_gate`) and the two transforms' isolated
`stage :: rest` head-position byte-effect theorems (`Reactor/Stage/{Gzip,Cors}.lean`),
they establish:

- `full2_reduces` — on an admitted dispatch every one of the seven gates passes
  (`jwtAdminStage_pass` … `policyStage_pass`, each discharging its gate over the
  REAL library decision), so `runPipeline deployStagesFull2` collapses to the five
  inner response transforms threaded through the outer deploy header rewrite.
- `full2_gzip_ce_inner` — for any gzip-accepting request, the response entering the
  outer rewrite carries `Content-Encoding: gzip` (the real `acceptsGzip` decision
  driving it, past the CORS stage that runs after gzip in the onion).
- `full2_cors_acao_inner` — when the real `Cors.acaoValue` admits the origin, that
  same inner response carries the exact `Access-Control-Allow-Origin` value.
- `full2_gzip_cors_drive` — the three composed: the full build is the deploy header
  rewrite of the inner fold, and that fold carries BOTH headers. The outer rewrite's
  only header-dropping op is the hop-by-hop strip, which keeps both (they are
  non-hop, non-`Server`/`x-upstream`/`x-corr`) — the `deployProg_preserves_field`
  mechanism, the same one `servePipelineFull_hsts` uses for HSTS. That both reach
  the wire is confirmed by the transcript above (the `String.toUTF8` header names
  are not kernel-reducible, so the final name-inequality is empirical, as elsewhere
  in this tree).

## Structure

- The §7g seams are `def`s/theorems layered over the same proven kernel as
  `serveFull` / `serveGuarded` / `servePipeline` / `servePipelineFull`, the JWT
  composed seam, `deployStagesFull2`, and the §7d–§7f theorems.
- `lake build Reactor.Deploy` and `lake build orb` are green; zero sorries in these
  files. (`QuicHeaderProt.lean` is an unrelated WIP file, imported by nothing and
  not in the orb's dependency chain.)

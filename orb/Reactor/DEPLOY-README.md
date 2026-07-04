# Reactor/Deploy.lean — the deployed configuration + full pipeline (GRAND-COMPOSE)

A wiring counts only when the real library drives the
config+serve the DEPLOYED orb binary runs. Before this file, `main` ran
`Reactor.serve` over `Reactor.Config.demoConfig`, whose TLS/WS/SOCKS codec
fields were inert stubs, and the proxy/DNS/observe/lifecycle wirings lived on
bespoke side configs. `Reactor/Deploy.lean` is the keystone that moves them
onto the deployed path; `Arena/Orb.lean`'s `main` now runs it.

## What main executes

```
stdin bytes
  └─ Reactor.Deploy.deployStep ObsState.init          (Arena/Orb.lean main)
       ├─ serveFull                                    (response bytes, stdout)
       │    ├─ Reactor.step deployConfig …             the PROVEN reactor
       │    ├─ FSM sends forwarded faithfully          (serveFull_faithful)
       │    └─ dispatch → App.handle demoAppConfig     real Route.Match.bestMatch
       │         └─ headers ← Header.run deployProg    the REAL rewrite algebra:
       │              • Lifecycle.stdRewrite            strip hop-by-hop, Server: drorb
       │              • x-upstream: ←deployPlan         REAL proxy LB → REAL DNS
       │              • x-corr:     ←Trace.process      REAL correlation assignment
       └─ ObsState                                     REAL Metrics.inc / Tap.step / Trace
```

`deployConfig := wireSocks ⟨0⟩ false (Ws.wireWs (TlsWire.wireTls TlsWire.demoTlsCfg demoConfig))`
— every codec field set through the lanes' own transformers, `demoConfig` not edited.

`deployPlan subs := DnsWire.resolveSubs demoResolver (ProxyServe.serveProxyOn demoProxyApp demoCtx subs)`
— the reverse-proxy routing and the DNS pass run on the reactor's own
submissions, and their result is stamped into the served bytes.

## Libraries the deployed orb now drives (on the path main runs)

| Library / engine                          | Where in the deployed path | Wired by |
|---|---|---|
| Arena HTTP/1.1 parser (`Arena.Parse`)     | `deployConfig.h1Parse` (was already real) | `deploy_h1_arena` |
| H2 engine (`Reactor.H2`)                  | `deployConfig.h2Init/h2Feed/h2Send` (was already real) | `deploy_h2_real` |
| **TLS** (`Tls.step` handshake+record)     | `deployConfig.hsFeed/tlsRecv/tlsSend` | `TlsWire.wireTls`; `deploy_uses_real_tls` |
| **WebSocket** (frame decode + `Ws.Reassembly`) | `deployConfig.wsFeed/wsEncode` | `Ws.wireWs`; `deploy_uses_real_ws` |
| **SOCKS** (`Socks.hstep`)                 | `deployConfig.socksFeed` | `wireSocks`; `deploy_uses_real_socks` |
| **App router** (`Route.Match.bestMatch`)  | dispatch → `App.handle demoAppConfig` | `deploy_routes`, `deploy_routes_bestMatch` |
| **Reverse proxy** (`Proxy.selectChain` over health-filtered `demoPool`) | `deployPlan` → `x-upstream` header | `deploy_plan_resolved`, `deploy_pipeline_seam` |
| **DNS** (`DnsWire.resolve`, real wire-format response parse) | `deployPlan` resolves the LB's pick | `deploy_plan_resolved` |
| **Header algebra** (`Header.run`: hop-strip, `set`) | response headers before serialize | `deployResp_headers`, `deploy_keeps_server` |
| **Trace** (`Trace.process` correlation)   | `x-corr` header + `ObsState.corrs` | `deploy_emits_corr`, `deploy_observes` |
| **Metrics** (`Metrics.Registry.inc`)      | `deployStep` state (stderr line) | `deploy_metrics_exact` |
| **Tap** (`Tap.step` gate)                 | `deployStep` state | `deploy_observes` |
| Serializer (`Reactor.serialize`, framing proven) | every synthesized response byte | `serialize_framing` via `serveFull` |

Not on this path: `Lifecycle`'s Drain admission gate and `Pki`/`Quic`/`Rate`
lanes remain composed at their own seams (Drain gates accepts, which the
one-request stdin shell has no accept loop for).

## Seam theorems (all in `Reactor/Deploy.lean`, zero sorries)

- `deploy_uses_real_tls` — the deployed `hsFeed/tlsRecv/tlsSend` are exactly the
  `TlsWire` adapters over the real `Tls.step` machine (rfl), not the stubs.
- `deploy_uses_real_ws`, `deploy_uses_real_socks`, `deploy_h1_arena`,
  `deploy_h2_real` — same, per lane.
- `serveFull_faithful` — FSM-decided responses forwarded byte-for-byte (a 400/431
  is never rewritten by the pipeline).
- `deploy_routes` / `deploy_routes_bestMatch` — regression: a deployed dispatch
  serves (the rewrite of) `App.handle` = the route the REAL `bestMatch` chose,
  status untouched by the rewrite (`deploy_rewrite_status`).
- `deploy_plan_resolved` — **new on the deployed path**: for any dispatched
  request the upstream plan is exactly `connectUpstream ⟨1572395042⟩`
  (= 93.184.216.34): REAL routing picked the proxy route, the REAL LB skipped
  the unhealthy backend and chose `demoB2`, the REAL DNS parser resolved its
  A record. `deploy_pipeline_seam` composes target + pool eligibility + resolution.
- `deploy_emits_upstream` / `deploy_emits_corr` / `deploy_keeps_server` — the
  proxy/DNS address and the `Trace` id are readable (`Header.get`) in the
  emitted headers; `Server: drorb` survives the extra stamps.
- `deploy_metrics_exact`, `deploy_observes` — the deployed step advances the
  REAL Metrics/Tap/Trace state (`Metrics.inc_exact`).
- `deployStep_serves` — what `main` writes is definitionally `serveFull`.

Axiom audit: every theorem above depends only on
`{propext, Quot.sound, Classical.choice}` (checked with `#print axioms`).

## Runtime verification (the deployed binary)

```
$ printf 'GET /health HTTP/1.1\r\n\r\n' | ./.lake/build/bin/orb
HTTP/1.1 200 OK
Server: drorb
x-upstream: 1572395042
x-corr: 71.69.84.32.47.104.101.97.108.116.104.32.72.84.84.80.47.49.46.49.13.10.13.10
Content-Length: 2

ok
(stderr) orb: reactor.requests=1 corrs=1

$ printf 'GET /nope HTTP/1.1\r\n\r\n' | ./.lake/build/bin/orb
HTTP/1.1 404 Not Found            (body: not found, same deploy headers)

$ printf 'BAD\x01GARBAGE\r\n\r\n' | ./.lake/build/bin/orb
HTTP/1.1 400 Bad Request          (FSM's own canned response, forwarded faithfully)
```

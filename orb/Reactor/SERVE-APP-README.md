# SERVE-APP — the running orb routes via the real Route+Policy App layer

## Routing

`Reactor.serve`'s dispatch case composes the App layer (`Reactor.App`, driving
`Route.Match.bestMatch`) rather than answering every parsed request with a
hardcoded `ok200 (okBody req)`. A bare `dispatch req` (the FSM parsed a
request but emitted no response of its own) is answered by

```
App.handle demoAppConfig req
```

where `demoAppConfig := App.demoApp` is the *same* concrete `AppConfig` the App
layer's seam theorems are proven about — an exact `/health → 200 "ok"`, a
`/static` prefix route, and a `404 "not found"` default. Routing is what
`serve` does, driven by the real router rather than a hardcode.

The routing lives in:
- `Reactor/Serve.lean` — imports `Reactor.App`; `demoResp`'s dispatch case
  calls `App.handle demoAppConfig`; provides `serve_routes` and
  `serve_routes_bestMatch`.
- `Arena/Orb.lean` — drives `Reactor.serve`, so the routing flows through it.

`okBody` is retained because `Reactor.KeepAlive.appResponse`
consumes it; the demo `serve` path does not use it.

## The seam

The App-layer seam `App.app_routes_total` proves `handle`'s output
is exactly `responseOfHandler` of the route `Route.Match.bestMatch` selected.
`serve` wires that seam into the running reactor and lifts it through:

- **`serve_routes`** — when the FSM emits no response of its own
  (`sendsOf (reactorSubs input) = []`) and the submission list heads with a
  `dispatch req`, the served bytes are exactly
  `serialize (App.handle demoAppConfig req)`. No hardcoded status appears; the
  wire bytes are the serializer applied to the App layer's routed response.

- **`serve_routes_bestMatch`** — lifts `app_routes_total` through `serve`:
  the served bytes serialize `responseOfHandler` of the route the *real*
  `Route.Match.bestMatch` chose over `demoAppConfig.table`. A `serve` that
  ignored the router would fail the second conjunct.

`serve_faithful` governs the other half: when the FSM
emits its own response bytes (a canned 400/431, a pipelined send), `serve`
forwards them verbatim — routing never overrides an FSM send. `serve_demo_wf`
is generic over whatever `Response` `demoResp` returns, so
the framing decomposition holds for the routed response.

## Verification (printf against the built `orb` exe)

`lake build Reactor` and `lake build orb` are green; zero sorries.

| Input (stdin) | Output bytes |
|---|---|
| `GET /health HTTP/1.1\r\nHost: x\r\n\r\n` | `HTTP/1.1 200 OK\r\nContent-Length: 2\r\n\r\nok` |
| `GET /nope HTTP/1.1\r\nHost: x\r\n\r\n` | `HTTP/1.1 404 Not Found\r\nContent-Length: 9\r\n\r\nnot found` |
| `GET /health\r\n\r\n` (no HTTP version) | `HTTP/1.1 400 Bad Request\r\nContent-Length: 0\r\n\r\n` |

- `/health` routes to the exact route → `200 OK`, body `ok` (the real
  `bestMatch` picked the `Pat.exact ["health"]` handler).
- `/nope` falls through to the `404` default handler.
- The malformed request (missing HTTP version) is rejected inside the FSM, which
  emits its own canned `400 Bad Request` (Content-Length 0). This travels the
  `serve_faithful` path — a forwarded FSM send, not the routed demo path — so the
  canned 400 is preserved verbatim, exactly as `serve_faithful` states.

## Axioms

`serve_routes`, `serve_routes_bestMatch`, `serve_faithful`, `serve_demo_wf` each
depend only on `[propext, Quot.sound]` — within the permitted
`{propext, Quot.sound, Classical.choice}` subset.

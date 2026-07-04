# PROXY-COMPOSE — the reverse-proxy handler, invoked on the running reactor path

## The finding this closes

Finding #35: `Reactor.Proxy.proxyHandle` drove the **real**
load balancer (`Proxy.selectChain` over the tiered, health-filtered selection
algebra), but nothing on the running reactor path ever *called* it. A real library,
stranded — an island. This slice makes the proxy handler actually run: a route can
now be a reverse-proxy route, and a dispatched request matching one is forwarded to
the LB-chosen backend by the same code path the reactor already uses.

## What changed

**`Reactor/App.lean` (owned edit).** `Handler` grew from a bare `structure` (a
static status+body) into an inductive with two variants:

- `Handler.static status body` — answer locally (the original seed case);
- `Handler.proxy pool` — this route is a reverse-proxy route; `pool` is the real
  `Reactor.Proxy.ProxyPool` (policy chain + health-annotated backend pool).

`responseOfHandler` is total over both (a proxy route's Response projection is a
`502` placeholder — its real answer flows on the submission path, not the Response
path). `demoApp` and every `App` seam theorem (`app_routes_total`,
`app_chosen_route_matches`, the Policy seam) are unchanged: `demoApp` is all-static,
so `Reactor.Serve`'s theorems about it are untouched.

**`Reactor/ProxyServe.lean` (new, owned).** The composition that was missing:

- `routeProxy ac ctx req` — run `Route.Match.bestMatch` over the app's effective
  table; if the matched route's handler is `Handler.proxy pool`, **invoke the real
  `proxyHandle pool`** (which runs `Proxy.selectChain` and emits `connectUpstream`
  to the chosen backend). A static route emits nothing here; no match emits nothing.
- `serveProxyOn ac ctx subs` — pin `routeProxy` onto the reactor's own `dispatch`
  submission: scan the running reactor's submission list and run `routeProxy` on the
  request the reactor dispatched. Same `dispatch` seam `Reactor.Serve` answers with a
  Response, answered here with proxy submissions.
- `reactorSubs cfg input` / `serveProxy cfg ac ctx input` — the running reactor: one
  recv completion through the **proven** `Reactor.step` (the copy-once reactor of
  `Reactor.Contract`), then `serveProxyOn` its output. So the proxy is invoked on
  bytes that actually flowed through `Reactor.step`, not a standalone call.

## The seam theorem — `proxy_route_connects`

```
theorem proxy_route_connects
    (ac : AppConfig) (ctx : Proxy.Ctx) (req : Request)
    (rest : List RingSubmission) (pool : ProxyPool) (r : Route.Match.Route Handler)
    {b : Proxy.Backend}
    (hbest : Route.Match.bestMatch ac.table (targetSegments req.target) = some r)
    (hpx   : r.handler = Handler.proxy pool)
    (hsel  : chooseUpstream pool ctx = some b) :
    targetedUpstream (serveProxyOn ac ctx (RingSubmission.dispatch req :: rest))
        = some (addrOf b)
      ∧ b ∈ pool.backends
      ∧ b.eligible = true
      ∧ Proxy.bestTier pool.backends = some b.tier
```

For a request whose matched route is a proxy route (`hbest` + `hpx`) and whose pool
the real `Proxy.selectChain` (via `chooseUpstream`) picks backend `b` from (`hsel`),
the running path emits a `connectUpstream` targeting **exactly** `addrOf b`, and `b`
is a healthy, administratively-active member of the pool in the best nonempty tier.

This is **`App` routing composed with `Reactor.Proxy.proxy_selects_healthy`** (which
is itself `Proxy.selectChain_eligible` transported through the reactor). The proof is
`routeProxy_proxy` (routing hands off to the real `proxyHandle`) followed by
`proxy_selects_healthy`. A router that ignored `bestMatch` breaks the first conjunct;
a selector that returned an unhealthy or non-pool backend breaks the eligibility
conjuncts.

Two companions make the wiring concrete:

- `serveProxy_connects` lifts the same fact onto the `Reactor.step` byte path: when
  the *running* reactor leads with a `dispatch req` for a proxy-routed request,
  `serveProxy` connects to the healthy LB choice.
- `demoProxy_route_connects` exhibits it on the real `Reactor.Proxy.demoPool`: a
  catch-all reverse-proxy route (`prefix []`) over a pool whose backend 0 is unhealthy
  and backends 1,2 are healthy. The running path routes any dispatched request into
  the LB and connects to `addrOf demoB2` — the healthy least-connections winner —
  skipping the unhealthy backend a naive "first backend" stub would have dialed.

`serveProxyOn_static_no_connect` is the dual: a static-route match emits **no**
upstream connect, so the reactor never dials an upstream for a locally-served route.

## Status

- `lake build Reactor.App Reactor.ProxyServe` — green.
- Zero `sorry`, zero unclosed goals.
- `#print axioms` for every theorem above ⊆ `{propext, Quot.sound}` (a subset of the
  allowed `{propext, Quot.sound, Classical.choice}`).
- `Reactor.lean` extended with `import Reactor.ProxyServe`.

Note: the *whole-library* `lake build Reactor` is currently red in `Reactor.H2`
(and briefly `Reactor.Config`), which belong to a concurrent H2-wiring lane changing
the shared `Proto.H2Conn` shape — outside this module's scope and not
caused by this change. The two owned targets build green on their own.

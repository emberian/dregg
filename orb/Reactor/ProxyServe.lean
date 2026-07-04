import Reactor.App
import Reactor.Proxy
import Reactor.Contract

/-!
# Reactor.ProxyServe — the reverse-proxy handler, wired onto the running reactor

`Reactor.Proxy.proxyHandle` drives the *real* load balancer (`Proxy.selectChain`
over the health-filtered selection algebra). This file wires it onto the running
reactor path, so a proxy-routed request actually reaches it. It composes two proven
libraries — App routing and Proxy selection:

  * **App routing** — `Route.Match.bestMatch` over an `AppConfig`'s effective table
    selects the route for a request (`Reactor.App`). A route now carries a
    `Handler`, which gained a `proxy pool` variant (`Reactor.App.Handler.proxy`).
  * **Proxy selection** — when the matched route is a proxy route, `proxyHandle`
    runs `Proxy.selectChain` on the route's pool and emits the reactor's
    `connectUpstream` submission to the LB-chosen healthy backend (`Reactor.Proxy`).

The wiring, outside-in:

  * `routeProxy` — the composition: `bestMatch` the request, and if the matched
    route's handler is `Handler.proxy pool`, INVOKE the real `proxyHandle pool` on
    it (a static route emits nothing here — it is answered by `App.handle`'s
    Response path). This is the call that hands a proxy-routed request to the
    load balancer.
  * `serveProxyOn` — pin `routeProxy` onto the reactor's own `dispatch` submission:
    scan the running reactor's submission list, and run `routeProxy` on the request
    the reactor dispatched. Same seam `Reactor.Serve` answers with a Response,
    answered here with proxy submissions.
  * `reactorSubs` / `serveProxy` — the *running* reactor: one recv completion
    through the PROVEN `Reactor.step` (the copy-once reactor of `Reactor.Contract`),
    then `serveProxyOn` its output. So the proxy is invoked on bytes that actually
    flowed through `Reactor.step`, not a standalone call.

**Seam theorem — `proxy_route_connects`.** For a request whose matched route is a
proxy route (`bestMatch … = some r`, `r.handler = Handler.proxy pool`) and whose
pool the real `Proxy.selectChain` picks backend `b` from, the running path emits a
`connectUpstream` targeting exactly `addrOf b` — and `b` is a healthy, active
member of the pool in the best nonempty tier. This is `App` routing composed with
`Reactor.Proxy.proxy_selects_healthy` (which is itself `Proxy.selectChain_eligible`
transported through the reactor). A handler that hardcoded a backend, or a router
that ignored `bestMatch`, would each break a conjunct. `serveProxy_connects` lifts
the same fact onto the `Reactor.step` byte path; `demoProxy_route_connects` exhibits
it concretely on the real `demoPool` (the LB skips the unhealthy backend 0 and dials
the healthy least-connections winner, backend 2).
-/

namespace Reactor.ProxyServe

open Proto (Bytes Request)
open Reactor.App (AppConfig Handler targetSegments)
open Reactor.Proxy (ProxyPool proxyHandle chooseUpstream targetedUpstream addrOf
  proxy_selects_healthy)

/-! ## The routing→proxy composition -/

/-- **The missing call.** Route the request through the app's effective table with
the REAL `Route.Match.bestMatch`; if the matched route is a **proxy route**
(`Handler.proxy pool`), INVOKE the real `proxyHandle pool` — which runs
`Proxy.selectChain` over the health-filtered pool and emits a `connectUpstream` to
the chosen backend. A static route emits nothing here (its answer is
`App.handle`'s Response); no match emits nothing. -/
def routeProxy (ac : AppConfig) (ctx : Proxy.Ctx) (req : Request) : List RingSubmission :=
  match Route.Match.bestMatch ac.table (targetSegments req.target) with
  | some r =>
    match r.handler with
    | Handler.proxy pool  => proxyHandle pool ctx req
    | Handler.static _ _  => []
  | none => []

/-- Pin the proxy onto the reactor's own `dispatch` submission: scan the running
reactor's submission list for its `dispatch` and run `routeProxy` on that request.
Every non-dispatch submission is skipped — this is the same `dispatch` seam that
`Reactor.Serve` answers with a Response. -/
def serveProxyOn (ac : AppConfig) (ctx : Proxy.Ctx) :
    List RingSubmission → List RingSubmission
  | [] => []
  | RingSubmission.dispatch req :: _ => routeProxy ac ctx req
  | _ :: rest => serveProxyOn ac ctx rest

/-- The running reactor as a submission producer: one recv completion through the
PROVEN `Reactor.step` (copy-once reactor, `Reactor.Contract`). Parameterized by the
FSM config so this file stays off the shared demo-config module. -/
def reactorSubs (cfg : Proto.Config) (input : Bytes) : List RingSubmission :=
  (Reactor.step cfg (Proto.State.active Proto.Conn.mkPlain)
    (Reactor.RingEvent.recvInto 0 input)).2

/-- **The reverse-proxy on the running reactor path.** Run the proven reactor on
the input bytes, then route its `dispatch` to the proxy handler. -/
def serveProxy (cfg : Proto.Config) (ac : AppConfig) (ctx : Proxy.Ctx) (input : Bytes) :
    List RingSubmission :=
  serveProxyOn ac ctx (reactorSubs cfg input)

/-! ## The composition lemmas -/

/-- On a proxy route, `routeProxy` reduces to the REAL `proxyHandle` on the route's
pool — the router genuinely hands off to the load balancer, no reimplementation. -/
theorem routeProxy_proxy (ac : AppConfig) (ctx : Proxy.Ctx) (req : Request)
    (pool : ProxyPool) (r : Route.Match.Route Handler)
    (hbest : Route.Match.bestMatch ac.table (targetSegments req.target) = some r)
    (hpx : r.handler = Handler.proxy pool) :
    routeProxy ac ctx req = proxyHandle pool ctx req := by
  simp only [routeProxy, hbest, hpx]

/-- `serveProxyOn` on a submission list headed by `dispatch req` runs `routeProxy`
on that request — the proxy sits exactly on the reactor's `dispatch` output. -/
theorem serveProxyOn_dispatch (ac : AppConfig) (ctx : Proxy.Ctx) (req : Request)
    (rest : List RingSubmission) :
    serveProxyOn ac ctx (RingSubmission.dispatch req :: rest) = routeProxy ac ctx req := rfl

/-! ## The seam theorem -/

/-- **`proxy_route_connects` — the routing-to-proxy seam.** For a request whose matched
route is a proxy route (`bestMatch = some r`, `r.handler = Handler.proxy pool`) and
whose pool the REAL `Proxy.selectChain` (via `chooseUpstream`) picks backend `b`
from, the running path — `serveProxyOn` on the reactor's `dispatch req` — emits a
`connectUpstream` targeting exactly `addrOf b`, and `b` is a healthy, administratively
active member of the pool sitting in the best nonempty tier.

This is `App` routing (`hbest`, `hpx`) composed with
`Reactor.Proxy.proxy_selects_healthy` (`hsel`): the proxy handler is invoked
directly from the reactor's dispatch. A router that ignored `bestMatch` would break
the first conjunct; a selector that returned an unhealthy/non-pool backend would
break the eligibility conjuncts. -/
theorem proxy_route_connects (ac : AppConfig) (ctx : Proxy.Ctx) (req : Request)
    (rest : List RingSubmission) (pool : ProxyPool) (r : Route.Match.Route Handler)
    {b : Proxy.Backend}
    (hbest : Route.Match.bestMatch ac.table (targetSegments req.target) = some r)
    (hpx : r.handler = Handler.proxy pool)
    (hsel : chooseUpstream pool ctx = some b) :
    targetedUpstream (serveProxyOn ac ctx (RingSubmission.dispatch req :: rest))
        = some (addrOf b)
      ∧ b ∈ pool.backends
      ∧ b.eligible = true
      ∧ Proxy.bestTier pool.backends = some b.tier := by
  have hrun : serveProxyOn ac ctx (RingSubmission.dispatch req :: rest)
      = proxyHandle pool ctx req := by
    rw [serveProxyOn_dispatch]; exact routeProxy_proxy ac ctx req pool r hbest hpx
  rw [hrun]
  exact proxy_selects_healthy pool ctx req hsel

/-- **The seam on the `Reactor.step` byte path.** When the *running* reactor
(`reactorSubs` = one recv completion through the proven `Reactor.step`) leads with a
`dispatch req` for a proxy-routed request, `serveProxy` connects to exactly the
backend the real `Proxy.selectChain` chose from the healthy set. The proxy is
invoked on bytes that actually flowed through `Reactor.step`. -/
theorem serveProxy_connects (cfg : Proto.Config) (ac : AppConfig) (ctx : Proxy.Ctx)
    (input : Bytes) (req : Request) (rest : List RingSubmission)
    (pool : ProxyPool) (r : Route.Match.Route Handler) {b : Proxy.Backend}
    (hsub : reactorSubs cfg input = RingSubmission.dispatch req :: rest)
    (hbest : Route.Match.bestMatch ac.table (targetSegments req.target) = some r)
    (hpx : r.handler = Handler.proxy pool)
    (hsel : chooseUpstream pool ctx = some b) :
    targetedUpstream (serveProxy cfg ac ctx input) = some (addrOf b)
      ∧ b ∈ pool.backends
      ∧ b.eligible = true
      ∧ Proxy.bestTier pool.backends = some b.tier := by
  unfold serveProxy
  rw [hsub]
  exact proxy_route_connects ac ctx req rest pool r hbest hpx hsel

/-- **No upstream connect for a non-proxy match.** A static route emits nothing on
the proxy submission path — the reactor never dials an upstream for a locally-served
route. -/
theorem serveProxyOn_static_no_connect (ac : AppConfig) (ctx : Proxy.Ctx)
    (req : Request) (rest : List RingSubmission) (r : Route.Match.Route Handler)
    {status : Nat} {body : Bytes}
    (hbest : Route.Match.bestMatch ac.table (targetSegments req.target) = some r)
    (hst : r.handler = Handler.static status body) :
    serveProxyOn ac ctx (RingSubmission.dispatch req :: rest) = [] := by
  rw [serveProxyOn_dispatch]
  simp only [routeProxy, hbest, hst]

/-! ## A concrete instantiation (real routing → real LB, driven end-to-end)

The demo proxies *every* path (a `prefix []` catch-all reverse-proxy route) to the
real `Reactor.Proxy.demoPool`: backend 0 is unhealthy, backends 1 and 2 are healthy,
and least-connections must dial backend 2. So the running path routes any dispatched
request into the LB and connects to the healthy winner — skipping the unhealthy
backend a naive "first backend" stub would have dialed. -/

/-- The reverse-proxy route: a `prefix []` catch-all whose pool is the real
`demoPool`. -/
def demoProxyRoute : Route.Match.Route Handler :=
  ⟨Route.Match.Pat.«prefix» [], Handler.proxy Reactor.Proxy.demoPool⟩

/-- A demo app whose only author route is the reverse-proxy route, with a 404
default. -/
def demoProxyApp : AppConfig where
  routes := [demoProxyRoute]
  defaultHandler := Handler.static 404 "not found".toUTF8.toList
  lid := 0
  policy := Policy.init Reactor.App.demoPolicyConfig
  routeKeyOf := fun _ => ⟨0, 0⟩

/-- Real routing picks the proxy route for every request (`prefix []` matches any
path; no exact route precedes it). -/
theorem demoProxy_bestMatch (req : Request) :
    Route.Match.bestMatch demoProxyApp.table (targetSegments req.target)
      = some demoProxyRoute := by
  simp only [demoProxyApp, AppConfig.table, List.cons_append, List.nil_append,
    Route.Match.bestMatch, List.find?, Route.Match.matchesExact, Route.Match.matchesPrefix,
    demoProxyRoute, List.isPrefixOf]

/-- **The running proxy path, concretely.** For any dispatched request, the running
proxy path over `demoProxyApp` connects to `addrOf demoB2` — the healthy
least-connections winner the REAL `Proxy.selectChain` chose, skipping the unhealthy
backend 0. -/
theorem demoProxy_route_connects (req : Request) (rest : List RingSubmission) :
    targetedUpstream (serveProxyOn demoProxyApp Reactor.Proxy.demoCtx
        (RingSubmission.dispatch req :: rest)) = some (addrOf Reactor.Proxy.demoB2)
      ∧ Reactor.Proxy.demoB2 ∈ Reactor.Proxy.demoPool.backends
      ∧ Reactor.Proxy.demoB2.eligible = true
      ∧ Proxy.bestTier Reactor.Proxy.demoPool.backends = some Reactor.Proxy.demoB2.tier :=
  proxy_route_connects demoProxyApp Reactor.Proxy.demoCtx req rest Reactor.Proxy.demoPool
    demoProxyRoute (demoProxy_bestMatch req) rfl Reactor.Proxy.demo_chooses_b2

end Reactor.ProxyServe

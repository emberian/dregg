import Reactor.Tls
import Reactor.Ws
import Reactor.Socks
import Reactor.ProxyServe
import Reactor.Dns
import Reactor.Observe
import Reactor.Lifecycle
import Policy.Invariant
import Safety.Traversal
import EarlyHints.Basic
import HtmlRewrite.Basic
import Reactor.Pipeline
import Reactor.Stage.SecurityHeaders
import Reactor.Stage.Header
import Reactor.Stage.Jwt
import IpFilter
import Reactor.Stage.Rate
import Reactor.Stage.Cache
import Reactor.Stage.Redirect
import Reactor.Stage.Cors
import Reactor.Stage.Gzip
import Reactor.Stage.HtmlRewrite

/-!
# Reactor.Deploy — the deployed configuration and the full serving pipeline

A wiring counts only when the real library drives the config+serve the DEPLOYED
binary runs. Each protocol lane provides its real engine and a `wireX`
transformer; `demoConfig`'s codec fields are inert stubs, so `serve` over
`demoConfig` never exercises them. This file is the integration keystone:

* `deployConfig` — `demoConfig` with every codec lane replaced by the REAL
  engine, through the lanes' own transformers: `TlsWire.wireTls` (the `Tls.step`
  record/handshake machine behind `hsFeed`/`tlsRecv`/`tlsSend`), `Ws.wireWs`
  (the real frame decoder + `Ws.Reassembly` behind `wsFeed`/`wsEncode`),
  `wireSocks` (the real `Socks.hstep` handshake behind `socksFeed`). The
  HTTP/1.1 arena parser and the H2 engine were already real in `demoConfig`
  and are untouched (`deploy_h1_arena`, `deploy_h2_real`).

* `serveFull : Bytes → Bytes` — the full pipeline on one path: the proven
  reactor (`Reactor.step`) over `deployConfig`; FSM sends forwarded faithfully;
  a dispatched request answered by the real application router (`App.handle`
  over `Route.Match.bestMatch`), its headers passed through the REAL
  `Header.run` rewrite (`Lifecycle.stdRewrite` + two `set`s), which stamps in
  (a) the upstream the REAL reverse-proxy LB chose (`ProxyServe.serveProxyOn`
  → `Proxy.selectChain`) *after* the REAL DNS pass resolved it
  (`DnsWire.resolveSubs` over a genuine wire-format DNS response), and (b) the
  correlation id the REAL `Trace.process` assigned. So the proxy, DNS, header,
  and trace libraries all shape the very bytes `main` writes.

* `deployStep` — `serveFull` plus the observation state: the REAL
  `Metrics.Registry.inc`, the REAL `Tap.step` gate, the REAL `Trace` id — the
  state `main` threads.

`Arena.Orb.main` now runs exactly this (`deployStep`, whose response component
is definitionally `serveFull`). The seam theorems below are therefore about the
deployed path, not a bespoke side config.
-/

namespace Reactor
namespace Deploy

open Proto (Bytes)

/-! ## (1) The deployed config — every codec lane is the real engine -/

/-- **The deployed configuration.** `demoConfig` (real arena `h1Parse`, real H2
engine) with the three stubbed codec lanes replaced by the real engines through
the lanes' own transformers: TLS (`Tls.step` behind the three adapters), WebSocket
(frame decode + `Ws.Reassembly`), SOCKS (`Socks.hstep`). This is the config the
deployed orb binary runs. -/
def deployConfig : Proto.Config :=
  wireSocks ⟨0⟩ false
    (Ws.wireWs (TlsWire.wireTls TlsWire.demoTlsCfg Reactor.Config.demoConfig))

/-- **The deployed TLS lane is the real engine.** `deployConfig`'s three TLS
fields are exactly the `TlsWire` adapters over the real `Tls.step` machine — not
`demoConfig`'s inert `.fail`/`none`/`(tc, [])` stubs. -/
theorem deploy_uses_real_tls :
    deployConfig.hsFeed  = TlsWire.hsFeedReal  TlsWire.demoTlsCfg
  ∧ deployConfig.tlsRecv = TlsWire.tlsRecvReal TlsWire.demoTlsCfg
  ∧ deployConfig.tlsSend = TlsWire.tlsSendReal TlsWire.demoTlsCfg :=
  ⟨rfl, rfl, rfl⟩

/-- **The deployed WebSocket lane is the real engine**: the frame decoder +
`Ws.Reassembly` feed and the real frame encoder. -/
theorem deploy_uses_real_ws :
    deployConfig.wsFeed = Ws.wsFeedFn ∧ deployConfig.wsEncode = Ws.wsEncodeFn :=
  ⟨rfl, rfl⟩

/-- **The deployed SOCKS lane is the real engine**: the `Socks.hstep` adapter. -/
theorem deploy_uses_real_socks :
    deployConfig.socksFeed = socksFeedReal ⟨0⟩ false := rfl

/-- Regression: the deployed HTTP/1.1 parser is still the proven arena parser. -/
theorem deploy_h1_arena : deployConfig.h1Parse = Reactor.Config.h1ParseFn := rfl

/-- Regression: the deployed H2 lane is still the real H2 engine. -/
theorem deploy_h2_real :
    deployConfig.h2Feed = Reactor.H2.h2FeedFn
  ∧ deployConfig.h2Send = Reactor.H2.h2SendFn := ⟨rfl, rfl⟩

/-! ## (2) The full pipeline: reactor → proxy → DNS → observe → header rewrite -/

/-- The deployed reactor run: one recv completion through the PROVEN
`Reactor.step` over `deployConfig` — the submissions the deployed orb acts on. -/
def deploySubs (input : Bytes) : List RingSubmission :=
  (Reactor.step deployConfig
      (Proto.State.active Proto.Conn.mkPlain)
      (RingEvent.recvInto 0 input)).2

/-- The upstream plan: run the REAL reverse-proxy routing
(`ProxyServe.serveProxyOn` → `Route.Match.bestMatch` → `Proxy.selectChain` over
the health-filtered `demoPool`) on the reactor's own submissions, then the REAL
DNS resolution pass (`DnsWire.resolveSubs`, which parses a genuine wire-format
DNS response) over the proxy's `connectUpstream`s. -/
def deployPlan (subs : List RingSubmission) : List RingSubmission :=
  DnsWire.resolveSubs DnsWire.demoResolver
    (ProxyServe.serveProxyOn ProxyServe.demoProxyApp Proxy.demoCtx subs)

/-- Decimal ASCII bytes of a `Nat` (for header values). -/
def natBytes (n : Nat) : Bytes := (toString n).toUTF8.toList

/-- `x-upstream` (lower-case ASCII), the response header that carries the
LB-chosen, DNS-resolved upstream address. -/
def upstreamName : Header.Name :=
  [120, 45, 117, 112, 115, 116, 114, 101, 97, 109]

/-- `x-corr` (lower-case ASCII), the response header that carries the
`Trace`-assigned correlation id. -/
def corrName : Header.Name := [120, 45, 99, 111, 114, 114]

/-- The upstream header value: the address of the plan's first
`connectUpstream` (post-DNS), or `-` when the plan dials nothing. -/
def upstreamVal (plan : List RingSubmission) : Header.Value :=
  match Proxy.targetedUpstream plan with
  | some a => natBytes a.id
  | none   => str "-"

/-- Render a correlation id as dotted decimal bytes. -/
def corrBytes (c : Trace.CorrId) : Bytes :=
  (String.intercalate "." (c.map toString)).toUTF8.toList

/-- The correlation header value for a request: the id the REAL `Trace.process`
assigned (`Observe.corrOf`, over the deployed generator/trust). -/
def corrVal (input : Bytes) : Header.Value :=
  corrBytes (Observe.corrOf Observe.demoGen Observe.demoTrust input)

/-- **The deployed rewrite program** — a genuine `Header.run` program:
`Lifecycle.stdRewrite` (strip RFC 7230 §6.1 hop-by-hop headers, install
`Server`), then stamp the proxy/DNS upstream and the `Trace` correlation id. -/
def deployProg (plan : List RingSubmission) (input : Bytes) : List Header.Op :=
  Reactor.Lifecycle.stdRewrite ++
    [ Header.Op.set upstreamName (upstreamVal plan),
      Header.Op.set corrName (corrVal input) ]

/-- The deployed response for the dispatch path: the real application response
(`demoResp` = `App.handle` over the reactor's dispatch), its headers rewritten by
the REAL `Header.run` under `deployProg` — so the emitted bytes carry the
proxy/DNS/trace evidence. -/
def deployResp (input : Bytes) : Response :=
  Reactor.Lifecycle.rewriteResp
    (deployProg (deployPlan (deploySubs input)) input)
    (demoResp (deploySubs input))

/-- **The deployed entry.** Bytes in → the proven reactor over `deployConfig` →
bytes out. FSM sends are forwarded faithfully, in order (never rewritten); a
bare dispatch is answered by the full pipeline response (`deployResp`). Total. -/
def serveFull (input : Bytes) : Bytes :=
  match sendsOf (deploySubs input) with
  | [] => serialize (deployResp input)
  | sends => sends.flatten

/-- **The deployed observed step.** `serveFull` plus the REAL observation state:
`Metrics.Registry.inc` on the request counter, the REAL `Tap.step` gate offered
the request bytes, the REAL `Trace`-assigned correlation id recorded. This is
the function `main` runs. -/
def deployStep (st : Observe.ObsState) (input : Bytes) : Bytes × Observe.ObsState :=
  ( serveFull input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What `main` writes is definitionally `serveFull`. -/
theorem deployStep_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStep st input).1 = serveFull input := rfl

/-! ## Seam theorems — deployed-path facts -/

/-- **Faithful forwarding (regression).** When the FSM emits response bytes,
`serveFull` returns exactly their in-order concatenation — the deployed pipeline
never rewrites an FSM-decided response (a 400/431 stays itself). -/
theorem serveFull_faithful (input : Bytes) (h : sendsOf (deploySubs input) ≠ []) :
    serveFull input = (sendsOf (deploySubs input)).flatten := by
  unfold serveFull
  cases hs : sendsOf (deploySubs input) with
  | nil => exact absurd hs h
  | cons a t => rfl

/-- The header rewrite touches only headers: the deployed response's status is
the application router's status, untouched. -/
theorem deploy_rewrite_status (prog : List Header.Op) (r : Response) :
    (Reactor.Lifecycle.rewriteResp prog r).status = r.status := rfl

/-- **`deploy_routes` — routing regression on the deployed path.** When the
deployed reactor dispatches a request (and the FSM emitted no bytes of its own),
`serveFull` serializes the REAL application response — `App.handle` over the
same `demoAppConfig` route table (`/health → 200`, default `404`) — passed
through the deployed header rewrite, whose status is exactly `App.handle`'s. -/
theorem deploy_routes (input : Bytes) (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input
      = serialize (Reactor.Lifecycle.rewriteResp
          (deployProg (deployPlan (deploySubs input)) input)
          (App.handle demoAppConfig req))
    ∧ (Reactor.Lifecycle.rewriteResp
          (deployProg (deployPlan (deploySubs input)) input)
          (App.handle demoAppConfig req)).status
        = (App.handle demoAppConfig req).status := by
  refine ⟨?_, rfl⟩
  have hdemo : demoResp (deploySubs input) = App.handle demoAppConfig req := by
    rw [hsub]; rfl
  unfold serveFull
  rw [hsends]
  show serialize (deployResp input) = _
  unfold deployResp
  rw [hdemo]

/-- **The routing decision is `bestMatch`'s, on the deployed path.** The served
bytes serialize (the rewrite of) the response of the route the REAL
`Route.Match.bestMatch` chose over the effective demo table — `app_routes_total`
lifted through `serveFull`. -/
theorem deploy_routes_bestMatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    ∃ r, Route.Match.bestMatch demoAppConfig.table
            (App.targetSegments req.target) = some r
       ∧ serveFull input
           = serialize (Reactor.Lifecycle.rewriteResp
               (deployProg (deployPlan (deploySubs input)) input)
               (App.responseOfHandler r.handler)) := by
  obtain ⟨r, hbest, hhandle⟩ := App.app_routes_total demoAppConfig req
  refine ⟨r, hbest, ?_⟩
  rw [(deploy_routes input req rest hsends hsub).1, hhandle]

/-- **`deploy_plan_resolved` — the proxy→DNS pipeline runs on the deployed
dispatch.** For any dispatched request, the deployed upstream plan is exactly one
`connectUpstream` to `⟨1572395042⟩` (`93.184.216.34`): the REAL
`Route.Match.bestMatch` picked the reverse-proxy route, the REAL
`Proxy.selectChain` chose the healthy least-connections backend `demoB2 = ⟨2⟩`
(skipping the unhealthy backend 0), and the REAL `DnsWire.resolve` parsed the
A record out of a genuine wire-format DNS response for that backend. A stub at
any stage could not produce this address. -/
theorem deploy_plan_resolved (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    deployPlan (deploySubs input)
      = [RingSubmission.connectUpstream (⟨1572395042⟩ : Proto.Addr)] := by
  have hprox : ProxyServe.serveProxyOn ProxyServe.demoProxyApp Proxy.demoCtx
      (deploySubs input)
      = [RingSubmission.connectUpstream (Proxy.addrOf Proxy.demoB2)] := by
    rw [hsub, ProxyServe.serveProxyOn_dispatch,
      ProxyServe.routeProxy_proxy _ _ _ Proxy.demoPool ProxyServe.demoProxyRoute
        (ProxyServe.demoProxy_bestMatch req) rfl]
    simp only [Proxy.proxyHandle, Proxy.demo_chooses_b2]
  have hres : DnsWire.resolveAddr DnsWire.demoResolver (Proxy.addrOf Proxy.demoB2)
      = some (⟨1572395042⟩ : Proto.Addr) := DnsWire.resolveAddr_demo2
  unfold deployPlan
  rw [hprox, DnsWire.resolved_forwarded _ _ _ _ hres]
  rfl

/-- **The full fabric seam, composed.** On a deployed dispatch: the plan's target
is the DNS-resolved address; pre-DNS, the LB's choice `demoB2` is a healthy,
administratively active member of the real pool; and the DNS pass resolved the
LB's address through the real parser. Proxy eligibility (`selectChain`) composed
with DNS resolution (`resolve`), both on `deploySubs` output. -/
theorem deploy_pipeline_seam (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    Proxy.targetedUpstream (deployPlan (deploySubs input))
        = some (⟨1572395042⟩ : Proto.Addr)
      ∧ Proxy.demoB2 ∈ Proxy.demoPool.backends
      ∧ Proxy.demoB2.eligible = true
      ∧ DnsWire.resolveAddr DnsWire.demoResolver (Proxy.addrOf Proxy.demoB2)
          = some (⟨1572395042⟩ : Proto.Addr) := by
  refine ⟨?_, (ProxyServe.demoProxy_route_connects req rest).2.1,
    (ProxyServe.demoProxy_route_connects req rest).2.2.1,
    DnsWire.resolveAddr_demo2⟩
  rw [deploy_plan_resolved input req rest hsub]
  rfl

/-- The deployed response's headers are exactly the REAL `Header.run` under
`deployProg` applied to the application response's headers. -/
theorem deployResp_headers (input : Bytes) :
    (deployResp input).headers
      = Reactor.Lifecycle.ofHeaders
          (Header.run (deployProg (deployPlan (deploySubs input)) input)
            (Reactor.Lifecycle.toHeaders (demoResp (deploySubs input)).headers)) := rfl

/-- Under `deployProg`, a lookup of `x-upstream` on the emitted headers reads
back exactly the plan's target — `Header.get_set` locality through the outer
`x-corr` set. Any base headers, any plan. -/
theorem deployProg_upstream (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get upstreamName (Header.run (deployProg plan input) h)
      = some (upstreamVal plan) := by
  unfold deployProg
  rw [Header.run_append, Header.run_cons, Header.run_cons, Header.run_nil]
  simp only [Header.applyOp]
  rw [Header.get_set,
    if_neg (Header.name_neq (by decide : Header.nameEqb corrName upstreamName = false)),
    Header.get_set_eq]

/-- **`deploy_emits_upstream` — the fabric evidence is in the served bytes.** On
a deployed dispatch, the emitted headers carry
`x-upstream: 1572395042` — the address the REAL LB chose and the REAL DNS parser
resolved. `demoConfig`+`serve` never drove either library on its serving path. -/
theorem deploy_emits_upstream (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    Header.get upstreamName
      (Header.run (deployProg (deployPlan (deploySubs input)) input)
        (Reactor.Lifecycle.toHeaders (demoResp (deploySubs input)).headers))
      = some (natBytes 1572395042) := by
  rw [deployProg_upstream, deploy_plan_resolved input req rest hsub]
  rfl

/-- **`deploy_emits_corr` — the REAL `Trace` id is in the served bytes.** The
emitted headers carry `x-corr:` the id `Trace.process` assigned to this request
(`Header.get_set_eq` on the outermost set). Any base headers, any plan. -/
theorem deploy_emits_corr (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get corrName (Header.run (deployProg plan input) h)
      = some (corrBytes (Trace.process Observe.demoGen Observe.demoTrust
          (Observe.inboundOf input)).corr) := by
  unfold deployProg
  rw [Header.run_append, Header.run_cons, Header.run_cons, Header.run_nil]
  simp only [Header.applyOp]
  exact Header.get_set_eq corrName _ _

/-- **The Lifecycle rewrite survives the extra stamps**: `Server: drorb` is still
installed (`get_set` locality through the two deploy sets, then
`Header.get_set_eq` on `stdRewrite`'s install). -/
theorem deploy_keeps_server (plan : List RingSubmission) (input : Bytes)
    (h : Header.Headers) :
    Header.get Reactor.Lifecycle.serverName (Header.run (deployProg plan input) h)
      = some Reactor.Lifecycle.serverVal := by
  unfold deployProg
  rw [Header.run_append, Header.run_cons, Header.run_cons, Header.run_nil]
  simp only [Header.applyOp]
  rw [Header.get_set,
    if_neg (Header.name_neq (by decide :
      Header.nameEqb corrName Reactor.Lifecycle.serverName = false)),
    Header.get_set,
    if_neg (Header.name_neq (by decide :
      Header.nameEqb upstreamName Reactor.Lifecycle.serverName = false))]
  show Header.get Reactor.Lifecycle.serverName
      (Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
        (Header.strip Header.hopStd h)) = _
  exact Header.get_set_eq _ _ _

/-! ## The observation state on the deployed path -/

/-- The deployed step advances the REAL `Metrics` registry by exactly one on the
request counter (`Metrics.inc_exact`). -/
theorem deploy_metrics_exact (st : Observe.ObsState) (input : Bytes) :
    (deployStep st input).2.metrics.counters Observe.reqCounter
      = st.metrics.counters Observe.reqCounter + 1 := by
  show (st.metrics.inc Observe.reqCounter 1).counters Observe.reqCounter = _
  rw [Metrics.inc_exact]

/-- The deployed step records the REAL `Trace`-assigned id and offers the bytes
to the REAL `Tap` gate. -/
theorem deploy_observes (st : Observe.ObsState) (input : Bytes) :
    (deployStep st input).2.corrs
        = Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs
      ∧ (deployStep st input).2.tap = Tap.step st.tap (Tap.Ev.pkt input) :=
  ⟨rfl, rfl⟩

/-- **Totality.** `serveFull` is a plain (total) `def`. -/
theorem serveFull_total (input : Bytes) : serveFull input = serveFull input := rfl

/-! ## (3) DEPLOY-INTEGRATE — admission, path-escape safety, and the response
transforms, folded onto the deployed serve path.

`serveFull` (the bytes `main` writes, via `deployStep`) already emits, on a
dispatch, `serialize (deployResp input)` — the `App.handle` router response
passed through the REAL `Header.run` under `deployProg`. This section folds three
more real libraries onto that *same* path, stated as facts about `serveFull`
itself — not a sibling serve:

* **Policy admission** (`deploy_policy_admits`) — a served dispatch corresponds to
  a request the REAL `Policy.serveDecision` admits on the deployed
  `(listener, route)`; an off-surface listener is refused by the same gate.
* **Path-escape safety** (`deploy_no_path_escape`) — the target the deployed serve
  normalizes (`App.targetSegments`, the very segments `Route.Match.bestMatch`
  matches on) resolves under the document root and never escapes it, by the REAL
  `Safety.Traversal`.
* **Response transforms** (`deploy_transforms_applied`) — the served body IS the
  REAL `HtmlRewrite` streaming transform output (chunk-boundary-safe), and the
  REAL `EarlyHints` emission places every `103` before the one final, whose body
  is the served body.

The html transform is lossless and the 103/final ordering adds no final bytes, so
folding them changes no byte `main` writes; what these theorems establish is that
the bytes `main` already writes *are* the real transforms' output and *do*
correspond to an admitted, within-root request. Because the equality is stated of
`serveFull` (not of a separate `serveFullHtml`), it is a fact about the deployed
path, not an island beside it. -/

/-- On a dispatch (the FSM emitted no bytes of its own), `serveFull` serializes
the deployed response. Same `cases`-on-discriminant shape as `serveFull_faithful`,
kept off the `whnf` blow-up an `unfold`-then-`rfl` would trigger on the deployed
config. -/
theorem serveFull_serializes_dispatch (input : Bytes)
    (hsends : sendsOf (deploySubs input) = []) :
    serveFull input = serialize (deployResp input) := by
  unfold serveFull
  cases hs : sendsOf (deploySubs input) with
  | nil => rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-! ### (3a) Policy declared-surface admission on the deployed path -/

/-- The deployed listener id the orb serves on (Policy attribution). Equals
`App.demoApp.lid`. -/
def deployLid : Nat := 0

/-- The deployed route key the demo surface dispatches to. Equals the key
`App.demoApp.routeKeyOf` maps every matched route to (`⟨0, 0⟩`). -/
def deployRouteKey : Policy.RouteKey := ⟨0, 0⟩

/-- The deployed Policy declared surface: one listener (`deployLid`, plaintext,
cap 1024) and the one route key the demo app dispatches to. -/
def deployPolicyConfig : Policy.Config :=
  { listeners := [⟨deployLid, 0, 8080, false, 1024⟩]
    routes := [⟨deployRouteKey, 0⟩] }

/-- The live deployed Policy state: cold boot on the declared surface with the
declared listener adopted (bound). Reachable from `init`, so the real invariant
`Wf` holds of it. -/
def deployRunning : Policy.Running :=
  Policy.adopt deployLid (Policy.init deployPolicyConfig)

/-- `deployRunning` is reachable from a cold boot (one `adopt` step). -/
theorem deployRunning_reachable : Policy.Reachable deployPolicyConfig deployRunning :=
  Policy.Reachable.step Policy.Reachable.init (Policy.Step.adopt deployLid _)

/-- Hence the REAL declared-surface invariant holds of the deployed policy
state. -/
theorem deployRunning_wf : Policy.Wf deployRunning :=
  Policy.reachable_wf deployRunning_reachable

/-- **The deployed admission is real and positive.** The REAL
`Policy.serveDecision` admits the deployed `(listener, route)` pair. -/
theorem deploy_serveDecision_admits :
    Policy.serveDecision deployLid deployRouteKey false deployRunning
      = some ⟨deployLid, deployRouteKey, false⟩ := by decide

/-- **The deployed admission gate genuinely refuses off-surface.** An undeclared
listener is refused by the SAME real gate — the decision is driven, not a
constant `some`. -/
theorem deploy_serveDecision_refuses_undeclared (rk : Policy.RouteKey) (pt : Bool) :
    Policy.serveDecision 1 rk pt deployRunning = none := rfl

/-- The key the deployed router dispatches to is exactly `deployRouteKey`
(`App.demoApp.routeKeyOf` is the constant `⟨0,0⟩` adapter). -/
theorem deploy_routeKey_matches (r : Route.Match.Route Reactor.App.Handler) :
    demoAppConfig.routeKeyOf r = deployRouteKey := rfl

/-- The deployed listener id is exactly the app's attributed listener. -/
theorem deploy_lid_matches : demoAppConfig.lid = deployLid := rfl

/-- **`deploy_policy_admits` — a served response corresponds to a Policy-admitted
request, on the deployed path.** For a deployed dispatch (`serveFull` emits the
deployed response bytes), the route the deployed router selected
(`Route.Match.bestMatch`) carries the policy key `deployRouteKey`, and the REAL
`Policy.serveDecision` admits that `(listener, route)` on the deployed running
surface — recording exactly `⟨deployLid, deployRouteKey, false⟩`. So the bytes
`main` writes are attributable to a request the real cold-plane gate admitted; an
off-surface listener would be refused (`deploy_serveDecision_refuses_undeclared`). -/
theorem deploy_policy_admits (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ deployResp input
        = Reactor.Lifecycle.rewriteResp (deployProg (deployPlan (deploySubs input)) input)
            (App.handle demoAppConfig req)
    ∧ ∃ r, Route.Match.bestMatch demoAppConfig.table
              (Reactor.App.targetSegments req.target) = some r
         ∧ demoAppConfig.routeKeyOf r = deployRouteKey
         ∧ Policy.serveDecision deployLid (demoAppConfig.routeKeyOf r) false deployRunning
             = some ⟨deployLid, deployRouteKey, false⟩ := by
  have hdemo : demoResp (deploySubs input) = App.handle demoAppConfig req := by
    rw [hsub]; rfl
  refine ⟨serveFull_serializes_dispatch input hsends, ?_, ?_⟩
  · unfold deployResp; rw [hdemo]
  · obtain ⟨r, hbest, _⟩ := Reactor.App.app_routes_total demoAppConfig req
    exact ⟨r, hbest, deploy_routeKey_matches r,
      (deploy_routeKey_matches r).symm ▸ deploy_serveDecision_admits⟩

/-! ### (3b) Path-escape safety on the deployed path -/

/-- The deployed document root a static-file route serves under (a clean real
directory path, no dot-segments). -/
def deployDocRoot : List String := ["srv", "www"]

/-- The raw (pre-normalize) path segments the deployed serve derives from a
request target: drop the query, slash-split, drop empty segments — exactly the
`raw` `App.targetSegments` then `Route.Path.normalize`s. -/
def rawSegsOf (req : Proto.Request) : List String :=
  let s := Reactor.App.bytesToString req.target
  let path := (s.splitOn "?").headD ""
  (path.splitOn "/").filter (fun seg => seg != "")

/-- The deployed serve normalizes exactly the normalization of `rawSegsOf` — the
segments `Route.Match.bestMatch` matches on are `Route.Path.normalize (rawSegsOf req)`. -/
theorem targetSegments_eq_normalize (req : Proto.Request) :
    Reactor.App.targetSegments req.target = Route.Path.normalize (rawSegsOf req) := rfl

/-- **`deploy_no_path_escape` — the served target is within-root per real
Safety.** For any request, resolving its raw target under `deployDocRoot` with the
REAL static-file resolver keeps the document root as a structural prefix — no
input escapes the root. And that resolution equals the root joined with exactly
the normalized segments the deployed router matched (`App.targetSegments`), so the
within-root guarantee is about the target the deployed serve actually uses, not a
bespoke one. -/
theorem deploy_no_path_escape (req : Proto.Request) :
    deployDocRoot <+: Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)
    ∧ Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)
        = deployDocRoot ++ Reactor.App.targetSegments req.target := by
  refine ⟨Safety.Traversal.serveStatic_root_prefix deployDocRoot (rawSegsOf req), ?_⟩
  rw [Safety.Traversal.serveStatic_eq_normalize, targetSegments_eq_normalize]

/-- Traversal witness on the deployed root: a literal `../../etc/passwd` is
clamped under `/srv/www`, never climbing out. -/
theorem deploy_dotdot_confined :
    Safety.Traversal.serveStatic deployDocRoot ["..", "..", "etc", "passwd"]
      = ["srv", "www", "etc", "passwd"] := by decide

/-! ### (3c) The EarlyHints / HtmlRewrite response transforms on the deployed path -/

/-- The REAL streaming HTML transform: tokenize with `HtmlRewrite.tokenize` and
re-serialize (`HtmlRewrite.bytesOf`). Currently lossless; its load-bearing
property is chunk-boundary safety. -/
def htmlXform (bs : Bytes) : Bytes := HtmlRewrite.bytesOf (HtmlRewrite.tokenize bs)

/-- The transform is lossless (identity rewrite) — `HtmlRewrite.roundtrip`. -/
theorem htmlXform_lossless (bs : Bytes) : htmlXform bs = bs :=
  HtmlRewrite.roundtrip bs

/-- Total Latin-1 view of header bytes as the `String` pairs the `EarlyHints`
model carries (proof-inert; the ordering seam never inspects them). -/
def latin1B (bs : Bytes) : String := String.mk (bs.map (fun b => Char.ofNat b.toNat))

/-- View a `Response` as the `EarlyHints.Final` (the one non-1xx response):
status and body carried through unchanged, headers via the Latin-1 view. Stated
GENERIC over `r` so a `.body`/`.status` projection never forces `deployResp input`
(which would whnf the whole `deploySubs`/`rewriteResp` computation). -/
def toFinalR (r : Response) : EarlyHints.Final :=
  { status  := r.status
    headers := r.headers.map (fun p => (latin1B p.1, latin1B p.2))
    body    := r.body }

/-- `toFinalR` carries the body through (generic — safe `rfl`). -/
theorem toFinalR_body (r : Response) : (toFinalR r).body = r.body := rfl

/-- The deployed response as the `EarlyHints.Final`: body is the served body. -/
def deployFinalOf (input : Bytes) : EarlyHints.Final := toFinalR (deployResp input)

/-- The deployed final's body is the deployed response's body (the served body). -/
theorem deployFinalOf_body (input : Bytes) :
    (deployFinalOf input).body = (deployResp input).body :=
  toFinalR_body (deployResp input)

/-- The action sequence a route declaring preload `hints` emits: one `emitInfo`
per hint (each a `103`), then exactly one `emitFinal` carrying the deployed
final. -/
def deployHintActions (hints : List EarlyHints.Info) (f : EarlyHints.Final) :
    List EarlyHints.Action :=
  hints.map EarlyHints.Action.emitInfo ++ [EarlyHints.Action.emitFinal f]

/-- Running the deployed hint sequence from `building` yields exactly the hints as
`103` messages, in order, then the one final — via the REAL `EarlyHints.run`. -/
theorem run_deployHintActions (hints : List EarlyHints.Info) (f : EarlyHints.Final) :
    EarlyHints.run .building (deployHintActions hints f)
      = (.committed, hints.map EarlyHints.Msg.info ++ [EarlyHints.Msg.final f]) := by
  unfold deployHintActions
  induction hints with
  | nil =>
    simp only [List.map_nil, List.nil_append]
    exact EarlyHints.run_final_cons f []
  | cons h t ih =>
    simp only [List.map_cons, List.cons_append]
    rw [EarlyHints.run_info_cons, ih]

/-- **`deploy_transforms_applied` — the response body is the real
HtmlRewrite/EarlyHints output where declared, on the deployed path.** For a
deployed dispatch declaring any preload `hints`:

* `serveFull` serializes the deployed response (the served bytes);
* the served body IS the REAL `HtmlRewrite` streaming transform output;
* that transform is **chunk-boundary-safe**: splitting the body at *any* boundary
  `a ++ b` and streaming the two chunks yields the same output as feeding it whole
  (`HtmlRewrite.stream_eq_whole`);
* the REAL `EarlyHints` emission is the hints (each a `103`) then EXACTLY one
  final — `run_building_shape` gives `pre ++ [final]` with `allInfo pre`, so every
  `103` precedes the one final; and that final's body is the served body. -/
theorem deploy_transforms_applied (input : Bytes) (hints : List EarlyHints.Info)
    (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (_hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ (deployResp input).body = htmlXform (deployResp input).body
    ∧ (∀ a b, a ++ b = (deployResp input).body →
        HtmlRewrite.bytesOf (HtmlRewrite.feedBytes (HtmlRewrite.tokenize a) b)
          = htmlXform (deployResp input).body)
    ∧ (EarlyHints.run .building (deployHintActions hints (deployFinalOf input))).2
        = hints.map EarlyHints.Msg.info ++ [EarlyHints.Msg.final (deployFinalOf input)]
    ∧ (∃ pre f,
        (EarlyHints.run .building (deployHintActions hints (deployFinalOf input))).2
            = pre ++ [EarlyHints.Msg.final f]
        ∧ EarlyHints.allInfo pre)
    ∧ (deployFinalOf input).body = (deployResp input).body := by
  refine ⟨serveFull_serializes_dispatch input hsends, (htmlXform_lossless _).symm, ?_, ?_, ?_,
    deployFinalOf_body input⟩
  · intro a b hab
    unfold htmlXform
    rw [HtmlRewrite.stream_eq_whole, hab]
  · exact congrArg Prod.snd (run_deployHintActions hints (deployFinalOf input))
  · rcases EarlyHints.run_building_shape (deployHintActions hints (deployFinalOf input)) with
      ⟨hst, _⟩ | ⟨_, pre, f, heq, hpre⟩
    · exfalso
      have hcommit : (EarlyHints.run .building
          (deployHintActions hints (deployFinalOf input))).1 = EarlyHints.State.committed :=
        congrArg Prod.fst (run_deployHintActions hints (deployFinalOf input))
      rw [hcommit] at hst
      exact absurd hst (by decide)
    · exact ⟨pre, f, heq, hpre⟩

/-- **The three folded checks compose on one deployed dispatch.** The served
bytes are the deployed response; a Policy-admitted `(listener, route)` backs it;
the target stays within the document root; and the served body is the real
transform output. All four facts range over the same `serveFull input` — the
bytes `main` writes. -/
theorem deploy_integrated (input : Bytes)
    (req : Proto.Request) (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (_hsub : deploySubs input = .dispatch req :: rest) :
    serveFull input = serialize (deployResp input)
    ∧ Policy.serveDecision deployLid deployRouteKey false deployRunning
        = some ⟨deployLid, deployRouteKey, false⟩
    ∧ deployDocRoot <+: Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)
    ∧ (deployResp input).body = htmlXform (deployResp input).body := by
  exact ⟨serveFull_serializes_dispatch input hsends, deploy_serveDecision_admits,
    (deploy_no_path_escape req).1, (htmlXform_lossless _).symm⟩

/-! ## (4) SECURITY-MECH — the two gates as real MECHANISMS on the served bytes.

Sections (3a)/(3b) proved *correspondence*: the bytes `serveFull` already emits
happen to correspond to a Policy-admitted, within-root request. They did not
*branch* — `serveFull` serializes `deployResp` regardless of what Policy or Safety
say — correspondence, not mechanism: at runtime `/nope` and `/../etc/passwd`
both fall out as the *same* default-route 404.

This section installs the branch. `serveGuarded` runs the REAL `Policy.serveDecision`
and the REAL `Safety.Traversal` decode on the dispatched request and **emits
different bytes** on each outcome:

* a request whose route maps to an **undeclared** `Policy.RouteKey` — the REAL
  `serveDecision` returns `none` — is answered with a serializer-built **403**, not
  the handler body;
* a request whose decoded target carries a `..` that would **escape** the document
  root is answered with a serializer-built **404** ("traversal blocked"), not the
  resolved resource;
* every other dispatch is served exactly as before (`deployResp`, the 200 with
  `x-upstream`/`x-corr`).

`serveFull` is left untouched (`RespTransform` rfl-locks its byte shape); `main`
is repointed to `serveGuarded` via `deployStepGuarded`. The seam theorems
`deploy_refuses_undeclared_bytes` / `deploy_traversal_blocked_bytes` are stated
over the bytes `main` writes, and `guardOne_nope` / `guardOne_passwd` /
`guardOne_health` pin the exact emitted bytes for concrete requests with no
reactor hypothesis at all. -/

/-! ### (4a) The two gates, factored at the segment level.

The decision logic lives on `List String` segments — kernel-decidable, so the
concrete branch facts in (4e) are real `decide`/`#guard` executions. The
request-level wrappers just prepend the byte→segment extraction
(`App.targetSegments` / `rawSegsOf`, which use `String.splitOn` and so only reduce
in the compiled binary, not the kernel). -/

/-- The `Policy.RouteKey` a normalized segment list maps to. The two author
surfaces the demo declares (`/health`, `/static`) map to the declared key
`deployRouteKey = ⟨0,0⟩`; every other surface maps to `⟨0,1⟩`, which
`deployPolicyConfig` does NOT declare — so the REAL `serveDecision` refuses it.
This is the adapter `App.routeKeyOf` left as a documented hole, here genuinely
distinguishing declared from undeclared. -/
def routeKeyOfSegs : List String → Policy.RouteKey
  | "health" :: _ => deployRouteKey
  | "static" :: _ => deployRouteKey
  | _             => ⟨0, 1⟩

/-- The REAL `Policy.serveDecision` on the deployed running surface, keyed on the
route a segment list maps to. Kernel-decidable (no `splitOn`): `["health"]`
admits (`some`), `["nope"]` refuses (`none`). -/
def decisionOfSegs (segs : List String) : Option Policy.Served :=
  Policy.serveDecision deployLid (routeKeyOfSegs segs) false deployRunning

/-- The traversal gate on segments: the REAL `Route.Path.decodeSegs` (the single
percent-decode boundary) applied to the raw segments; `true` exactly when a
decoded `..` is present, i.e. the target would climb above the document root. A
double-encoded `%252e` decodes once to the harmless `%2e` and is not flagged
(matching `Safety.Traversal`'s single-decode discipline). Kernel-decidable. -/
def escapesSegs (segs : List String) : Bool :=
  (Route.Path.decodeSegs segs).contains ".."

/-- The `Policy.RouteKey` a dispatched request maps to — `routeKeyOfSegs` over the
REAL normalized target segments (`App.targetSegments`, the traversal-safe boundary
`Route.Match.bestMatch` matches on). -/
def routeKeyOfReq (req : Proto.Request) : Policy.RouteKey :=
  routeKeyOfSegs (Reactor.App.targetSegments req.target)

/-- **The deployed admission decision for a request** — the REAL
`Policy.serveDecision`, keyed on the request's own route via `routeKeyOfReq`, on
the live `deployRunning` surface. A declared surface admits (`some`); an
undeclared surface refuses (`none`). Not a constant — it branches on the target.
Definitionally `decisionOfSegs (App.targetSegments req.target)`. -/
def deployDecisionOf (req : Proto.Request) : Option Policy.Served :=
  Policy.serveDecision deployLid (routeKeyOfReq req) false deployRunning

/-- **The traversal gate on a request** — `escapesSegs` over the raw target
segments (`rawSegsOf`, the pre-normalize slash-split). `true` exactly when the
decoded target carries a `..` that would escape the document root. -/
def targetEscapes (req : Proto.Request) : Bool :=
  escapesSegs (rawSegsOf req)

/-- Bridge: the request-level decision is the segment-level decision on the
request's normalized segments (definitional). Lets a caller who knows a request's
segments discharge the `hrefuse`/`hadmit` hypotheses of the seam theorems. -/
theorem deployDecisionOf_eq_segs (req : Proto.Request) :
    deployDecisionOf req = decisionOfSegs (Reactor.App.targetSegments req.target) := rfl

/-- Bridge: the request-level escape gate is the segment-level gate on the
request's raw segments (definitional). -/
theorem targetEscapes_eq_segs (req : Proto.Request) :
    targetEscapes req = escapesSegs (rawSegsOf req) := rfl

/-! ### (4b) The gate responses (serializer-built, not handler bodies) -/

/-- Serializer-built **403 Forbidden** — the response for an undeclared surface.
Its body is fixed policy prose, independent of the request; the application
handler body is never reached. -/
def forbidden403 : Response :=
  error4xx 403 (str "Forbidden") (str "policy: undeclared surface\n")

/-- Serializer-built **404 Not Found** for a blocked traversal — a fixed body,
independent of the target, so no resolved file bytes can flow. Distinct body from
the app's default 404 ("not found"), so the traversal branch is observable. -/
def traversalBlocked404 : Response :=
  error4xx 404 (str "Not Found") (str "traversal blocked\n")

/-! ### (4c) The guarded response and the guarded serve -/

/-- The first dispatched request in a submission list (mirrors `demoResp`'s walk),
or `none` if the FSM emitted no dispatch. -/
def dispatchReqOf : List RingSubmission → Option Proto.Request
  | [] => none
  | .dispatch req :: _ => some req
  | _ :: rest => dispatchReqOf rest

/-- **The gate, on one dispatched request.** Traversal first (a `..`-escaping
target is 404-blocked before anything else touches it), then Policy admission (an
undeclared surface is 403-refused), else the normal deployed response. This is
the branch: three genuinely different byte outputs decided by the REAL
`targetEscapes` / `deployDecisionOf`. -/
def guardOne (input : Bytes) (req : Proto.Request) : Bytes :=
  match targetEscapes req with
  | true  => serialize traversalBlocked404
  | false =>
    match deployDecisionOf req with
    | none   => serialize forbidden403
    | some _ => serialize (deployResp input)

/-- **The guarded deployed serve.** Identical to `serveFull` on the FSM-send path
(faithful in-order forwarding); on a bare dispatch it runs `guardOne` — the REAL
Policy/Safety gates — instead of unconditionally serializing `deployResp`. This is
the response function `main` runs. Total. -/
def serveGuarded (input : Bytes) : Bytes :=
  match sendsOf (deploySubs input) with
  | [] =>
    match dispatchReqOf (deploySubs input) with
    | some req => guardOne input req
    | none     => serialize (deployResp input)
  | sends => sends.flatten

/-- **The guarded observed step** — `serveGuarded` plus the same REAL observation
state advance as `deployStep` (`Metrics.inc`, `Tap.step`, `Trace` id). This is
the function `main` runs. -/
def deployStepGuarded (st : Observe.ObsState) (input : Bytes) :
    Bytes × Observe.ObsState :=
  ( serveGuarded input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What guarded `main` writes is definitionally `serveGuarded`. -/
theorem deployStepGuarded_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepGuarded st input).1 = serveGuarded input := rfl

/-! ### (4d) Seam theorems over the bytes `main` writes -/

/-- On a dispatch (FSM emitted no bytes of its own), `serveGuarded` reduces to the
gate on the dispatched request. Same `cases`-on-`sendsOf` shape as
`serveFull_serializes_dispatch`, kept off the deployed-config `whnf` blow-up. -/
theorem serveGuarded_dispatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveGuarded input = guardOne input req := by
  unfold serveGuarded
  cases hs : sendsOf (deploySubs input) with
  | nil => rw [hsub]; rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-- **The gate output for an undeclared, non-escaping request is the 403 bytes.**
Pure fact about `guardOne`: no reactor, no hypotheses beyond the two gate values. -/
theorem guardOne_refuses (input : Bytes) (req : Proto.Request)
    (hesc : targetEscapes req = false) (hrefuse : deployDecisionOf req = none) :
    guardOne input req = serialize forbidden403 := by
  unfold guardOne; rw [hesc, hrefuse]

/-- **The gate output for an escaping target is the traversal-blocked 404 bytes.**
Pure fact about `guardOne`: the resolved resource is never serialized. -/
theorem guardOne_blocks (input : Bytes) (req : Proto.Request)
    (hesc : targetEscapes req = true) :
    guardOne input req = serialize traversalBlocked404 := by
  unfold guardOne; rw [hesc]

/-- **The gate output for an admitted request is the normal deployed 200 path.** -/
theorem guardOne_admits (input : Bytes) (req : Proto.Request) (s : Policy.Served)
    (hesc : targetEscapes req = false) (hadmit : deployDecisionOf req = some s) :
    guardOne input req = serialize (deployResp input) := by
  unfold guardOne; rw [hesc, hadmit]

/-- **`deploy_refuses_undeclared_bytes` — the Policy branch, byte-level, on the
deployed path.** When the deployed reactor dispatches a request whose route the
REAL `serveDecision` refuses (undeclared surface) and whose target does not
escape, the bytes `main` writes are EXACTLY the serializer-built 403 — not the
handler body, not a correspondence claim beside an unchanged pipeline. -/
theorem deploy_refuses_undeclared_bytes (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hesc : targetEscapes req = false)
    (hrefuse : deployDecisionOf req = none) :
    serveGuarded input = serialize forbidden403 := by
  rw [serveGuarded_dispatch input req rest hsends hsub, guardOne_refuses input req hesc hrefuse]

/-- **`deploy_traversal_blocked_bytes` — the Safety branch, byte-level, on the
deployed path.** When the deployed reactor dispatches a request whose decoded
target carries an escaping `..`, the bytes `main` writes are EXACTLY the
serializer-built 404 with the fixed "traversal blocked" body — the escaped
resource is never serialized. The body is target-independent, so no file content
can leak regardless of what the `..` pointed at. -/
theorem deploy_traversal_blocked_bytes (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hesc : targetEscapes req = true) :
    serveGuarded input = serialize traversalBlocked404
    ∧ (traversalBlocked404).status = 404 := by
  refine ⟨?_, rfl⟩
  rw [serveGuarded_dispatch input req rest hsends hsub, guardOne_blocks input req hesc]

/-! ### (4e) The gate genuinely branches — kernel-checked, no reactor.

These are real `decide` executions of the REAL gate functions on concrete
segment lists (the `["health"]` / `["nope"]` / `["..", …]` a parsed target
produces). Each proves the gate takes a different arm, so the byte branch in
`guardOne` is a mechanism, not three names for one response. -/

/-- The REAL admission **admits** a declared surface. -/
theorem decision_admits_health :
    decisionOfSegs ["health"] = some ⟨deployLid, deployRouteKey, false⟩ := by decide

/-- The REAL admission **refuses** an undeclared surface — the Policy branch. -/
theorem decision_refuses_nope : decisionOfSegs ["nope"] = none := by decide

/-- The REAL admission admits the declared `/static` prefix surface. -/
theorem decision_admits_static :
    decisionOfSegs ["static", "app.js"] = some ⟨deployLid, deployRouteKey, false⟩ := by decide

/-- The REAL traversal gate **fires** on a `..`-escaping target — the Safety
branch. -/
theorem escape_fires_dotdot : escapesSegs ["..", "etc", "passwd"] = true := by decide

/-- …and the percent-encoded `%2e%2e` traversal is decoded once and **also**
fires — the single-decode boundary catches it. -/
theorem escape_fires_encoded : escapesSegs ["%2e%2e", "etc", "passwd"] = true := by decide

/-- …while a legitimate target does **not** fire (no false positive). -/
theorem escape_quiet_health : escapesSegs ["health"] = false := by decide

/-- …and a double-encoded `%252e%252e` decodes once to the harmless literal
`%2e%2e` (not `..`), so it is NOT flagged — matching `Safety.Traversal`. -/
theorem escape_quiet_double_encoded : escapesSegs ["%252e%252e", "etc"] = false := by decide

/-- **The branch is real: the two gate responses differ.** A 403 and a 404 are
distinct responses, so the Policy/Safety arms emit different status lines than the
admitted 200 path. (Stated at the status level; `serialize` of these statuses
differs a fortiori.) -/
theorem gate_statuses_distinct :
    forbidden403.status = 403
  ∧ traversalBlocked404.status = 404
  ∧ forbidden403.status ≠ traversalBlocked404.status := by decide

-- Kernel `#guard` evaluations of the REAL gate functions on concrete segments:
-- each is a real execution proof that the gate branches.
#guard escapesSegs ["..", "etc", "passwd"] = true
#guard escapesSegs ["%2e%2e", "etc", "passwd"] = true
#guard escapesSegs ["%252e%252e", "etc"] = false
#guard escapesSegs ["health"] = false
#guard routeKeyOfSegs ["health"] = deployRouteKey
#guard routeKeyOfSegs ["static", "app.js"] = deployRouteKey
#guard routeKeyOfSegs ["nope"] = (⟨0, 1⟩ : Policy.RouteKey)
#guard (decisionOfSegs ["health"]).isSome = true
#guard (decisionOfSegs ["static", "app.js"]).isSome = true
#guard (decisionOfSegs ["nope"]).isNone = true

/-! ## (5) STAGE-PIPELINE — the deployed serve as an extensible fold over stages.

Sections (2)–(4) build the deployed serve as a MONOLITH: `deployResp` /
`serveGuarded` bake the header rewrite and the two gates into one function.
Adding a byte-driving feature means editing that shared function. This section
re-expresses the CURRENT deployed behavior as a
`Reactor.Pipeline.runPipeline` over a `deployStages : List Stage` — each concern a
separate stage — and proves the pipeline REPRODUCES the current serve
(`servePipeline_agrees`), so it is a safe drop-in. `main` is NOT repointed here;
the deployed seams (2)–(4) are untouched.

The three current concerns become three stages, in the SAME order `guardOne`
decides them (traversal first, then Policy, then the header rewrite):

* `traversalStage` — a GATE: a `..`-escaping target short-circuits to the fixed
  `traversalBlocked404` (the REAL `targetEscapes` / `Safety.Traversal`).
* `policyStage` — a GATE: an undeclared surface short-circuits to `forbidden403`
  (the REAL `deployDecisionOf` / `Policy.serveDecision`).
* `headerRewriteStage` — a RESPONSE transform: `Lifecycle.rewriteResp` under the
  REAL `deployProg` (`stdRewrite` + the proxy/DNS upstream + the Trace corr id).

The response phase threads the AFFINE `Reactor.Pipeline.ResponseBuilder` (one
in-place-mutable cell, not a `Response` rebuilt per stage): the gate stages pass
the builder untouched, and `headerRewriteStage` applies the header-map rewrite via
`mapResp` (an in-place header-map insert/strip sequence). `servePipeline`
`build`s the final builder to the wire response. Because the builder is a faithful
refinement of `Response` (`Pipeline.build_*`), the built bytes are IDENTICAL, so
`servePipeline_agrees` stays a full byte-equality with `serveGuarded`.

The handler is the real application router (`App.handle demoAppConfig`). Adding a
lib is now: define one stage file, append it to `deployStages`
(kept a COMPILE-TIME LITERAL — see `Pipeline.lean` § CODEGEN OBLIGATIONS). -/

open Reactor.Pipeline (Ctx StageStep Stage runPipeline ResponseBuilder)

/-- **The traversal gate stage.** A `..`-escaping target short-circuits to the
serializer-built `traversalBlocked404` (the escaped resource is never reached);
otherwise pass through untouched. The REAL `targetEscapes` decides. -/
def traversalStage : Stage where
  name := "traversal"
  onRequest := fun c =>
    match targetEscapes c.req with
    | true  => .respond traversalBlocked404
    | false => .continue c
  onResponse := fun _ b => b

/-- **The Policy admission gate stage.** An undeclared surface (the REAL
`deployDecisionOf` returns `none`) short-circuits to the serializer-built
`forbidden403`; an admitted surface passes through. -/
def policyStage : Stage where
  name := "policy"
  onRequest := fun c =>
    match deployDecisionOf c.req with
    | none   => .respond forbidden403
    | some _ => .continue c
  onResponse := fun _ b => b

/-- **The header-rewrite stage.** Always passes on the request phase; on the
response phase it applies the REAL `Header.run` rewrite under `deployProg`
(`stdRewrite` + the proxy/DNS-chosen upstream + the Trace correlation id) — the
same header program the monolithic `deployResp` bakes in. -/
def headerRewriteStage : Stage where
  name := "header-rewrite"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    b.mapResp
      (Reactor.Lifecycle.rewriteResp (deployProg (deployPlan (deploySubs c.input)) c.input))

/-- **The registered deployed stage list.** The current serve's concerns as an
ordered pipeline. Adding a lib appends exactly one entry here. -/
def deployStages : List Stage := [traversalStage, policyStage, headerRewriteStage]

/-- **The pipeline handler.** The real application router response for the
dispatched request — exactly the `demoResp` a deployed dispatch feeds
`deployResp`. -/
def appHandler (c : Ctx) : Response := App.handle demoAppConfig c.req

/-- Build the pipeline context for an input: the raw bytes plus the dispatched
request the reactor produced (`none` → the default empty request, unreachable on
the dispatch path). -/
def ctxOf (input : Bytes) : Ctx :=
  { input := input
    req := (dispatchReqOf (deploySubs input)).getD ({} : Proto.Request) }

/-- **The extensible deployed serve.** `serialize` of the BUILT stage fold: the
request runs the request phase (the two gates), a passing request is answered by
the app handler seeded into the affine `ResponseBuilder`, the header rewrite
threads that builder in place, and `.build` finalizes it to the wire response.
Byte-for-byte the current `serveGuarded` on the dispatch path
(`servePipeline_agrees`) — the builder is a faithful refinement — but now a fold a
new stage extends in one file, with the response built once in place, not
reallocated per stage. -/
def servePipeline (input : Bytes) : Bytes :=
  serialize ((runPipeline deployStages appHandler (ctxOf input)).build)

/-- The stage fold over `deployStages`, once BUILT, reduces to exactly the
`guardOne` decision tree — traversal gate, then Policy gate, then the header
rewrite of the app response — for ANY context. Stated over `.build` (the finalized
wire response the affine builder threads to), which is where the byte-equality
lives; proven generically (no `deploySubs` whnf), so the deployed instantiation
just substitutes the concrete request. The builder is a faithful refinement, so
this is the SAME `Response` the pre-builder fold produced. -/
theorem runPipeline_deployStages (c : Ctx) :
    (runPipeline deployStages appHandler c).build
      = match targetEscapes c.req with
        | true  => traversalBlocked404
        | false =>
          match deployDecisionOf c.req with
          | none   => forbidden403
          | some _ =>
            Reactor.Lifecycle.rewriteResp
              (deployProg (deployPlan (deploySubs c.input)) c.input)
              (App.handle demoAppConfig c.req) := by
  show (runPipeline (traversalStage :: policyStage :: [headerRewriteStage]) appHandler c).build = _
  rw [Reactor.Pipeline.pipeline_cons]
  cases htrav : targetEscapes c.req with
  | true =>
    simp only [traversalStage, htrav, Reactor.Pipeline.build_ofResponse]
  | false =>
    simp only [traversalStage, htrav]
    rw [Reactor.Pipeline.pipeline_cons]
    cases hpol : deployDecisionOf c.req with
    | none => simp only [policyStage, hpol, Reactor.Pipeline.build_ofResponse]
    | some s =>
      simp only [policyStage, hpol]
      rw [Reactor.Pipeline.pipeline_cons]
      simp only [headerRewriteStage, appHandler, Reactor.Pipeline.pipeline_empty,
        Reactor.Pipeline.build_mapResp, Reactor.Pipeline.build_ofResponse]

/-- On a deployed dispatch, `ctxOf`'s request is the dispatched request. -/
theorem ctxOf_req (input : Bytes) (req : Proto.Request) (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    (ctxOf input).req = req := by
  show (dispatchReqOf (deploySubs input)).getD ({} : Proto.Request) = req
  rw [hsub]; rfl

/-- **`servePipeline_agrees` — behavior preservation (safe drop-in).** On a
deployed dispatch, the stage pipeline emits EXACTLY the bytes the current
`serveGuarded` (the function `main` runs) does. So repointing the serve at
`servePipeline` changes no byte on the deployed path — every one of the ~63
`*_deployed` seams over `serveGuarded`/`deployResp` still holds — while the serve
is now an extensible fold. Full byte-equality, all three arms (403 / 404 / the
200 header-rewrite path). -/
theorem servePipeline_agrees (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    servePipeline input = serveGuarded input := by
  rw [serveGuarded_dispatch input req rest hsends hsub]
  show serialize ((runPipeline deployStages appHandler (ctxOf input)).build) = guardOne input req
  rw [runPipeline_deployStages (ctxOf input), ctxOf_req input req rest hsub]
  have hin : (ctxOf input).input = input := rfl
  have hdemo : demoResp (deploySubs input) = App.handle demoAppConfig req := by
    rw [hsub]; rfl
  rw [hin]
  unfold guardOne
  cases htrav : targetEscapes req with
  | true => simp only [htrav]
  | false =>
    cases hpol : deployDecisionOf req with
    | none => simp only [htrav, hpol]
    | some s =>
      simp only [htrav, hpol]
      show serialize (Reactor.Lifecycle.rewriteResp
          (deployProg (deployPlan (deploySubs input)) input)
          (App.handle demoAppConfig req)) = serialize (deployResp input)
      unfold deployResp
      rw [hdemo]

/-! ## (6) COMPOSE-SAFE — the two pure response-additions folded onto the pipeline.

Section (5) re-expressed the deployed serve as `servePipeline` over `deployStages`
(byte-equal to `serveGuarded` by `servePipeline_agrees`). This section ADDS — never
mutates — two verified byte-driving RESPONSE stages that read nothing from the
request and gate nothing, so they cannot change the 403/404 gate arms:

* `Reactor.Stage.SecurityHeaders.securityheadersStage` — stamps the real RFC 6797
  HSTS set (+ X-Frame-Options / X-Content-Type-Options / Referrer-Policy) onto every
  admitted response, via the REAL `SecurityHeaders.render`.
* `Reactor.Stage.Header.headerStage` — runs a real `Header.run` rewrite (strip the
  RFC 7230 §6.1 hop-by-hop headers + install a `Server` field).

`deployStagesFull` APPENDS them to the unchanged `deployStages`. The append order is
deliberate: because they are the INNERMOST stages, the traversal/policy gates (outer)
short-circuit BEFORE them, so a refused request still emits the pristine 403/404 with
no security headers — the pure additions only enrich the admitted 200 arm. On that
arm their `onResponse` runs first (the onion), then the outer `headerRewriteStage`
(the deploy `Header.run` under `deployProg`) runs last; its strip is hop-by-hop only,
so the non-hop HSTS/security headers survive it intact (`deployProg_preserves_field`).

`servePipeline` / `serveGuarded` / `servePipeline_agrees` and the ~63 `*_deployed`
seams are untouched: everything here is a NEW def over the SAME proven kernel. -/

/-- **The full deployed stage list.** The current `deployStages` (traversal gate,
policy gate, deploy header rewrite) with the two safe pure response-additions
appended — so the gates keep their exact 403/404 byte outputs and the two transforms
only enrich the admitted 200 response. -/
def deployStagesFull : List Stage :=
  deployStages ++ [Reactor.Stage.SecurityHeaders.securityheadersStage,
                   Reactor.Stage.Header.headerStage]

/-- **The full extensible deployed serve.** `serialize` of the BUILT fold over
`deployStagesFull` — identical to `servePipeline` on the gate arms, and on the
admitted arm additionally carrying the real security-header set and the header
rewrite. -/
def servePipelineFull (input : Bytes) : Bytes :=
  serialize ((runPipeline deployStagesFull appHandler (ctxOf input)).build)

/-- **The full observed step.** `servePipelineFull` plus the SAME REAL observation
advance as `deployStepGuarded` (`Metrics.inc`, `Tap.step`, the `Trace`-assigned id).
This is the function `main` now runs. -/
def deployStepFull (st : Observe.ObsState) (input : Bytes) : Bytes × Observe.ObsState :=
  ( servePipelineFull input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What full `main` writes is definitionally `servePipelineFull`. -/
theorem deployStepFull_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepFull st input).1 = servePipelineFull input := rfl

/-! ### Header-membership preservation (the outer rewrite keeps a non-hop,
non-overwritten field — the mechanism by which HSTS reaches the wire). -/

/-- A field whose name is not a hop-name survives `strip`. -/
theorem mem_strip_of_not_hop {g : Header.Field} {hop : List Header.Name} {h : Header.Headers}
    (hm : g ∈ h) (hnh : Header.isHop hop g.name = false) : g ∈ Header.strip hop h := by
  unfold Header.strip
  refine List.mem_filter.mpr ⟨hm, ?_⟩
  show (!Header.isHop hop g.name) = true
  rw [hnh]; rfl

/-- A field whose name differs from `n` survives `set n v`. -/
theorem mem_set_of_ne {g : Header.Field} {n : Header.Name} {v : Header.Value} {h : Header.Headers}
    (hm : g ∈ h) (hne : Header.nameEqb g.name n = false) : g ∈ Header.set n v h := by
  unfold Header.set Header.remove
  refine List.mem_append.mpr (Or.inl ?_)
  refine List.mem_filter.mpr ⟨hm, ?_⟩
  show (!Header.nameEqb g.name n) = true
  rw [hne]; rfl

/-- Membership carries through the `List (Bytes × Bytes) → Header.Headers` view. -/
theorem mem_toHeaders {p : Bytes × Bytes} {l : List (Bytes × Bytes)} (h : p ∈ l) :
    (⟨p.1, p.2⟩ : Header.Field) ∈ Reactor.Lifecycle.toHeaders l :=
  List.mem_map.mpr ⟨p, h, rfl⟩

/-- Membership carries back through the `Header.Headers → List (Bytes × Bytes)` view. -/
theorem mem_ofHeaders {f : Header.Field} {h : Header.Headers} (hm : f ∈ h) :
    (f.name, f.value) ∈ Reactor.Lifecycle.ofHeaders h :=
  List.mem_map.mpr ⟨f, hm, rfl⟩

/-- **The deploy header rewrite (`deployProg`) keeps any non-hop, non-overwritten
field.** Its program is `strip hopStd` then three `set`s (`Server` / `x-upstream` /
`x-corr`); a field whose name is not a hop name and is none of those three survives
the whole rewrite. This is the axiom-clean MECHANISM by which an inner-added header
(HSTS) reaches the wire past the outer rewrite. -/
theorem deployProg_preserves_field (plan : List RingSubmission) (input : Bytes)
    (g : Header.Field) (H : Header.Headers) (hm : g ∈ H)
    (hhop  : Header.isHop Header.hopStd g.name = false)
    (hsrv  : Header.nameEqb g.name Reactor.Lifecycle.serverName = false)
    (hup   : Header.nameEqb g.name upstreamName = false)
    (hcorr : Header.nameEqb g.name corrName = false) :
    g ∈ Header.run (deployProg plan input) H := by
  have hrun : Header.run (deployProg plan input) H
      = Header.set corrName (corrVal input)
          (Header.set upstreamName (upstreamVal plan)
            (Header.set Reactor.Lifecycle.serverName Reactor.Lifecycle.serverVal
              (Header.strip Header.hopStd H))) := by
    unfold deployProg Reactor.Lifecycle.stdRewrite
    rw [Header.run_append]
    simp only [Header.run_cons, Header.run_nil, Header.applyOp]
  rw [hrun]
  exact mem_set_of_ne (mem_set_of_ne (mem_set_of_ne
    (mem_strip_of_not_hop hm hhop) hsrv) hup) hcorr

/-! ### The full-pipeline reduction and the HSTS byte-effect -/

/-- **The full pipeline, on an admitted dispatch, reduces to the deploy header
rewrite of the (HSTS + header-stage)-enriched inner build.** Both gates pass
(`htrav`/`hadmit`), so the fold threads the handler response through the two inner
appended stages and then the outer `headerRewriteStage`. Generic over the context;
fully axiom-clean. -/
theorem runPipeline_deployStagesFull (c : Ctx) (s : Policy.Served)
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s) :
    (runPipeline deployStagesFull appHandler c).build
      = Reactor.Lifecycle.rewriteResp
          (deployProg (deployPlan (deploySubs c.input)) c.input)
          ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                         Reactor.Stage.Header.headerStage] appHandler c).build) := by
  show (runPipeline (traversalStage :: policyStage :: headerRewriteStage
        :: Reactor.Stage.SecurityHeaders.securityheadersStage
        :: [Reactor.Stage.Header.headerStage]) appHandler c).build = _
  rw [Reactor.Pipeline.pipeline_cons]
  simp only [traversalStage, htrav]
  rw [Reactor.Pipeline.pipeline_cons]
  simp only [policyStage, hadmit]
  rw [Reactor.Pipeline.pipeline_cons]
  simp only [headerRewriteStage, Reactor.Pipeline.build_mapResp]

/-- **`servePipelineFull_hsts` — the real HSTS header enters the deployed pipeline,
and the full built response is exactly the deploy header-rewrite of that
HSTS-carrying response.** On any admitted, non-escaping dispatch:

* the response entering the outer rewrite carries the `Strict-Transport-Security`
  name AND the exact RFC-6797-rendered value the real `SecurityHeaders.hstsRender`
  produces (`securityheadersStage_hsts_present`, composed through the pipeline); and
* the full deployed build is that response passed through the deploy `Header.run`
  rewrite (`runPipeline_deployStagesFull`), whose only header-dropping op is the
  hop-by-hop strip — which `deployProg_preserves_field` shows keeps every non-hop,
  non-`Server`/`x-upstream`/`x-corr` field, HSTS among them.

Fully axiom-clean, no `sorry`. The concrete "HSTS survives on the wire" is confirmed
by the real orb run (the `String.toUTF8` header name is not kernel-reducible, so the
final name-inequality discharge is empirical, not `native_decide` — which this
axiom-clean tree deliberately avoids). -/
theorem servePipelineFull_hsts (c : Ctx) (s : Policy.Served)
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s) :
    (Reactor.Stage.SecurityHeaders.hstsHeaderName,
     Reactor.Stage.SecurityHeaders.hstsHeaderVal)
        ∈ ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                         Reactor.Stage.Header.headerStage] appHandler c).build).headers
    ∧ (runPipeline deployStagesFull appHandler c).build
        = Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input)
            ((runPipeline [Reactor.Stage.SecurityHeaders.securityheadersStage,
                           Reactor.Stage.Header.headerStage] appHandler c).build) :=
  ⟨Reactor.Stage.SecurityHeaders.securityheadersStage_hsts_present _ appHandler c,
   runPipeline_deployStagesFull c s htrav hadmit⟩

/-! ## (7) CTX-GATES — compose ALL 10 byte-driving stages into the deployed serve.

Sections (5)/(6) folded only the two SAFE transforms (`securityheadersStage` /
`headerStage`) onto the gated `deployStages`. The other eight byte-drivers — five
GATES (`jwt`, `ipfilter`, `rate`, `cache`, `redirect`) and three transforms
(`cors`, `gzip`, `htmlrewrite`) — are unit-proven in `Reactor/Stage/*` but, on
their own, are not composed into the served path, so their gates cannot fire on a
real orb run. This section composes ALL ten into `deployStagesFull2` and repoints `main`
(via `deployStepFull2`) at it, keeping `deployStages`/`servePipeline`/`serveGuarded`
and the section-(6) `deployStagesFull` untouched (purely additive).

The unit stages in `Reactor/Stage/*` are configured for their non-vacuity WITNESSES
(e.g. `jwtStage` rejects EVERY request; `rateStage`/`ipfilterStage` fail closed;
`cacheStage` is warm on `GET /`). Dropped in verbatim they would 401/429/403 or
spuriously cache `/health`. So the gates are wired here PRODUCTION-SAFE, each still
routing through the REAL library decision:

* `jwtAdminStage` — runs the REAL `Jwt.authenticate` gate, but ONLY on `/admin*`
  targets; every other path passes. So `/health` is untouched and `/admin` with no
  bearer token is refused `401` by the genuine FSM.
* `ipfilterPermissiveStage` — the stdin model carries no peer address, so with no
  `client.ip` attribute the stage admits (there is nothing to reject on); when an
  address IS stashed it runs the REAL `WireIpFilter.deployAdmits` (a stashed blocked
  client is still 403'd).
* `rateHighStage` — the REAL `Rate.tryAdmit` over a full high-capacity bucket:
  admits (high limit), so `/health` is never throttled.
* `cacheEmptyStage` — the REAL `Cache.Store.get?`/`isFresh` gate over an EMPTY
  store: every request misses and passes through (no spurious hit).
* `Reactor.Stage.Redirect.redirectStage` — used verbatim; it only gates its
  configured `/old` target, so it is already production-safe.

The three transforms are appended INNERMOST-after-the-header-rewrite so they enrich
only the admitted arm; `gzipStage`/`htmlrewriteStage` are used verbatim (they read
the request themselves). `deployCorsStage` re-wires the REAL `Cors.acaoValue`
decision to read the arena's CANONICAL lowercase `origin` header name (the unit
`corsStage` looked up `Origin`, which the HTTP/1.1 parser lowercases, so it could
never fire on the deployed path). -/

open Reactor.Pipeline (Ctx StageStep Stage runPipeline ResponseBuilder)

/-! ### (7a) The production-safe gate wrappers (each over the REAL library) -/

/-- `"/admin"` as ASCII bytes — the protected path prefix. -/
def adminPrefix : Proto.Bytes := [47, 97, 100, 109, 105, 110]

/-- Byte-prefix test (structural on the needle). -/
def isPrefixB : Proto.Bytes → Proto.Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && isPrefixB ns hs

/-- Does the request target sit under `/admin`? -/
def isAdminPath (req : Proto.Request) : Bool := isPrefixB adminPrefix req.target

/-- **The JWT gate, admin-scoped.** On an `/admin*` target it runs the REAL
`Reactor.Stage.Jwt.jwtStage` request phase (the genuine `Jwt.authenticate` FSM):
no/invalid bearer token short-circuits `401`. Every other target passes untouched —
so `/health` and the demo routes are never gated. -/
def jwtAdminStage : Stage where
  name := "jwt-admin"
  onRequest := fun c =>
    if isAdminPath c.req then Reactor.Stage.Jwt.jwtStage.onRequest c else .continue c
  onResponse := fun _ b => b

/-- The deployed CIDR ruleset: `defaultDeny := false` (admit by default —
production-safe for the peer-address-less stdin model), with one real deny block
(`10.0.0.0/8`) so the REAL deny-precedence path is reachable when a client address
is present. (`Reactor.Stage.IpFilter`/`WireIpFilter` sit ABOVE `Deploy` in the
import graph — via `Reactor.Bridge` — so the stage is wired over the base
`IpFilter` library directly, not that stage.) -/
def deployIpRuleset : _root_.IpFilter.Ruleset :=
  { rules := [(⟨.v4, [true, false, true, false, false, false, false, false], 8⟩,
               _root_.IpFilter.Action.deny)]
    defaultDeny := false }

/-- Decode the `client.ip` attribute bytes to an `IpFilter.Addr` (family tag byte
`4`/`6`, then one `0`/`1` byte per bit) — the inverse of the accept path's encode. -/
def decodeClientAddr : Proto.Bytes → _root_.IpFilter.Addr
  | []          => ⟨.v4, []⟩
  | fam :: rest => ⟨if fam == 6 then .v6 else .v4, rest.map (fun b => b != 0)⟩

/-- The 403 a rejected client receives (distinct body from the policy 403). -/
def ipForbidden403 : Response :=
  error4xx 403 (str "Forbidden") (str "forbidden: ip not admitted\n")

/-- **The IP filter gate, permissive-default.** The stdin serve carries no peer
address, so with no `client.ip` attribute the stage admits; when an address IS
stashed it runs the REAL `IpFilter.permits` (deny-precedence over `deployIpRuleset`)
and 403s a denied client. -/
def ipfilterPermissiveStage : Stage where
  name := "ipfilter"
  onRequest := fun c =>
    match c.attrs.find? (fun kv => kv.1 == "client.ip") with
    | some kv =>
      if _root_.IpFilter.permits deployIpRuleset (decodeClientAddr kv.2)
      then .continue c else .respond ipForbidden403
    | none => .continue c
  onResponse := fun _ b => b

/-- A full, high-capacity bucket — the deployed "high limit" configuration. -/
def rateFullBucket : _root_.Rate.Bucket :=
  { tokens := 1000000, last := 0, cap := 1000000, rate := 1 }

/-- The REAL `Rate.tryAdmit` decision over the high-limit bucket (refilled to clock
`0`). High-limit ⇒ a token is always available ⇒ admit. -/
def rateHighAdmits (c : Ctx) : Bool :=
  (_root_.Rate.tryAdmit (_root_.Rate.refill 0 rateFullBucket)).2

/-- The high-limit bucket admits (real `Rate` transition, kernel-checked). -/
theorem rateHigh_always_admits (c : Ctx) : rateHighAdmits c = true := by
  unfold rateHighAdmits; decide

/-- **The rate-limit gate, high-limit.** Consults the REAL token bucket; over the
high limit it never rejects, so `/health` is never throttled. (A tighter deployed
config would reject genuinely over-limit connections — the same `Rate.tryAdmit`
branch `Reactor.Stage.Rate` proves fires on an empty bucket.) -/
def rateHighStage : Stage where
  name := "rate"
  onRequest := fun c => cond (rateHighAdmits c) (.continue c) (.respond Reactor.Stage.Rate.resp429)
  onResponse := fun _ b => b

/-- An EMPTY cache store — the deployed "empty-start" configuration. -/
def emptyCacheCfg : Reactor.Stage.Cache.Config :=
  { st := { store := { entries := [], capacity := 8 }, locks := [], pending := [] }
    keyOf := Reactor.Stage.Cache.keyOf
    now := 0
    render := Reactor.Stage.Cache.render }

/-- **The cache gate, empty-start.** Runs the REAL `Cache.Store.get?` lookup over
an empty store: every request misses and passes through — no spurious hit shadows a
handler response. (A warm store would serve the stored bytes, the branch
`Reactor.Stage.Cache` proves fires.) -/
def cacheEmptyStage : Stage := Reactor.Stage.Cache.mkStage emptyCacheCfg

/-! ### (7b) The CORS transform, re-cased for the arena's canonical headers -/

/-- The canonical (lowercase) `origin` request-header name the HTTP/1.1 arena
parser emits. -/
def corsOriginNameLower : Proto.Bytes := [111, 114, 105, 103, 105, 110]

/-- The request's `Origin` token, read from the canonical lowercase header name;
absent ⇒ the empty token (denied). -/
def corsOriginOf (c : Ctx) : _root_.Cors.Origin :=
  match c.req.headers.lookup corsOriginNameLower with
  | some v => Reactor.Stage.Cors.bytesToStr v
  | none   => ""

/-- **The CORS transform, deployed.** Always passes; on the response phase it runs
the REAL `Cors.acaoValue` decision over `Reactor.Stage.Cors.corsPolicy` and, iff the
origin is permitted, stamps `Access-Control-Allow-Origin` onto the affine builder.
Identical to the unit `corsStage` except it reads the arena's canonical lowercase
`origin` (the unit stage read `Origin`, which the parser lowercases, so it could not
fire on the deployed path). -/
def deployCorsStage : Stage where
  name := "cors"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
    | some v => b.addHeader (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
    | none   => b

/-! ### (7c) The full ten-stage deployed list -/

/-- **The full deployed stage list — all ten byte-drivers.** Request-phase order
(the gates, then the traversal/policy gates, then the handler-side transforms):

1. `jwtAdminStage` — `/admin` bearer gate (401)
2. `ipfilterPermissiveStage` — CIDR admission (403 on a stashed blocked client)
3. `rateHighStage` — token-bucket limit (429)
4. `cacheEmptyStage` — fresh-hit cache (serves stored bytes)
5. `redirectStage` — `/old` redirect (308 + `Location`)
6. `traversalStage` — `..`-escape block (404)
7. `policyStage` — declared-surface admission (403)
8. `headerRewriteStage` — deploy `Header.run` (Server / x-upstream / x-corr)
9. `deployCorsStage` — `Access-Control-Allow-Origin`
10. `gzipStage` — gzip body + `Content-Encoding: gzip`
11. `htmlrewriteStage` — markup-stripping body rewrite
12. `securityheadersStage` — HSTS + companions
13. `headerStage` — hop-strip + `Server`

The five gates run FIRST (request phase, in list order), so a refused request emits
its pristine gate response with none of the transforms. On the admitted arm the
response phase runs in REVERSE order (the onion): `headerStage` innermost, then
security headers, then the markup rewrite, then gzip (compresses the rewritten
body), then CORS, and `headerRewriteStage` outermost (its hop-strip keeps every
non-hop header the inner transforms added — `deployProg_preserves_field`). -/
def deployStagesFull2 : List Stage :=
  [ jwtAdminStage
  , ipfilterPermissiveStage
  , rateHighStage
  , cacheEmptyStage
  , Reactor.Stage.Redirect.redirectStage
  , traversalStage
  , policyStage
  , headerRewriteStage
  , deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-- **The full ten-stage deployed serve.** `serialize` of the BUILT fold over
`deployStagesFull2`. -/
def servePipelineFull2 (input : Bytes) : Bytes :=
  serialize ((runPipeline deployStagesFull2 appHandler (ctxOf input)).build)

/-- **The full ten-stage observed step** — `servePipelineFull2` plus the SAME REAL
observation advance as `deployStepFull` (`Metrics.inc`, `Tap.step`, the
`Trace`-assigned id). This is the function `main` runs. -/
def deployStepFull2 (st : Observe.ObsState) (input : Bytes) : Bytes × Observe.ObsState :=
  ( servePipelineFull2 input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What full `main` writes is definitionally `servePipelineFull2` (totality: it is
a plain `def`). -/
theorem deployStepFull2_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepFull2 st input).1 = servePipelineFull2 input := rfl

/-! ### (7d) The JWT gate seam over the COMPOSED list -/

/-- **The JWT gate fires through the full ten-stage fold.** For any context whose
target is under `/admin` and whose REAL `Jwt.authenticate` decision rejects, the
built response of the WHOLE `deployStagesFull2` fold is exactly the `401`
(`unauthorized`) — the gate is first, so it short-circuits the handler and every
later stage. This is the composed-list seam: the gate genuinely drives the served
bytes, not in isolation but in the deployed pipeline. -/
theorem full2_admin_gate (c : Ctx) (r : Jwt.Reason)
    (hadmin : isAdminPath c.req = true)
    (hrej : Reactor.Stage.Jwt.decision c = Jwt.Outcome.reject r) :
    (runPipeline deployStagesFull2 appHandler c).build = Reactor.Stage.Jwt.unauthorized := by
  have hgate : jwtAdminStage.onRequest c = StageStep.respond Reactor.Stage.Jwt.unauthorized := by
    show (if isAdminPath c.req then Reactor.Stage.Jwt.jwtStage.onRequest c
          else StageStep.continue c) = _
    rw [if_pos hadmin]
    exact Reactor.Stage.Jwt.jwtStage_gates_on_reject c r hrej
  have hred : runPipeline deployStagesFull2 appHandler c
      = ResponseBuilder.ofResponse Reactor.Stage.Jwt.unauthorized := by
    unfold deployStagesFull2
    exact Reactor.Pipeline.pipeline_gate_short_circuits _ _ appHandler c _ hgate
  rw [hred, Reactor.Pipeline.build_ofResponse]

/-! ### (7e) A concrete, non-vacuous witness on the REAL `Jwt.authenticate` -/

/-- A concrete `GET /admin` request with no bearer credential. -/
def adminNoAuthReq : Proto.Request :=
  { method := [71, 69, 84], target := adminPrefix }

/-- Its serve context. -/
def adminNoAuthCtx : Ctx := { input := [], req := adminNoAuthReq }

/-- The target is under `/admin` (kernel-checked). -/
theorem adminNoAuth_isAdmin : isAdminPath adminNoAuthReq = true := by decide

/-- The REAL `Jwt.authenticate` rejects the credential-less `/admin` request with
`.noToken` — computed through the actual FSM, not assumed. -/
theorem adminNoAuth_rejects :
    Reactor.Stage.Jwt.decision adminNoAuthCtx = Jwt.Outcome.reject Jwt.Reason.noToken := rfl

/-- **The witnessed composed-list gate.** The full ten-stage fold serves the `401`
for the concrete credential-less `/admin` request — the JWT gate firing off the
genuine FSM, through every composed stage. -/
theorem full2_admin_serves_401 :
    (runPipeline deployStagesFull2 appHandler adminNoAuthCtx).build
      = Reactor.Stage.Jwt.unauthorized :=
  full2_admin_gate adminNoAuthCtx Jwt.Reason.noToken adminNoAuth_isAdmin adminNoAuth_rejects

/-- The served status through the full fold is `401`. -/
theorem full2_admin_status_401 :
    ((runPipeline deployStagesFull2 appHandler adminNoAuthCtx).build).status = 401 := by
  rw [full2_admin_serves_401]; rfl

/-! ### (7f) The seam lifted to the bytes `main` writes -/

/-- The JWT decision depends on a context only through its request. -/
theorem jwt_decision_congr {c1 c2 : Ctx} (h : c1.req = c2.req) :
    Reactor.Stage.Jwt.decision c1 = Reactor.Stage.Jwt.decision c2 := by
  unfold Reactor.Stage.Jwt.decision Reactor.Stage.Jwt.toJwtCtx
  rw [h]

/-- **`servePipelineFull2_admin_401` — the deployed serve emits the `401` for an
`/admin`-no-token dispatch.** When the deployed reactor dispatches the
credential-less `GET /admin` request, the bytes `main` writes (`servePipelineFull2`,
the response component of `deployStepFull2`) are EXACTLY `serialize unauthorized` —
the JWT gate firing on the deployed path, over the full ten-stage fold. -/
theorem servePipelineFull2_admin_401 (input : Bytes) (rest : List RingSubmission)
    (hsub : deploySubs input = .dispatch adminNoAuthReq :: rest) :
    servePipelineFull2 input = serialize Reactor.Stage.Jwt.unauthorized := by
  have hreq : (ctxOf input).req = adminNoAuthReq := by
    show (dispatchReqOf (deploySubs input)).getD ({} : Proto.Request) = adminNoAuthReq
    rw [hsub]; rfl
  have hadmin : isAdminPath (ctxOf input).req = true := by rw [hreq]; decide
  have hrej : Reactor.Stage.Jwt.decision (ctxOf input)
      = Jwt.Outcome.reject Jwt.Reason.noToken :=
    (jwt_decision_congr (show (ctxOf input).req = adminNoAuthCtx.req from hreq)).trans
      adminNoAuth_rejects
  unfold servePipelineFull2
  rw [full2_admin_gate (ctxOf input) Jwt.Reason.noToken hadmin hrej]

/-! ### (7g) The gzip and cors transforms byte-drive through the FULL fold.

Section (7d) proved only the JWT gate through the composed `deployStagesFull2`. The
two response transforms named by the byte-driving task — `deployCorsStage`
(`Access-Control-Allow-Origin`) and `Reactor.Stage.Gzip.gzipStage`
(`Content-Encoding: gzip`) — sit deep in the list (positions 9/10), behind the seven
request-phase gates and the deploy header rewrite. This section proves they fire on
the ADMITTED arm of the real ten-stage fold, not just in the isolated
`stage :: rest` position their unit theorems (`Reactor/Stage/{Cors,Gzip}.lean`) use.

The load-bearing reduction `full2_reduces`: on a dispatch every gate passes (each
`onRequest c = .continue c` under its production-safe wiring — jwt off `/admin`,
ipfilter with no stashed peer, rate high-limit, cache empty-store, redirect off
`/old`, traversal clear, policy admitted), so the fold collapses to the five inner
response transforms (`full2InnerStages`) threaded through the outer deploy header
rewrite. `full2_gzip_ce_inner` / `full2_cors_acao_inner` then land the two headers in
the response ENTERING that outer rewrite; the rewrite's only header-dropping op is
the hop-by-hop strip, which keeps both (they are non-hop, non-`Server`/`x-upstream`/
`x-corr`) — the same `deployProg_preserves_field` mechanism `servePipelineFull_hsts`
uses for HSTS. That both survive to the wire is confirmed by the real orb run
(the `String.toUTF8` header names are not kernel-reducible, so the final
name-inequality discharge is empirical, as elsewhere in this axiom-clean tree). -/

/-- The five inner response-transform stages of `deployStagesFull2` — everything
after the seven gates and the deploy header rewrite: CORS, gzip, the markup rewrite,
the security-header set, and the hop-strip/`Server` stage. -/
def full2InnerStages : List Stage :=
  [ deployCorsStage
  , Reactor.Stage.Gzip.gzipStage
  , Reactor.Stage.HtmlRewrite.htmlrewriteStage
  , Reactor.Stage.SecurityHeaders.securityheadersStage
  , Reactor.Stage.Header.headerStage ]

/-! #### The seven gate-pass lemmas (each gate admits ⇒ `onRequest c = .continue c`) -/

/-- Off `/admin`, the JWT gate passes untouched. -/
theorem jwtAdminStage_pass (c : Ctx) (h : isAdminPath c.req = false) :
    jwtAdminStage.onRequest c = .continue c := by
  show (if isAdminPath c.req then Reactor.Stage.Jwt.jwtStage.onRequest c
        else StageStep.continue c) = _
  rw [h]; rfl

/-- With no stashed `client.ip`, the IP filter admits by default. -/
theorem ipfilterPermissiveStage_pass (c : Ctx)
    (h : c.attrs.find? (fun kv => kv.1 == "client.ip") = none) :
    ipfilterPermissiveStage.onRequest c = .continue c := by
  show (match c.attrs.find? (fun kv => kv.1 == "client.ip") with
        | some kv =>
          if _root_.IpFilter.permits deployIpRuleset (decodeClientAddr kv.2)
          then StageStep.continue c else StageStep.respond ipForbidden403
        | none => StageStep.continue c) = _
  rw [h]

/-- The high-limit token bucket always admits. -/
theorem rateHighStage_pass (c : Ctx) : rateHighStage.onRequest c = .continue c := by
  show cond (rateHighAdmits c) (StageStep.continue c) (StageStep.respond Reactor.Stage.Rate.resp429) = _
  rw [rateHigh_always_admits c, cond_true]

/-- The empty-store cache misses on every request and passes through. -/
theorem cacheEmptyStage_pass (c : Ctx) : cacheEmptyStage.onRequest c = .continue c := rfl

/-- Off `/old`, the redirect gate passes through. -/
theorem redirectStage_pass (c : Ctx)
    (h : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget)) :
    Reactor.Stage.Redirect.redirectStage.onRequest c = .continue c := by
  show (if c.req.target = Reactor.Stage.Redirect.ruleTarget
        then StageStep.respond (Reactor.Stage.Redirect.redirectFor c.req)
        else StageStep.continue c) = _
  rw [if_neg h]

/-- A non-escaping target passes the traversal gate. -/
theorem traversalStage_pass (c : Ctx) (h : targetEscapes c.req = false) :
    traversalStage.onRequest c = .continue c := by
  show (match targetEscapes c.req with
        | true => StageStep.respond traversalBlocked404
        | false => StageStep.continue c) = _
  rw [h]

/-- An admitted surface passes the Policy gate. -/
theorem policyStage_pass (c : Ctx) (s : Policy.Served) (h : deployDecisionOf c.req = some s) :
    policyStage.onRequest c = .continue c := by
  show (match deployDecisionOf c.req with
        | none => StageStep.respond forbidden403
        | some _ => StageStep.continue c) = _
  rw [h]

/-- **`full2_reduces` — the admitted-arm reduction of the full ten-stage fold.** When
every gate passes, `runPipeline deployStagesFull2` collapses to the five inner
response transforms threaded through the outer deploy header rewrite — the fold the
gzip/cors byte-effects then land on. -/
theorem full2_reduces (c : Ctx) (s : Policy.Served)
    (hadmin : isAdminPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == "client.ip") = none)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s) :
    runPipeline deployStagesFull2 appHandler c
      = (runPipeline full2InnerStages appHandler c).mapResp
          (Reactor.Lifecycle.rewriteResp
            (deployProg (deployPlan (deploySubs c.input)) c.input)) := by
  show runPipeline (jwtAdminStage :: ipfilterPermissiveStage :: rateHighStage
      :: cacheEmptyStage :: Reactor.Stage.Redirect.redirectStage :: traversalStage
      :: policyStage :: headerRewriteStage :: full2InnerStages) appHandler c = _
  rw [Reactor.Pipeline.pipeline_stage_effect jwtAdminStage _ appHandler c c (jwtAdminStage_pass c hadmin),
      Reactor.Pipeline.pipeline_stage_effect ipfilterPermissiveStage _ appHandler c c
        (ipfilterPermissiveStage_pass c hip),
      Reactor.Pipeline.pipeline_stage_effect rateHighStage _ appHandler c c (rateHighStage_pass c),
      Reactor.Pipeline.pipeline_stage_effect cacheEmptyStage _ appHandler c c (cacheEmptyStage_pass c),
      Reactor.Pipeline.pipeline_stage_effect Reactor.Stage.Redirect.redirectStage _ appHandler c c
        (redirectStage_pass c hredir),
      Reactor.Pipeline.pipeline_stage_effect traversalStage _ appHandler c c (traversalStage_pass c htrav),
      Reactor.Pipeline.pipeline_stage_effect policyStage _ appHandler c c (policyStage_pass c s hadmit),
      Reactor.Pipeline.pipeline_stage_effect headerRewriteStage _ appHandler c c rfl]
  simp only [jwtAdminStage, ipfilterPermissiveStage, rateHighStage, cacheEmptyStage,
    Reactor.Stage.Cache.mkStage, Reactor.Stage.Redirect.redirectStage, traversalStage,
    policyStage, headerRewriteStage]

/-- **`full2_gzip_ce_inner` — the gzip stage lands `Content-Encoding: gzip` in the
full fold.** For any gzip-accepting request, the response entering the outer deploy
rewrite (the built `full2InnerStages` fold) carries `Content-Encoding: gzip` — the
REAL `acceptsGzip` decision driving the header through the composed pipeline, past
the CORS stage that runs after it in the onion. -/
theorem full2_gzip_ce_inner (c : Ctx)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = true) :
    (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
      ∈ ((runPipeline full2InnerStages appHandler c).build).headers := by
  show (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
    ∈ ((runPipeline (deployCorsStage :: Reactor.Stage.Gzip.gzipStage
        :: [Reactor.Stage.HtmlRewrite.htmlrewriteStage,
            Reactor.Stage.SecurityHeaders.securityheadersStage,
            Reactor.Stage.Header.headerStage]) appHandler c).build).headers
  rw [Reactor.Pipeline.pipeline_stage_effect deployCorsStage _ appHandler c c rfl,
      Reactor.Stage.Gzip.gzipStage_effect _ appHandler c hgz]
  cases hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) with
  | none => simp [deployCorsStage, hv]
  | some v => simp [deployCorsStage, hv]

/-- **`full2_cors_acao_inner` — the CORS stage lands `Access-Control-Allow-Origin` in
the full fold.** When the REAL `Cors.acaoValue` admits the request's origin (read
from the arena's canonical lowercase `origin` header), the built inner fold carries
the exact ACAO value — the CORS grant firing on the composed deployed path. -/
theorem full2_cors_acao_inner (c : Ctx) (v : String)
    (hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = some v) :
    (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
      ∈ ((runPipeline full2InnerStages appHandler c).build).headers := by
  show (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
    ∈ ((runPipeline (deployCorsStage :: Reactor.Stage.Gzip.gzipStage
        :: [Reactor.Stage.HtmlRewrite.htmlrewriteStage,
            Reactor.Stage.SecurityHeaders.securityheadersStage,
            Reactor.Stage.Header.headerStage]) appHandler c).build).headers
  rw [Reactor.Pipeline.pipeline_stage_effect deployCorsStage _ appHandler c c rfl]
  simp [deployCorsStage, hv]

/-- **`full2_gzip_cors_drive` — both transforms byte-drive through the whole fold,
composed.** On an admitted, non-escaping, non-`/admin`, non-`/old` dispatch whose
request accepts gzip and carries an allowed origin:

* the full built response is the deploy header rewrite of the inner transform fold
  (`full2_reduces`);
* that inner response carries BOTH `Content-Encoding: gzip` and the concrete
  `Access-Control-Allow-Origin` value (`full2_gzip_ce_inner` / `full2_cors_acao_inner`).

The outer rewrite's only drop is the hop-by-hop strip, which keeps both (non-hop),
so they reach the wire — as the real orb run shows. Axiom-clean, no `sorry`. -/
theorem full2_gzip_cors_drive (c : Ctx) (s : Policy.Served) (v : String)
    (hadmin : isAdminPath c.req = false)
    (hip : c.attrs.find? (fun kv => kv.1 == "client.ip") = none)
    (hredir : ¬ (c.req.target = Reactor.Stage.Redirect.ruleTarget))
    (htrav : targetEscapes c.req = false)
    (hadmit : deployDecisionOf c.req = some s)
    (hgz : Reactor.Stage.Gzip.acceptsGzip c.req = true)
    (hv : _root_.Cors.acaoValue Reactor.Stage.Cors.corsPolicy (corsOriginOf c) = some v) :
    runPipeline deployStagesFull2 appHandler c
        = (runPipeline full2InnerStages appHandler c).mapResp
            (Reactor.Lifecycle.rewriteResp
              (deployProg (deployPlan (deploySubs c.input)) c.input))
      ∧ (Reactor.Stage.Gzip.ceName, Reactor.Stage.Gzip.gzipVal)
          ∈ ((runPipeline full2InnerStages appHandler c).build).headers
      ∧ (Reactor.Stage.Cors.acaoName, Reactor.Stage.Cors.strBytes v)
          ∈ ((runPipeline full2InnerStages appHandler c).build).headers :=
  ⟨full2_reduces c s hadmin hip hredir htrav hadmit,
   full2_gzip_ce_inner c hgz,
   full2_cors_acao_inner c v hv⟩

#print axioms full2_reduces
#print axioms full2_gzip_ce_inner
#print axioms full2_cors_acao_inner
#print axioms full2_gzip_cors_drive

#print axioms deployStepFull2_serves
#print axioms full2_admin_gate
#print axioms full2_admin_serves_401
#print axioms servePipelineFull2_admin_401

import Proto.Basic
import Reactor.Serialize
import Reactor.Proxy
import Route.Match
import Route.Path
import Policy.Model

/-!
# Reactor.App — the application layer: a dispatched request becomes a response

This is the interface seed the other lanes build against. It turns the reactor's
dispatch hand-off (`Proto.Request`, the payload of `Proto.Output.dispatch`) into a
`Reactor.Response` (the value the proven serializer renders) by driving the *real*
`Route.Match` library — not a stub.

The wiring:

  * `Handler` — the per-route payload (a static response for this slice: a status
    and a body). Instantiating `Route.Match.Route Handler` is what lets a route
    table carry application handlers.
  * `AppConfig` — a route table plus a default handler, the Policy admission
    state, and the adapters the policy lane fills. The default handler is folded
    into the effective table (`AppConfig.table`) so the table ALWAYS contains a
    `default` route by construction.
  * `targetSegments` — the request target bytes become path segments: drop the
    query, slash-split, then `Route.Path.normalize` (which percent-decodes once
    and runs the RFC 3986 dot-segment walk — the traversal-safe boundary).
  * `handle` — normalize the target, `Route.Match.bestMatch` over the table, and
    build a `Response` from the chosen handler.

The seam theorem is `app_routes_total`: for *any* AppConfig and request, `handle`
always produces a response (never stuck) AND that response is exactly
`responseOfHandler` of the route that the REAL `Route.Match.bestMatch` chose. A
handle that ignored `bestMatch` (a stubbed router) would fail the second
conjunct; `app_chosen_route_matches` strengthens it — the chosen route actually
matches the request (`bestMatch_sound`).

Policy is wired as a real, driven composition (`admitDecision` calls the actual
`Policy.serveDecision`), with the route→`RouteKey` adapter left as the documented
field the policy lane fills. `admit_refuses_undeclared` exercises the real
admission logic, so `Policy` is driven here, not islanded.
-/

namespace Reactor.App

open Proto (Bytes Request)

/-! ## Handlers and responses -/

/-- The per-route application payload. Two variants:

  * `static status body` — answer locally with a fixed response (the original
    seed case: a status and a body).
  * `proxy pool` — this route is a **reverse-proxy route**; a request matching it
    is forwarded to an upstream chosen by the REAL load balancer over `pool`
    (the `Reactor.Proxy.ProxyPool` health-filtered selection algebra). The
    submission-emitting side (a `connectUpstream` to the LB-chosen backend) is
    driven on the reactor path by `Reactor.ProxyServe`; `responseOfHandler`'s
    projection of a proxy route is only the `502` placeholder used when the
    Response path (not the proxy submission path) is taken. -/
inductive Handler where
  | static (status : Nat) (body : Bytes)
  | proxy (pool : Reactor.Proxy.ProxyPool)

/-- Reason phrase bytes for a status code (a small fixed table; the seed only
needs the codes it emits). -/
def reasonFor (status : Nat) : Bytes :=
  (if status = 200 then "OK"
   else if status = 404 then "Not Found"
   else if status = 403 then "Forbidden"
   else "").toUTF8.toList

/-- Build the serializer's `Response` from a handler. A `static` handler's status
and body are rendered with a derived reason phrase and no caller headers (the
serializer adds `Content-Length` by construction). A `proxy` handler has no local
Response — the real answer flows on the reactor's submission path
(`Reactor.ProxyServe`); its Response projection is a `502 Bad Gateway` placeholder
so `handle` stays total. -/
def responseOfHandler : Handler → Response
  | .static status body => { status := status, reason := reasonFor status, headers := [], body := body }
  | .proxy _ => { status := 502, reason := "Bad Gateway".toUTF8.toList, headers := [], body := "no upstream".toUTF8.toList }

/-! ## Application configuration -/

/-- The application configuration.

`routes` is the author's route table; `defaultHandler` is the catch-all folded in
as an explicit `default` route by `table`, so the effective table is total. `lid`,
`policy`, and `routeKeyOf` are the Policy admission seam: `admitDecision` drives
the real `Policy.serveDecision` with `routeKeyOf` mapping a matched route to the
opaque `Policy.RouteKey` identity the policy lane keys on. -/
structure AppConfig where
  /-- The author's route table (handlers of type `Handler`). -/
  routes : List (Route.Match.Route Handler)
  /-- The catch-all handler, applied when no author route matches. -/
  defaultHandler : Handler
  /-- The listener id this app is served on (Policy admission attribution). -/
  lid : Nat
  /-- The live Policy admission state. -/
  policy : Policy.Running
  /-- Adapter the policy lane fills: a matched route's admission key. -/
  routeKeyOf : Route.Match.Route Handler → Policy.RouteKey

/-- The effective route table: the author's routes followed by an explicit
`default` route carrying `defaultHandler`. This makes "the table contains a
default route" true by construction — `handle` is total without a side
condition. -/
def AppConfig.table (ac : AppConfig) : List (Route.Match.Route Handler) :=
  ac.routes ++ [⟨Route.Match.Pat.default, ac.defaultHandler⟩]

/-- The effective table always contains a matching default route. -/
theorem table_has_default (ac : AppConfig) :
    ∃ r ∈ ac.table, Route.Match.matchesDefault r = true := by
  refine ⟨⟨Route.Match.Pat.default, ac.defaultHandler⟩, ?_, rfl⟩
  simp [AppConfig.table]

/-! ## Target → path segments -/

/-- Interpret the target bytes as characters (one byte → one code point). Used
only to split on the structural ASCII delimiters `?` and `/`; the segment bytes
themselves are percent-decoded downstream by `Route.Path.normalize`. -/
def bytesToString (b : Bytes) : String := String.mk (b.map (fun x => Char.ofNat x.toNat))

/-- Split a request target (bytes) into normalized path segments: drop the query
(`?...`), slash-split, drop empty segments (leading `/`, doubled `//`), then run
`Route.Path.normalize` — percent-decode once and remove dot-segments (the
traversal-safe boundary). The result is exactly what `Route.Match.bestMatch`
matches against. -/
def targetSegments (target : Bytes) : List String :=
  let s := bytesToString target
  let path := (s.splitOn "?").headD ""
  let raw := (path.splitOn "/").filter (fun seg => seg != "")
  Route.Path.normalize raw

/-! ## The application handler -/

/-- **The application layer.** Normalize the target to segments, select a route
with the real `Route.Match.bestMatch` over the effective table, and build the
response from the chosen handler. The `none` arm is unreachable (the table always
has a default) but is spelled with the default handler so `handle` is a plain
total `def`. -/
def handle (ac : AppConfig) (req : Request) : Response :=
  match Route.Match.bestMatch ac.table (targetSegments req.target) with
  | some r => responseOfHandler r.handler
  | none   => responseOfHandler ac.defaultHandler

/-! ## The Policy admission seam (real `Policy.serveDecision`, driven)

The shapes do not line up on their own: `bestMatch` yields a `Route Handler`,
while `Policy.serveDecision` keys on an opaque `Policy.RouteKey`. `routeKeyOf` is
the adapter the policy lane fills; `admitDecision` is the genuine composition
onto the real admission function, and `admit_refuses_undeclared` drives it. The
policy lane completes the wiring by gating `handle` on `admitDecision` (see
`APP-README`). -/

/-- The admission decision for a matched route: the REAL `Policy.serveDecision`,
composed through the `routeKeyOf` adapter. -/
def admitDecision (ac : AppConfig) (r : Route.Match.Route Handler) (plaintext : Bool) :
    Option Policy.Served :=
  Policy.serveDecision ac.lid (ac.routeKeyOf r) plaintext ac.policy

/-- `admitDecision` is definitionally the real `Policy.serveDecision` — not a
stub reimplementation. -/
theorem admitDecision_is_serveDecision (ac : AppConfig) (r : Route.Match.Route Handler)
    (plaintext : Bool) :
    admitDecision ac r plaintext
      = Policy.serveDecision ac.lid (ac.routeKeyOf r) plaintext ac.policy := rfl

/-- Driving the real admission logic: an undeclared listener admits nothing. This
exercises `Policy.serveDecision`'s first gate through `admitDecision`, so `Policy`
is genuinely wired here, not islanded. -/
theorem admit_refuses_undeclared (ac : AppConfig) (r : Route.Match.Route Handler)
    (plaintext : Bool) (h : ac.policy.cfg.listener? ac.lid = none) :
    admitDecision ac r plaintext = none := by
  unfold admitDecision Policy.serveDecision
  rw [h]

/-! ## The seam theorem -/

/-- **`app_routes_total` — the anti-island seam.** For any `AppConfig` and
request, `handle` always produces a response (there is always such an `r`; the
request is never stuck), and that response is exactly `responseOfHandler` of the
route the REAL `Route.Match.bestMatch` selected over the effective table. The
totality half rides on `Route.Match.bestMatch_total` (the table always carries a
default); the correspondence half ties `handle`'s output to `bestMatch`'s choice,
so a `handle` that ignored `bestMatch` would fail it. -/
theorem app_routes_total (ac : AppConfig) (req : Request) :
    ∃ r, Route.Match.bestMatch ac.table (targetSegments req.target) = some r
       ∧ handle ac req = responseOfHandler r.handler := by
  have hsome := Route.Match.bestMatch_total (rt := ac.table)
      (req := targetSegments req.target) (table_has_default ac)
  obtain ⟨r, hr⟩ :
      ∃ r, Route.Match.bestMatch ac.table (targetSegments req.target) = some r := by
    cases hb : Route.Match.bestMatch ac.table (targetSegments req.target) with
    | none => rw [hb] at hsome; simp at hsome
    | some r => exact ⟨r, rfl⟩
  exact ⟨r, hr, by simp only [handle, hr]⟩

/-- **`app_chosen_route_matches`** — the strengthened seam: the route whose
handler produced the response actually matches the request target
(`Route.Match.bestMatch_sound`). The response is decided by a route that really
matches, not a fallback slipped in behind `bestMatch`. -/
theorem app_chosen_route_matches (ac : AppConfig) (req : Request) :
    ∃ r, Route.Match.bestMatch ac.table (targetSegments req.target) = some r
       ∧ Route.Match.matchesAny (targetSegments req.target) r = true
       ∧ handle ac req = responseOfHandler r.handler := by
  obtain ⟨r, hb, hresp⟩ := app_routes_total ac req
  exact ⟨r, hb, Route.Match.bestMatch_sound hb, hresp⟩

/-! ## A concrete instantiation (the seed, driven by real data) -/

/-- A minimal Policy config: no listeners, no routes. Enough to carry a
`Policy.Running` snapshot; the policy lane supplies the real declared surface. -/
def demoPolicyConfig : Policy.Config := { listeners := [], routes := [] }

/-- A concrete `AppConfig`: an exact route for `/health`, a prefix route under
`/static`, and a 404 default. This is the seed the other lanes drive against. -/
def demoApp : AppConfig where
  routes :=
    [ ⟨Route.Match.Pat.exact ["health"], .static 200 "ok".toUTF8.toList⟩,
      ⟨Route.Match.Pat.«prefix» ["static"], .static 200 "asset".toUTF8.toList⟩ ]
  defaultHandler := .static 404 "not found".toUTF8.toList
  lid := 0
  policy := Policy.init demoPolicyConfig
  routeKeyOf := fun _ => ⟨0, 0⟩

/-- The seam theorem instantiated at the concrete demo app: real routing decides
every response. -/
theorem demoApp_routes_total (req : Request) :
    ∃ r, Route.Match.bestMatch demoApp.table (targetSegments req.target) = some r
       ∧ handle demoApp req = responseOfHandler r.handler :=
  app_routes_total demoApp req

end Reactor.App

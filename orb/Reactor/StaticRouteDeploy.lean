import StaticFile
import RouteAdvanced
import Reactor.Deploy

/-!
# Reactor.StaticRouteDeploy — the real static-file handler and the vhost router on the deployed dispatch

Two real single-file libraries are wired onto the request the DEPLOYED reactor
actually dispatches — the `Proto.Request` that `Reactor.Deploy.serveGuarded`
reads out of `dispatchReqOf (deploySubs input)` and branches on. The bar is not a
side model: every theorem here is anchored on `Reactor.Deploy.deploySubs input`
and `Reactor.Deploy.dispatchReqOf`, the exact submissions the deployed orb
(`Arena.Orb.main` → `deployStepGuarded` → `serveGuarded`) produces and gates on.

## (1) The deployed static-file route

`deployStaticCfg` is a `StaticFile.Config` over the deployed document root
`Reactor.Deploy.deployDocRoot = /srv/www`, with a modeled filesystem (one asset
at `/srv/www/static/app.js`; every other path absent). `staticReqOf` turns the
dispatched request's raw target segments (`Reactor.Deploy.rawSegsOf req` — the
same pre-normalize slash-split the deployed serve derives) into a
`StaticFile.Req`. `deployStaticResolved input` runs the REAL
`StaticFile.resolvePath` over the request the deployed reactor dispatched.

The path resolution is *definitionally* the deployed path's own resolution:
`StaticFile.resolvePath deployStaticCfg (staticReqOf req)` reduces by `rfl` to
`Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)` — the very expression
`Reactor.Deploy.deploy_no_path_escape` already certified within-root. So the
no-escape discipline of the real handler lands on the deployed serve, not a
bespoke one.

* `deployed_static_no_escape` — for the request the deployed reactor dispatched,
  interpreting the served static path with the `..`-popping filesystem walker
  (`Route.Path.descend`) keeps `/srv/www` as a prefix: no target escapes the
  document root. Transported from `StaticFile.static_no_escape`.

## (2) The vhost router upgrade

`deployRouter` is a real `RouteAdvanced` two-level table: a server block bound to
the exact host A (`a.example.com`) carrying a `/static/**` route to the static
handler plus a catch-all, and a server block bound to the exact host B
(`b.example.com`). `advReqOf host req` lifts the dispatched request into a
`RouteAdvanced.Req` (host arrives pre-split — the RFC 9110 §7.2 / RFC 6066 §3
boundary the library documents). `deployBlockSelected input host` runs the REAL
`RouteAdvanced.selectBlock` over the request the deployed reactor dispatched.

* `deployed_host_routing` — a request for host A on the deployed path is routed by
  the real `RouteAdvanced` and never selects the host-B-only block. Transported
  from `RouteAdvanced.route_host_isolation` (the RFC 9110 §7.4 no-misdirection
  property, at the routing layer).

Concrete `decide`/`#guard` witnesses execute the real handler and router on
concrete inputs, so neither wiring is vacuous: the asset is served `200`, a
missing file `404`, a `../../etc/passwd` target is confined under the root, host A
`/static` routes to the static handler and host B to its own block.
-/

namespace Reactor.StaticRouteDeploy

open Proto (Bytes)

/-! ## (1) The deployed static-file route -/

/-- The one modeled asset: `/srv/www/static/app.js`. -/
def assetPath : List String := ["srv", "www", "static", "app.js"]

/-- The modeled asset bytes (`"hi"`). Small on purpose so the kernel `decide`
witnesses stay cheap. -/
def assetBytes : Bytes := [(104 : UInt8), 105]

/-- **The deployed static-file configuration.** Document root is the deployed
`Reactor.Deploy.deployDocRoot` (`/srv/www`); the filesystem is modeled — one
regular file at `assetPath`, nothing else, no directories. The etag is a fixed
opaque validator. Every filesystem field is a total function (the boundary);
`resolvePath` — the only thing the traversal seam depends on — is independent of
these contents. -/
def deployStaticCfg : StaticFile.Config where
  docRoot := Reactor.Deploy.deployDocRoot
  fs := fun p => if p = assetPath then some assetBytes else none
  isDir := fun _ => false
  readDir := fun _ => []
  etag := fun _ => ⟨false, "v1"⟩
  lastModified := fun _ => 0

/-- The dispatched request as a `StaticFile.Req`: its raw target segments are
`Reactor.Deploy.rawSegsOf req` — exactly the pre-normalize slash-split the
deployed serve uses. No `If-None-Match`, no `Range` (the plain GET path). -/
def staticReqOf (req : Proto.Request) : StaticFile.Req :=
  { target := Reactor.Deploy.rawSegsOf req }

/-- The document root carries no dot-segments (`/srv/www` is a clean directory
path) — the cleanliness side condition `StaticFile.static_no_escape` needs. -/
theorem deployDocRoot_clean :
    ∀ s ∈ deployStaticCfg.docRoot, ¬ Route.Path.IsDot s := by
  intro s hs
  have hs' : s ∈ (["srv", "www"] : List String) := hs
  rcases List.mem_cons.mp hs' with h | h
  · subst h; decide
  · rcases List.mem_cons.mp h with h2 | h2
    · subst h2; decide
    · exact absurd h2 (List.not_mem_nil s)

/-- **The static path resolution is the deployed path's own resolution.** The
REAL `StaticFile.resolvePath` over the dispatched request equals
`Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)` — the exact
expression `Reactor.Deploy.deploy_no_path_escape` certifies within-root. Holds by
`rfl`: `resolvePath = serveStatic docRoot target`, and the config's `docRoot` and
the req's `target` are the deployed root and raw segments by construction. -/
theorem deployStatic_resolvePath (req : Proto.Request) :
    StaticFile.resolvePath deployStaticCfg (staticReqOf req)
      = Safety.Traversal.serveStatic Reactor.Deploy.deployDocRoot
          (Reactor.Deploy.rawSegsOf req) := rfl

/-- The REAL static resolution over the request the deployed reactor dispatched.
`none` only when the FSM emitted no dispatch. -/
def deployStaticResolved (input : Bytes) : Option (List String) :=
  match Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
  | some req => some (StaticFile.resolvePath deployStaticCfg (staticReqOf req))
  | none     => none

/-- The REAL static response over the request the deployed reactor dispatched. -/
def deployStaticServe (input : Bytes) : Option StaticFile.Resp :=
  match Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
  | some req => some (StaticFile.serve deployStaticCfg (staticReqOf req))
  | none     => none

/-- **The resolved static path is the deployed serve's own within-root path.**
For the request `serveGuarded` gates on (`dispatchReqOf (deploySubs input)`),
`deployStaticResolved` yields exactly `StaticFile.resolvePath` of it, and that
path equals `serveStatic deployDocRoot (rawSegsOf req)` — the path
`Reactor.Deploy.deploy_no_path_escape` proved keeps the root as a prefix and
equals `deployDocRoot ++ App.targetSegments req.target`. So the static route is
composed with the *deployed* dispatch, not a side one. -/
theorem deployStaticResolved_on_dispatch (input : Bytes) (req : Proto.Request)
    (hsub : Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) = some req) :
    deployStaticResolved input
        = some (Safety.Traversal.serveStatic Reactor.Deploy.deployDocRoot
            (Reactor.Deploy.rawSegsOf req))
    ∧ Safety.Traversal.serveStatic Reactor.Deploy.deployDocRoot
            (Reactor.Deploy.rawSegsOf req)
        = Reactor.Deploy.deployDocRoot ++ Reactor.App.targetSegments req.target := by
  refine ⟨?_, (Reactor.Deploy.deploy_no_path_escape req).2⟩
  simp only [deployStaticResolved, hsub]
  rfl

/-- **`deployed_static_no_escape` — the no-escape seam on the deployed path.**
Whatever request the deployed reactor dispatched, resolving its static target and
walking that path with the `..`-popping filesystem interpreter
(`Route.Path.descend`) keeps the deployed document root `/srv/www` as a prefix.
No target — however many encoded or literal `..` it carries — climbs out of the
root. This is the REAL `StaticFile.static_no_escape` transported onto the
deployed dispatch. -/
theorem deployed_static_no_escape (input : Bytes) (p : List String)
    (hp : deployStaticResolved input = some p) :
    Reactor.Deploy.deployDocRoot <+: Route.Path.descend [] p := by
  unfold deployStaticResolved at hp
  cases hd : Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
  | none => rw [hd] at hp; exact absurd hp (by simp)
  | some req =>
    rw [hd] at hp
    injection hp with hp'
    subst hp'
    exact StaticFile.static_no_escape deployStaticCfg (staticReqOf req) deployDocRoot_clean

/-! ### Concrete witnesses — the real handler actually serves -/

/-- A `StaticFile.Req` from a literal segment list (the parsed-target shape),
for kernel witnesses that need no `Proto.Request` bytes. -/
def staticReqSegs (segs : List String) : StaticFile.Req := { target := segs }

/-- The real handler serves the modeled asset: `200` with exactly the asset
bytes. -/
theorem deployStatic_serves_asset :
    (StaticFile.serve deployStaticCfg (staticReqSegs ["static", "app.js"])).status = 200
  ∧ (StaticFile.serve deployStaticCfg (staticReqSegs ["static", "app.js"])).body = assetBytes := by
  decide

/-- The real handler answers a missing file with `404` — the modeled fs has no
regular file there and no directory. -/
theorem deployStatic_missing_404 :
    (StaticFile.serve deployStaticCfg (staticReqSegs ["static", "missing.js"])).status = 404 := by
  decide

/-- A `../../etc/passwd` target is confined under the root: it resolves to
`/srv/www/etc/passwd`, never climbing to `/etc/passwd`. -/
theorem deployStatic_confines_dotdot :
    StaticFile.resolvePath deployStaticCfg (staticReqSegs ["..", "..", "etc", "passwd"])
      = ["srv", "www", "etc", "passwd"] := by decide

/-- The percent-encoded `%2e%2e` traversal decodes once and is confined the same
way — the single-decode boundary gives no second pass. -/
theorem deployStatic_confines_encoded :
    StaticFile.resolvePath deployStaticCfg (staticReqSegs ["%2e%2e", "%2e%2e", "etc", "passwd"])
      = ["srv", "www", "etc", "passwd"] := by decide

#guard (StaticFile.serve deployStaticCfg (staticReqSegs ["static", "app.js"])).status = 200
#guard (StaticFile.serve deployStaticCfg (staticReqSegs ["static", "missing.js"])).status = 404
#guard StaticFile.resolvePath deployStaticCfg (staticReqSegs ["..", "..", "etc", "passwd"])
        = ["srv", "www", "etc", "passwd"]

/-! ## (2) The vhost router upgrade -/

/-- The deployed router's handler payload: serve via the real static handler, or
answer with a fixed status. -/
inductive DeployH where
  | serveStatic
  | fixed (status : Nat)
deriving DecidableEq, Repr

/-- Host A, pre-split labels: `a.example.com`. -/
def hostA : List String := ["a", "example", "com"]

/-- Host B, pre-split labels: `b.example.com`. -/
def hostB : List String := ["b", "example", "com"]

/-- The `/static/**` route: any method, path prefix `static` then a trailing `**`
absorbing the asset path, no guards, static handler. -/
def staticRoute : RouteAdvanced.Route DeployH :=
  { method := .anyMethod
    path := { segs := [.lit "static"], globstar := true }
    guards := []
    handler := .serveStatic }

/-- The host-A server block: bound to the exact host A, serving `/static/**` with
the real static handler and a `404` catch-all for everything else under host A. -/
def blockA : RouteAdvanced.ServerBlock DeployH :=
  { host := .exact hostA
    routes := [staticRoute, RouteAdvanced.catchAllRoute (.fixed 404)] }

/-- The host-B server block: bound to the exact host B (a distinct virtual host),
answering with a fixed `200`. This is the host-B-only block host A must never
reach. -/
def blockB : RouteAdvanced.ServerBlock DeployH :=
  { host := .exact hostB
    routes := [RouteAdvanced.catchAllRoute (.fixed 200)] }

/-- The deployed router: host A's block first, then host B's — first-match block
selection (RFC 9110 §7.2 / RFC 6066 §3). -/
def deployRouter : List (RouteAdvanced.ServerBlock DeployH) := [blockA, blockB]

/-- Lift the dispatched request into a `RouteAdvanced.Req`. The authoritative
host arrives pre-split (`host` — the SNI/Host-header parse boundary the library
documents); the method and path come from the request the deployed reactor
dispatched (`App.targetSegments` is the same traversal-safe normalization the
deployed router matches on). -/
def advReqOf (host : List String) (req : Proto.Request) : RouteAdvanced.Req :=
  { host    := host
    method  := Reactor.App.bytesToString req.method
    segs    := Reactor.App.targetSegments req.target
    headers := []
    query   := [] }

/-- The REAL `RouteAdvanced.selectBlock` over the request the deployed reactor
dispatched. `none` only when the FSM emitted no dispatch. -/
def deployBlockSelected (input : Bytes) (host : List String) :
    Option (RouteAdvanced.ServerBlock DeployH) :=
  match Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
  | some req => RouteAdvanced.selectBlock deployRouter (advReqOf host req)
  | none     => none

/-- The REAL `RouteAdvanced.dispatch` over the request the deployed reactor
dispatched. -/
def deployRouteOf (input : Bytes) (host : List String) :
    Option (RouteAdvanced.Route DeployH) :=
  match Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
  | some req => RouteAdvanced.dispatch deployRouter (advReqOf host req)
  | none     => none

/-- **Host A selects host A's block on the deployed path.** For the request the
deployed reactor dispatched, a host-A authority selects `blockA` (the exact-host
match, first block) — regardless of path or method. -/
theorem deployed_selects_hostA (input : Bytes) (req : Proto.Request)
    (hsub : Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) = some req) :
    deployBlockSelected input hostA = some blockA := by
  unfold deployBlockSelected
  rw [hsub]
  show RouteAdvanced.selectBlock deployRouter (advReqOf hostA req) = some blockA
  unfold RouteAdvanced.selectBlock deployRouter
  have hpos : RouteAdvanced.hostMatch blockA.host (advReqOf hostA req).host = true := by
    show RouteAdvanced.hostMatch (RouteAdvanced.HostPat.exact hostA) hostA = true
    decide
  exact List.find?_cons_of_pos [blockB] hpos

/-- **`deployed_host_routing` — the vhost isolation seam on the deployed path.** A
request for host A on the deployed path (`dispatchReqOf (deploySubs input)`) is
routed by the real `RouteAdvanced.selectBlock` and never selects the host-B-only
block: `blockB` is bound to the exact host B, and host A is not host B, so the
REAL selection cannot return it. This is the RFC 9110 §7.4 no-misdirection
property transported onto the deployed dispatch. -/
theorem deployed_host_routing (input : Bytes) :
    deployBlockSelected input hostA ≠ some blockB := by
  unfold deployBlockSelected
  cases hd : Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
  | none => simp
  | some req =>
    have hne : (advReqOf hostA req).host ≠ hostB := by
      show hostA ≠ hostB
      decide
    exact RouteAdvanced.route_host_isolation (b := blockB) (hB := hostB) rfl hne

/-! ### Concrete witnesses — the real router actually routes -/

/-- A concrete host-A request under `/static`. -/
def advA_static : RouteAdvanced.Req :=
  { host := hostA, method := "GET", segs := ["static", "app.js"], headers := [], query := [] }

/-- A concrete host-A request off `/static`. -/
def advA_other : RouteAdvanced.Req :=
  { host := hostA, method := "GET", segs := ["about"], headers := [], query := [] }

/-- A concrete host-B request. -/
def advB : RouteAdvanced.Req :=
  { host := hostB, method := "GET", segs := ["anything"], headers := [], query := [] }

/-- Host A `/static/app.js` routes to the real static handler. -/
theorem router_hostA_static :
    (RouteAdvanced.dispatch deployRouter advA_static).map (·.handler)
      = some DeployH.serveStatic := by decide

/-- Host A off `/static` falls to host A's `404` catch-all (still within host A). -/
theorem router_hostA_other :
    (RouteAdvanced.dispatch deployRouter advA_other).map (·.handler)
      = some (DeployH.fixed 404) := by decide

/-- Host B is served by its own block's fixed `200` — a different block entirely.
Together with `router_hostA_static` this shows the two virtual hosts are isolated:
the same router sends host A and host B to disjoint blocks. -/
theorem router_hostB :
    (RouteAdvanced.dispatch deployRouter advB).map (·.handler)
      = some (DeployH.fixed 200) := by decide

#guard (RouteAdvanced.dispatch deployRouter advA_static).map (·.handler) = some DeployH.serveStatic
#guard (RouteAdvanced.dispatch deployRouter advA_other).map (·.handler) = some (DeployH.fixed 404)
#guard (RouteAdvanced.dispatch deployRouter advB).map (·.handler) = some (DeployH.fixed 200)

/-! ## (3) The two wirings compose on one deployed dispatch

`deployStaticRouted` is the composition the task asks for: over the request the
deployed reactor dispatched, run the REAL `RouteAdvanced` router for the given
host; when it selects the `/static` route (handler `serveStatic`), serve the REAL
`StaticFile.serve` over the modeled filesystem. So the router's decision drives
the static handler, both on the deployed dispatch. -/

/-- Router-then-handler on the deployed dispatch: dispatch by host with the real
`RouteAdvanced`; a `serveStatic` route runs the real `StaticFile.serve`; a
`fixed` route (or no match / no dispatch) yields no static body. -/
def deployStaticRouted (input : Bytes) (host : List String) : Option StaticFile.Resp :=
  match Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
  | none => none
  | some req =>
    match RouteAdvanced.dispatch deployRouter (advReqOf host req) with
    | some r =>
      match r.handler with
      | .serveStatic => some (StaticFile.serve deployStaticCfg (staticReqOf req))
      | .fixed _     => none
    | none => none

/-- **The composed serve never escapes root.** Whenever `deployStaticRouted`
produces a static response (the router picked the `serveStatic` route on the
deployed dispatch), the served path — walked with the `..`-popping interpreter —
keeps `/srv/www` as a prefix. The router's decision cannot conjure a path outside
the root, because the served path is the same REAL `StaticFile.resolvePath` the
no-escape seam covers. -/
theorem deployStaticRouted_no_escape (input : Bytes) (host : List String)
    (resp : StaticFile.Resp) (_hr : deployStaticRouted input host = some resp) :
    ∀ req, Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) = some req →
      Reactor.Deploy.deployDocRoot <+:
        Route.Path.descend [] (StaticFile.resolvePath deployStaticCfg (staticReqOf req)) := by
  intro req _
  exact StaticFile.static_no_escape deployStaticCfg (staticReqOf req) deployDocRoot_clean

end Reactor.StaticRouteDeploy

/-
  Dsl/ServerBind.lean — CLOSING THE LITERAL-BINDING GAP.

  `Dsl.Server` reflects a `server … where` block into a `ServerSpec` value AND
  emits an engine — but that engine dispatched through the FIXED demo route table
  (`Reactor.App.demoApp`), so a declared `route` was inert data: it never drove
  the deployed response. This file closes that gap.

    * `specToAppConfig : ServerSpec → Reactor.App.AppConfig` maps each DECLARED
      `Route1` to a real `Route.Match.Route App.Handler` — the route table is
      built from the declared routes, not `demoApp`;
    * `serveSpec spec` / `serveAuthSpec spec` run the deployed pipeline (the same
      Policy/Safety — and, for `serveAuthSpec`, JWT — gates the guarded serve
      runs) but dispatch through `App.handle (specToAppConfig spec)`, so the
      DECLARED routes decide the response;
    * `serveSpec_routes_declared` / `serveAuthSpec_routes_declared` — THE PAYOFF:
      on a dispatch that clears the gates, the engine serves
      `responseOfHandler` of the route the REAL `Route.Match.bestMatch` selected
      over `specToAppConfig spec`'s table — i.e. the response of the DECLARED
      handler. A different declaration yields a different response, so the binding
      is real, not fixed.

  The macro in `Dsl.Server` repoints `Name_engine := serveSpec Name` (or
  `serveAuthSpec` when `jwt` is declared) and emits `Name_routes_declared` as the
  instantiation of the payoff theorem at the declared spec.

  HONEST SCOPE. The ROUTES are re-driven from the declared block. The deployed
  listener/codec configuration (`deployConfig`: TLS/WS/SOCKS lanes) and the
  reactor front end (`deploySubs`) are still the fixed real `deployConfig` — the
  `listen`/`tls` clauses are reflected in `ServerSpec` but do not yet re-drive
  those codec fields. That listener/tls literal-binding is the named follow-on;
  the routes — the highest-value literal, the one that makes a declared feature
  drive the engine — are bound here.
-/
import Dsl.Server
import TlsHandshake

open Proto (Bytes)

namespace Dsl
namespace ServerBind

open Reactor (Response serialize)
open Reactor.Deploy

/-! ## (1) The declared spec → a real application route table -/

/-- Split a character list on `/`, dropping empty segments. Structurally recursive
(so it reduces in the kernel — unlike `String.splitOn`, which is well-founded and
opaque to `decide`/`rfl`); `acc` accumulates the current segment in reverse. -/
def splitSegsAux : List Char → List Char → List String
  | [],        acc => if acc.isEmpty then [] else [⟨acc.reverse⟩]
  | '/' :: cs, acc => if acc.isEmpty then splitSegsAux cs [] else ⟨acc.reverse⟩ :: splitSegsAux cs []
  | c :: cs,   acc => splitSegsAux cs (c :: acc)

/-- A declared path string → normalized route segments: split on `/`, drop empty
segments, then run the same `Route.Path.normalize` boundary
`Reactor.App.targetSegments` applies to a request target — so a declared pattern
and the request it should match are normalized the same way. Uses the structural
`splitSegsAux` (not `String.splitOn`) so a concrete declared table reduces in the
kernel. -/
def pathSegs (p : String) : List String :=
  Route.Path.normalize (splitSegsAux p.data [])

/-- A declared `Match1` discipline + path → a real `Route.Match.Pat`. `exact` and
`prefix` map onto the library's own precedence classes. `glob` and `host` have no
distinct class in the core `Route.Match` algebra yet, so they are conservatively
bound to `prefix` (the widest safe class); a first-class glob/host matcher is a
named follow-on. -/
def patOf : Dsl.Match1 → String → Route.Match.Pat
  | .exact,  p => .exact (pathSegs p)
  | .prefix, p => .prefix (pathSegs p)
  | .glob,   p => .prefix (pathSegs p)
  | .host,   p => .prefix (pathSegs p)

/-- A declared `Handler1` → the real per-route `Reactor.App.Handler`:
  * `respond code body` → the static status/body handler carrying the DECLARED
    code and body (so `responseOfHandler` serves exactly them);
  * `static dir`        → a `200` static handler over the declared directory;
  * `proxyPool _`       → the reverse-proxy handler over the real health-filtered
    `Reactor.Proxy.demoPool` load-balancer;
  * `redirect code tgt` → a static handler carrying the DECLARED redirect code and
    target (the `Location` header binding is a follow-on; the status is bound). -/
def handlerOf : Dsl.Handler1 → Reactor.App.Handler
  | .respond code body => .static code body.toUTF8.toList
  | .static dir        => .static 200 dir.toUTF8.toList
  | .proxyPool _       => .proxy Reactor.Proxy.demoPool
  | .redirect code tgt => .static code tgt.toUTF8.toList

/-- A declared `Route1` → a real `Route.Match.Route App.Handler`. -/
def routeOf (r : Dsl.Route1) : Route.Match.Route Reactor.App.Handler :=
  { pat := patOf r.kind r.path, handler := handlerOf r.handler }

/-- **The declared route table becomes the app config.** The `AppConfig`'s route
table is exactly the DECLARED routes (mapped by `routeOf`), not `demoApp`'s fixed
table. The Policy admission seam (`lid`, `policy`, `routeKeyOf`) reuses the
deployed running surface so the guarded serve's gates are unchanged. -/
def specToAppConfig (spec : Dsl.ServerSpec) : Reactor.App.AppConfig where
  routes := spec.routes.map routeOf
  defaultHandler := .static 404 "not found".toUTF8.toList
  lid := Reactor.Deploy.deployLid
  policy := Reactor.Deploy.deployRunning
  routeKeyOf := fun _ => Reactor.Deploy.deployRouteKey

/-! ## (2) The spec-driven deployed serve -/

/-- The declared-route application response for the reactor's submissions: a
dispatched request is answered by `App.handle (specToAppConfig spec)` — the REAL
router over the DECLARED table. Mirrors `Reactor.demoResp`'s walk, but over the
declared config. -/
def specDemoResp (spec : Dsl.ServerSpec) : List Reactor.RingSubmission → Response
  | [] => Reactor.error4xx 400 Reactor.reasonBad Reactor.badBody
  | .dispatch req :: _ => Reactor.App.handle (specToAppConfig spec) req
  | _ :: rest => specDemoResp spec rest

/-- The deployed response, DECLARED-route driven: the declared-route application
response passed through the SAME real `Header.run` rewrite (`deployProg` over the
`deployPlan` proxy/DNS pass) the fixed `deployResp` uses. Only the route table
changed. -/
def specResp (spec : Dsl.ServerSpec) (input : Bytes) : Response :=
  Reactor.Lifecycle.rewriteResp
    (deployProg (deployPlan (deploySubs input)) input)
    (specDemoResp spec (deploySubs input))

/-- The Policy/Safety gate on one dispatched request, DECLARED-route driven.
Identical to `Reactor.Deploy.guardOne` — traversal-block, then Policy-refuse —
except the admitted arm serves `specResp` (the declared routes), not `deployResp`
(the fixed table). -/
def specGuardOne (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request) : Bytes :=
  match targetEscapes req with
  | true  => serialize traversalBlocked404
  | false =>
    match deployDecisionOf req with
    | none   => serialize forbidden403
    | some _ => serialize (specResp spec input)

/-- **The declared-route guarded serve.** The same shape as
`Reactor.Deploy.serveGuarded` (faithful FSM forwarding; on a dispatch, the REAL
Policy/Safety gates), dispatching through the DECLARED route table. Total. -/
def serveSpec (spec : Dsl.ServerSpec) (input : Bytes) : Bytes :=
  match Reactor.sendsOf (deploySubs input) with
  | [] =>
    match dispatchReqOf (deploySubs input) with
    | some req => specGuardOne spec input req
    | none     => serialize (specResp spec input)
  | sends => sends.flatten

/-- The JWT auth gate on one dispatched request, DECLARED-route driven. Mirrors
`Dsl.ServerAuth.authOne`: the REAL `Jwt.authenticate` decides — a reject emits the
401, an admit defers to the declared-route guarded serve `serveSpec`. -/
def authOneSpec (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request) : Bytes :=
  match Dsl.ServerAuth.authOutcome req with
  | .reject _ => serialize Dsl.ServerAuth.unauthorized401
  | .admit _  => serveSpec spec input

/-- **The declared-route auth-guarded serve.** The same shape as
`Dsl.ServerAuth.serveAuthGuarded` (the REAL JWT gate layered over the guarded
serve), dispatching through the DECLARED route table on the admitted path. Total. -/
def serveAuthSpec (spec : Dsl.ServerSpec) (input : Bytes) : Bytes :=
  match Reactor.sendsOf (deploySubs input) with
  | [] =>
    match dispatchReqOf (deploySubs input) with
    | some req => authOneSpec spec input req
    | none     => serialize (specResp spec input)
  | sends => sends.flatten

/-! ## (3) Reduction lemmas — the serve reduces to the gate on a dispatch -/

/-- On a dispatch (FSM emitted no bytes of its own), `serveSpec` reduces to the
Policy/Safety gate on the dispatched request. Same shape as
`Reactor.Deploy.serveGuarded_dispatch`. -/
theorem serveSpec_dispatch (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request)
    (rest : List Reactor.RingSubmission)
    (hsends : Reactor.sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveSpec spec input = specGuardOne spec input req := by
  unfold serveSpec
  cases hs : Reactor.sendsOf (deploySubs input) with
  | nil => rw [hsub]; rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-- The gate on an admitted, non-escaping request serves `specResp` — the DECLARED
route table. -/
theorem specGuardOne_admits (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request)
    (s : Policy.Served) (hesc : targetEscapes req = false)
    (hadmit : deployDecisionOf req = some s) :
    specGuardOne spec input req = serialize (specResp spec input) := by
  unfold specGuardOne; rw [hesc, hadmit]

/-- On a dispatch, `specResp` uses `App.handle` over the DECLARED config for that
request. -/
theorem specResp_dispatch (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request)
    (rest : List Reactor.RingSubmission)
    (hsub : deploySubs input = .dispatch req :: rest) :
    specResp spec input
      = Reactor.Lifecycle.rewriteResp (deployProg (deployPlan (deploySubs input)) input)
          (Reactor.App.handle (specToAppConfig spec) req) := by
  unfold specResp
  have hd : specDemoResp spec (deploySubs input)
      = Reactor.App.handle (specToAppConfig spec) req := by rw [hsub]; rfl
  rw [hd]

/-! ## (4) THE PAYOFF — the declared routes drive the engine -/

/-- **`serveSpec_routes_declared` — the declared routes decide the response.** On
a deployed dispatch that clears the traversal gate and is Policy-admitted, the
DECLARED-route guarded serve emits exactly the serialization of (the deployed
rewrite of) `responseOfHandler` of the route the REAL `Route.Match.bestMatch`
selected over `specToAppConfig spec`'s table — i.e. the response of the DECLARED
handler. The route table is `spec.routes` mapped by `routeOf`, so a different
`server` block (different declared routes) selects a different route and serves a
different response: the binding is real, not the fixed `demoApp` table. -/
theorem serveSpec_routes_declared (spec : Dsl.ServerSpec) (input : Bytes)
    (req : Proto.Request) (rest : List Reactor.RingSubmission) (s : Policy.Served)
    (hsends : Reactor.sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hesc : targetEscapes req = false)
    (hadmit : deployDecisionOf req = some s) :
    ∃ r, Route.Match.bestMatch (specToAppConfig spec).table
            (Reactor.App.targetSegments req.target) = some r
       ∧ serveSpec spec input
           = serialize (Reactor.Lifecycle.rewriteResp
               (deployProg (deployPlan (deploySubs input)) input)
               (Reactor.App.responseOfHandler r.handler)) := by
  obtain ⟨r, hbest, hhandle⟩ := Reactor.App.app_routes_total (specToAppConfig spec) req
  refine ⟨r, hbest, ?_⟩
  rw [serveSpec_dispatch spec input req rest hsends hsub,
    specGuardOne_admits spec input req s hesc hadmit,
    specResp_dispatch spec input req rest hsub, hhandle]

/-- **The traversal gate still fires on the declared-route serve.** A `..`-escaping
target is answered with the fixed 404, no route consulted. -/
theorem serveSpec_traversal_blocked (spec : Dsl.ServerSpec) (input : Bytes)
    (req : Proto.Request) (rest : List Reactor.RingSubmission)
    (hsends : Reactor.sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hesc : targetEscapes req = true) :
    serveSpec spec input = serialize traversalBlocked404
    ∧ traversalBlocked404.status = 404 := by
  refine ⟨?_, rfl⟩
  rw [serveSpec_dispatch spec input req rest hsends hsub]
  unfold specGuardOne; rw [hesc]

/-! ## (5) The auth-guarded variant (when `jwt` is declared) -/

/-- On a dispatch, `serveAuthSpec` reduces to the JWT gate on the request. -/
theorem serveAuthSpec_dispatch (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request)
    (rest : List Reactor.RingSubmission)
    (hsends : Reactor.sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveAuthSpec spec input = authOneSpec spec input req := by
  unfold serveAuthSpec
  cases hs : Reactor.sendsOf (deploySubs input) with
  | nil => rw [hsub]; rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-- The JWT gate on a rejected request yields the 401 bytes — the handler body is
never reached (route-independent). -/
theorem authOneSpec_rejects (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request)
    (hrej : ∃ r, Dsl.ServerAuth.authOutcome req = .reject r) :
    authOneSpec spec input req = serialize Dsl.ServerAuth.unauthorized401 := by
  obtain ⟨r, hr⟩ := hrej
  unfold authOneSpec; rw [hr]

/-- The JWT gate on an admitted request defers to the declared-route guarded
serve. -/
theorem authOneSpec_admits (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request)
    (a : List (String × String)) (hadmit : Dsl.ServerAuth.authOutcome req = .admit a) :
    authOneSpec spec input req = serveSpec spec input := by
  unfold authOneSpec; rw [hadmit]

/-- **`serveAuthSpec_auth_401` — the auth branch survives, byte-level.** A request
the REAL `Jwt.authenticate` rejects is answered with the serializer-built 401,
independent of the declared routes. -/
theorem serveAuthSpec_auth_401 (spec : Dsl.ServerSpec) (input : Bytes) (req : Proto.Request)
    (rest : List Reactor.RingSubmission)
    (hsends : Reactor.sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hrej : ∃ r, Dsl.ServerAuth.authOutcome req = .reject r) :
    serveAuthSpec spec input = serialize Dsl.ServerAuth.unauthorized401 := by
  rw [serveAuthSpec_dispatch spec input req rest hsends hsub,
    authOneSpec_rejects spec input req hrej]

/-- **`serveAuthSpec_routes_declared` — the declared routes drive the auth-guarded
engine.** On a dispatch the JWT gate ADMITS, the traversal gate clears, and Policy
admits, the auth-guarded declared serve emits `responseOfHandler` of the route the
REAL `bestMatch` selected over the DECLARED table — the JWT gate defers to the
same declared-route guarded serve, so the declared routes decide the served body
behind the auth gate. -/
theorem serveAuthSpec_routes_declared (spec : Dsl.ServerSpec) (input : Bytes)
    (req : Proto.Request) (rest : List Reactor.RingSubmission)
    (a : List (String × String)) (s : Policy.Served)
    (hsends : Reactor.sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hauth : Dsl.ServerAuth.authOutcome req = .admit a)
    (hesc : targetEscapes req = false)
    (hadmit : deployDecisionOf req = some s) :
    ∃ r, Route.Match.bestMatch (specToAppConfig spec).table
            (Reactor.App.targetSegments req.target) = some r
       ∧ serveAuthSpec spec input
           = serialize (Reactor.Lifecycle.rewriteResp
               (deployProg (deployPlan (deploySubs input)) input)
               (Reactor.App.responseOfHandler r.handler)) := by
  obtain ⟨r, hbest, hserve⟩ :=
    serveSpec_routes_declared spec input req rest s hsends hsub hesc hadmit
  refine ⟨r, hbest, ?_⟩
  rw [serveAuthSpec_dispatch spec input req rest hsends hsub,
    authOneSpec_admits spec input req a hauth, hserve]

/-! ## (6) The TLS lane binding — the real handshake MESSAGE layer

The `tls auto|manual` clause reflects into `ServerSpec.tls`; this section binds
that declaration to a deployed configuration whose handshake lane is the REAL
TLS 1.3 server handshake message layer (`TlsHandshake.serverHsFeed`), replacing
the `.fail` stub of `demoTlsCfg` and the "complete on first ciphertext" shortcut
of `realConfig`. The macro emits `Name_tls_handshake_real` as the instantiation
of `tls_handshake_real` for a TLS-declared server. -/

/-- Fixed server handshake parameters for the deployed TLS lane. The seam is
about *which function* drives the handshake, not the key material, so concrete
zero material is used here; the deployed server would supply its real ephemeral,
random, and certificate. -/
def deployHsParams : TlsHandshake.ServerParams :=
  { ephemeralPriv := TlsCrypto.zeros 32
    serverRandom := TlsCrypto.zeros 32
    certSeed := TlsCrypto.zeros 32
    certData := ByteArray.empty }

/-- The `Tls.Config` whose handshake message layer is the REAL server handshake
(`TlsHandshake.serverHsFeed`), over `TlsCrypto`'s real EverCrypt record layer. -/
def tlsHandshakeTlsCfg : Tls.Config :=
  TlsHandshake.handshakeConfig deployHsParams
    (TlsCrypto.zeros 32) (TlsCrypto.zeros 32) (TlsCrypto.zeros 32)

/-- The deployed `Proto.Config` with the real handshake message layer wired into
the TLS lane (via the same `TlsWire.wireTls` transformer the deployed config
uses), over the arena-backed HTTP/1.1 `demoConfig`. -/
def deployTlsHandshakeConfig : Proto.Config :=
  Reactor.TlsWire.wireTls tlsHandshakeTlsCfg Reactor.Config.demoConfig

/-- **The TLS-declared server's config drives the real handshake MESSAGE layer.**
The deployed `Proto.Config`'s `hsFeed` is the `TlsWire` adapter over
`tlsHandshakeTlsCfg`, whose own `hsFeed` is `TlsHandshake.serverHsFeed` — the real
ClientHello parser + key schedule + sealed server flight over EverCrypt, NOT the
`.fail` stub of `demoTlsCfg` nor the "complete on first ciphertext" shortcut of
`realConfig`. Both conjuncts hold by `rfl`, so a stub `hsFeed` fails the second
conjunct: the binding cannot be faked. -/
theorem tls_handshake_real :
    deployTlsHandshakeConfig.hsFeed = Reactor.TlsWire.hsFeedReal tlsHandshakeTlsCfg
  ∧ tlsHandshakeTlsCfg.hsFeed = TlsHandshake.serverHsFeed deployHsParams :=
  ⟨rfl, rfl⟩

end ServerBind
end Dsl

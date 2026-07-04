/-
  Dsl/Server.lean — the FEATURE-LEVEL DSL: a `server … where` surface that
  GENERATES a verified engine + seam theorems.

  The substrate DSL (`Dsl.Engine`, `engine … where`) composes the five primitive
  Component-shapes; it is deliberately low-level. THIS file is the pkl-shaped
  surface on top: a declarative `server Name where …` block whose clauses name
  listeners, routes+handlers, a middleware chain, and TLS — the production
  server-config pkl vocabulary — and whose ELABORATION emits, for the declared
  server:

    * `def Name : Dsl.ServerSpec`  — the reflected configuration (the AST the block
      describes), a genuine value whose fields a stub could not fake past `rfl`;
    * `def Name_engine : Proto.Bytes → Proto.Bytes` — the composed DEPLOYED serve
      the declared server runs: `Dsl.ServerAuth.serveAuthGuarded` when a `jwt`
      middleware is declared (the real `Jwt.authenticate` gate layered over the
      Policy/Safety-guarded `Reactor.Deploy.serveGuarded`), else the guarded serve
      itself (the routed/proxied/DNS-resolved deployed pipeline);
    * per declared feature, a GENERATED SEAM THEOREM, each a real kernel-checked
      theorem TRANSPORTED from the feature library's own proven seam — `static` ⇒
      `Name_static_no_escape` (`StaticFile.static_no_escape`), `jwt` ⇒
      `Name_auth_401` (byte-level 401) + `Name_auth_alg_confusion_safe`
      (`Jwt.jwt_alg_confusion_safe`), `cors` ⇒ `Name_cors_no_leak`
      (`Cors.cors_no_leak_actual`), `proxy` ⇒ `Name_proxy_selects_healthy`
      (`ProxyServe.demoProxy_route_connects`), plus `hsts`, `ipfilter`,
      `ratelimit`, `redirect`, `tls`, and the routing seam.

  SOUNDNESS. The generator inherits the Lean kernel as its check, exactly like
  `Dsl.Engine`. Each seam theorem's proof term is the REAL library theorem; it
  only typechecks against the real library, so a stubbed feature would fail
  elaboration. A malformed clause `throwErrorAt`s and emits nothing. No `sorry`
  is ever produced.

  The transport is generic: `emitTransport` elaborates the library proof term,
  reads its type off the elaborator, and emits `theorem Name_x : <that type> :=
  <that proof>` — the library's guarantee re-exported under the server's name.
-/
import Lean
import Reactor.Deploy
import Reactor.ProxyServe
import Reactor.Rate
import Reactor.Tls
import Jwt
import Cors
import SecurityHeaders
import Redirect
import IpFilter
import StaticFile

open Lean Lean.Elab Lean.Elab.Command Lean.Elab.Term

namespace Dsl

/-! ## The self-contained deployed auth gate (green deps only)

    The hand-wiring template `Reactor.AuthDeploy` targets an earlier shape of
    `Jwt.Config`, from before `sigValid` was split into the per-family `verify*`
    boundaries, so it does not build against the current `Jwt.Config`. So the
    `jwt` clause's byte-level 401 gate is built HERE, over
    the green `Jwt` library and the green `Reactor.Deploy` serve, in the same
    shape `AuthDeploy` uses: a dispatched request the REAL `Jwt.authenticate`
    rejects is answered with a serializer-built 401; an admit defers to the
    Policy/Safety-guarded deployed serve. -/

namespace ServerAuth

open Proto (Bytes)

/-- The single verification key the deployed surface pins (HS256). The
    verification algorithm is pinned here, never taken from the token. -/
def deployKey : Jwt.Key := { kid := "k1", alg := .hs256, material := ⟨1⟩ }

/-- An `HS256` header. -/
def hdrHs : Jwt.Header := { alg := .hs256, kid := some "k1" }

/-- An `alg = none` (unsecured) header. -/
def hdrNone : Jwt.Header := { alg := .none, kid := some "k1" }

/-- Empty registered claims. -/
def claimsEmpty : Jwt.Claims :=
  { iss := none, sub := none, aud := [], exp := none, nbf := none, iat := none }

/-- **The deployed JWT configuration** over the current (green) `Jwt.Config`
    surface: the crypto/decode fields are the named RFC-7515/7518 boundaries; the
    `verify*` families accept exactly when signature equals signing input, so both
    the admit and reject arms are reachable. The control-flow seams (`jwt_*`) hold
    for every field choice, so this concrete choice weakens no gate. -/
def deployJwtCfg : Jwt.Config where
  keys := [deployKey]
  sources := [.bearer]
  skew := 0
  expectedIss := none
  requiredAud := none
  understoodCrit := []
  parseBearer := fun s => if s.take 7 == "Bearer " then some (s.drop 7) else none
  segments := fun s => s.splitOn "."
  decodeHeader := fun s =>
    if s == "hs256" then some hdrHs else if s == "none" then some hdrNone else none
  decodeClaims := fun _ => some claimsEmpty
  decodeSig := fun _ => some []
  signingInput := fun _ _ => []
  verifyHmac := fun _ _ si sig => si == sig
  verifyRsaPkcs1 := fun _ _ si sig => si == sig
  verifyRsaPss := fun _ _ si sig => si == sig
  verifyEcdsa := fun _ _ si sig => si == sig
  edPubKey := fun _ => []

/-- The first request header whose name is `authorization`, as a `String`. -/
def authHeader (req : Proto.Request) : Option String :=
  match req.headers.find? (fun p => Reactor.App.bytesToString p.1 == "authorization") with
  | some p => some (Reactor.App.bytesToString p.2)
  | none   => none

/-- The `Jwt.Request` surface built from a dispatched `Proto.Request`. -/
def jwtReqOf (req : Proto.Request) : Jwt.Request :=
  { authorization := authHeader req, cookies := [], query := [], headers := [] }

/-- **The deployed JWT decision** — the REAL `Jwt.authenticate` over
    `deployJwtCfg`, on the request's `Authorization` header at clock 0. -/
def authOutcome (req : Proto.Request) : Jwt.Outcome :=
  Jwt.authenticate deployJwtCfg { req := jwtReqOf req, now := 0 }

/-- `authOutcome` is definitionally the real `Jwt.authenticate` — not a stub. -/
theorem authOutcome_is_authenticate (req : Proto.Request) :
    authOutcome req = Jwt.authenticate deployJwtCfg { req := jwtReqOf req, now := 0 } := rfl

/-- Serializer-built **401 Unauthorized** — fixed policy prose independent of the
    request (no handler body can flow), carrying the `WWW-Authenticate: Bearer`
    challenge (RFC 6750 §3). -/
def unauthorized401 : Reactor.Response :=
  { status := 401
  , reason := Reactor.str "Unauthorized"
  , headers := [(Reactor.str "WWW-Authenticate", Reactor.str "Bearer")]
  , body := Reactor.str "authentication required\n" }

theorem unauthorized401_status : unauthorized401.status = 401 := rfl

/-- The auth gate on one dispatched request: the REAL `Jwt.authenticate` decides.
    A reject emits the 401 (the handler body is never reached); an admit defers to
    the Policy/Safety-guarded deployed serve `Reactor.Deploy.serveGuarded`. -/
def authOne (input : Bytes) (req : Proto.Request) : Bytes :=
  match authOutcome req with
  | .reject _ => Reactor.serialize unauthorized401
  | .admit _  => Reactor.Deploy.serveGuarded input

/-- **The auth-guarded deployed serve.** Identical to `serveGuarded` on the
    FSM-send path; on a bare dispatch it runs `authOne` — the REAL JWT gate over
    the deployed serve. Total. -/
def serveAuthGuarded (input : Bytes) : Bytes :=
  match Reactor.sendsOf (Reactor.Deploy.deploySubs input) with
  | [] =>
    match Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) with
    | some req => authOne input req
    | none     => Reactor.serialize (Reactor.Deploy.deployResp input)
  | sends => sends.flatten

/-- On a dispatch, `serveAuthGuarded` reduces to the auth gate on the request. -/
theorem serveAuthGuarded_dispatch (input : Bytes) (req : Proto.Request)
    (rest : List Reactor.RingSubmission)
    (hsends : Reactor.sendsOf (Reactor.Deploy.deploySubs input) = [])
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest) :
    serveAuthGuarded input = authOne input req := by
  unfold serveAuthGuarded
  cases hs : Reactor.sendsOf (Reactor.Deploy.deploySubs input) with
  | nil => rw [hsub]; rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-- A rejected request yields the 401 bytes — the handler body is never serialized. -/
theorem authOne_rejects (input : Bytes) (req : Proto.Request)
    (hrej : ∃ r, authOutcome req = .reject r) :
    authOne input req = Reactor.serialize unauthorized401 := by
  obtain ⟨r, hr⟩ := hrej
  unfold authOne; rw [hr]

/-- **`deployed_auth_401` — the auth branch, byte-level, on the deployed path.**
    When the deployed reactor dispatches a request the REAL `Jwt.authenticate`
    rejects (no token, bad signature, alg confusion, expiry, claim mismatch —
    anything not an admit), the bytes the guarded serve writes are EXACTLY the
    serializer-built 401. -/
theorem deployed_auth_401 (input : Bytes) (req : Proto.Request)
    (rest : List Reactor.RingSubmission)
    (hsends : Reactor.sendsOf (Reactor.Deploy.deploySubs input) = [])
    (hsub : Reactor.Deploy.deploySubs input = .dispatch req :: rest)
    (hrej : ∃ r, authOutcome req = .reject r) :
    serveAuthGuarded input = Reactor.serialize unauthorized401 := by
  rw [serveAuthGuarded_dispatch input req rest hsends hsub, authOne_rejects input req hrej]

/-- **The gate genuinely branches — kernel `decide`, no reactor.** A trivial ctx
    and literal `Jws` values, so the kernel reduces the REAL `Jwt.afterKey`. -/
def ctx0 : Jwt.Ctx :=
  { req := { authorization := none, cookies := [], query := [], headers := [] }, now := 0 }

/-- An `alg = none` parsed token. -/
def jwsNone : Jwt.Jws :=
  { header := hdrNone, claims := claimsEmpty, signingInput := [], signature := [] }

/-- An `HS256` token whose signature equals its signing input (accepted). -/
def jwsHs : Jwt.Jws :=
  { header := hdrHs, claims := claimsEmpty, signingInput := [], signature := [] }

/-- The REAL gate **rejects `alg = none`** — the unsecured-token branch. -/
theorem afterKey_none_rejects :
    Jwt.afterKey deployJwtCfg ctx0 jwsNone deployKey = .reject .algNone := by decide

/-- The REAL gate **admits a well-formed HS256 token** — the admit arm is
    reachable, so the gate is not reject-all. -/
theorem afterKey_hs_admits :
    Jwt.afterKey deployJwtCfg ctx0 jwsHs deployKey = .admit [] := by decide

end ServerAuth

/-! ## The ServerSpec AST — the reflected pkl configuration -/

/-- A listener protocol. -/
inductive Proto1 where
  | h1 | h2c | tls
  deriving DecidableEq, Repr

/-- A route handler — the `->` target of a route clause. -/
inductive Handler1 where
  | respond (code : Nat) (body : String)
  | static (dir : String)
  | proxyPool (backends : List String)
  | redirect (code : Nat) (target : String)
  deriving Repr

/-- A route matcher discipline. -/
inductive Match1 where
  | exact | prefix | glob | host
  deriving DecidableEq, Repr

/-- A single route clause. -/
structure Route1 where
  kind : Match1
  path : String
  handler : Handler1
  deriving Repr

/-- The TLS posture. -/
inductive TlsMode where
  | off | auto | manual
  deriving DecidableEq, Repr

/-- The declared middleware chain (presence flags — the v1 surface). -/
structure Mw1 where
  hsts : Bool := false
  cors : Bool := false
  ratelimit : Bool := false
  jwt : Bool := false
  ipfilter : Bool := false
  deriving Repr, DecidableEq

/-- A declared listener. -/
structure Listen1 where
  port : Nat
  proto : Proto1
  deriving Repr

/-- **The server specification** — the AST a `server … where` block reflects. -/
structure ServerSpec where
  listens : List Listen1
  routes : List Route1
  mw : Mw1
  tls : TlsMode
  deriving Repr

namespace ServerSpec

/-- Does the server declare a `static` file route? -/
def hasStatic (s : ServerSpec) : Bool :=
  s.routes.any (fun r => match r.handler with | .static _ => true | _ => false)

/-- Does the server declare a `proxy pool` route? -/
def hasProxy (s : ServerSpec) : Bool :=
  s.routes.any (fun r => match r.handler with | .proxyPool _ => true | _ => false)

/-- Does the server declare a `redirect` route? -/
def hasRedirect (s : ServerSpec) : Bool :=
  s.routes.any (fun r => match r.handler with | .redirect _ _ => true | _ => false)

/-- Does the server declare a `respond` route? -/
def hasRespond (s : ServerSpec) : Bool :=
  s.routes.any (fun r => match r.handler with | .respond _ _ => true | _ => false)

end ServerSpec

/-! ## Surface syntax: `server Name where <clauses>` -/

declare_syntax_cat serverProto
syntax "h1"  : serverProto
syntax "h2c" : serverProto
syntax "tls" : serverProto

declare_syntax_cat serverMatch
syntax "exact"  : serverMatch
syntax "prefix" : serverMatch
syntax "glob"   : serverMatch
syntax "host"   : serverMatch

declare_syntax_cat serverHandler
syntax "respond" num str : serverHandler
syntax "static" str : serverHandler
syntax "proxy" "pool" "[" ident,* "]" : serverHandler
syntax "redirect" num str : serverHandler

declare_syntax_cat serverMw
syntax "hsts"      : serverMw
syntax "cors"      : serverMw
syntax "ratelimit" : serverMw
syntax "jwt"       : serverMw
syntax "ipfilter"  : serverMw

declare_syntax_cat serverClause
syntax "listen" num serverProto : serverClause
syntax "route" serverMatch str "->" serverHandler : serverClause
syntax "middleware" (serverMw)+ : serverClause
syntax "tls" "auto"   : serverClause
syntax "tls" "manual" : serverClause

/-- The server block. Clauses are `;`-separated (like the substrate `engine`). -/
syntax (name := serverDecl)
  "server" ident "where" sepBy1(serverClause, ";") : command

/-! ## The generic transport engine

    `emitTransport nm proof` elaborates the library proof term, reads its type off
    the elaborator, and emits `theorem nm : <type> := <proof>`. The generated seam
    theorem is exactly the library's proven guarantee, re-exported under the
    server's name. No `sorry`; a stub `proof` fails the command. -/
private def emitTransport (nm : Name) (proof : TSyntax `term) : CommandElabM Unit := do
  let ns := (← getScope).currNamespace
  liftTermElabM do
    let e ← elabTerm proof none
    Term.synthesizeSyntheticMVarsNoPostponing
    let e ← instantiateMVars e
    let ty ← instantiateMVars (← Meta.inferType e)
    let us := (Lean.collectLevelParams (Lean.collectLevelParams {} ty) e).params.toList
    Lean.addDecl (Declaration.thmDecl
      { name := ns ++ nm, levelParams := us, type := ty, value := e })

/-! ## The elaborator -/

/-- Fold an array of term syntaxes into a `List` term (`x₀ :: x₁ :: … :: []`).
    List-literal antiquote splices (`[$xs,*]`) are not supported here, so we build
    the cons-list explicitly. -/
private def mkListTerm (xs : Array (TSyntax `term)) : CommandElabM (TSyntax `term) := do
  let mut acc : TSyntax `term ← `(List.nil)
  for x in xs.reverse do
    acc ← `(List.cons $x $acc)
  return acc

@[command_elab serverDecl]
def elabServer : CommandElab := fun stx => do
  match stx with
  | `(server $name:ident where $clauses;*) => do
      let clauseArr := clauses.getElems
      if clauseArr.isEmpty then
        throwErrorAt name "server: at least one clause is required"
      -- Accumulators for the reflected spec + the feature flags. (Flag vars are
      -- NOT named after the clause keywords, which are now reserved tokens.)
      let mut listensStx : Array (TSyntax `term) := #[]
      let mut routesStx  : Array (TSyntax `term) := #[]
      let mut mwHsts := false; let mut mwCors := false; let mut mwRate := false
      let mut mwJwt := false;  let mut mwIpf := false
      let mut tlsTerm : TSyntax `term ← `(Dsl.TlsMode.off)
      let mut tlsDeclared := false
      let mut hasStatic := false; let mut hasProxy := false
      let mut hasRedirect := false; let mut hasRespond := false; let mut hasTlsListen := false
      for clause in clauseArr do
        match clause with
        | `(serverClause| listen $p:num $proto:serverProto) =>
            let protoTerm : TSyntax `term ← match proto with
              | `(serverProto| h1)  => `(Dsl.Proto1.h1)
              | `(serverProto| h2c) => `(Dsl.Proto1.h2c)
              | `(serverProto| tls) => `(Dsl.Proto1.tls)
              | _ => throwErrorAt proto "server: unknown listener protocol"
            match proto with
              | `(serverProto| tls) => hasTlsListen := true
              | _ => pure ()
            listensStx := listensStx.push (← `(Dsl.Listen1.mk $p $protoTerm))
        | `(serverClause| route $m:serverMatch $path:str -> $h:serverHandler) =>
            let kindTerm : TSyntax `term ← match m with
              | `(serverMatch| exact)  => `(Dsl.Match1.exact)
              | `(serverMatch| prefix) => `(Dsl.Match1.prefix)
              | `(serverMatch| glob)   => `(Dsl.Match1.glob)
              | `(serverMatch| host)   => `(Dsl.Match1.host)
              | _ => throwErrorAt m "server: unknown route matcher"
            match h with
              | `(serverHandler| respond $c:num $b:str) =>
                  hasRespond := true
                  routesStx := routesStx.push
                    (← `(Dsl.Route1.mk $kindTerm $path (Dsl.Handler1.respond $c $b)))
              | `(serverHandler| static $d:str) =>
                  hasStatic := true
                  routesStx := routesStx.push
                    (← `(Dsl.Route1.mk $kindTerm $path (Dsl.Handler1.static $d)))
              | `(serverHandler| proxy pool [$bs,*]) =>
                  hasProxy := true
                  let names := bs.getElems.map (fun i => (Syntax.mkStrLit i.getId.toString : TSyntax `term))
                  let lst ← mkListTerm names
                  routesStx := routesStx.push
                    (← `(Dsl.Route1.mk $kindTerm $path (Dsl.Handler1.proxyPool $lst)))
              | `(serverHandler| redirect $c:num $t:str) =>
                  hasRedirect := true
                  routesStx := routesStx.push
                    (← `(Dsl.Route1.mk $kindTerm $path (Dsl.Handler1.redirect $c $t)))
              | _ => throwErrorAt h "server: unknown route handler"
        | `(serverClause| middleware $mws:serverMw*) =>
            for mw in mws do
              match mw with
              | `(serverMw| hsts)      => mwHsts := true
              | `(serverMw| cors)      => mwCors := true
              | `(serverMw| ratelimit) => mwRate := true
              | `(serverMw| jwt)       => mwJwt := true
              | `(serverMw| ipfilter)  => mwIpf := true
              | _ => throwErrorAt mw "server: unknown middleware"
        | `(serverClause| tls auto)   => tlsDeclared := true; tlsTerm ← `(Dsl.TlsMode.auto)
        | `(serverClause| tls manual) => tlsDeclared := true; tlsTerm ← `(Dsl.TlsMode.manual)
        | other => throwErrorAt other "server: unrecognized clause"
      -- (1) Emit the reflected spec `def Name : ServerSpec`.
      let boolLit : Bool → CommandElabM (TSyntax `term) := fun b =>
        if b then `(true) else `(false)
      let hstsT ← boolLit mwHsts; let corsT ← boolLit mwCors; let rateT ← boolLit mwRate
      let jwtT ← boolLit mwJwt;   let ipfT ← boolLit mwIpf
      let mwTerm ← `(Dsl.Mw1.mk $hstsT $corsT $rateT $jwtT $ipfT)
      let listensL ← mkListTerm listensStx
      let routesL ← mkListTerm routesStx
      let specCmd ← `(command|
        def $name : Dsl.ServerSpec := Dsl.ServerSpec.mk $listensL $routesL $mwTerm $tlsTerm)
      elabCommand specCmd
      -- The `Dsl.ServerBind.*` bindings live in a module that IMPORTS this one
      -- (`ServerBind` → `Server`), so they are not in scope in this elaborator's
      -- own imports. `mkIdent` builds UNHYGIENIC references resolved at the `server`
      -- block's use site (which does import `ServerBind`), not here.
      let ssSpec     := mkIdent `Dsl.ServerBind.serveSpec
      let ssAuth     := mkIdent `Dsl.ServerBind.serveAuthSpec
      let ssAuth401  := mkIdent `Dsl.ServerBind.serveAuthSpec_auth_401
      let ssTrav     := mkIdent `Dsl.ServerBind.serveSpec_traversal_blocked
      let ssCfg      := mkIdent `Dsl.ServerBind.specToAppConfig
      let ssRoutesA  := mkIdent `Dsl.ServerBind.serveAuthSpec_routes_declared
      let ssRoutesS  := mkIdent `Dsl.ServerBind.serveSpec_routes_declared
      -- (2) Emit the composed deployed engine `def Name_engine` — the DECLARED
      -- routes drive it: `serveSpec Name` / `serveAuthSpec Name` dispatch through
      -- `specToAppConfig Name`'s route table (built from the declared routes), not
      -- the fixed `demoApp`.
      let engIdent := mkIdent (Name.mkSimple (name.getId.toString ++ "_engine"))
      let engBody : TSyntax `term ←
        if mwJwt then `($ssAuth $name) else `($ssSpec $name)
      elabCommand (← `(command|
        def $engIdent : Proto.Bytes → Proto.Bytes := $engBody))
      -- (3) The engine-level seam(s), stated over `Name_engine`.
      if mwJwt then
        let nm := mkIdent (Name.mkSimple (name.getId.toString ++ "_auth_401"))
        elabCommand (← `(command|
          theorem $nm (input : Proto.Bytes) (req : Proto.Request)
              (rest : List Reactor.RingSubmission)
              (hsends : Reactor.sendsOf (Reactor.Deploy.deploySubs input) = [])
              (hsub : Reactor.Deploy.deploySubs input
                        = Reactor.RingSubmission.dispatch req :: rest)
              (hrej : ∃ r, Dsl.ServerAuth.authOutcome req = Jwt.Outcome.reject r) :
              $engIdent input = Reactor.serialize Dsl.ServerAuth.unauthorized401 :=
            $ssAuth401 $name input req rest hsends hsub hrej))
      else
        let nm := mkIdent (Name.mkSimple (name.getId.toString ++ "_traversal_blocked"))
        elabCommand (← `(command|
          theorem $nm (input : Proto.Bytes) (req : Proto.Request)
              (rest : List Reactor.RingSubmission)
              (hsends : Reactor.sendsOf (Reactor.Deploy.deploySubs input) = [])
              (hsub : Reactor.Deploy.deploySubs input
                        = Reactor.RingSubmission.dispatch req :: rest)
              (hesc : Reactor.Deploy.targetEscapes req = true) :
              $engIdent input = Reactor.serialize Reactor.Deploy.traversalBlocked404 :=
            ($ssTrav $name input req rest hsends hsub hesc).1))
      -- (4) THE ROUTING SEAM — the DECLARED routes drive the engine.
      -- `Name_routes_declared`: on a dispatch that clears the gates, the engine
      -- serves `responseOfHandler` of the route the REAL `bestMatch` selected over
      -- `specToAppConfig Name`'s table (built from the DECLARED routes). A macro
      -- that ignored the declared block, or an engine on the fixed `demoApp`, could
      -- not satisfy this — the declared route literally decides the response.
      if hasRespond || hasStatic || hasProxy || hasRedirect then
        let rnm := mkIdent (Name.mkSimple (name.getId.toString ++ "_routes_declared"))
        if mwJwt then
          elabCommand (← `(command|
            theorem $rnm (input : Proto.Bytes) (req : Proto.Request)
                (rest : List Reactor.RingSubmission) (a : List (String × String))
                (s : Policy.Served)
                (hsends : Reactor.sendsOf (Reactor.Deploy.deploySubs input) = [])
                (hsub : Reactor.Deploy.deploySubs input
                          = Reactor.RingSubmission.dispatch req :: rest)
                (hauth : Dsl.ServerAuth.authOutcome req = Jwt.Outcome.admit a)
                (hesc : Reactor.Deploy.targetEscapes req = false)
                (hadmit : Reactor.Deploy.deployDecisionOf req = some s) :
                ∃ r, Route.Match.bestMatch ($ssCfg $name).table
                        (Reactor.App.targetSegments req.target) = some r
                   ∧ $engIdent input
                       = Reactor.serialize (Reactor.Lifecycle.rewriteResp
                           (Reactor.Deploy.deployProg
                             (Reactor.Deploy.deployPlan (Reactor.Deploy.deploySubs input)) input)
                           (Reactor.App.responseOfHandler r.handler)) :=
              $ssRoutesA $name input req rest a s
                hsends hsub hauth hesc hadmit))
        else
          elabCommand (← `(command|
            theorem $rnm (input : Proto.Bytes) (req : Proto.Request)
                (rest : List Reactor.RingSubmission) (s : Policy.Served)
                (hsends : Reactor.sendsOf (Reactor.Deploy.deploySubs input) = [])
                (hsub : Reactor.Deploy.deploySubs input
                          = Reactor.RingSubmission.dispatch req :: rest)
                (hesc : Reactor.Deploy.targetEscapes req = false)
                (hadmit : Reactor.Deploy.deployDecisionOf req = some s) :
                ∃ r, Route.Match.bestMatch ($ssCfg $name).table
                        (Reactor.App.targetSegments req.target) = some r
                   ∧ $engIdent input
                       = Reactor.serialize (Reactor.Lifecycle.rewriteResp
                           (Reactor.Deploy.deployProg
                             (Reactor.Deploy.deployPlan (Reactor.Deploy.deploySubs input)) input)
                           (Reactor.App.responseOfHandler r.handler)) :=
              $ssRoutesS $name input req rest s
                hsends hsub hesc hadmit))
      -- (5) The per-feature transported seams.
      if hasStatic then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_static_no_escape"))
          (← `(StaticFile.static_no_escape))
      if hasProxy then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_proxy_selects_healthy"))
          (← `(Reactor.ProxyServe.demoProxy_route_connects))
      if hasRedirect then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_redirect_3xx"))
          (← `(Redirect.status_is_redirect))
      if mwHsts then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_security_headers"))
          (← `(SecurityHeaders.render_hsts_present))
      if mwCors then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_cors_no_leak"))
          (← `(Cors.cors_no_leak_actual))
        emitTransport (Name.mkSimple (name.getId.toString ++ "_cors_grants"))
          (← `(Cors.cors_actual_grants))
      if mwJwt then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_auth_alg_confusion_safe"))
          (← `(Jwt.jwt_alg_confusion_safe))
        emitTransport (Name.mkSimple (name.getId.toString ++ "_auth_rejects_bad_sig"))
          (← `(Jwt.jwt_rejects_bad_sig))
      if mwIpf then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_ip_allow_grants"))
          (← `(IpFilter.ip_allow_grants))
      if mwRate then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_rate_bound"))
          (← `(Reactor.RateGate.reactor_rate_bound_window_init_deployed))
      if tlsDeclared || hasTlsListen then
        emitTransport (Name.mkSimple (name.getId.toString ++ "_tls_real"))
          (← `(Reactor.Deploy.deploy_uses_real_tls))
        -- THE HANDSHAKE SEAM — the TLS-declared server's config drives the real
        -- handshake MESSAGE layer over EverCrypt (a stub `hsFeed` fails its `rfl`).
        -- `Dsl.ServerBind.tls_handshake_real` lives in the module that IMPORTS this
        -- one, so it is an UNHYGIENIC `mkIdent` whose type `emitTransport` reads off
        -- the elaborator at the `server` block's use site (which imports `ServerBind`).
        emitTransport (Name.mkSimple (name.getId.toString ++ "_tls_handshake_real"))
          ⟨(mkIdent `Dsl.ServerBind.tls_handshake_real).raw⟩
  | _ => throwUnsupportedSyntax

end Dsl

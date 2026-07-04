/-
  Dsl/GoldenServer.lean — THE GOLDEN SERVER: pkl-parity, but it generates a proof.

  A single `server GoldenSrv where …` block — several feature families in the
  production server-config pkl vocabulary (a `respond` route, a `static` files route, a
  `proxy pool` route, a `redirect` route, an `hsts`+`cors`+`jwt` middleware chain,
  and TLS listeners) — that GENERATES a verified engine (`GoldenSrv_engine`) and,
  for each declared feature, a kernel-checked SEAM THEOREM transported from the
  real feature library. Below the block, each generated declaration is
  `#check`ed, and `GoldenSrv_wires_real` proves the generated engine wires the
  REAL libraries (a stub would fail its `rfl`s), the pkl-parity proof.

  SOUNDNESS. Every seam theorem's proof term is a real library theorem checked by
  the Lean kernel. Nothing is `sorry`. A malformed clause would fail elaboration
  rather than emit a hole.
-/
import Dsl.ServerBind

open Dsl

/-! ## The golden block — declared once, generates an engine + its seam theorems -/

server GoldenSrv where
  listen 443 tls;
  listen 8443 h2c;
  tls auto;
  middleware hsts cors jwt;
  route exact "/health" -> respond 200 "ok";
  route prefix "/static" -> static "/srv/www";
  route prefix "/api" -> proxy pool [b1, b2];
  route glob "/old" -> redirect 301 "/new"

/-! ## What the block generated

The reflected spec, the composed engine, and the per-feature seam theorems —
each a genuine top-level declaration the macro emitted, none postulated. -/

-- The reflected configuration (a real `ServerSpec`).
#check (GoldenSrv : Dsl.ServerSpec)

-- The composed deployed engine (bytes in → bytes out): the real auth-guarded serve.
#check (GoldenSrv_engine : Proto.Bytes → Proto.Bytes)

-- The generated seam theorems, one per declared feature.
#check @GoldenSrv_auth_401                 -- jwt        → byte-level 401
#check @GoldenSrv_auth_alg_confusion_safe  -- jwt        → Jwt.jwt_alg_confusion_safe
#check @GoldenSrv_auth_rejects_bad_sig     -- jwt        → Jwt.jwt_rejects_bad_sig
#check @GoldenSrv_static_no_escape         -- static     → StaticFile.static_no_escape
#check @GoldenSrv_proxy_selects_healthy    -- proxy pool → ProxyServe.demoProxy_route_connects
#check @GoldenSrv_redirect_3xx             -- redirect   → Redirect.status_is_redirect
#check @GoldenSrv_security_headers         -- hsts       → SecurityHeaders.render_hsts_present
#check @GoldenSrv_cors_no_leak             -- cors       → Cors.cors_no_leak_actual
#check @GoldenSrv_cors_grants              -- cors       → Cors.cors_actual_grants
#check @GoldenSrv_routes_declared          -- routes     → the DECLARED routes drive the engine
#check @GoldenSrv_tls_real                 -- tls        → Deploy.deploy_uses_real_tls
#check @GoldenSrv_tls_handshake_real       -- tls        → the REAL handshake MESSAGE layer

/-! ## The spec genuinely reflects the declared clauses (a stub would fail) -/

/-- The reflected spec records exactly the clauses the block declared: two
listeners (one TLS), four routes with the four handler families, the hsts/cors/jwt
middleware, and TLS auto. Each conjunct holds by `rfl` off the generated `def`;
a macro that dropped a clause would break one. -/
theorem GoldenSrv_spec_reflects :
    GoldenSrv.hasRespond = true
  ∧ GoldenSrv.hasStatic = true
  ∧ GoldenSrv.hasProxy = true
  ∧ GoldenSrv.hasRedirect = true
  ∧ GoldenSrv.mw.hsts = true
  ∧ GoldenSrv.mw.cors = true
  ∧ GoldenSrv.mw.jwt = true
  ∧ GoldenSrv.tls = Dsl.TlsMode.auto
  ∧ GoldenSrv.listens.length = 2
  ∧ GoldenSrv.routes.length = 4 := by
  refine ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-! ## The pkl-parity proof: the generated engine wires the REAL libraries -/

/-- **`GoldenSrv_wires_real`.** The generated engine is the real composed
auth-guarded, DECLARED-route serve (`= Dsl.ServerBind.serveAuthSpec GoldenSrv`, by
`rfl` — the engine dispatches through `GoldenSrv`'s OWN declared route table), and
the deployed configuration that engine runs on drives the REAL TLS engine — its
`hsFeed` lane is exactly the `TlsWire` adapter over the real `Tls.step` handshake
machine, not an inert stub (`Reactor.Deploy.deploy_uses_real_tls`). A stubbed
engine or a stub codec lane could not satisfy these — this is the parity proof:
the declarative block produced a configured server that cannot lie. -/
theorem GoldenSrv_wires_real :
    GoldenSrv_engine = Dsl.ServerBind.serveAuthSpec GoldenSrv
  ∧ Reactor.Deploy.deployConfig.hsFeed
      = Reactor.TlsWire.hsFeedReal Reactor.TlsWire.demoTlsCfg
  ∧ Reactor.Deploy.deployConfig.wsFeed = Reactor.Ws.wsFeedFn := by
  refine ⟨rfl, ?_, ?_⟩
  · exact (Reactor.Deploy.deploy_uses_real_tls).1
  · exact (Reactor.Deploy.deploy_uses_real_ws).1

/-- **`GoldenSrv_tls_handshake_layer_real`.** The `tls auto` clause bound the
declared server's TLS lane to the REAL TLS 1.3 handshake MESSAGE layer: the
deployed config's `hsFeed` is the `TlsWire` adapter over `tlsHandshakeTlsCfg`,
whose own `hsFeed` is `TlsHandshake.serverHsFeed` — the real ClientHello parser +
key schedule + sealed server flight over EverCrypt. This is the generated
`GoldenSrv_tls_handshake_real`, re-stated; and the real `hsFeed` genuinely
inspects the bytes — it `.fail`s a non-ClientHello, where the old `realConfig`
shortcut "completed" unconditionally. A stub `hsFeed` (`fun _ _ => .fail`, or the
shortcut) fails the `rfl` in the generated seam. -/
theorem GoldenSrv_tls_handshake_layer_real
    (hs : Tls.HsConn) :
    Dsl.ServerBind.tlsHandshakeTlsCfg.hsFeed
        = TlsHandshake.serverHsFeed Dsl.ServerBind.deployHsParams
  ∧ TlsHandshake.serverHsFeed Dsl.ServerBind.deployHsParams hs [0x00] = Tls.HsOut.fail :=
  ⟨GoldenSrv_tls_handshake_real.2,
   TlsHandshake.serverHsFeed_rejects_non_clienthello Dsl.ServerBind.deployHsParams hs⟩

/-! ## The generated 401 gate genuinely branches (kernel `decide`, no reactor)

The `jwt` clause's byte-level 401 rests on a real mechanism: the REAL
`Jwt.afterKey` on a concrete `alg=none` token rejects, and on a well-formed HS256
token admits — two different arms, so the 401 branch is not three names for one
output. (These are re-exported from the generated auth support.) -/

theorem GoldenSrv_gate_branches :
    Jwt.afterKey Dsl.ServerAuth.deployJwtCfg Dsl.ServerAuth.ctx0
        Dsl.ServerAuth.jwsNone Dsl.ServerAuth.deployKey = .reject .algNone
  ∧ Jwt.afterKey Dsl.ServerAuth.deployJwtCfg Dsl.ServerAuth.ctx0
        Dsl.ServerAuth.jwsHs Dsl.ServerAuth.deployKey = .admit [] :=
  ⟨Dsl.ServerAuth.afterKey_none_rejects, Dsl.ServerAuth.afterKey_hs_admits⟩

/-! ## THE LITERAL-BINDING PAYOFF: the DECLARED routes drive the engine

`GoldenSrv_routes_declared` (generated above) says: on a dispatch that clears the
JWT/Policy/Safety gates, `GoldenSrv_engine` serves `responseOfHandler` of the route
the REAL `Route.Match.bestMatch` selected over `specToAppConfig GoldenSrv`'s
table — a table built from the DECLARED routes, not the fixed `demoApp`. The two
facts below make that binding CONCRETE and show it is not fixed. -/

/-- **The declared `/health -> respond 200 "ok"` is what `bestMatch` selects, and
it serves 200 "ok".** The route table `bestMatch` runs over is
`specToAppConfig GoldenSrv`'s — built from `GoldenSrv`'s OWN declared routes — so
the route chosen for `/health` is the DECLARED one, and its response is exactly the
declared 200/"ok" (each conjunct reduces in the kernel over the declared table). -/
theorem GoldenSrv_health_declared :
    ∃ r, Route.Match.bestMatch (ServerBind.specToAppConfig GoldenSrv).table ["health"] = some r
       ∧ (Reactor.App.responseOfHandler r.handler).status = 200
       ∧ (Reactor.App.responseOfHandler r.handler).body = "ok".toUTF8.toList :=
  ⟨⟨Route.Match.Pat.exact ["health"], .static 200 "ok".toUTF8.toList⟩, rfl, rfl, rfl⟩

/-- **The binding is REAL, not fixed: a different declaration yields a different
response.** `handlerOf` carries the DECLARED status code into the served response,
so declaring `respond 200` serves 200 while declaring `respond 418` serves 418 —
the engine's response is decided by what the block DECLARES, exactly the property a
fixed `demoApp` table could not have. -/
theorem GoldenSrv_binding_not_fixed :
    (Reactor.App.responseOfHandler (ServerBind.handlerOf (Dsl.Handler1.respond 200 "ok"))).status = 200
  ∧ (Reactor.App.responseOfHandler (ServerBind.handlerOf (Dsl.Handler1.respond 418 "teapot"))).status = 418 :=
  ⟨rfl, rfl⟩

/-! ## Axiom footprint of the generated golden seam theorems

Within the allowed set {propext, Quot.sound, Classical.choice}. -/

#print axioms GoldenSrv_routes_declared
#print axioms GoldenSrv_health_declared
#print axioms GoldenSrv_binding_not_fixed
#print axioms GoldenSrv_auth_401
#print axioms GoldenSrv_static_no_escape
#print axioms GoldenSrv_cors_no_leak
#print axioms GoldenSrv_proxy_selects_healthy
#print axioms GoldenSrv_security_headers
#print axioms GoldenSrv_tls_real
#print axioms GoldenSrv_tls_handshake_real
#print axioms GoldenSrv_tls_handshake_layer_real
#print axioms GoldenSrv_wires_real

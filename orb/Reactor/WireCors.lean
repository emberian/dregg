import Reactor.MiddlewareDeploy

/-!
# Reactor.WireCors — CORS is already attached to the deployed serve path

The CORS library's security property — **a forbidden origin never receives
`Access-Control-Allow-Origin`** (`Cors.cors_no_leak_actual`) — is already
transported onto the path `Arena.Orb.main` runs, in
`Reactor/MiddlewareDeploy.lean`. This file does not add a second copy; it
`#check`s the existing deployed seams so the attachment is visible from a
`Wire*` file and audits that they rest on the standard axioms only.

Where CORS lands on the deployed path (`Reactor.MiddlewareDeploy`):

* `deployMwHeaders input o` is the REAL `Middleware.run` of the deployed
  response-security chain (`SecurityHeaders` outside, `Cors.actualResponse`
  inside) folded over `baseHeaders input` — the `String` view of the very
  headers `Reactor.Deploy.serveFull` serializes on a dispatch. The tie to the
  bytes `main` writes is `deployed_mw_over_serveFull` (under the dispatch side
  condition `sendsOf (deploySubs input) = []`): `serveFull input =
  serialize (deployResp input)` and `baseHeaders input` is exactly that
  response's headers.

* `deployed_cors_no_leak` — a disallowed origin: the CORS layer collapses to
  `[]`, so the deployed headers are byte-identical to the no-CORS response and
  the CORS decision carries no ACAO (discharged by `Cors.cors_no_leak_actual`).

* `deployed_cors_no_leak_full` — the whole-header statement: for a disallowed
  origin (and a base with no ACAO, true on the deployed path) the entire
  deployed header set has `Cors.hasAcao = false`. This is the target property,
  landed on the deployed response.

* `deployed_cors_grants` — the dual: an allowed origin *does* get ACAO, so the
  gate genuinely branches (not a constant `false`).

The concrete `deployCorsPolicy` witnesses the branch: `origin_denied_evil`
(off-allowlist → refused) and `origin_allowed_app` (on-allowlist → allowed),
both `by decide`.
-/

namespace Reactor
namespace WireCors

open Reactor.MiddlewareDeploy

/-! ## The existing deployed CORS seams, checked from a Wire file -/

-- The library core theorem being transported.
#check @Cors.cors_no_leak_actual

-- A disallowed origin gains nothing on the deployed response.
#check @Reactor.MiddlewareDeploy.deployed_cors_no_leak

-- The whole deployed header set: forbidden origin ⇒ no ACAO anywhere.
#check @Reactor.MiddlewareDeploy.deployed_cors_no_leak_full

-- The gate branches: an allowed origin does receive ACAO.
#check @Reactor.MiddlewareDeploy.deployed_cors_grants

-- The chain runs over the bytes `serveFull` writes on a dispatch.
#check @Reactor.MiddlewareDeploy.deployed_mw_over_serveFull

-- The concrete policy makes the branch real, not vacuous.
#check @Reactor.MiddlewareDeploy.origin_denied_evil
#check @Reactor.MiddlewareDeploy.origin_allowed_app

/-! ## Axiom audit — the deployed CORS seam is closed on the standard axioms -/

#print axioms Reactor.MiddlewareDeploy.deployed_cors_no_leak
#print axioms Reactor.MiddlewareDeploy.deployed_cors_no_leak_full
#print axioms Reactor.MiddlewareDeploy.deployed_cors_grants
#print axioms Reactor.MiddlewareDeploy.deployed_mw_over_serveFull

end WireCors
end Reactor

import Reactor.MiddlewareDeploy
import Reactor.Bridge

/-!
# Reactor.WireSecurityHeaders — SecurityHeaders is already on the deployed path

The `SecurityHeaders` core property (HSTS/CSP/X-Frame-Options present and
well-formed on the response — headline `render_hsts_present`, the emitted set
contains a `Strict-Transport-Security` field) is **already** transported onto the
deployed serve path by `Reactor.MiddlewareDeploy`.

`Reactor.MiddlewareDeploy.deployed_security_headers` states that the deployed
middleware header set (`deployMwHeaders`, the REAL `Middleware.run` onion over the
headers `Deploy.serveFull` serializes — see `deployed_mw_over_serveFull`) carries
`Strict-Transport-Security` with the rendered HSTS value. Its proof is exactly the
library theorem `SecurityHeaders.render_hsts_present` read out of the onion, and
`SecurityHeaders.hsts_wellformed` is landed on the deployed policy as
`hsts_wellformed_deploy`.

This file does not add a new seam — it would duplicate the one above. It only
pins the existing deployed seam by `#check`, so the wiring is recorded and
audited here without a second copy.
-/

namespace Reactor.WireSecurityHeaders

open Reactor.MiddlewareDeploy

-- The deployed SecurityHeaders seam: HSTS is present on the deployed serve path.
#check @deployed_security_headers

-- The library well-formedness landed on the deployed HSTS policy.
#check @hsts_wellformed_deploy

-- The library core property it rests on.
#check @SecurityHeaders.render_hsts_present
#check @SecurityHeaders.hsts_wellformed

/-- Local alias recording that the deployed SecurityHeaders seam is in place:
`Strict-Transport-Security` is present on the headers `serveFull` writes, with the
rendered HSTS value. Definitionally the existing seam — no new content. -/
theorem securityheaders_deployed_confirmed
    (input : Proto.Bytes) (o : Cors.Origin) :
    (deployMwHeaders input o).lookup "Strict-Transport-Security"
      = some (SecurityHeaders.hstsRender deployHsts) :=
  deployed_security_headers input o

#print axioms securityheaders_deployed_confirmed

end Reactor.WireSecurityHeaders

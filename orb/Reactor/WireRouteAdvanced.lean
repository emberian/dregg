import Reactor.StaticRouteDeploy

/-!
# Reactor.WireRouteAdvanced — RouteAdvanced host isolation, already on the deployed path

The `RouteAdvanced` core property — a request for host A is never served by a
block bound only to the exact host B (`RouteAdvanced.route_host_isolation`, the
RFC 9110 §7.4 no-misdirection property at the routing layer) — is ALREADY
transported onto the deployed serve path in `Reactor/StaticRouteDeploy.lean` as
`Reactor.StaticRouteDeploy.deployed_host_routing`.

That theorem is anchored on `Reactor.Deploy.dispatchReqOf (deploySubs input)` —
the exact `Proto.Request` that `Reactor.Deploy.serveGuarded` reads and gates on,
i.e. the submissions `Arena.Orb.main` (→ `deployStepGuarded` → `serveGuarded`)
actually produces. Its proof discharges via `RouteAdvanced.route_host_isolation`
over the real `RouteAdvanced.selectBlock`, so it TRANSPORTS the library property
onto the deployed dispatch rather than restating it.

This file adds nothing new; it only pins the existing deployed seam so a
duplicate is not introduced. -/

namespace Reactor.WireRouteAdvanced

-- The deployed vhost-isolation seam: host A on the deployed path never selects
-- the host-B-only block.
#check @Reactor.StaticRouteDeploy.deployed_host_routing

-- The library core theorem it transports.
#check @RouteAdvanced.route_host_isolation

end Reactor.WireRouteAdvanced

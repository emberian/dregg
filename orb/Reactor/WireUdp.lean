import Reactor.WireRest
import Reactor.Udp

/-!
# Reactor.WireUdp — confirmation: the UDP session-affinity seam is already deployed

The per-client UDP relay session-affinity property lives in `Udp/Session.lean` as
`Udp.affinity_two_datagrams`: two datagrams from one live client are both
forwarded to the SAME recorded binding — the client is not split across upstreams
mid-session.

That property is ALREADY transported onto the deployed path. No new seam is
needed here; duplicating it would be redundant. This file only `#check`s the
existing deployed seams so the confirmation is kernel-witnessed:

* `Reactor.WireRest.udp_affinity_deployed` — the affinity property carried on the
  deployed served body (`deployDatagram input = (Reactor.Deploy.deployResp input).body`),
  transported from `Udp.affinity_two_datagrams` through the deployed-response
  view. This is the affinity seam on the Bridge/deploy surface.

* `Reactor.UdpWire.udp_session_affinity_seam_deployed` — the same affinity property over
  `orbStep`/`orbRun` at `Reactor.Deploy.deployConfig`, the config the deployed
  orb actually executes (`serveFull`/`serveGuarded`, what `Arena.Orb.main` runs).

Both are proven in their home files with `#print axioms` closed on the standard
axioms. This file re-audits them to make the already-wired status explicit.
-/

namespace Reactor.WireUdp

-- The deployed affinity seam on the served-body surface.
#check @Reactor.WireRest.udp_affinity_deployed

-- The deployed affinity seam over the orb config `main` runs.
#check @Reactor.UdpWire.udp_session_affinity_seam_deployed

-- The library core property both seams transport.
#check @Udp.affinity_two_datagrams

#print axioms Reactor.WireRest.udp_affinity_deployed
#print axioms Reactor.UdpWire.udp_session_affinity_seam_deployed

end Reactor.WireUdp

import Reactor.Dns
import Reactor.Bridge

/-!
# Reactor.WireDns — the DNS resolve-before-connect seam, landed on the deployed path

`Reactor/Dns.lean` (namespace `Reactor.DnsWire`) proves the library's core property:
the pre-connect DNS resolution pass `resolveSubs` never dials a hardcoded or
unresolved address. Every `connectUpstream a'` it emits carries an `a'` that is the
REAL `Dns.resolve` of the response bytes the resolver held for some pre-resolution
connect `a` the reactor actually emitted — `dns_resolves_before_connect`. The
load-bearing totality underneath is `Dns.decodeName`'s anti-loop termination: a
compression pointer is followed only when it jumps strictly backward, so an
adversarial DNS response resolves to "no address" (`dns_terminates_on_loop`) rather
than hanging the upstream-connect path.

That seam was proven over an *arbitrary* submission stream `subs`. This file lands
it on the exact stream the deployed binary produces. `Arena.Orb.main` →
`Reactor.Deploy.deployStep` → `serveFull` runs `Reactor.step deployConfig`, whose
submissions are `Reactor.Deploy.deploySubs input`. The `Reactor.Bridge` lift
(`deploySubs_eq_reactorSubs`, `rfl` on the plainH1 recv path) transports any
property of `reactorSubs input` onto `deploySubs input`. Instantiating that lift at
the DNS seam's property gives `dns_deployed`: on the submissions the deployed orb
actually acts on, every surviving upstream connect is a real DNS parse of the
backend hostname — no hardcoded target, no unresolved host, no divergent loop.

This is a transport, not a restatement: the mathematical content is entirely
`dns_resolves_before_connect`; the lift only moves the quantified submission
argument from the test reactor to the deployed one.
-/

namespace Reactor.WireDns

open Proto (Bytes Addr)
open Reactor.DnsWire

/-- The DNS seam's property, as a predicate on a submission stream: every
`connectUpstream a'` the resolution pass emits has a real-DNS-resolved
pre-resolution preimage that was itself in the stream. This is exactly the
statement `dns_resolves_before_connect` proves, abstracted over the stream so the
Bridge lift can move it from `reactorSubs` to `deploySubs`. -/
def ResolvedBeforeConnect (R : Resolver) (subs : List RingSubmission) : Prop :=
  ∀ a' : Addr, RingSubmission.connectUpstream a' ∈ resolveSubs R subs →
    ∃ (a : Addr) (host : List (List UInt8)) (msg : Bytes),
        RingSubmission.connectUpstream a ∈ subs
      ∧ R.lookup a = some (host, msg)
      ∧ resolve host msg = some a'

/-- **`dns_deployed` — the anti-loop resolve-before-connect seam on the deployed
serve path.** On the submissions the deployed orb acts on (`deploySubs input`, what
`Arena.Orb.main` → `serveFull` runs), every `connectUpstream a'` surviving the DNS
resolution pass carries an `a'` that is the REAL `Dns.resolve` of the response bytes
the resolver held for some pre-resolution connect `a` the deployed reactor actually
emitted. So the deployed path dials only DNS-parsed backend addresses — never a
hardcoded target, never an unresolved host, and (by totality of `Dns.decodeName`)
never a diverging compression-pointer loop.

Proven by transporting the library seam `dns_resolves_before_connect` from
`reactorSubs input` to `deploySubs input` through the `Reactor.Bridge.lift`; the
resolution content is entirely the library theorem's. -/
theorem dns_deployed (R : Resolver) (input : Bytes) :
    ResolvedBeforeConnect R (Reactor.Deploy.deploySubs input) :=
  Reactor.Bridge.lift (P := ResolvedBeforeConnect R) input
    (fun a' h => dns_resolves_before_connect R (Reactor.reactorSubs input) a' h)

/-- Unfolded form, for readers who want the seam without the `ResolvedBeforeConnect`
alias: the deployed connect address is a real DNS parse of a backend hostname the
deployed reactor emitted a pre-resolution connect for. -/
theorem dns_deployed_unfolded (R : Resolver) (input : Bytes) (a' : Addr)
    (h : RingSubmission.connectUpstream a'
          ∈ resolveSubs R (Reactor.Deploy.deploySubs input)) :
    ∃ (a : Addr) (host : List (List UInt8)) (msg : Bytes),
        RingSubmission.connectUpstream a ∈ Reactor.Deploy.deploySubs input
      ∧ R.lookup a = some (host, msg)
      ∧ resolve host msg = some a' :=
  dns_deployed R input a' h

#print axioms dns_deployed

end Reactor.WireDns

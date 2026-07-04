import Reactor.Bridge
import IpFilter

/-!
# Reactor.WireIpFilter — the CIDR IP filter attached to the DEPLOYED admission surface

`IpFilter` proved a real access-control core: a decision `permits` over an ordered
allow/deny CIDR ruleset with **deny-precedence** and a **default-deny** toggle
(`ip_deny_precedence`, `ip_default_applies`, `ip_allow_grants`, `ip_default_deny_empty`).
That theorem was proved in isolation, about an abstract `Ruleset`.

This file moves it from *island* to *connected* by keying the ruleset on the value
the deployed path actually exposes: `Reactor.Deploy.deployLid`, the single listener
the deployed binary (`Arena.Orb.main` → `Reactor.Deploy.deployStep(Guarded)` →
`serveFull`) serves on (`deployPolicyConfig.listeners = [⟨deployLid, …, 8080, …⟩]`,
and `demoAppConfig.lid = deployLid`). `deployIpPolicy` is the admission ruleset for
*that* listener, and `deployAdmits` is the IP-filter decision that gates a connection
before it reaches the deployed serve path. Every theorem below is the corresponding
`IpFilter` core theorem, specialized to the deployed admission policy — the library's
guarantee, holding of the surface the deployed orb accepts connections on.

Honest scope (the WireMore/Isolation posture): this is a *proof-attachment* seam. It
states `IpFilter`'s real, meaning-constraining decision theorems about the deployed
listener's admission policy, discharged by `IpFilter`'s own proofs. It is not (yet) a
runtime driver that reads the peer address off the accepted socket and drops the fd in
the event loop; what it establishes is that deny-precedence and default-deny hold of
the admission surface the deployed listener presents.
-/

namespace Reactor
namespace WireIpFilter

open IpFilter

/-! ## The deployed admission policy, keyed on the deployed listener -/

/-- A trusted CIDR admitted at the deployed listener: the v4 `10.0.0.0/8` private
range, modeled as the 8-bit prefix `00001010` (`10`), family-tagged v4. -/
def trustedCidr : Cidr := { family := .v4, net := [false,false,false,false,true,false,true,false], len := 8 }

/-- A blocked CIDR that *overlaps* the trusted one — `10.13.0.0/16`, the 16-bit
prefix `00001010 00001101` (`10.13`). An address in this block sits inside the
trusted `/8` (so it matches the allow rule) **and** inside this `/16` deny rule,
making deny-precedence observable rather than vacuous. -/
def blockedCidr : Cidr :=
  { family := .v4
  , net := [false,false,false,false,true,false,true,false, false,false,false,false,true,true,false,true]
  , len := 16 }

/-- **The deployed admission ruleset for `Reactor.Deploy.deployLid`.** Ordered
allow-then-deny over the two overlapping CIDRs, `defaultDeny := true`: an address is
admitted only if it lands in the trusted range *and* not in the blocked sub-range;
everything else (including everything unlisted) is rejected. Deny-precedence and
default-deny are the two properties transported below. The listener this gates is
the one the deployed binary serves on (`deployPolicyConfig.listeners`). -/
def deployIpPolicy : Ruleset :=
  { rules := [(trustedCidr, .allow), (blockedCidr, .deny)]
  , defaultDeny := true }

/-- Admission of client address `a` at the deployed listener: the `IpFilter` decision
over the deployed admission policy. `true` = admit and hand to the serve path. -/
def deployAdmits (a : Addr) : Bool := permits deployIpPolicy a

/-! ## The transported core — deny-precedence and default-deny on the deployed surface -/

/-- **`ipfilter_deployed` — deny-precedence holds at the deployed listener.** Any
client address that matches a deny rule of the deployed admission policy is refused
admission, whatever the allow rules say. This is `IpFilter.ip_deny_precedence`
transported onto `deployAdmits` — the security core (a blocklisted peer is dropped
before the serve path, regardless of any overlapping allow) landed on the surface the
deployed orb accepts on. -/
theorem ipfilter_deployed (a : Addr) (h : matchesDeny deployIpPolicy a = true) :
    deployAdmits a = false :=
  ip_deny_precedence deployIpPolicy a h

/-- **Default-deny at the deployed listener.** A client address matching *no* rule of
the deployed admission policy is refused — the fail-closed default (`defaultDeny = true`)
on the deployed surface. `IpFilter.ip_default_applies` transported, then reduced by the
policy's default toggle. -/
theorem deployIp_default_deny (a : Addr)
    (hd : matchesDeny deployIpPolicy a = false)
    (ha : matchesAllow deployIpPolicy a = false) :
    deployAdmits a = false := by
  have := ip_default_applies deployIpPolicy a hd ha
  simpa [deployAdmits, deployIpPolicy] using this

/-- **Allow grants at the deployed listener.** A client address matching an allow rule
with no matching deny is admitted to the serve path. `IpFilter.ip_allow_grants`
transported onto `deployAdmits`. -/
theorem deployIp_allow_grants (a : Addr)
    (hd : matchesDeny deployIpPolicy a = false)
    (ha : matchesAllow deployIpPolicy a = true) :
    deployAdmits a = true :=
  ip_allow_grants deployIpPolicy a hd ha

/-- **Family separation on the deployed surface.** A v6 client address never matches
the deployed policy's v4 CIDRs — `IpFilter.ip_family_mismatch` on each rule. So a v6
peer is neither allow-matched nor deny-matched by the (v4-only) deployed policy, and
falls through to the default-deny. Concrete witness of the model's family disjointness
on the deployed listener. -/
theorem deployIp_v6_not_v4_matched (a : Addr) (h : a.family = .v6) :
    matchCidr trustedCidr a = false ∧ matchCidr blockedCidr a = false := by
  refine ⟨ip_family_mismatch trustedCidr a ?_, ip_family_mismatch blockedCidr a ?_⟩
  · rw [h]; exact fun h' => by cases h'
  · rw [h]; exact fun h' => by cases h'

/-! ## Grounding — the policy is not vacuous: a concrete overlap rejects, a clean host admits -/

/-- A concrete client in the blocked sub-range `10.13.0.0/16` (32-bit v4 address
`10.13.0.0`). It sits inside the trusted `/8` allow *and* the `/16` deny. -/
def blockedClient : Addr :=
  { family := .v4
  , bits := [false,false,false,false,true,false,true,false,   -- 10
             false,false,false,false,true,true,false,true,     -- 13
             false,false,false,false,false,false,false,false,  -- 0
             false,false,false,false,false,false,false,false] }-- 0

/-- A concrete client in the trusted `/8` but *outside* the `/16` deny — `10.1.0.0`. -/
def cleanClient : Addr :=
  { family := .v4
  , bits := [false,false,false,false,true,false,true,false,   -- 10
             false,false,false,false,false,false,false,true,   -- 1
             false,false,false,false,false,false,false,false,
             false,false,false,false,false,false,false,false] }

/-- **The overlap is real: deny-precedence actually fires.** `blockedClient` matches
the allow rule (it is in the trusted `/8`) yet is rejected, because the deny rule wins.
This grounds `ipfilter_deployed` — the transported theorem is discharging a genuine
allow∩deny collision, not an empty hypothesis. -/
theorem deployIp_blocked_rejected :
    matchesAllow deployIpPolicy blockedClient = true
    ∧ deployAdmits blockedClient = false := by
  decide

/-- **A clean trusted host is admitted.** `cleanClient` is inside the allow `/8` and
outside the deny `/16`, so the deployed listener admits it. -/
theorem deployIp_clean_admitted : deployAdmits cleanClient = true := by decide

/-- **An unlisted host is rejected by default.** A loopback-ish `127.0.0.1`-shaped
address matches neither CIDR and falls to fail-closed default-deny. -/
theorem deployIp_unlisted_rejected :
    deployAdmits
      { family := .v4
      , bits := [false,true,true,true,true,true,true,true,   -- 127
                 false,false,false,false,false,false,false,false,
                 false,false,false,false,false,false,false,false,
                 false,false,false,false,false,false,false,true] } = false := by decide

/-! ## Axiom audit — every deployed seam closed on the standard axioms only -/

#print axioms ipfilter_deployed
#print axioms deployIp_default_deny
#print axioms deployIp_allow_grants
#print axioms deployIp_v6_not_v4_matched
#print axioms deployIp_blocked_rejected
#print axioms deployIp_clean_admitted
#print axioms deployIp_unlisted_rejected

end WireIpFilter
end Reactor

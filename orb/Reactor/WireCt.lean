import Reactor.Bridge
import Ct.Inclusion

/-!
# Reactor.WireCt — Certificate Transparency attached to the DEPLOYED serve path

`Ct` proves RFC 6962 inclusion-proof soundness (`Ct.inclusion_sound`, the `→` of
theorem 1): against the *genuine* signed tree head `mth HS xs`, if *any* — possibly
adversarial — audit path recomputes that head for a claimed leaf, then the claimed
leaf is the genuine `i`-th entry of the log. This is the security core; it spends
collision resistance (`hnode_inj`/`hleaf_inj`) to force the claimed leaf to equal
the real one. On its own it is an island: a statement about an abstract `List Leaf`.

This file lands that guarantee on the bytes the deployed binary actually writes.
`Arena.Orb.main` runs `Reactor.Deploy.deployStepGuarded` → `serveGuarded` (and
`deployStep` → `serveFull`), whose output is the served response `Bytes`. Model a
Certificate Transparency log as the sequence of those deployed served responses:
each leaf is one response the deployed orb emitted. `Ct.inclusion_sound`,
instantiated with `Leaf := Bytes` and the deployed served bytes as the claimed
leaf, then says: a monitor holding only the log's signed head cannot be shown an
inclusion proof placing *other* bytes at the position where the deployed path
served `serveGuarded input` — the log commits exactly the deployed response.

Anchor to the one shared reactor: `serveGuarded`/`serveFull` are built from
`Reactor.Deploy.deploySubs input`, which `Reactor.Bridge.deploySubs_eq_reactorSubs`
pins to `Reactor.reactorSubs input` — the very submissions the island lanes were
proven over. So the leaf logged here is the response of the proven reactor, not a
fresh side model.

Honest scope (same posture as `Reactor.WireMore`): this is a proof-attachment
seam. It states CT's real, collision-resistance-spending soundness theorem about
the actual deployed served bytes, discharged by `Ct`'s own proof — not a runtime
log-server that signs heads on disk. What it establishes is that CT's inclusion
guarantee *holds of the response the deployed path carries*, closing the island.
-/

namespace Reactor
namespace WireCt

open Proto (Bytes)
open Ct

/-- **`ct_deployed` — the deployed served response is CT-committed, soundly.**
Take a Certificate Transparency log `log : List Bytes` of served responses over an
arbitrary collision-resistant `HashScheme`, and suppose the deployed served bytes
`Reactor.Deploy.serveGuarded input` (what guarded `main` writes) are claimed at
index `i`. If *any* audit `path` recomputes the log's genuine signed head
`mth HS log` from that leaf's hash, then the log's `i`-th entry really *is*
`serveGuarded input` — `Ct.inclusion_sound` transported onto the deployed response.
No adversary can forge an inclusion proof placing different bytes at `i`: the log
binds the exact bytes the deployed orb served. -/
theorem ct_deployed {H : Type} (HS : HashScheme Bytes H)
    (input : Bytes) (log : List Bytes) (i : Nat) (path : List H)
    (hi : i < log.length)
    (hverify :
      rootFromPath HS (HS.hleaf (Reactor.Deploy.serveGuarded input)) i log.length path
        = some (mth HS log)) :
    log[i]? = some (Reactor.Deploy.serveGuarded input) :=
  inclusion_sound HS log.length log i (Reactor.Deploy.serveGuarded input) path rfl hi hverify

/-- **`ct_deployed_serveFull` — same seam over the unguarded deployed entry.**
`serveFull` is the response `Reactor.Deploy.deployStep` (`main`'s pre-Policy entry)
writes; its served bytes are likewise soundly committed by any CT log that carries
them at index `i`. -/
theorem ct_deployed_serveFull {H : Type} (HS : HashScheme Bytes H)
    (input : Bytes) (log : List Bytes) (i : Nat) (path : List H)
    (hi : i < log.length)
    (hverify :
      rootFromPath HS (HS.hleaf (Reactor.Deploy.serveFull input)) i log.length path
        = some (mth HS log)) :
    log[i]? = some (Reactor.Deploy.serveFull input) :=
  inclusion_sound HS log.length log i (Reactor.Deploy.serveFull input) path rfl hi hverify

/-- **`ct_deployed_iff` — full RFC 6962 theorem 1 on the deployed response.**
Against the log's real head, the honest audit path for index `i` verifies the
deployed served bytes `serveGuarded input` *iff* those bytes are the genuine
`i`-th logged response — soundness (no forged inclusion) and completeness (the
honest proof always checks) together, landed on the bytes `main` writes. -/
theorem ct_deployed_iff {H : Type} [DecidableEq H] (HS : HashScheme Bytes H)
    (input : Bytes) (log : List Bytes) (i : Nat) (hi : i < log.length) :
    verifyInclusion HS (HS.hleaf (Reactor.Deploy.serveGuarded input)) i log.length
        (auditPath HS log i) (mth HS log) = true
      ↔ log[i]? = some (Reactor.Deploy.serveGuarded input) :=
  inclusion_iff HS hi

/-! ## Axiom audit — the deployed CT seam is closed on the standard axioms only -/

#print axioms ct_deployed
#print axioms ct_deployed_serveFull
#print axioms ct_deployed_iff

end WireCt
end Reactor

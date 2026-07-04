import Reactor.CacheDeploy
import Reactor.Bridge

/-!
# Reactor.WireCache — confirming the deployed RFC 9111 cache seam

The Cache library's core property to transport is RFC 9111 §4.2: a **fresh cache
hit is served with no upstream fetch**. That transport is already installed on
the deployed path in `Reactor/CacheDeploy.lean`:

* `Cache.cache_hit_fresh` is the library core theorem (a fresh stored entry steps
  to a single `serve` effect, contacting no origin).
* `Reactor.CacheDeploy.deployed_cache_hit_no_upstream` transports it onto the
  deployed proxy gate: on a fresh entry the deployed cache plan collapses to `[]`
  and `Proxy.targetedUpstream = none` — the origin is not dialed. The gate is
  defined over `Reactor.Deploy.deploySubs` (the miss branch forwards to
  `deployPlan (deploySubs input)`, the same submissions the un-cached deployed
  path — what `Arena.Orb.main` runs — emits), so the hit seam sits directly on
  the deployed serve path.

This file does not re-prove or duplicate that seam; it only pins the existing
deployed corollary (and its coalescing companions) with `#check`, and audits the
axiom set. -/

namespace Reactor.WireCache

open Proto (Bytes)

-- The deployed fresh-hit seam: a fresh cached entry dials nothing on the
-- deployed path. This IS the RFC 9111 §4.2 property landed over deploySubs.
#check @Reactor.CacheDeploy.deployed_cache_hit_no_upstream

-- Its concrete witness: the warm deployed cache serves without dialing.
#check @Reactor.CacheDeploy.deployCacheWarm_hit_no_upstream

-- The library core theorem the seam transports.
#check @Cache.cache_hit_fresh

-- The Bridge lift the deployed path is built on (deploySubs = reactorSubs).
#check @Reactor.Bridge.lift

/-- A local alias so the deployed fresh-hit seam is nameable from this file as
`cache_deployed`, without restating any content. -/
theorem cache_deployed (input : Bytes) (cs : Cache.St) (k : Cache.Key)
    (now : Nat) (e : Cache.Stored)
    (hget : cs.store.get? k = some e) (hfresh : e.meta.isFresh now = true) :
    Reactor.CacheDeploy.deployCachedPlan input cs k now = []
    ∧ Reactor.Proxy.targetedUpstream
        (Reactor.CacheDeploy.deployCachedPlan input cs k now) = none :=
  Reactor.CacheDeploy.deployed_cache_hit_no_upstream input cs k now e hget hfresh

#print axioms cache_deployed

end Reactor.WireCache

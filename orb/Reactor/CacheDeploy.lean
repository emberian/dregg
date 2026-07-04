import Cache
import Reactor.Deploy

/-!
# Reactor.CacheDeploy — the RFC 9111 response cache, gating the deployed proxy path

`Reactor.Deploy` proved that the deployed orb, on a dispatched request, runs the
REAL reverse-proxy fabric: `deployPlan (deploySubs input)` routes the reactor's
own submissions through `ProxyServe.serveProxyOn` (→ `Route.Match.bestMatch` →
`Proxy.selectChain`) and then the REAL `DnsWire.resolve` pass, producing exactly
one `connectUpstream` to the LB-chosen, DNS-resolved backend
(`Reactor.Deploy.deploy_plan_resolved`). Every deployed dispatch therefore dials
the origin — there is no cache in front of it.

This file installs one. It composes the REAL `Cache` machine (the bounded,
coalescing shared cache of RFC 9111, `Cache.step`) *in front of* that deployed
proxy plan, so the cache genuinely decides whether the deployed reactor connects
upstream at all:

* `planOfEffs` maps one `Cache.step` verdict onto the deployed submissions. If the
  cache's effects contact the origin (`Cache.Eff.isUpstream` — a `fetch` or a
  `revalidate`), the miss/stale forwards through the REAL deployed proxy plan
  (`deployPlan (deploySubs input)`) — the same connect the un-cached deployed path
  emits. If they do not (a fresh hit serves from the store), it emits **nothing** —
  no `connectUpstream`.
* `deployCachedPlan` is the one-request gate; `deployCachedRun` folds it over a
  burst of concurrent requests, threading the cache state through `Cache.step`.

So the cache is not a sibling model beside the deployed path: its verdict is the
*only* thing standing between a request and `deployPlan (deploySubs input)`.

## Seam theorems (over the deployed proxy plan)

* **`deployed_cache_hit_no_upstream`** — on a fresh cached entry the deployed path
  emits **no** `connectUpstream` at all: `Cache.cache_hit_fresh` (the fresh entry
  is served with no origin contact) transported through `planOfEffs` collapses the
  deployed plan to `[]`, so `Proxy.targetedUpstream = none`. The origin is not
  dialed.
* **`deployed_cache_miss_connects`** — the branch is real: on a miss over a
  dispatched request, the SAME gate forwards to the full deployed proxy plan and
  connects to `⟨1572395042⟩` (`93.184.216.34`) — the address the REAL LB chose and
  the REAL DNS parser resolved (`deploy_plan_resolved`). Cache hit ⇒ no dial; cache
  miss ⇒ the real deployed dial.
* **`deployed_cache_coalesce`** — `K` concurrent misses for one key over the
  deployed path collapse to **exactly one** deployed proxy plan: the leader forwards
  (`deployPlan (deploySubs input)`), every follower coalesces and emits nothing, so
  the whole burst's submissions equal a single upstream fetch. This transports
  `Cache.coalesce_single_fetch`'s "one fetch, K−1 waits" onto the deployed
  connect. `deployed_cache_coalesce_one_upstream` counts it: exactly one
  `connectUpstream` for the entire burst.

The concrete `deployCache` (an empty bounded cache) and `deployCacheWarm` (one
fresh stored entry) discharge the store hypotheses by `rfl`/`decide`, exhibiting
both arms end-to-end with no reactor hypothesis on the store side.
-/

namespace Reactor
namespace CacheDeploy

open Proto (Bytes)
open Reactor.Deploy (deployPlan deploySubs deploy_plan_resolved)

/-! ## The gate: one cache verdict → the deployed proxy submissions -/

/-- Map one `Cache.step`'s effects onto the deployed proxy submissions. A verdict
that contacts the origin (`Cache.Eff.isUpstream` — `fetch`/`revalidate`) forwards
to the REAL deployed proxy plan (`deployPlan (deploySubs input)`, the one
`connectUpstream` the un-cached deployed path emits); a verdict that does not (a
fresh `serve` hit, or a coalesced `wait`) emits **no** submission. -/
def planOfEffs (input : Bytes) (es : List Cache.Eff) : List RingSubmission :=
  if es.any Cache.Eff.isUpstream then deployPlan (deploySubs input) else []

theorem planOfEffs_serve (input : Bytes) (k : Cache.Key) (b : Cache.Body) :
    planOfEffs input [Cache.Eff.serve k b] = [] := by
  simp [planOfEffs, Cache.Eff.isUpstream]

theorem planOfEffs_wait (input : Bytes) (k : Cache.Key) :
    planOfEffs input [Cache.Eff.wait k] = [] := by
  simp [planOfEffs, Cache.Eff.isUpstream]

theorem planOfEffs_fetch (input : Bytes) (k : Cache.Key) :
    planOfEffs input [Cache.Eff.fetch k] = deployPlan (deploySubs input) := by
  simp [planOfEffs, Cache.Eff.isUpstream]

/-- **The cache gate on one request over the deployed path.** Consult the REAL
`Cache` machine for `(k, now)`; forward its verdict onto the deployed proxy plan.
A fresh hit ⇒ `[]` (no upstream); a miss/stale ⇒ the real deployed connect. -/
def deployCachedPlan (input : Bytes) (cs : Cache.St) (k : Cache.Key) (now : Nat) :
    List RingSubmission :=
  planOfEffs input (Cache.step cs (.request k now)).2

/-- Fold the cache gate over a burst of concurrent cache inputs, threading the
REAL `Cache.step` state through each. The submissions of the whole burst are the
concatenation of each request's deployed plan. -/
def deployCachedRun (input : Bytes) (cs : Cache.St) :
    List Cache.Input → List RingSubmission
  | [] => []
  | i :: is =>
    planOfEffs input (Cache.step cs i).2
      ++ deployCachedRun input (Cache.step cs i).1 is

/-- Is this submission an upstream connect? -/
def RingSubmission.isConnectUpstream : RingSubmission → Bool
  | .connectUpstream _ => true
  | _                  => false

/-- Count the `connectUpstream` submissions — the number of times the deployed
path dials the origin. -/
def countConnect (subs : List RingSubmission) : Nat :=
  (subs.filter RingSubmission.isConnectUpstream).length

/-! ## Seam 1 — a fresh cached entry dials nothing on the deployed path -/

/-- **`deployed_cache_hit_no_upstream`.** When `k` has a fresh stored response,
the deployed cache gate emits **no** submission — in particular no
`connectUpstream`. This is `Cache.cache_hit_fresh` (a fresh entry is served with
no origin contact, §4.2) transported through `planOfEffs`: the fresh `serve`
verdict is not `isUpstream`, so the deployed proxy plan is never invoked. The
origin is not dialed. -/
theorem deployed_cache_hit_no_upstream (input : Bytes) (cs : Cache.St) (k : Cache.Key)
    (now : Nat) (e : Cache.Stored)
    (hget : cs.store.get? k = some e) (hfresh : e.meta.isFresh now = true) :
    deployCachedPlan input cs k now = []
    ∧ Reactor.Proxy.targetedUpstream (deployCachedPlan input cs k now) = none := by
  have hserve : (Cache.step cs (.request k now)).2 = [Cache.Eff.serve k e.body] :=
    (Cache.cache_hit_fresh cs k now e hget hfresh).1
  have hnil : deployCachedPlan input cs k now = [] := by
    unfold deployCachedPlan
    rw [hserve]; exact planOfEffs_serve input k e.body
  exact ⟨hnil, by rw [hnil]; rfl⟩

/-! ## Seam 2 — a miss dials exactly the real deployed backend (the branch is real) -/

/-- **`deployed_cache_miss_connects`.** The gate genuinely branches. When `k` is a
miss (no stored entry, no in-flight fetch) and the deployed reactor dispatched the
request, the SAME gate forwards to the full deployed proxy plan and connects to
`⟨1572395042⟩` (`93.184.216.34`) — the LB-chosen, DNS-resolved backend of
`deploy_plan_resolved`. Cache hit ⇒ `deployed_cache_hit_no_upstream` (no dial);
cache miss ⇒ this real deployed dial. -/
theorem deployed_cache_miss_connects (input : Bytes) (cs : Cache.St) (k : Cache.Key)
    (now : Nat) (req : Proto.Request) (rest : List RingSubmission)
    (hget : cs.store.get? k = none) (hlock : cs.locked k = false)
    (hsub : deploySubs input = .dispatch req :: rest) :
    deployCachedPlan input cs k now
        = [RingSubmission.connectUpstream (⟨1572395042⟩ : Proto.Addr)]
    ∧ Reactor.Proxy.targetedUpstream (deployCachedPlan input cs k now)
        = some (⟨1572395042⟩ : Proto.Addr) := by
  have hfetch : (Cache.step cs (.request k now)).2 = [Cache.Eff.fetch k] := by
    rw [Cache.step_miss_unlocked cs k now hget hlock]
  have hplan : deployCachedPlan input cs k now = deployPlan (deploySubs input) := by
    unfold deployCachedPlan
    rw [hfetch]; exact planOfEffs_fetch input k
  rw [hplan, deploy_plan_resolved input req rest hsub]
  exact ⟨rfl, rfl⟩

/-! ## Seam 3 — concurrent misses coalesce to one deployed fetch -/

/-- A burst all of whose steps are coalesced followers (each emits `[wait k]` and
preserves the follower predicate `P`) contributes **no** submissions to the
deployed run — every `wait` maps to `[]` under `planOfEffs`. Parameterized over
`P` so it feeds the miss-coalescing proof (mirrors `Cache.all_wait_run`). -/
theorem deployRun_all_wait (input : Bytes) (k : Cache.Key) (now : Nat) (P : Cache.St → Prop)
    (hstep : ∀ t, P t → (Cache.step t (.request k now)).2 = [Cache.Eff.wait k]
                        ∧ P (Cache.step t (.request k now)).1) :
    ∀ (m : Nat) (t : Cache.St), P t →
      deployCachedRun input t (Cache.reqs k now m) = [] := by
  intro m
  induction m with
  | zero => intro t _; rfl
  | succ m ih =>
    intro t ht
    obtain ⟨he, hP⟩ := hstep t ht
    have hcons : deployCachedRun input t (Cache.reqs k now (m + 1))
        = planOfEffs input (Cache.step t (.request k now)).2
          ++ deployCachedRun input (Cache.step t (.request k now)).1 (Cache.reqs k now m) := by
      simp only [Cache.reqs, List.replicate_succ, deployCachedRun]
    rw [hcons, he, planOfEffs_wait, List.nil_append]
    exact ih _ hP

/-- **`deployed_cache_coalesce`.** `K = n` concurrent requests for one key (a cache
miss: no stored entry, no in-flight fetch) over the deployed path collapse to
**exactly one** deployed proxy plan. The leader miss forwards to
`deployPlan (deploySubs input)` — the real reverse-proxy + DNS connect — and every
one of the `n−1` followers coalesces (emits nothing), so the whole burst's
submissions are a single upstream fetch. This transports
`Cache.coalesce_single_fetch` (one `fetch`, `n−1` `wait`s, §4 request collapsing)
onto the deployed connect. -/
theorem deployed_cache_coalesce (input : Bytes) (cs : Cache.St) (k : Cache.Key) (now n : Nat)
    (hn : 0 < n) (hget : cs.store.get? k = none) (hlock : cs.locked k = false) :
    deployCachedRun input cs (Cache.reqs k now n) = deployPlan (deploySubs input) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- The follower invariant: still a miss, but now locked — preserved by every
  -- follower step (which touches only `pending`).
  let P : Cache.St → Prop := fun t => t.store.get? k = none ∧ t.locked k = true
  have hfollow : ∀ t, P t → (Cache.step t (.request k now)).2 = [Cache.Eff.wait k]
                          ∧ P (Cache.step t (.request k now)).1 := by
    intro t ht
    rw [Cache.step_miss_locked t k now ht.1 ht.2]
    exact ⟨rfl, ht.1, ht.2⟩
  -- Split the leader step off the burst.
  have hcons : deployCachedRun input cs (Cache.reqs k now (m + 1))
      = planOfEffs input (Cache.step cs (.request k now)).2
        ++ deployCachedRun input (Cache.step cs (.request k now)).1 (Cache.reqs k now m) := by
    simp only [Cache.reqs, List.replicate_succ, deployCachedRun]
  have h2 : (Cache.step cs (.request k now)).2 = [Cache.Eff.fetch k] := by
    rw [Cache.step_miss_unlocked cs k now hget hlock]
  have h1 : (Cache.step cs (.request k now)).1 = { cs with locks := k :: cs.locks } := by
    rw [Cache.step_miss_unlocked cs k now hget hlock]
  have hP : P { cs with locks := k :: cs.locks } := ⟨hget, Cache.locked_cons_self cs k⟩
  rw [hcons, h2, h1, planOfEffs_fetch,
    deployRun_all_wait input k now P hfollow m _ hP, List.append_nil]

/-- **`deployed_cache_coalesce_one_upstream`.** The count, on a dispatch: the whole
burst of `n` concurrent misses dials the origin **exactly once**. Composes
`deployed_cache_coalesce` (the burst = one deployed plan) with
`deploy_plan_resolved` (that plan is one `connectUpstream`). -/
theorem deployed_cache_coalesce_one_upstream (input : Bytes) (cs : Cache.St) (k : Cache.Key)
    (now n : Nat) (req : Proto.Request) (rest : List RingSubmission)
    (hn : 0 < n) (hget : cs.store.get? k = none) (hlock : cs.locked k = false)
    (hsub : deploySubs input = .dispatch req :: rest) :
    countConnect (deployCachedRun input cs (Cache.reqs k now n))
        = 1
    ∧ Reactor.Proxy.targetedUpstream (deployCachedRun input cs (Cache.reqs k now n))
        = some (⟨1572395042⟩ : Proto.Addr) := by
  rw [deployed_cache_coalesce input cs k now n hn hget hlock,
    deploy_plan_resolved input req rest hsub]
  exact ⟨rfl, rfl⟩

/-! ## Concrete instances — both arms driven end-to-end -/

/-- A concrete deployed cache: empty, bounded at 1024 entries. -/
def deployCache : Cache.St := Cache.init 1024

theorem deployCache_empty (k : Cache.Key) : deployCache.store.get? k = none := rfl
theorem deployCache_unlocked (k : Cache.Key) : deployCache.locked k = false := rfl

/-- A demo cache key. -/
def demoKey : Cache.Key := ⟨0, 0, []⟩

/-- A demo fresh stored entry: freshness lifetime 1000s, age 0, no validator — so
`isFresh` holds for a long window from `now = 0`. -/
def demoFreshStored : Cache.Stored :=
  { key := demoKey
    body := ⟨0⟩
    meta := { freshnessLifetime := 1000, correctedInitialAge := 0, responseTime := 0, etag := none } }

/-- A warm deployed cache: `demoKey` already holds `demoFreshStored`. -/
def deployCacheWarm : Cache.St :=
  { store := { entries := [demoFreshStored], capacity := 1024 }, locks := [], pending := [] }

theorem deployCacheWarm_get : deployCacheWarm.store.get? demoKey = some demoFreshStored := rfl

theorem demoFreshStored_fresh : demoFreshStored.meta.isFresh 0 = true := by decide

/-- **The warm cache serves without dialing, concretely.** For any deployed input,
the fresh `demoKey` entry is served from the deployed cache with no
`connectUpstream` at all. -/
theorem deployCacheWarm_hit_no_upstream (input : Bytes) :
    deployCachedPlan input deployCacheWarm demoKey 0 = []
    ∧ Reactor.Proxy.targetedUpstream (deployCachedPlan input deployCacheWarm demoKey 0) = none :=
  deployed_cache_hit_no_upstream input deployCacheWarm demoKey 0 demoFreshStored
    deployCacheWarm_get demoFreshStored_fresh

/-- **The empty cache dials the real backend, concretely.** For a deployed
dispatch, a miss on the empty `deployCache` connects to the real LB/DNS-resolved
`⟨1572395042⟩`. -/
theorem deployCache_miss_connects (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission) (k : Cache.Key) (now : Nat)
    (hsub : deploySubs input = .dispatch req :: rest) :
    deployCachedPlan input deployCache k now
        = [RingSubmission.connectUpstream (⟨1572395042⟩ : Proto.Addr)]
    ∧ Reactor.Proxy.targetedUpstream (deployCachedPlan input deployCache k now)
        = some (⟨1572395042⟩ : Proto.Addr) :=
  deployed_cache_miss_connects input deployCache k now req rest
    (deployCache_empty k) (deployCache_unlocked k) hsub

/-- **Concurrent misses on the empty cache coalesce to one real dial.** For a
deployed dispatch, `n > 0` concurrent misses on `deployCache` produce exactly one
`connectUpstream` to the real backend. -/
theorem deployCache_coalesce_one_upstream (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission) (k : Cache.Key) (now n : Nat) (hn : 0 < n)
    (hsub : deploySubs input = .dispatch req :: rest) :
    countConnect (deployCachedRun input deployCache (Cache.reqs k now n)) = 1
    ∧ Reactor.Proxy.targetedUpstream (deployCachedRun input deployCache (Cache.reqs k now n))
        = some (⟨1572395042⟩ : Proto.Addr) :=
  deployed_cache_coalesce_one_upstream input deployCache k now n req rest hn
    (deployCache_empty k) (deployCache_unlocked k) hsub

end CacheDeploy
end Reactor

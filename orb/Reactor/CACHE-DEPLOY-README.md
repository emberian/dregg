# CACHE-DEPLOY — the RFC 9111 response cache, gating the deployed proxy path

`Reactor/CacheDeploy.lean` composes the real `Cache` machine (RFC 9111, the
bounded coalescing shared cache) *in front of* the deployed reverse-proxy plan, so
the cache genuinely decides whether the deployed reactor connects upstream.

## What was already true, and what was missing

`Reactor.Deploy` proved that a deployed dispatch runs the real proxy fabric:

    deployPlan (deploySubs input)
      = ProxyServe.serveProxyOn …  (Route.Match.bestMatch → Proxy.selectChain)
        then DnsWire.resolve …
      = [connectUpstream ⟨1572395042⟩]          -- deploy_plan_resolved

Every deployed dispatch dials the origin. There was no cache in front of it: a
second request for a resource already fetched would dial again, and a burst of
concurrent requests would dial once per request.

## The wiring (on the deployed path)

The gate maps one `Cache.step` verdict onto the deployed submissions:

    planOfEffs input es :=
      if es.any Cache.Eff.isUpstream
      then deployPlan (deploySubs input)   -- miss/stale: the REAL deployed connect
      else []                              -- fresh hit / coalesced wait: no dial

* `deployCachedPlan input cs k now` — the one-request gate: consult the real
  `Cache.step cs (.request k now)`, forward its verdict through `planOfEffs`.
* `deployCachedRun input cs is` — folds the gate over a burst of concurrent cache
  inputs, threading the real `Cache.step` state through each.

`deployPlan (deploySubs input)` is the *same* plan the un-cached deployed path
emits — the cache's verdict is the only thing standing between a request and that
connect. This is not a sibling model beside the deployed path.

## Seam theorems

* **`deployed_cache_hit_no_upstream`** — on a fresh cached entry the deployed path
  emits nothing, so `Proxy.targetedUpstream = none`: the origin is not dialed. This
  transports `Cache.cache_hit_fresh` (a fresh entry is served with no origin
  contact, §4.2) through `planOfEffs` — the fresh `serve` verdict is not
  `isUpstream`, so `deployPlan (deploySubs input)` is never invoked.

* **`deployed_cache_miss_connects`** — the branch is real. On a miss over a
  dispatched request, the *same* gate forwards to the full deployed proxy plan and
  connects to `⟨1572395042⟩` (`93.184.216.34`) — the LB-chosen, DNS-resolved
  backend of `deploy_plan_resolved`. Cache hit ⇒ no dial; cache miss ⇒ the real
  deployed dial.

* **`deployed_cache_coalesce`** — `n` concurrent misses for one key over the
  deployed path collapse to *exactly one* deployed proxy plan: the leader forwards
  `deployPlan (deploySubs input)`, every one of the `n−1` followers coalesces and
  emits nothing, so the whole burst's submissions equal a single upstream fetch.
  This transports `Cache.coalesce_single_fetch` ("one fetch, K−1 waits", §4 request
  collapsing) onto the deployed connect via the follower lemma `deployRun_all_wait`.

* **`deployed_cache_coalesce_one_upstream`** — the count, on a dispatch: the whole
  burst dials the origin `countConnect … = 1`, and targets the real backend.
  Composes `deployed_cache_coalesce` with `deploy_plan_resolved`.

## Concrete instances (both arms, end-to-end)

* `deployCache = Cache.init 1024` — empty bounded cache; store hypotheses close by
  `rfl`. `deployCache_miss_connects` and `deployCache_coalesce_one_upstream` drive
  the miss / coalesce arms on a deployed dispatch.
* `deployCacheWarm` — `demoKey` already holds a fresh entry (lifetime 1000 s, age 0,
  `demoFreshStored_fresh` by `decide`). `deployCacheWarm_hit_no_upstream` drives the
  hit arm: no dial, for any input.

## Status

`lake build Reactor.CacheDeploy` green; zero sorries. `#print axioms` on every seam
theorem: `{propext, Classical.choice, Quot.sound}` only. Spine (`Proto`,
`Reactor.Deploy`, `Reactor.Bridge`, `Arena`) green.

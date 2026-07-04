import Reactor.Pipeline
import Cache

/-!
# Reactor.Stage.Cache — the RFC 9111 fresh-hit cache GATE

A byte-driving pipeline stage that turns the real `Cache` library's fresh-hit
decision into a short-circuit on the deployed serve path. On a **fresh cache
hit** (`Cache.Store.get?` finds an entry AND `Cache.Meta.isFresh` holds at the
stage's clock) the stage `.respond`s with the stored response bytes — the
handler and every later stage are skipped, no upstream is dialed. On a **miss**
(no stored entry) the stage `.continue`s: the request passes through untouched
and the handler's bytes flow.

The decision is the genuine `Cache` transition data — `Store.get?` (the §4.1
exact-key lookup) and `Meta.isFresh` (the §4.2 `freshness_lifetime > current_age`
test) — not a re-implementation. The only boundary is `render : Cache.Body →
Response`: the origin's body bytes are outside the `Cache` model (its `Body` is
an opaque token, exactly as documented in `Cache.lean`), so a config function
supplies the actual stored bytes — the same uninterpreted-boundary shape the
`Tls`/`Cache` libraries use for their crypto/body payloads.

The byte-effect is a GATE short-circuit: `cacheStage_serves_stored` proves the
built pipeline output IS `render`'s stored `Response` — for ANY tail and
handler — so a fresh hit genuinely changes the emitted bytes (the cached body,
not the handler's), and `cacheStage_miss_passthrough` proves a miss leaves the
tail's bytes exactly as they were.
-/

namespace Reactor.Stage.Cache

open Reactor (Response natToDec reasonOK)
open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## The gate, parameterized by a cache configuration -/

/-- A deployed cache-stage configuration: the (warm) cache state, how a request
maps to a `Cache.Key`, the clock the freshness test consults, and the boundary
`render` that turns the opaque stored `Body` token into the actual stored
response bytes. -/
structure Config where
  /-- The cache state consulted on the request phase. -/
  st : _root_.Cache.St
  /-- §4.1 cache-key derivation from the dispatched request. -/
  keyOf : Ctx → _root_.Cache.Key
  /-- The clock (seconds) the freshness test reads (`Cache.lean`: time is data). -/
  now : Nat
  /-- Boundary: the stored body token → the stored response bytes it stands for. -/
  render : _root_.Cache.Body → Response

/-- The request-phase decision, wired to the REAL `Cache` lookup + freshness
test: a fresh stored entry gates with `render`'s stored bytes; anything else
(miss, or a stale entry) passes through. -/
def Config.onReq (cfg : Config) (c : Ctx) : StageStep :=
  match cfg.st.store.get? (cfg.keyOf c) with
  | some e => if e.meta.isFresh cfg.now = true then .respond (cfg.render e.body) else .continue c
  | none => .continue c

/-- The stage: a gate on the request phase; the response phase is the identity
(a gate contributes bytes by short-circuiting, not by transforming the tail). -/
def mkStage (cfg : Config) : Stage where
  name := "cache"
  onRequest := cfg.onReq
  onResponse := fun _ b => b

/-! ## The gate's request-phase reductions (real `Cache` decision) -/

/-- A fresh hit gates with the stored bytes. -/
theorem onReq_hit (cfg : Config) (c : Ctx) (e : _root_.Cache.Stored)
    (hget : cfg.st.store.get? (cfg.keyOf c) = some e)
    (hfresh : e.meta.isFresh cfg.now = true) :
    cfg.onReq c = .respond (cfg.render e.body) := by
  simp [Config.onReq, hget, hfresh]

/-- A miss passes through unchanged. -/
theorem onReq_miss (cfg : Config) (c : Ctx)
    (hget : cfg.st.store.get? (cfg.keyOf c) = none) :
    cfg.onReq c = .continue c := by
  simp [Config.onReq, hget]

/-! ## The byte-effects (generic over any config) -/

/-- **Fresh-hit byte-effect (the gate).** On a fresh cache hit the built
pipeline output IS the stored response `render` supplies — for ANY tail and
handler. The handler and every later stage are skipped: the emitted bytes are
the cached bytes, not whatever the upstream would have produced. This rides on
`pipeline_gate_short_circuits`; `build_ofResponse` finalizes the gate's
response. -/
theorem mkStage_hit_serves_stored (cfg : Config) (rest : List Stage)
    (handler : Ctx → Response) (c : Ctx) (e : _root_.Cache.Stored)
    (hget : cfg.st.store.get? (cfg.keyOf c) = some e)
    (hfresh : e.meta.isFresh cfg.now = true) :
    (runPipeline (mkStage cfg :: rest) handler c).build = cfg.render e.body := by
  have hg : (mkStage cfg).onRequest c = .respond (cfg.render e.body) :=
    onReq_hit cfg c e hget hfresh
  rw [pipeline_gate_short_circuits (mkStage cfg) rest handler c (cfg.render e.body) hg,
    build_ofResponse]

/-- **Miss passthrough.** On a cache miss the stage is transparent: the built
pipeline output equals the tail's output — the stored bytes do NOT appear and
the handler's bytes flow through. Rides on `pipeline_stage_effect`; the gate's
identity `onResponse` leaves the threaded builder untouched. -/
theorem mkStage_miss_passthrough (cfg : Config) (rest : List Stage)
    (handler : Ctx → Response) (c : Ctx)
    (hget : cfg.st.store.get? (cfg.keyOf c) = none) :
    runPipeline (mkStage cfg :: rest) handler c = runPipeline rest handler c := by
  have hc : (mkStage cfg).onRequest c = .continue c := onReq_miss cfg c hget
  rw [pipeline_stage_effect (mkStage cfg) rest handler c c hc]
  rfl

/-! ## A concrete deployed stage (real warm cache, real fresh entry) -/

/-- §4.1 key derivation: fold the method / target bytes into the numeric key
components (`vary` empty — no `Vary` selection modeled here). -/
def hashBytes (b : Bytes) : Nat := b.foldl (fun a x => a * 257 + x.toNat + 1) 0

/-- A request's `Cache.Key`: method + target hashed, no `Vary`. -/
def keyOf (c : Ctx) : _root_.Cache.Key :=
  { method := hashBytes c.req.method, uri := hashBytes c.req.target, vary := [] }

/-- Boundary render: the stored response bytes for a cached body token — a
distinctive `cache-hit:<id>` body (so different stored entries render to
different bytes), status 200. -/
def render (body : _root_.Cache.Body) : Response :=
  { status := 200
    reason := reasonOK
    headers := [("x-cache".toUTF8.toList, "HIT".toUTF8.toList)]
    body := "cache-hit:".toUTF8.toList ++ natToDec body.id }

/-- The demo request that is warm in the cache (method `GET`, target `/`, as
explicit ASCII byte lists so the key hash reduces in the kernel). -/
def demoReq : Request :=
  { method := [71, 69, 84], target := [47] }

/-- Its serve context. -/
def demoCtx : Ctx := { input := [], req := demoReq }

/-- A fresh entry: lifetime 100s, age 0 at store time, no validator. At clock 0
its `current_age` is 0 < 100, so `isFresh` holds. -/
def freshMeta : _root_.Cache.Meta :=
  { freshnessLifetime := 100, correctedInitialAge := 0, responseTime := 0, etag := none }

/-- The stored body token for the warm entry. -/
def demoBody : _root_.Cache.Body := { id := 7 }

/-- The warm stored response, keyed exactly at the demo request's key. -/
def demoStored : _root_.Cache.Stored :=
  { key := keyOf demoCtx, body := demoBody, meta := freshMeta }

/-- A warm cache holding the one fresh entry. -/
def warmSt : _root_.Cache.St :=
  { store := { entries := [demoStored], capacity := 8 }, locks := [], pending := [] }

/-- The deployed cache configuration. -/
def cacheCfg : Config := { st := warmSt, keyOf := keyOf, now := 0, render := render }

/-- **The deployed cache stage** appended to `deployStages`. -/
def cacheStage : Stage := mkStage cacheCfg

/-! ## The concrete fresh-hit / miss facts (real `Cache` lib fires) -/

/-- The warm cache's lookup finds the fresh entry for the demo request. -/
theorem warm_get : warmSt.store.get? (keyOf demoCtx) = some demoStored := by
  simp [warmSt, demoStored, _root_.Cache.Store.get?]

/-- The stored entry is fresh at the stage's clock (real §4.2 test). -/
theorem warm_fresh : demoStored.meta.isFresh cacheCfg.now = true := by
  decide

/-- **The concrete byte-effect.** The deployed `cacheStage`, on the warm demo
request, serves EXACTLY the stored `cache-hit:7` response — for any tail and
handler. A fresh hit genuinely changes the emitted bytes to the cached bytes. -/
theorem cacheStage_serves_stored (rest : List Stage) (handler : Ctx → Response) :
    (runPipeline (cacheStage :: rest) handler demoCtx).build = render demoBody :=
  mkStage_hit_serves_stored cacheCfg rest handler demoCtx demoStored warm_get warm_fresh

/-- The served body is the distinctive stored bytes `"cache-hit:7"` — visible in
the built output, independent of the handler. -/
theorem cacheStage_hit_body (rest : List Stage) (handler : Ctx → Response) :
    ((runPipeline (cacheStage :: rest) handler demoCtx).build).body
      = "cache-hit:".toUTF8.toList ++ natToDec 7 := by
  rw [cacheStage_serves_stored]
  rfl

/-- A request not in the warm cache (different target) misses: lookup is none. -/
theorem miss_get :
    warmSt.store.get? (keyOf { input := [], req := { demoReq with target := [47, 111] } })
      = none := by
  have h : _root_.Cache.eqK demoStored.key
      (keyOf { input := [], req := { demoReq with target := [47, 111] } }) = false := by
    decide
  simp [warmSt, _root_.Cache.Store.get?, List.find?_cons, h]

/-- **Concrete miss passthrough.** For the uncached request, `cacheStage` is
transparent — the tail's bytes flow through unchanged. -/
theorem cacheStage_miss (rest : List Stage) (handler : Ctx → Response) :
    runPipeline (cacheStage :: rest) handler
        { input := [], req := { demoReq with target := [47, 111] } }
      = runPipeline rest handler
        { input := [], req := { demoReq with target := [47, 111] } } :=
  mkStage_miss_passthrough cacheCfg rest handler _ miss_get

#print axioms cacheStage_serves_stored
#print axioms cacheStage_hit_body
#print axioms cacheStage_miss

end Reactor.Stage.Cache

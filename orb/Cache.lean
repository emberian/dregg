/-!
# HTTP response cache — a bounded proxy cache with coalescing (RFC 9111)

A sans-IO model of the shared (proxy) HTTP cache described by RFC 9111,
*HTTP Caching*. The cache is a total, pure transition system

    step : St → Input → St × List Eff

over an explicit clock: every input that can consult freshness carries
the current time `now : Nat` (seconds), so the machine holds no clock of
its own — time is data. This matches RFC 9111 §5.6.7's "now" and lets the
freshness/age arithmetic be stated as ordinary theorems about `Nat`.

What is captured, by RFC 9111 section:

* **§4.1 — cache keys.** Entries are keyed by `Key = (method, uri, vary)`.
  The `vary` component is the tuple of selected request-header values the
  origin's Vary field nominates (§4.1); two requests share a stored
  response only if their whole `Key` (including `vary`) is equal. `*` in
  a Vary field is modeled as a `vary` value that never equals a live
  request's, so it always misses.
* **§4.2 / §4.2.1 / §5.2.2.1 — freshness.** A stored entry carries a
  `freshnessLifetime` (the origin's max-age / s-maxage, or Expires−Date
  per §4.2.1 — the boundary computes which; here it is one number) and is
  *fresh* at `now` iff `freshness_lifetime > current_age` (§4.2).
* **§4.2.3 / §5.1 — age.** `mkMeta` computes `corrected_initial_age` from
  `apparent_age = max(0, response_time − date_value)` and
  `corrected_age_value = age_value + response_delay` exactly as §4.2.3;
  `current_age = corrected_initial_age + resident_time`. Nat subtraction
  supplies the `max(0, …)` clamp for free.
* **§4 / §4.2.4 / §4.3 — validation on stale.** A stale entry with an
  entity-tag validator (`ETag`, §4.3) triggers a single conditional
  revalidation (`If-None-Match`); a `304 (Not Modified)` refreshes the
  stored entry's freshness in place (§4.3.3, §4.3.4), resetting its age
  to zero as of the validation time.
* **§4 request collapsing — coalescing.** RFC 9111 §4 permits a cache to
  "collapse requests … combine multiple incoming requests into a single
  forward request upon a cache miss." A per-key lock (`locks`) does this:
  the first miss becomes the *leader* and emits one upstream effect; each
  concurrent miss for the same key becomes a *waiter* (`pending`) and
  emits none. When the upstream response arrives, the leader and all
  waiters are served from that single fetch.
* **§3 (storage bound) — eviction.** The store is bounded by a fixed
  `capacity` and evicts least-recently-used entries: insertion prepends
  and truncates to `capacity`; a hit moves its entry to the front.

The uninterpreted boundary (cf. the `Tls` library's crypto fields): the
machine never decides whether a validator *matches*. Whether a
revalidation returns `304 (Not Modified)` or a full `200` response is
supplied by the environment as the input constructor (`notModified` vs
`upstream`), just as ciphertext outcomes enter `Tls` through named
`Config` functions. The origin's body bytes and validator comparison are
outside the model.

Now discharged (were boundary in the first pass):
* §4.2.2 heuristic freshness — `heuristicLifetime` computes the
  `num/den · (Date − Last-Modified)` fraction; `heuristic_freshness_bounded`
  and `heuristic_le_age` bound it by the document's apparent age.
* §4.2.1 directive-selection precedence — `Directives`/`selectLifetime`
  model `s-maxage > max-age > Expires−Date`; `select_prefers_sMaxAge`,
  `select_maxAge_over_expires`, `select_expires_last` prove the override
  order. (These feed the `freshnessLifetime` the boundary hands to `mkMeta`.)
* §4.4 invalidation by unsafe methods — the `invalidate` input drops every
  entry keyed at the URI; `unsafe_method_invalidates` proves the next lookup
  misses, `invalidate_preserves_other` that unrelated URIs are untouched.

Still boundary / out of scope:
* §5.2 the full Cache-Control directive grammar and HTTP date parsing
  (§4.2 case/zone rules).

## Theorems

* `step_total` / `step_deterministic` — total, functional transition.
* `cache_hit_fresh` — a fresh entry is served with **no upstream call**
  (§4.2): the step emits exactly `serve`, and nothing `isUpstream`.
* `cache_revalidate_stale` — a stale entry with a validator triggers
  **exactly one** revalidation (the step emits exactly `[revalidate k tag]`)
  and takes the per-key lock; `stale_follower_waits` shows a second
  concurrent stale request only waits.
* `coalesce_single_fetch` — **K concurrent misses for one key produce
  exactly one upstream fetch and K−1 waits** (§4 request collapsing).
* `coalesce_single_revalidate` — the same collapsing for stale
  revalidation: K concurrent stale requests ⇒ one revalidate, K−1 waits.
* `upstream_serves_all` / `notModified_serves_all` — the one completion
  serves the leader **and** every coalesced waiter (`waiters + 1` serves).
* `cache_bounded` — the store never exceeds `capacity`, in every
  reachable state.
* Freshness/age accounting: `isFresh_true_iff`, `revalidate_age_zero`
  (a 304 resets age to 0), `revalidate_fresh` (a 304 with positive
  lifetime restores freshness), `currentAge_mono` (age is nondecreasing
  in the clock).
-/

namespace Cache

/-! ## Keys, bodies, freshness metadata -/

/-- A cache key (§4.1): request method, target URI, and the tuple of
selected request-header values nominated by the stored response's Vary
field. All three are opaque identifiers here. A Vary member of `*` is
represented by a `vary` value chosen never to equal a live request's, so
such an entry always misses. -/
structure Key where
  method : Nat
  uri : Nat
  vary : List Nat
deriving Repr, DecidableEq

/-- Opaque response payload token (the body bytes are outside the model). -/
structure Body where
  id : Nat
deriving Repr, DecidableEq

/-- Freshness/validation metadata for a stored response. -/
structure Meta where
  /-- §4.2.1: the response's freshness lifetime in seconds (max-age /
  s-maxage / Expires−Date — the boundary picks which). -/
  freshnessLifetime : Nat
  /-- §4.2.3: `corrected_initial_age`, computed once at store time. -/
  correctedInitialAge : Nat
  /-- §4.2.3: `response_time` — the clock when the response was received
  or last successfully validated. `resident_time = now − response_time`. -/
  responseTime : Nat
  /-- §4.3: entity-tag validator, if the origin supplied an `ETag`. -/
  etag : Option Nat
deriving Repr, DecidableEq

/-- §4.2.3: `current_age = corrected_initial_age + resident_time`, with
`resident_time = now − response_time` (Nat subtraction clamps at 0). -/
def Meta.currentAge (m : Meta) (now : Nat) : Nat :=
  m.correctedInitialAge + (now - m.responseTime)

/-- §4.2: `response_is_fresh = (freshness_lifetime > current_age)`. -/
def Meta.isFresh (m : Meta) (now : Nat) : Bool :=
  decide (m.currentAge now < m.freshnessLifetime)

/-- A stored response: its key, payload, and freshness metadata. -/
structure Stored where
  key : Key
  body : Body
  meta : Meta
deriving Repr

/-- A full response from the origin, as received (§4.2.3 inputs). The
boundary hands `freshnessLifetime` in already resolved from the response
directives. -/
structure Resp where
  body : Body
  /-- §4.2.3 `date_value`: the origin's Date header. -/
  dateValue : Nat
  /-- §5.1 / §4.2.3 `age_value`: the received Age header (0 if absent). -/
  ageValue : Nat
  /-- §4.2.3 `request_time`: clock when the request that produced this
  response was initiated. -/
  requestTime : Nat
  /-- §4.2.1: resolved freshness lifetime. -/
  freshnessLifetime : Nat
  /-- §4.3: entity-tag validator, if present. -/
  etag : Option Nat
deriving Repr

/-- Metadata carried by a `304 (Not Modified)` for §4.3.4 freshening: an
updated freshness lifetime and (possibly refreshed) validator. -/
structure Upd where
  freshnessLifetime : Nat
  etag : Option Nat
deriving Repr

/-- §4.2.3: build stored metadata from a received response.
`response_time` is the clock at receipt.

    apparent_age        = max(0, response_time − date_value)
    response_delay      = response_time − request_time
    corrected_age_value = age_value + response_delay
    corrected_initial_age = max(apparent_age, corrected_age_value)

Nat subtraction realizes each `max(0, …)`. -/
def mkMeta (r : Resp) (responseTime : Nat) : Meta :=
  let apparentAge := responseTime - r.dateValue
  let responseDelay := responseTime - r.requestTime
  let correctedAgeValue := r.ageValue + responseDelay
  { freshnessLifetime := r.freshnessLifetime
    correctedInitialAge := max apparentAge correctedAgeValue
    responseTime := responseTime
    etag := r.etag }

def mkStored (k : Key) (r : Resp) (responseTime : Nat) : Stored :=
  { key := k, body := r.body, meta := mkMeta r responseTime }

/-- §4.3.4: freshen metadata on a `304`. The response was just validated,
so its age resets to 0 as of `now`; the freshness lifetime and validator
are taken from the 304 (§3.2 header update). -/
def Meta.revalidate (_m : Meta) (upd : Upd) (now : Nat) : Meta :=
  { freshnessLifetime := upd.freshnessLifetime
    correctedInitialAge := 0
    responseTime := now
    etag := upd.etag }

/-! ## Key equality as a Bool (avoids BEq lawfulness plumbing) -/

/-- Decidable key equality reflected to `Bool`. -/
def eqK (a b : Key) : Bool := decide (a = b)

@[simp] theorem eqK_refl (a : Key) : eqK a a = true := by simp [eqK]

theorem eqK_true {a b : Key} (h : eqK a b = true) : a = b := by
  simpa [eqK] using h

/-! ## The bounded LRU store -/

/-- A capacity-bounded store, most-recently-used first. -/
structure Store where
  entries : List Stored
  capacity : Nat
deriving Repr

/-- Look up the stored response for a key (§4.1 exact-key match). -/
def Store.get? (s : Store) (k : Key) : Option Stored :=
  s.entries.find? (fun e => eqK e.key k)

/-- Insert/replace, LRU: drop any existing entry for the key, prepend the
new one, and truncate to `capacity` — evicting the least-recently-used
tail (§3 storage bound). -/
def Store.insert (s : Store) (e : Stored) : Store :=
  { s with entries := (e :: s.entries.filter (fun x => !eqK x.key e.key)).take s.capacity }

/-- A hit moves the entry to the front (LRU recency). Truncation keeps the
result within `capacity`. -/
def Store.touch (s : Store) (k : Key) : Store :=
  match s.get? k with
  | some e => { s with entries := (e :: s.entries.filter (fun x => !eqK x.key k)).take s.capacity }
  | none => s

/-- §4.3.4: apply a 304 freshening to the entry(ies) for a key. -/
def Store.refresh (s : Store) (k : Key) (upd : Upd) (now : Nat) : Store :=
  { s with entries := s.entries.map (fun e =>
      if eqK e.key k = true then { e with meta := e.meta.revalidate upd now } else e) }

/-- §4.4 invalidation: drop every stored entry whose target URI is `uri`,
regardless of method or `vary`. An unsafe request (POST/PUT/DELETE) to a URI
invalidates *all* cached responses keyed at that URI (§4.4: "the URI(s) in
… the request target"). -/
def Store.invalidate (s : Store) (uri : Nat) : Store :=
  { s with entries := s.entries.filter (fun e => !decide (e.key.uri = uri)) }

/-! ## Machine effects, inputs, and state -/

/-- Observable effects of one step. -/
inductive Eff where
  /-- An unconditional upstream fetch (a cache miss forwards). -/
  | fetch (k : Key)
  /-- A conditional upstream revalidation, `If-None-Match: tag` (§4.3.1). -/
  | revalidate (k : Key) (tag : Nat)
  /-- A response served to a client (leader or a coalesced waiter). -/
  | serve (k : Key) (body : Body)
  /-- A request parked as a coalesced waiter behind an in-flight fetch. -/
  | wait (k : Key)
deriving Repr, DecidableEq

/-- `true` on effects that contact the origin (fetch or revalidate). -/
def Eff.isUpstream : Eff → Bool
  | .fetch _ => true
  | .revalidate _ _ => true
  | _ => false

def Eff.isFetch : Eff → Bool
  | .fetch _ => true
  | _ => false

def Eff.isRevalidate : Eff → Bool
  | .revalidate _ _ => true
  | _ => false

def Eff.isWait : Eff → Bool
  | .wait _ => true
  | _ => false

/-- Inputs. Every freshness-consulting input carries the clock `now`. -/
inductive Input where
  /-- A client requests `k` at time `now`. -/
  | request (k : Key) (now : Nat)
  /-- The upstream fetch/revalidation for `k` returned a full response. -/
  | upstream (k : Key) (r : Resp) (now : Nat)
  /-- The revalidation for `k` returned `304 (Not Modified)` (§4.3.3). -/
  | notModified (k : Key) (upd : Upd) (now : Nat)
  /-- §4.4: an unsafe method (POST/PUT/DELETE) was forwarded to `uri`; its
  non-error response invalidates every cached entry keyed at that URI. -/
  | invalidate (uri : Nat) (now : Nat)
deriving Repr

/-- Machine state: the bounded store, the set of keys with an in-flight
upstream request (`locks`), and the bag of parked waiters (`pending`; the
number of occurrences of `k` is the count of coalesced waiters for `k`). -/
structure St where
  store : Store
  locks : List Key
  pending : List Key
deriving Repr

/-- `true` iff an upstream request for `k` is already in flight. -/
def St.locked (s : St) (k : Key) : Bool := s.locks.any (fun x => eqK x k)

/-- Initial empty state with the given capacity. -/
def init (cap : Nat) : St :=
  { store := { entries := [], capacity := cap }, locks := [], pending := [] }

/-! ## The transition -/

/-- The total, pure step. -/
def step (s : St) : Input → St × List Eff
  | .request k now =>
    match s.store.get? k with
    | some e =>
      if e.meta.isFresh now = true then
        -- §4.2 fresh hit: serve without contacting the origin.
        ({ s with store := s.store.touch k }, [Eff.serve k e.body])
      else if s.locked k = true then
        -- stale, but a revalidation is already in flight: coalesce.
        ({ s with pending := k :: s.pending }, [Eff.wait k])
      else
        -- stale leader: revalidate with the validator if we have one,
        -- else a plain conditional-less refetch (§4.3 / §4.2.4).
        match e.meta.etag with
        | some tag => ({ s with locks := k :: s.locks }, [Eff.revalidate k tag])
        | none => ({ s with locks := k :: s.locks }, [Eff.fetch k])
    | none =>
      if s.locked k = true then
        -- miss, but a fetch for this key is already in flight: coalesce.
        ({ s with pending := k :: s.pending }, [Eff.wait k])
      else
        -- miss leader: one upstream fetch (§4 request collapsing).
        ({ s with locks := k :: s.locks }, [Eff.fetch k])
  | .upstream k r now =>
    if s.locked k = true then
      -- store the response and serve the leader + every coalesced waiter
      -- from this single fetch; release the lock.
      ({ store := s.store.insert (mkStored k r now)
         locks := s.locks.erase k
         pending := s.pending.filter (fun x => !eqK x k) },
       List.replicate (s.pending.countP (fun x => eqK x k) + 1) (Eff.serve k r.body))
    else
      (s, [])
  | .notModified k upd now =>
    match s.store.get? k with
    | some e =>
      if s.locked k = true then
        -- §4.3.4 freshen in place, serve leader + waiters, release lock.
        ({ store := s.store.refresh k upd now
           locks := s.locks.erase k
           pending := s.pending.filter (fun x => !eqK x k) },
         List.replicate (s.pending.countP (fun x => eqK x k) + 1) (Eff.serve k e.body))
      else (s, [])
    | none => (s, [])
  | .invalidate uri _ =>
    -- §4.4: drop every cached entry at this URI. No client-facing effect: the
    -- unsafe method's own response is forwarded outside the cache model.
    ({ s with store := s.store.invalidate uri }, [])

/-- The induced step relation. -/
def Steps (s : St) (i : Input) (s' : St) (e : List Eff) : Prop :=
  step s i = (s', e)

/-- Fold the step over an input trace, flattening every step's effects. -/
def runEffs (s : St) : List Input → List Eff
  | [] => []
  | i :: is => (step s i).2 ++ runEffs (step s i).1 is

/-- `n` concurrent requests for one key at one instant. -/
def reqs (k : Key) (now n : Nat) : List Input :=
  List.replicate n (Input.request k now)

/-- Count the effects satisfying a predicate. -/
def countE (p : Eff → Bool) (es : List Eff) : Nat := (es.filter p).length

/-- States reachable from some initial state. -/
inductive Reachable : St → Prop where
  | init (cap : Nat) : Reachable (init cap)
  | step (s : St) (i : Input) : Reachable s → Reachable (step s i).1

/-! ## Totality and determinism -/

theorem step_total (s : St) (i : Input) : ∃ s' e, Steps s i s' e :=
  ⟨(step s i).1, (step s i).2, rfl⟩

theorem step_deterministic (s : St) (i : Input)
    {s₁ s₂ : St} {e₁ e₂ : List Eff}
    (h₁ : Steps s i s₁ e₁) (h₂ : Steps s i s₂ e₂) :
    s₁ = s₂ ∧ e₁ = e₂ := by
  have h := h₁.symm.trans h₂
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

/-! ## Freshness and age accounting (§4.2, §4.2.3) -/

theorem isFresh_true_iff (m : Meta) (now : Nat) :
    m.isFresh now = true ↔ m.currentAge now < m.freshnessLifetime := by
  simp [Meta.isFresh]

/-- A 304 resets the entry's age to 0 as of the validation instant. -/
theorem revalidate_age_zero (m : Meta) (upd : Upd) (now : Nat) :
    (m.revalidate upd now).currentAge now = 0 := by
  simp [Meta.revalidate, Meta.currentAge]

/-- §4.3.4: a 304 with a positive freshness lifetime restores freshness. -/
theorem revalidate_fresh (m : Meta) (upd : Upd) (now : Nat)
    (h : 0 < upd.freshnessLifetime) :
    (m.revalidate upd now).isFresh now = true := by
  rw [isFresh_true_iff, revalidate_age_zero]
  exact h

/-- Age is nondecreasing in the clock (fixed metadata). -/
theorem currentAge_mono (m : Meta) {t₁ t₂ : Nat} (h : t₁ ≤ t₂) :
    m.currentAge t₁ ≤ m.currentAge t₂ := by
  simp only [Meta.currentAge]
  exact Nat.add_le_add_left (Nat.sub_le_sub_right h _) _

/-! ## Cache hit: fresh entries never contact the origin (§4.2) -/

/-- **A fresh entry is served without any upstream call.** The step for a
request whose key has a fresh stored response emits exactly one `serve`
(the stored body) and no origin-contacting effect. -/
theorem cache_hit_fresh (s : St) (k : Key) (now : Nat) (e : Stored)
    (hget : s.store.get? k = some e) (hfresh : e.meta.isFresh now = true) :
    (step s (.request k now)).2 = [Eff.serve k e.body] ∧
    (∀ o ∈ (step s (.request k now)).2, o.isUpstream = false) := by
  have h2 : (step s (.request k now)).2 = [Eff.serve k e.body] := by
    simp [step, hget, hfresh]
  refine ⟨h2, ?_⟩
  intro o ho
  rw [h2] at ho
  simp only [List.mem_singleton] at ho
  subst ho
  rfl

/-! ## Reduction lemmas for the request cases (feed the trace proofs) -/

theorem step_miss_unlocked (s : St) (k : Key) (now : Nat)
    (hget : s.store.get? k = none) (hlock : s.locked k = false) :
    step s (.request k now) = ({ s with locks := k :: s.locks }, [Eff.fetch k]) := by
  simp [step, hget, hlock]

theorem step_miss_locked (s : St) (k : Key) (now : Nat)
    (hget : s.store.get? k = none) (hlock : s.locked k = true) :
    step s (.request k now) = ({ s with pending := k :: s.pending }, [Eff.wait k]) := by
  simp [step, hget, hlock]

theorem step_stale_unlocked_etag (s : St) (k : Key) (now : Nat) (e : Stored) (tag : Nat)
    (hget : s.store.get? k = some e) (hfresh : e.meta.isFresh now = false)
    (hetag : e.meta.etag = some tag) (hlock : s.locked k = false) :
    step s (.request k now) = ({ s with locks := k :: s.locks }, [Eff.revalidate k tag]) := by
  simp [step, hget, hfresh, hlock, hetag]

theorem step_stale_locked (s : St) (k : Key) (now : Nat) (e : Stored)
    (hget : s.store.get? k = some e) (hfresh : e.meta.isFresh now = false)
    (hlock : s.locked k = true) :
    step s (.request k now) = ({ s with pending := k :: s.pending }, [Eff.wait k]) := by
  simp [step, hget, hfresh, hlock]

/-- Taking a fresh lock makes the key locked. -/
theorem locked_cons_self (s : St) (k : Key) :
    ({ s with locks := k :: s.locks } : St).locked k = true := by
  simp [St.locked, List.any_cons]

/-! ## Revalidation on stale (§4.2.4, §4.3) -/

/-- **A stale entry with a validator triggers exactly one revalidation.**
The leader step emits precisely `[revalidate k tag]` — one origin
contact — and takes the per-key lock. -/
theorem cache_revalidate_stale (s : St) (k : Key) (now : Nat) (e : Stored) (tag : Nat)
    (hget : s.store.get? k = some e) (hfresh : e.meta.isFresh now = false)
    (hetag : e.meta.etag = some tag) (hlock : s.locked k = false) :
    (step s (.request k now)).2 = [Eff.revalidate k tag] ∧
    (step s (.request k now)).1.locked k = true := by
  rw [step_stale_unlocked_etag s k now e tag hget hfresh hetag hlock]
  exact ⟨rfl, locked_cons_self s k⟩

/-- A second, concurrent stale request only waits — it does not launch a
second revalidation. -/
theorem stale_follower_waits (s : St) (k : Key) (now : Nat) (e : Stored)
    (hget : s.store.get? k = some e) (hfresh : e.meta.isFresh now = false)
    (hlock : s.locked k = true) :
    (step s (.request k now)).2 = [Eff.wait k] := by
  rw [step_stale_locked s k now e hget hfresh hlock]

/-! ## Coalescing: one upstream call for K concurrent requests (§4) -/

theorem countE_append (p : Eff → Bool) (a b : List Eff) :
    countE p (a ++ b) = countE p a + countE p b := by
  simp [countE, List.filter_append, List.length_append]

/-- A run of `m` requests, each of which is a coalesced follower (its step
emits exactly `[wait k]` and preserves the follower predicate `P`), counts
zero upstream fetches and exactly `m` waits. Parameterizing over `P` lets
this serve both the miss and the stale coalescing proofs. -/
theorem all_wait_run (k : Key) (now : Nat) (P : St → Prop)
    (hstep : ∀ t, P t → (step t (.request k now)).2 = [Eff.wait k]
                        ∧ P (step t (.request k now)).1) :
    ∀ (m : Nat) (t : St), P t →
      countE Eff.isFetch (runEffs t (reqs k now m)) = 0 ∧
      countE Eff.isRevalidate (runEffs t (reqs k now m)) = 0 ∧
      countE Eff.isWait (runEffs t (reqs k now m)) = m := by
  intro m
  induction m with
  | zero => intro t _; simp [reqs, runEffs, countE]
  | succ m ih =>
    intro t ht
    obtain ⟨he, hP⟩ := hstep t ht
    have hcons : runEffs t (reqs k now (m + 1))
        = (step t (.request k now)).2
          ++ runEffs (step t (.request k now)).1 (reqs k now m) := by
      simp [reqs, List.replicate_succ, runEffs]
    obtain ⟨hf, hr, hw⟩ := ih _ hP
    have hwF : countE Eff.isFetch [Eff.wait k] = 0 := rfl
    have hwR : countE Eff.isRevalidate [Eff.wait k] = 0 := rfl
    have hwW : countE Eff.isWait [Eff.wait k] = 1 := rfl
    rw [hcons, he]
    refine ⟨?_, ?_, ?_⟩
    · rw [countE_append, hwF, hf]
    · rw [countE_append, hwR, hr]
    · rw [countE_append, hwW, hw]; omega

/-- The follower predicate for a miss: no stored entry, and the key is
already locked. Preserved by every follower step (which touches only
`pending`). -/
theorem coalesce_single_fetch (s : St) (k : Key) (now n : Nat)
    (hn : 0 < n) (hget : s.store.get? k = none) (hlock : s.locked k = false) :
    countE Eff.isFetch (runEffs s (reqs k now n)) = 1 ∧
    countE Eff.isWait (runEffs s (reqs k now n)) = n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- The follower invariant for the tail run.
  let P : St → Prop := fun t => t.store.get? k = none ∧ t.locked k = true
  have hfollow : ∀ t, P t → (step t (.request k now)).2 = [Eff.wait k]
                          ∧ P (step t (.request k now)).1 := by
    intro t ht
    rw [step_miss_locked t k now ht.1 ht.2]
    exact ⟨rfl, ht.1, ht.2⟩
  -- First (leader) step, then the all-wait tail.
  have hcons : runEffs s (reqs k now (m + 1))
      = [Eff.fetch k] ++ runEffs { s with locks := k :: s.locks } (reqs k now m) := by
    simp only [reqs, List.replicate_succ, runEffs]
    rw [step_miss_unlocked s k now hget hlock]
  have hP : P { s with locks := k :: s.locks } :=
    ⟨hget, locked_cons_self s k⟩
  obtain ⟨hf, _, hw⟩ := all_wait_run k now P hfollow m { s with locks := k :: s.locks } hP
  have hF1 : countE Eff.isFetch [Eff.fetch k] = 1 := rfl
  have hW0 : countE Eff.isWait [Eff.fetch k] = 0 := rfl
  rw [hcons]
  refine ⟨?_, ?_⟩
  · rw [countE_append, hF1, hf]
  · rw [countE_append, hW0, hw]; omega

/-- The same collapsing for revalidation: K concurrent **stale** requests
for one key (validator present, lock free) produce exactly one revalidate
and K−1 waits. -/
theorem coalesce_single_revalidate (s : St) (k : Key) (now n : Nat) (e : Stored) (tag : Nat)
    (hn : 0 < n) (hget : s.store.get? k = some e) (hfresh : e.meta.isFresh now = false)
    (hetag : e.meta.etag = some tag) (hlock : s.locked k = false) :
    countE Eff.isRevalidate (runEffs s (reqs k now n)) = 1 ∧
    countE Eff.isWait (runEffs s (reqs k now n)) = n - 1 := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  -- The follower invariant: the same stale entry is still stored, locked.
  let P : St → Prop := fun t =>
    t.store.get? k = some e ∧ e.meta.isFresh now = false ∧ t.locked k = true
  have hfollow : ∀ t, P t → (step t (.request k now)).2 = [Eff.wait k]
                          ∧ P (step t (.request k now)).1 := by
    intro t ht
    obtain ⟨hg, hs, hl⟩ := ht
    rw [step_stale_locked t k now e hg hs hl]
    exact ⟨rfl, hg, hs, hl⟩
  have hcons : runEffs s (reqs k now (m + 1))
      = [Eff.revalidate k tag] ++ runEffs { s with locks := k :: s.locks } (reqs k now m) := by
    simp only [reqs, List.replicate_succ, runEffs]
    rw [step_stale_unlocked_etag s k now e tag hget hfresh hetag hlock]
  have hP : P { s with locks := k :: s.locks } :=
    ⟨hget, hfresh, locked_cons_self s k⟩
  obtain ⟨_, hr, hw⟩ := all_wait_run k now P hfollow m { s with locks := k :: s.locks } hP
  have hR1 : countE Eff.isRevalidate [Eff.revalidate k tag] = 1 := rfl
  have hW0 : countE Eff.isWait [Eff.revalidate k tag] = 0 := rfl
  rw [hcons]
  refine ⟨?_, ?_⟩
  · rw [countE_append, hR1, hr]
  · rw [countE_append, hW0, hw]; omega

/-! ## Completion serves everyone waiting behind the one fetch (§4) -/

/-- An upstream completion serves the leader **and** every coalesced
waiter: exactly `pending.count k + 1` `serve` effects come out of the one
fetch. -/
theorem upstream_serves_all (s : St) (k : Key) (r : Resp) (now : Nat)
    (hlock : s.locked k = true) :
    (step s (.upstream k r now)).2
      = List.replicate (s.pending.countP (fun x => eqK x k) + 1) (Eff.serve k r.body) := by
  simp [step, hlock]

/-- A 304 completion likewise serves the leader and all waiters from the
stored (now-freshened) body. -/
theorem notModified_serves_all (s : St) (k : Key) (upd : Upd) (now : Nat) (e : Stored)
    (hget : s.store.get? k = some e) (hlock : s.locked k = true) :
    (step s (.notModified k upd now)).2
      = List.replicate (s.pending.countP (fun x => eqK x k) + 1) (Eff.serve k e.body) := by
  simp [step, hget, hlock]

/-! ## The store never exceeds capacity (§3 storage bound) -/

/-- The bound invariant. -/
def Bounded (s : St) : Prop := s.store.entries.length ≤ s.store.capacity

theorem Store.insert_len (s : Store) (e : Stored) :
    (s.insert e).entries.length ≤ (s.insert e).capacity := by
  simp only [Store.insert, List.length_take]
  exact Nat.min_le_left _ _

theorem Store.touch_len (s : Store) (k : Key)
    (h : s.entries.length ≤ s.capacity) :
    (s.touch k).entries.length ≤ (s.touch k).capacity := by
  unfold Store.touch
  split
  · simp only [List.length_take]; exact Nat.min_le_left _ _
  · exact h

theorem Store.refresh_len (s : Store) (k : Key) (upd : Upd) (now : Nat) :
    (s.refresh k upd now).entries.length = s.entries.length := by
  simp [Store.refresh]

theorem Store.invalidate_len (s : Store) (uri : Nat)
    (h : s.entries.length ≤ s.capacity) :
    (s.invalidate uri).entries.length ≤ (s.invalidate uri).capacity := by
  simp only [Store.invalidate]
  exact Nat.le_trans (List.length_filter_le _ _) h

theorem bounded_init (cap : Nat) : Bounded (init cap) := by
  simp [Bounded, init]

/-- Every step keeps the store within capacity. -/
theorem step_bounded (s : St) (i : Input) (h : Bounded s) : Bounded (step s i).1 := by
  unfold Bounded at h ⊢
  cases i with
  | request k now =>
    simp only [step]
    split
    · split
      · exact Store.touch_len s.store k h
      · split
        · exact h
        · split <;> exact h
    · split <;> exact h
  | upstream k r now =>
    simp only [step]
    split
    · exact Store.insert_len s.store _
    · exact h
  | notModified k upd now =>
    simp only [step]
    split
    · split
      · show (s.store.refresh k upd now).entries.length ≤ (s.store.refresh k upd now).capacity
        rw [Store.refresh_len]; exact h
      · exact h
    · exact h
  | invalidate uri now =>
    simp only [step]
    exact Store.invalidate_len s.store uri h

/-- **The store never exceeds capacity**, in every reachable state. -/
theorem cache_bounded {s : St} (h : Reachable s) : Bounded s := by
  induction h with
  | init cap => exact bounded_init cap
  | step s i _ ih => exact step_bounded s i ih

/-! ## Heuristic freshness (§4.2.2)

When no explicit freshness (no `max-age`/`s-maxage`, no `Expires`) is present, a
cache MAY assign a heuristic freshness lifetime. The common heuristic (RFC 9111
§4.2.2, and the "10% of the document's age" rule the RFC's example describes) is
a fixed *fraction* — `num/den` — of the document's age at storage,
`Date − Last-Modified`. The engine's boundary decides *whether* to apply a
heuristic; the arithmetic (and its bound) is proven here so the resulting
`freshnessLifetime` handed to `mkMeta` is a checked quantity, not a guess. -/

/-- §4.2.2 heuristic lifetime: `⌊(Date − Last-Modified) · num / den⌋`. With
`num = 1, den = 10` this is the 10% rule. Nat subtraction clamps a
`Last-Modified` in the future to a zero age. -/
def heuristicLifetime (num den dateValue lastModified : Nat) : Nat :=
  ((dateValue - lastModified) * num) / den

/-- **`heuristic_freshness_bounded`.** The heuristic lifetime never exceeds the
`num/den` fraction of the document's apparent age: `lifetime · den ≤ age · num`.
In particular a `≤ 100%` fraction (`num ≤ den`) yields a lifetime no larger than
the document's own age — the §4.2.2 sanity property (a heuristic freshness must
not outrun the evidence it is derived from). -/
theorem heuristic_freshness_bounded (num den dateValue lastModified : Nat) :
    heuristicLifetime num den dateValue lastModified * den
      ≤ (dateValue - lastModified) * num := by
  unfold heuristicLifetime
  exact Nat.div_mul_le_self _ _

/-- The `num ≤ den` corollary: a heuristic freshness lifetime is at most the
document's apparent age (`Expires` never exceeds the evidence). Holds even for
`den = 0`, where Nat division yields `0`. -/
theorem heuristic_le_age (num den dateValue lastModified : Nat)
    (hfrac : num ≤ den) :
    heuristicLifetime num den dateValue lastModified ≤ dateValue - lastModified := by
  unfold heuristicLifetime
  apply Nat.div_le_of_le_mul
  calc (dateValue - lastModified) * num
      ≤ (dateValue - lastModified) * den := Nat.mul_le_mul (Nat.le_refl _) hfrac
    _ = den * (dateValue - lastModified) := Nat.mul_comm _ _

/-! ## Explicit-freshness directive precedence (§4.2.1)

When explicit freshness *is* present, §4.2.1 fixes the precedence a shared cache
uses: `s-maxage` overrides `max-age`, and either overrides an `Expires − Date`.
The higher-priority directive wins outright (§4.2.1: a shared cache "MUST ignore
the Expires and max-age … when the s-maxage directive is present"). -/

/-- The freshness-bearing response directives a shared cache reads (§5.2.2). Each
is optional; `expiresMinusDate` is the already-computed `Expires − Date` age. -/
structure Directives where
  sMaxAge : Option Nat
  maxAge : Option Nat
  expiresMinusDate : Option Nat
deriving Repr, DecidableEq

/-- §4.2.1 selection for a shared cache: `s-maxage`, else `max-age`, else
`Expires − Date`, else no explicit lifetime (heuristic territory). -/
def selectLifetime (d : Directives) : Option Nat :=
  match d.sMaxAge with
  | some s => some s
  | none => match d.maxAge with
      | some m => some m
      | none => d.expiresMinusDate

/-- **`s-maxage` overrides everything** (§4.2.1). -/
theorem select_prefers_sMaxAge (d : Directives) (s : Nat) (h : d.sMaxAge = some s) :
    selectLifetime d = some s := by
  simp [selectLifetime, h]

/-- Absent `s-maxage`, `max-age` overrides `Expires` (§4.2.1). -/
theorem select_maxAge_over_expires (d : Directives) (m : Nat)
    (h0 : d.sMaxAge = none) (h1 : d.maxAge = some m) :
    selectLifetime d = some m := by
  simp [selectLifetime, h0, h1]

/-- Absent both `s-maxage` and `max-age`, `Expires − Date` is used (§4.2.1). -/
theorem select_expires_last (d : Directives)
    (h0 : d.sMaxAge = none) (h1 : d.maxAge = none) :
    selectLifetime d = d.expiresMinusDate := by
  simp [selectLifetime, h0, h1]

/-! ## Unsafe-method invalidation (§4.4)

A non-error response to an unsafe request method (POST, PUT, DELETE, …) at a URI
invalidates the cache's stored responses for that URI. The `invalidate` input
drops every entry keyed there; the next request for the URI is therefore a
miss. -/

/-- Key equality forces URI equality. -/
theorem eqK_uri {a b : Key} (h : eqK a b = true) : a.uri = b.uri := by
  rw [eqK_true h]

/-- **`unsafe_method_invalidates`.** After an unsafe-method invalidation for
`uri`, *no* cached entry keyed at that URI survives: `get?` for any key with
that URI misses, whatever its method or `vary`. -/
theorem unsafe_method_invalidates (s : St) (uri now : Nat) (k : Key)
    (hk : k.uri = uri) :
    (step s (.invalidate uri now)).1.store.get? k = none := by
  simp only [step, Store.get?, Store.invalidate]
  rw [List.find?_eq_none]
  intro e he
  -- `e` survived the filter, so its URI is not `uri`; but `k.uri = uri`, so
  -- `e.key ≠ k`, hence the key-equality test is false.
  rw [List.mem_filter] at he
  obtain ⟨_, hsurv⟩ := he
  simp only [Bool.not_eq_true', decide_eq_false_iff_not] at hsurv
  -- goal: ¬ eqK e.key k = true. If it matched, e.key.uri = k.uri = uri, but e
  -- survived the filter, so e.key.uri ≠ uri.
  intro hcon
  exact hsurv ((eqK_uri hcon).trans hk)

/-- Invalidation is monotone and targeted: it removes only entries at the named
URI, so any key whose URI differs is untouched (its lookup is unchanged). -/
theorem invalidate_preserves_other (s : St) (uri now : Nat) (k : Key)
    (hk : ¬ k.uri = uri) :
    (step s (.invalidate uri now)).1.store.get? k = s.store.get? k := by
  simp only [step, Store.get?, Store.invalidate]
  induction s.store.entries with
  | nil => rfl
  | cons e rest ih =>
    -- If `e` matched `k` it would share `k`'s URI, which is not `uri`; so a
    -- kept-or-dropped `e` never affects the `k` lookup.
    have hkey_of : e.key.uri = uri → eqK e.key k = false := by
      intro hd
      cases hc : eqK e.key k with
      | false => rfl
      | true => exact absurd ((eqK_uri hc).symm.trans hd) hk
    rw [List.filter_cons]
    by_cases hd : e.key.uri = uri
    · rw [if_neg (by simp [hd]), List.find?_cons, hkey_of hd, ih]
    · rw [if_pos (by simp [hd]), List.find?_cons, List.find?_cons, ih]

end Cache

#print axioms Cache.heuristic_freshness_bounded
#print axioms Cache.heuristic_le_age
#print axioms Cache.select_prefers_sMaxAge
#print axioms Cache.unsafe_method_invalidates
#print axioms Cache.invalidate_preserves_other
#print axioms Cache.cache_bounded

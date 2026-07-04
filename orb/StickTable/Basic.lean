/-
StickTable — a keyed cross-request counter table as a sequential transition
system over an explicit clock (the per-shard view).

A stick table pins a key (a client IP, a header value, a cookie — here all
abstracted to `Nat`) to a small record of accounting state: a request counter
and a last-seen timestamp.  A request `track`s its key, bumping the counter and
refreshing last-seen; a `lookup` reads the entry back subject to TTL; expired
entries are evicted.  This is the state behind per-key rate aggregation and
session stickiness across requests.

Convention: time is an input.  There is no ambient clock.  Every transition and
query that depends on time takes the current clock reading `now` as an explicit
argument.  The last-seen refresh is written `max e.lastSeen now`, so the recorded
time never moves backward even on a stale (out-of-order) reading — the model
*enforces* the monotone-time discipline rather than assuming it, exactly as the
token bucket's refill stutters on a backward clock.  Under a genuinely monotone
clock (`e.lastSeen ≤ now`) the `max` collapses to `now`, matching the reference
`touch` that stores the current time unconditionally.

State:

  * `Entry { count, lastSeen }` — the per-key accounting record.
  * `Table := List (Nat × Entry)` — an association list keyed by `Nat`.  The
    finite-map view: order is immaterial once keys are unique (`Wf`).

This file is the SEQUENTIAL (per-shard) model.  The cross-shard concurrent merge
— the global counter is the per-key sum / last-seen max over shards, and the
observed concurrent execution must linearize to this sequential model — is a
named obligation **CR-2** stated in `StickTable.Shard` and in the notes.  It is
evidence-under-net, not a chain proof, and is deliberately NOT discharged here:
this model contains no concurrency.

Transitions / queries:

  * `bump k now` (a.k.a. `track`) — increment `k`'s counter by one and refresh
    its last-seen to `max old now`; create the entry (counter `1`, last-seen
    `now`) if `k` is absent.  No other key is touched.
  * `lookup k ttl now` — read `k`'s entry, returning it only if it is still live
    (`now < lastSeen + ttl`); an entry past its TTL reads back as absent.
  * `evict ttl now` — drop every entry past its TTL.

Theorems proved here (per step):

  1. `bump_getCount_self` / `bump_getCount_other` / `bump_find_other` — `track`
     increments exactly the tracked key's counter by one, refreshes its
     last-seen, and changes no other key.
  2. `lookup_expired` / `evict_removes_expired` / `evict_preserves_live` — an
     entry past its TTL is not returned by `lookup` and is removed by `evict`;
     a live entry survives.
  3. `Wf_nil` / `bump_Wf` / `evict_Wf` — the table stays a finite key-unique map.
  4. `bump_getLastSeen_mono` — last-seen never moves backward under a bump
     (lifted over traces in `StickTable.Trace`).

The counting bound (theorem 5) and the trace-level monotone-time lift live in
`StickTable.Trace`; the cross-shard merge and CR-2 live in `StickTable.Shard`.
-/

namespace StickTable

/-- Library version. -/
def version : String := "0.1.0"

/-- The per-key accounting record: a request counter and a last-seen timestamp
(clock units). -/
structure Entry where
  /-- Number of `track` events recorded for this key. -/
  count : Nat
  /-- Clock value at the most recent `track` on this key. -/
  lastSeen : Nat
deriving Repr, DecidableEq

/-- A stick table: an association list from key (`Nat`) to `Entry`.  The
finite-map view — a `List`, hence finite; key-unique under `Wf`. -/
abbrev Table := List (Nat × Entry)

/-- The keys currently present, in table order. -/
def keys (t : Table) : List Nat := t.map Prod.fst

/-- Well-formedness: keys are unique.  Together with `Table` being a `List`
(finite) this is the finite key-unique map invariant. -/
def Wf (t : Table) : Prop := (keys t).Nodup

/-- Look up a key's entry, scanning left to right.  Under `Wf` the first match
is the only match, so scan order is immaterial. -/
def find (k : Nat) : Table → Option Entry
  | [] => none
  | (k', e) :: rest => if k' = k then some e else find k rest

/-- The current counter for `k` (`0` if absent). -/
def getCount (k : Nat) (t : Table) : Nat := (find k t).elim 0 Entry.count

/-- The current last-seen for `k` (`0` if absent). -/
def getLastSeen (k : Nat) (t : Table) : Nat := (find k t).elim 0 Entry.lastSeen

/-- **`track`**: record a request for `k` at clock `now`.  Increment `k`'s
counter by one and refresh its last-seen to `max old now`; if `k` is absent,
create the entry with counter `1` and last-seen `now`.  The `max` is what
enforces monotone time on a stale reading. -/
def bump (k now : Nat) : Table → Table
  | [] => [(k, ⟨1, now⟩)]
  | (k', e) :: rest =>
      if k' = k then (k', ⟨e.count + 1, max e.lastSeen now⟩) :: rest
      else (k', e) :: bump k now rest

/-- `track` is `bump` — the request-facing name. -/
abbrev track (k now : Nat) (t : Table) : Table := bump k now t

/-- Whether an entry is still live at clock `now` under time-to-idle `ttl`:
the idle span `now - lastSeen` is under `ttl`, i.e. `now < lastSeen + ttl`. -/
def live (ttl now : Nat) (e : Entry) : Bool := decide (now < e.lastSeen + ttl)

/-- **`lookup`**: read `k`'s entry, but only if it is still live.  An entry past
its TTL reads back as absent. -/
def lookup (k ttl now : Nat) (t : Table) : Option Entry :=
  match find k t with
  | some e => if live ttl now e then some e else none
  | none => none

/-- **`evict`**: drop every entry past its TTL at clock `now`. -/
def evict (ttl now : Nat) (t : Table) : Table :=
  t.filter (fun p => live ttl now p.2)

/-! ### Basic membership / lookup lemmas -/

/-- A found entry is a genuine member of the table. -/
theorem find_mem {k : Nat} {t : Table} {e : Entry} (h : find k t = some e) :
    (k, e) ∈ t := by
  induction t with
  | nil => simp [find] at h
  | cons p rest ih =>
    obtain ⟨k', e'⟩ := p
    simp only [find] at h
    by_cases hk : k' = k
    · rw [if_pos hk] at h
      injection h with he; subst he; subst hk
      exact List.mem_cons_self _ _
    · rw [if_neg hk] at h
      exact List.mem_cons_of_mem _ (ih h)

/-- Absent key ⇒ failed lookup. -/
theorem find_none_of_not_mem_keys {k : Nat} {t : Table} (h : k ∉ keys t) :
    find k t = none := by
  induction t with
  | nil => rfl
  | cons p rest ih =>
    obtain ⟨k', e⟩ := p
    simp only [keys, List.map_cons, List.mem_cons, not_or] at h
    obtain ⟨hne, hrest⟩ := h
    simp only [find]
    rw [if_neg (fun he => hne he.symm)]
    exact ih (by simpa [keys] using hrest)

/-- Under `Wf`, membership determines the lookup: the entry paired with `k` in
the table is exactly what `find k` returns.  This is finite-map functionality —
key-uniqueness makes the scan deterministic. -/
theorem mem_find_of_wf {k : Nat} {e : Entry} {t : Table}
    (hwf : Wf t) (hmem : (k, e) ∈ t) : find k t = some e := by
  induction t with
  | nil => cases hmem
  | cons p rest ih =>
    obtain ⟨a, ea⟩ := p
    have hnd : a ∉ keys rest ∧ (keys rest).Nodup := by
      have : (a :: keys rest).Nodup := by simpa [Wf, keys] using hwf
      simpa [List.nodup_cons] using this
    simp only [find]
    rcases List.mem_cons.mp hmem with h | h
    · -- head is (k, e)
      injection h with hk he   -- hk : k = a, he : e = ea
      rw [if_pos hk.symm]
      exact congrArg some he.symm
    · -- (k, e) is in the tail; then a ≠ k since a ∉ keys rest
      have hkeys : k ∈ keys rest := by
        have := List.mem_map_of_mem Prod.fst h
        simpa [keys] using this
      have hak : a ≠ k := fun he => hnd.1 (he ▸ hkeys)
      rw [if_neg hak]
      exact ih hnd.2 h

/-! ### Theorem 1 — `track` increments exactly the tracked key, frames the rest -/

/-- `track` on a present key: its entry becomes counter+1, last-seen refreshed. -/
theorem bump_find_self_present {k now : Nat} {t : Table} {e : Entry}
    (h : find k t = some e) :
    find k (bump k now t) = some ⟨e.count + 1, max e.lastSeen now⟩ := by
  induction t with
  | nil => simp [find] at h
  | cons p rest ih =>
    obtain ⟨k', e'⟩ := p
    simp only [find] at h
    by_cases hk : k' = k
    · rw [if_pos hk] at h
      injection h with he; subst he
      simp only [bump, find, if_pos hk]
    · rw [if_neg hk] at h
      simp only [bump, find, if_neg hk]
      exact ih h

/-- `track` on an absent key: it is created with counter `1`, last-seen `now`. -/
theorem bump_find_self_absent {k now : Nat} {t : Table} (h : find k t = none) :
    find k (bump k now t) = some ⟨1, now⟩ := by
  induction t with
  | nil => simp [bump, find]
  | cons p rest ih =>
    obtain ⟨k', e'⟩ := p
    simp only [find] at h
    by_cases hk : k' = k
    · rw [if_pos hk] at h; simp at h
    · rw [if_neg hk] at h
      simp only [bump, find, if_neg hk]
      exact ih h

/-- `track` changes no key other than the tracked one. -/
theorem bump_find_other {k now k' : Nat} (hne : k' ≠ k) (t : Table) :
    find k' (bump k now t) = find k' t := by
  induction t with
  | nil =>
    simp only [bump, find]
    rw [if_neg (fun he => hne he.symm)]
  | cons p rest ih =>
    obtain ⟨a, e⟩ := p
    by_cases hak : a = k
    · have haknk' : a ≠ k' := fun he => hne (he ▸ hak)
      simp only [bump, find, if_pos hak]
      rw [if_neg haknk', if_neg haknk']
    · simp only [bump, find, if_neg hak]
      by_cases hak' : a = k'
      · rw [if_pos hak', if_pos hak']
      · rw [if_neg hak', if_neg hak', ih]

/-- **Theorem 1 (counter increment).**  `track k` raises `k`'s counter by
exactly one — whether `k` was present (counter `c` ↦ `c+1`) or absent (`0` ↦
`1`).  No capping: unlike the rate limiter this is an exact `+1`. -/
theorem bump_getCount_self (k now : Nat) (t : Table) :
    getCount k (bump k now t) = getCount k t + 1 := by
  unfold getCount
  cases h : find k t with
  | some e => rw [bump_find_self_present h]; simp [Option.elim]
  | none => rw [bump_find_self_absent h]; simp [Option.elim]

/-- **Theorem 1 (frame, counter).**  `track k` leaves every other key's counter
untouched. -/
theorem bump_getCount_other {k now k' : Nat} (hne : k' ≠ k) (t : Table) :
    getCount k' (bump k now t) = getCount k' t := by
  unfold getCount; rw [bump_find_other hne]

/-- **Theorem 1 (last-seen refresh).**  On a present key, `track` refreshes
last-seen to `max old now`; under a monotone clock (`old ≤ now`) this is exactly
`now`. -/
theorem bump_lastSeen_refresh {k now : Nat} {t : Table} {e : Entry}
    (h : find k t = some e) :
    getLastSeen k (bump k now t) = max e.lastSeen now := by
  unfold getLastSeen; rw [bump_find_self_present h]; rfl

theorem bump_lastSeen_refresh_mono {k now : Nat} {t : Table} {e : Entry}
    (h : find k t = some e) (hmono : e.lastSeen ≤ now) :
    getLastSeen k (bump k now t) = now := by
  rw [bump_lastSeen_refresh h]; exact Nat.max_eq_right hmono

/-! ### Theorem 3 — the table stays a finite key-unique map -/

/-- The empty table is well-formed. -/
theorem Wf_nil : Wf ([] : Table) := by simp [Wf, keys]

/-- Every key of `bump k now t` is either `k` or an old key of `t`. -/
theorem mem_keys_bump {x k now : Nat} {t : Table}
    (h : x ∈ keys (bump k now t)) : x = k ∨ x ∈ keys t := by
  induction t with
  | nil =>
    simp only [bump, keys, List.map_cons, List.map_nil, List.mem_cons,
      List.not_mem_nil, or_false] at h
    exact Or.inl h
  | cons p rest ih =>
    obtain ⟨a, e⟩ := p
    by_cases hak : a = k
    · simp only [bump, if_pos hak, keys, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inl (hak ▸ h)
      · exact Or.inr (by simp only [keys, List.map_cons, List.mem_cons]; exact Or.inr h)
    · simp only [bump, if_neg hak, keys, List.map_cons, List.mem_cons] at h
      rcases h with h | h
      · exact Or.inr (by simp only [keys, List.map_cons, List.mem_cons]; exact Or.inl h)
      · rcases ih h with h' | h'
        · exact Or.inl h'
        · exact Or.inr (by simp only [keys, List.map_cons, List.mem_cons]; exact Or.inr h')

/-- **Theorem 3 (`track` preserves the invariant).**  `track` keeps keys unique:
it updates an existing key in place or appends a genuinely new key. -/
theorem bump_Wf (k now : Nat) {t : Table} (hwf : Wf t) : Wf (bump k now t) := by
  induction t with
  | nil => simp [Wf, keys, bump]
  | cons p rest ih =>
    obtain ⟨a, e⟩ := p
    have hnd : a ∉ keys rest ∧ (keys rest).Nodup := by
      have : (a :: keys rest).Nodup := by simpa [Wf, keys] using hwf
      simpa [List.nodup_cons] using this
    by_cases hak : a = k
    · -- in-place update: keys are literally unchanged
      have hb : bump k now ((a, e) :: rest)
              = (a, ⟨e.count + 1, max e.lastSeen now⟩) :: rest := by
        simp only [bump]; rw [if_pos hak]
      rw [hb]
      simpa [Wf, keys] using hwf
    · have ihrest : Wf (bump k now rest) := ih (by simpa [Wf] using hnd.2)
      have hb : bump k now ((a, e) :: rest) = (a, e) :: bump k now rest := by
        simp only [bump]; rw [if_neg hak]
      rw [hb]
      simp only [Wf, keys, List.map_cons, List.nodup_cons]
      refine ⟨?_, by simpa [Wf, keys] using ihrest⟩
      intro hmem
      rcases mem_keys_bump (t := rest) (by simpa [keys] using hmem) with h' | h'
      · exact hak (by rw [h'])
      · exact hnd.1 h'

/-- **Theorem 3 (`evict` preserves the invariant).**  Filtering by liveness only
removes entries, so key-uniqueness is preserved. -/
theorem evict_Wf (ttl now : Nat) {t : Table} (hwf : Wf t) : Wf (evict ttl now t) := by
  have hsub : List.Sublist ((evict ttl now t).map Prod.fst) (t.map Prod.fst) :=
    (List.filter_sublist t).map Prod.fst
  exact hsub.nodup hwf

/-! ### Theorem 2 — TTL expiry: not looked up, evicted -/

/-- **Theorem 2 (expiry, read side).**  An entry past its TTL is not returned by
`lookup` — it reads back as absent. -/
theorem lookup_expired {k ttl now : Nat} {t : Table} {e : Entry}
    (h : find k t = some e) (hexp : ¬ (now < e.lastSeen + ttl)) :
    lookup k ttl now t = none := by
  simp only [lookup, h, live, decide_eq_true_eq, if_neg hexp]

/-- A live entry is returned by `lookup` unchanged. -/
theorem lookup_live {k ttl now : Nat} {t : Table} {e : Entry}
    (h : find k t = some e) (hlive : now < e.lastSeen + ttl) :
    lookup k ttl now t = some e := by
  simp only [lookup, h, live, decide_eq_true_eq, if_pos hlive]

/-- **Theorem 2 (expiry, evict side).**  Under `Wf`, an entry past its TTL is
removed by `evict` — it is eligible for eviction and actually gone. -/
theorem evict_removes_expired {k ttl now : Nat} {t : Table} {e : Entry}
    (hwf : Wf t) (h : find k t = some e) (hexp : ¬ (now < e.lastSeen + ttl)) :
    find k (evict ttl now t) = none := by
  apply find_none_of_not_mem_keys
  intro hk
  -- k present in the filtered table ⇒ some entry with key k survived the filter
  simp only [keys, List.mem_map] at hk
  obtain ⟨pr, hpr_mem, hpr_key⟩ := hk
  rw [evict, List.mem_filter] at hpr_mem
  obtain ⟨hpr_t, hpr_live⟩ := hpr_mem
  obtain ⟨kk, ee⟩ := pr
  simp only at hpr_key
  have hkk : kk = k := hpr_key
  -- that surviving entry is, by Wf, exactly `e`
  have hfind : find kk t = some ee := mem_find_of_wf hwf hpr_t
  rw [hkk, h] at hfind
  have hee : e = ee := by injection hfind
  -- but `e` is expired: contradiction with it having survived the live filter
  simp only [live, decide_eq_true_eq] at hpr_live
  rw [← hee] at hpr_live
  exact hexp hpr_live

/-- A live entry survives `evict` (under `Wf`). -/
theorem evict_preserves_live {k ttl now : Nat} {t : Table} {e : Entry}
    (hwf : Wf t) (h : find k t = some e) (hlive : now < e.lastSeen + ttl) :
    find k (evict ttl now t) = some e := by
  apply mem_find_of_wf (evict_Wf ttl now hwf)
  rw [evict, List.mem_filter]
  exact ⟨find_mem h, by simp only [live, decide_eq_true_eq]; exact hlive⟩

/-! ### Theorem 4 — monotone-time discipline (per step) -/

/-- **Theorem 4 (per step).**  A `track` never moves any key's last-seen
backward: the tracked key advances to `max old now ≥ old`, every other key is
untouched.  Holds unconditionally — the `max` enforces it even on a stale
reading. -/
theorem bump_getLastSeen_mono (k now k' : Nat) (t : Table) :
    getLastSeen k' t ≤ getLastSeen k' (bump k now t) := by
  by_cases hkk : k' = k
  · subst hkk
    cases h : find k' t with
    | none => simp [getLastSeen, h]
    | some e =>
      rw [bump_lastSeen_refresh h]
      simp only [getLastSeen, h, Option.elim]
      exact Nat.le_max_left _ _
  · exact Nat.le_of_eq (by unfold getLastSeen; rw [bump_find_other hkk])

end StickTable

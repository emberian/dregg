/-
Pool — reactor-local buffer pools with size classes.

A single-threaded network reactor recycles byte buffers instead of paying a
heap allocation per receive/send.  `Pool.BufferPool` is the general-purpose
pool: seven size classes, powers of two from 1 KiB to 64 KiB, each class a
LIFO stack (just-freed buffers are cache-hot) capped at `maxPerClass`
entries.  Requests above the largest class bypass the pool entirely;
returned buffers are accepted only when their capacity is *exactly* a class
size (a buffer that was reallocated to a non-standard capacity is dropped,
not cached).

Buffers are modeled by their capacity (`Nat`); buckets are `List Nat` with
the head as the stack top.  The bucket array is a total function
`Nat → List Nat`, meaningful on `[0, numClasses)`.

Theorem groups:

* **Class selection** — `sizeClass` picks the *least* class that holds the
  request (`sizeClass_adequate`, `sizeClass_minimal`), is total on
  `[0, maxSize]` (`sizeClass_complete`) and rejects oversized requests
  (`sizeClass_oversized`); `exactClass` accepts exactly the class sizes
  (`exactClass_some`, `exactClass_classSize`).
* **Invariant preservation** — `WF.get`, `WF.put`: every bucket holds only
  exact-capacity buffers and never exceeds `maxPerClass`.
* **Adequacy** — `get_capacity`: the buffer handed out always holds the
  request.
* **Conservation** — `put_get` (LIFO round trip: put then get of the same
  class returns the very same buffer and restores the pool exactly),
  `get_hit_cached` / `put_accept_cached` (the cached count moves by exactly
  one), `get_miss` / `put_drop_*` (misses and drops leave the pool
  untouched), `cached_le` (the pool's total footprint is bounded).
-/

namespace Pool

/-! ### Pointwise-updated total functions -/

/-- Point update of a total function. -/
def upd {α : Type} (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else f j

@[simp] theorem upd_self {α : Type} (f : Nat → α) (i : Nat) (v : α) :
    upd f i v i = v := by
  simp [upd]

theorem upd_ne {α : Type} (f : Nat → α) (v : α) {i j : Nat} (h : j ≠ i) :
    upd f i v j = f j := by
  simp [upd, h]

/-- Updating twice at the same point keeps the last write. -/
theorem upd_upd {α : Type} (f : Nat → α) (i : Nat) (v w : α) :
    upd (upd f i v) i w = upd f i w := by
  funext j
  by_cases hj : j = i
  · rw [hj, upd_self, upd_self]
  · rw [upd_ne _ _ hj, upd_ne _ _ hj, upd_ne _ _ hj]

/-- Writing back the current value is the identity. -/
theorem upd_eval_self {α : Type} (f : Nat → α) (i : Nat) :
    upd f i (f i) = f := by
  funext j
  by_cases hj : j = i
  · rw [hj, upd_self]
  · rw [upd_ne _ _ hj]

/-! ### Size classes -/

/-- Number of size classes. -/
def numClasses : Nat := 7

/-- Smallest pooled capacity (class 0): 1 KiB. -/
def minSize : Nat := 1024

/-- Largest pooled capacity (class `numClasses - 1`): 64 KiB. -/
def maxSize : Nat := 65536

/-- Length cap per class: at most this many idle buffers are retained. -/
def maxPerClass : Nat := 48

/-- Capacity of class `i`: `minSize · 2^i` (1K, 2K, 4K, 8K, 16K, 32K, 64K). -/
def classSize : Nat → Nat
  | 0 => minSize
  | i + 1 => 2 * classSize i

theorem classSize_pos (i : Nat) : 0 < classSize i := by
  induction i with
  | zero => decide
  | succ i ih => simp only [classSize]; omega

theorem classSize_mono {i j : Nat} (h : i ≤ j) : classSize i ≤ classSize j := by
  induction j with
  | zero => cases Nat.le_zero.mp h; exact Nat.le_refl _
  | succ j ih =>
    by_cases hij : i = j + 1
    · rw [hij]; exact Nat.le_refl _
    · have h1 := ih (by omega)
      have h2 := classSize_pos j
      simp only [classSize]
      omega

theorem classSize_max : classSize (numClasses - 1) = maxSize := by decide

/-- Least class index in `[start, start + fuel)` whose capacity holds `n`. -/
def scan (n : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, start =>
    if n ≤ classSize start then some start else scan n fuel (start + 1)

/-- The class an `n`-byte request draws from: the least class that holds it,
or `none` when the request exceeds `maxSize` (pool bypass). -/
def sizeClass (n : Nat) : Option Nat := scan n numClasses 0

/-- Everything a successful scan guarantees: the hit is inside the scanned
window, holds the request, and every earlier class in the window is too
small. -/
theorem scan_some {n fuel start i : Nat} (h : scan n fuel start = some i) :
    start ≤ i ∧ i < start + fuel ∧ n ≤ classSize i
      ∧ (∀ j, start ≤ j → j < i → classSize j < n) := by
  induction fuel generalizing start with
  | zero => exact Option.noConfusion h
  | succ fuel ih =>
    unfold scan at h
    by_cases hn : n ≤ classSize start
    · rw [if_pos hn] at h
      obtain rfl := Option.some.inj h
      exact ⟨Nat.le_refl _, by omega, hn, fun j h1 h2 => by omega⟩
    · rw [if_neg hn] at h
      obtain ⟨h1, h2, h3, h4⟩ := ih h
      refine ⟨by omega, by omega, h3, ?_⟩
      intro j hj1 hj2
      by_cases hj : j = start
      · rw [hj]; omega
      · exact h4 j (by omega) hj2

/-- A failed scan means every class in the window is too small. -/
theorem scan_none {n fuel start : Nat} (h : scan n fuel start = none) :
    ∀ j, start ≤ j → j < start + fuel → classSize j < n := by
  induction fuel generalizing start with
  | zero => intro j h1 h2; omega
  | succ fuel ih =>
    unfold scan at h
    by_cases hn : n ≤ classSize start
    · rw [if_pos hn] at h; exact Option.noConfusion h
    · rw [if_neg hn] at h
      intro j h1 h2
      by_cases hj : j = start
      · rw [hj]; omega
      · exact ih h j (by omega) (by omega)

theorem sizeClass_lt {n i : Nat} (h : sizeClass n = some i) : i < numClasses := by
  have := (scan_some h).2.1
  omega

/-- **Adequacy**: the selected class holds the request. -/
theorem sizeClass_adequate {n i : Nat} (h : sizeClass n = some i) :
    n ≤ classSize i :=
  (scan_some h).2.2.1

/-- **Minimality**: every smaller class is too small — the pool wastes at
most one doubling. -/
theorem sizeClass_minimal {n i : Nat} (h : sizeClass n = some i) :
    ∀ j, j < i → classSize j < n := by
  intro j hj
  exact (scan_some h).2.2.2 j (Nat.zero_le j) hj

/-- **Completeness**: every request up to `maxSize` gets a class. -/
theorem sizeClass_complete {n : Nat} (h : n ≤ maxSize) :
    ∃ i, sizeClass n = some i ∧ i < numClasses := by
  cases hs : sizeClass n with
  | some i => exact ⟨i, rfl, sizeClass_lt hs⟩
  | none =>
    have hlast := scan_none hs (numClasses - 1) (by omega) (by decide)
    rw [classSize_max] at hlast
    omega

/-- **Bypass**: oversized requests are never pooled. -/
theorem sizeClass_oversized {n : Nat} (h : maxSize < n) : sizeClass n = none := by
  cases hs : sizeClass n with
  | none => rfl
  | some i =>
    have h1 := sizeClass_adequate hs
    have h2 := classSize_mono (Nat.le_of_lt_succ (by
      have := sizeClass_lt hs
      omega : i < Nat.succ (numClasses - 1)))
    rw [classSize_max] at h2
    omega

/-- Class index for an *exact* class-size capacity — the acceptance test on
the return path (a reallocated, off-class buffer must not be cached). -/
def exactScan (c : Nat) : Nat → Nat → Option Nat
  | 0, _ => none
  | fuel + 1, start =>
    if c = classSize start then some start else exactScan c fuel (start + 1)

def exactClass (c : Nat) : Option Nat := exactScan c numClasses 0

theorem exactScan_some {c fuel start i : Nat} (h : exactScan c fuel start = some i) :
    start ≤ i ∧ i < start + fuel ∧ c = classSize i := by
  induction fuel generalizing start with
  | zero => exact Option.noConfusion h
  | succ fuel ih =>
    unfold exactScan at h
    by_cases hc : c = classSize start
    · rw [if_pos hc] at h
      obtain rfl := Option.some.inj h
      exact ⟨Nat.le_refl _, by omega, hc⟩
    · rw [if_neg hc] at h
      obtain ⟨h1, h2, h3⟩ := ih h
      exact ⟨by omega, by omega, h3⟩

theorem exactClass_lt {c i : Nat} (h : exactClass c = some i) : i < numClasses := by
  have := (exactScan_some h).2.1
  omega

/-- **Exactness**: an accepted return has exactly its class's capacity. -/
theorem exactClass_some {c i : Nat} (h : exactClass c = some i) :
    c = classSize i :=
  (exactScan_some h).2.2

/-- Every class size is accepted (into some class of that exact size). -/
theorem exactClass_classSize {i : Nat} (h : i < numClasses) :
    ∃ j, exactClass (classSize i) = some j ∧ classSize j = classSize i := by
  cases hs : exactClass (classSize i) with
  | some j => exact ⟨j, rfl, (exactClass_some hs).symm⟩
  | none =>
    exfalso
    -- scan every window position; position i matches.
    have : ∀ fuel start, start ≤ i → i < start + fuel →
        exactScan (classSize i) fuel start ≠ none := by
      intro fuel
      induction fuel with
      | zero => intro start h1 h2; omega
      | succ fuel ih =>
        intro start h1 h2
        unfold exactScan
        by_cases hc : classSize i = classSize start
        · rw [if_pos hc]; exact fun h => Option.noConfusion h
        · rw [if_neg hc]
          have hne : start ≠ i := fun he => hc (by rw [he])
          exact ih (start + 1) (by omega) (by omega)
    exact this numClasses 0 (Nat.zero_le i) (by omega) hs

/-! ### The pool -/

/-- The buffer pool: one LIFO bucket per size class.  Buckets at or past
`numClasses` are never touched and stay empty. -/
structure BufferPool where
  buckets : Nat → List Nat

namespace BufferPool

/-- The empty pool. -/
def empty : BufferPool where
  buckets := fun _ => []

/-- Request a buffer of at least `n` bytes.  Returns the granted capacity
and the new pool: a pooled buffer when the class has one (hit), a fresh
class-sized buffer otherwise (miss), or a direct allocation for oversized
requests (bypass — the pool is untouched in the last two cases). -/
def get (p : BufferPool) (n : Nat) : Nat × BufferPool :=
  match sizeClass n with
  | some i =>
    match p.buckets i with
    | c :: rest => (c, ⟨upd p.buckets i rest⟩)
    | [] => (classSize i, p)
  | none => (n, p)

/-- Return a buffer of capacity `c`.  Accepted only when `c` is exactly a
class size and the class is below its length cap; otherwise the buffer is
dropped (freed), never cached. -/
def put (p : BufferPool) (c : Nat) : BufferPool :=
  match exactClass c with
  | some i =>
    if (p.buckets i).length < maxPerClass
    then ⟨upd p.buckets i (c :: p.buckets i)⟩
    else p
  | none => p

/-! ### Case-shape lemmas -/

theorem get_hit {p : BufferPool} {n i c : Nat} {rest : List Nat}
    (hi : sizeClass n = some i) (hb : p.buckets i = c :: rest) :
    p.get n = (c, ⟨upd p.buckets i rest⟩) := by
  simp [get, hi, hb]

theorem get_miss {p : BufferPool} {n i : Nat}
    (hi : sizeClass n = some i) (hb : p.buckets i = []) :
    p.get n = (classSize i, p) := by
  simp [get, hi, hb]

theorem get_oversized {p : BufferPool} {n : Nat} (hi : sizeClass n = none) :
    p.get n = (n, p) := by
  simp [get, hi]

theorem put_accept {p : BufferPool} {c i : Nat}
    (hi : exactClass c = some i) (hlen : (p.buckets i).length < maxPerClass) :
    p.put c = ⟨upd p.buckets i (c :: p.buckets i)⟩ := by
  simp [put, hi, hlen]

theorem put_drop_full {p : BufferPool} {c i : Nat}
    (hi : exactClass c = some i) (hlen : ¬(p.buckets i).length < maxPerClass) :
    p.put c = p := by
  simp [put, hi, hlen]

theorem put_drop_mismatch {p : BufferPool} {c : Nat} (hi : exactClass c = none) :
    p.put c = p := by
  simp [put, hi]

/-! ### The invariant -/

/-- Well-formedness:

* `exact_cap` — every cached buffer has exactly its class's capacity, so a
  hit hands out precisely what the class promises;
* `len_cap` — no bucket exceeds the per-class cap, so the pool's idle
  footprint is bounded. -/
structure WF (p : BufferPool) : Prop where
  exact_cap : ∀ i, ∀ c ∈ p.buckets i, c = classSize i
  len_cap : ∀ i, (p.buckets i).length ≤ maxPerClass

protected theorem WF.empty : (empty : BufferPool).WF where
  exact_cap := by intro i c h; exact absurd h (List.not_mem_nil c)
  len_cap := by intro i; exact Nat.zero_le _

protected theorem WF.get {p : BufferPool} (h : p.WF) (n : Nat) :
    ((p.get n).2).WF := by
  cases hi : sizeClass n with
  | none => rw [get_oversized hi]; exact h
  | some i =>
    cases hb : p.buckets i with
    | nil => rw [get_miss hi hb]; exact h
    | cons c rest =>
      rw [get_hit hi hb]
      refine ⟨?_, ?_⟩ <;> dsimp only
      · intro j c' hc'
        by_cases hj : j = i
        · rw [hj] at hc' ⊢
          rw [upd_self] at hc'
          exact h.exact_cap i c' (by rw [hb]; exact List.mem_cons_of_mem c hc')
        · rw [upd_ne _ _ hj] at hc'
          exact h.exact_cap j c' hc'
      · intro j
        by_cases hj : j = i
        · rw [hj, upd_self]
          have := h.len_cap i
          rw [hb] at this
          simp only [List.length_cons] at this
          omega
        · rw [upd_ne _ _ hj]
          exact h.len_cap j

protected theorem WF.put {p : BufferPool} (h : p.WF) (c : Nat) :
    (p.put c).WF := by
  cases hi : exactClass c with
  | none => rw [put_drop_mismatch hi]; exact h
  | some i =>
    by_cases hlen : (p.buckets i).length < maxPerClass
    · rw [put_accept hi hlen]
      refine ⟨?_, ?_⟩ <;> dsimp only
      · intro j c' hc'
        by_cases hj : j = i
        · rw [hj] at hc' ⊢
          rw [upd_self] at hc'
          cases List.mem_cons.mp hc' with
          | inl he => rw [he]; exact exactClass_some hi
          | inr hin => exact h.exact_cap i c' hin
        · rw [upd_ne _ _ hj] at hc'
          exact h.exact_cap j c' hc'
      · intro j
        by_cases hj : j = i
        · rw [hj, upd_self]
          simp only [List.length_cons]
          omega
        · rw [upd_ne _ _ hj]
          exact h.len_cap j
    · rw [put_drop_full hi hlen]; exact h

/-! ### Capacity never exceeded (named corollaries) -/

/-- After any `put`, every bucket still respects the length cap — a flood of
returns cannot grow the pool past its bound. -/
theorem put_len_le {p : BufferPool} (h : p.WF) (c i : Nat) :
    ((p.put c).buckets i).length ≤ maxPerClass :=
  (h.put c).len_cap i

/-- Total idle buffers cached below class `k`. -/
def sumLen (f : Nat → List Nat) : Nat → Nat
  | 0 => 0
  | k + 1 => sumLen f k + (f k).length

/-- Total idle buffers cached in the pool. -/
def cached (p : BufferPool) : Nat := sumLen p.buckets numClasses

theorem sumLen_congr {f g : Nat → List Nat} {k : Nat}
    (h : ∀ j, j < k → f j = g j) : sumLen f k = sumLen g k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    have hk := h k (Nat.lt_succ_self k)
    simp [sumLen, ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), hk]

/-- A point update changes the sum by the difference of the lengths. -/
theorem sumLen_upd (f : Nat → List Nat) (i : Nat) (l : List Nat)
    {k : Nat} (h : i < k) :
    sumLen (upd f i l) k + (f i).length = sumLen f k + l.length := by
  induction k with
  | zero => omega
  | succ k ih =>
    by_cases hik : i = k
    · subst hik
      have hcong : sumLen (upd f i l) i = sumLen f i :=
        sumLen_congr (fun j hj => upd_ne f l (by omega))
      simp only [sumLen, hcong, upd_self]
      omega
    · have hne : k ≠ i := by omega
      simp only [sumLen, upd_ne f l hne]
      have := ih (by omega)
      omega

theorem sumLen_le_of_bound {f : Nat → List Nat} {b : Nat}
    (h : ∀ i, (f i).length ≤ b) (k : Nat) : sumLen f k ≤ k * b := by
  induction k with
  | zero => exact Nat.zero_le _
  | succ k ih =>
    simp only [sumLen, Nat.succ_mul]
    have := h k
    omega

/-- The pool's total idle footprint is bounded: at most
`numClasses · maxPerClass` buffers are ever cached. -/
theorem cached_le {p : BufferPool} (h : p.WF) :
    p.cached ≤ numClasses * maxPerClass :=
  sumLen_le_of_bound h.len_cap numClasses

/-! ### Adequacy -/

/-- The buffer handed out always holds the request, whichever path served
it: a pooled hit (exact class capacity), a fresh class-sized allocation, or
an oversized direct allocation. -/
theorem get_capacity {p : BufferPool} (h : p.WF) (n : Nat) :
    n ≤ (p.get n).1 := by
  cases hi : sizeClass n with
  | none => rw [get_oversized hi]; exact Nat.le_refl _
  | some i =>
    cases hb : p.buckets i with
    | nil => rw [get_miss hi hb]; exact sizeClass_adequate hi
    | cons c rest =>
      rw [get_hit hi hb]
      have hc : c = classSize i :=
        h.exact_cap i c (by rw [hb]; exact List.mem_cons_self c rest)
      rw [hc]
      exact sizeClass_adequate hi

/-- A pooled request is granted exactly its class's capacity — hit or miss. -/
theorem get_class_exact {p : BufferPool} (h : p.WF) {n i : Nat}
    (hi : sizeClass n = some i) : (p.get n).1 = classSize i := by
  cases hb : p.buckets i with
  | nil => rw [get_miss hi hb]
  | cons c rest =>
    rw [get_hit hi hb]
    exact h.exact_cap i c (by rw [hb]; exact List.mem_cons_self c rest)

/-! ### Conservation -/

/-- **LIFO round trip.** Returning a buffer and immediately requesting its
class hands back the very same buffer and restores the pool exactly —
nothing is created, lost, or reordered. -/
theorem put_get {p : BufferPool} {c n i : Nat}
    (hi : exactClass c = some i) (hn : sizeClass n = some i)
    (hlen : (p.buckets i).length < maxPerClass) :
    (p.put c).get n = (c, p) := by
  rw [put_accept hi hlen]
  have hb : (⟨upd p.buckets i (c :: p.buckets i)⟩ : BufferPool).buckets i
      = c :: p.buckets i := upd_self ..
  rw [get_hit hn hb]
  show (c, (⟨upd (upd p.buckets i (c :: p.buckets i)) i (p.buckets i)⟩ : BufferPool))
    = (c, p)
  rw [upd_upd, upd_eval_self]

/-- A hit removes exactly one buffer from the pool. -/
theorem get_hit_cached {p : BufferPool} {n i c : Nat} {rest : List Nat}
    (hi : sizeClass n = some i) (hb : p.buckets i = c :: rest) :
    ((p.get n).2).cached + 1 = p.cached := by
  rw [get_hit hi hb]
  have h := sumLen_upd p.buckets i rest (sizeClass_lt hi)
  rw [hb] at h
  simp only [List.length_cons] at h
  show sumLen (upd p.buckets i rest) numClasses + 1 = sumLen p.buckets numClasses
  omega

/-- An accepted return adds exactly one buffer to the pool. -/
theorem put_accept_cached {p : BufferPool} {c i : Nat}
    (hi : exactClass c = some i) (hlen : (p.buckets i).length < maxPerClass) :
    (p.put c).cached = p.cached + 1 := by
  rw [put_accept hi hlen]
  have h := sumLen_upd p.buckets i (c :: p.buckets i) (exactClass_lt hi)
  simp only [List.length_cons] at h
  show sumLen (upd p.buckets i (c :: p.buckets i)) numClasses
    = sumLen p.buckets numClasses + 1
  omega

end BufferPool

end Pool

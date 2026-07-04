/-
Slab — a dense, fd-keyed connection table.

A single-threaded network reactor keeps per-connection state keyed by file
descriptor.  `Slab.Table` realizes the abstract partial map `fd ⇀ σ` as

  * an indirection vector `fdIndex : fd → Option slot` (direct-indexed, no
    hashing),
  * a dense slot store `slots : slot → Option σ`,
  * a reverse map `slotFd : slot → fd` (iteration without cross-borrowing),
  * a LIFO free list of dead slots, so freed slots are reused cache-warm.

Vectors are modeled as total functions together with an explicit bound
(`nSlots`); reads at or past the bound are `none`.  This keeps everything the
refinement proof is about — the two-level indirection, the dense store, the
LIFO recycling discipline — while eliding machine-level array plumbing
(pre-sizing, growth, and the numeric empty-slot sentinel, which is modeled by
`Option`).  File descriptors are modeled as `Nat`; rejection of negative fds
is a boundary check below this model.
-/

namespace Slab

universe u

variable {α : Type u} {σ : Type u}

/-! ### Pointwise-updated total functions -/

/-- Point update of a total function. -/
def upd (f : Nat → α) (i : Nat) (v : α) : Nat → α :=
  fun j => if j = i then v else f j

@[simp] theorem upd_self (f : Nat → α) (i : Nat) (v : α) : upd f i v i = v := by
  simp [upd]

theorem upd_ne (f : Nat → α) (v : α) {i j : Nat} (h : j ≠ i) :
    upd f i v j = f j := by
  simp [upd, h]

/-! ### Counting live slots

`liveCount f n` counts the `some` entries of `f` below `n`.  It is the
specification for the table's cached `count` field. -/

/-- Number of live (`some`) entries of `f` on `[0, n)`. -/
def liveCount (f : Nat → Option σ) : Nat → Nat
  | 0 => 0
  | n + 1 => liveCount f n + (if (f n).isSome then 1 else 0)

theorem liveCount_congr {f g : Nat → Option σ} {n : Nat}
    (h : ∀ i, i < n → f i = g i) : liveCount f n = liveCount g n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn := h n (Nat.lt_succ_self n)
    simp [liveCount, ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), hn]

/-- Master lemma: a point update changes the live count by the difference of
the `isSome` flags. -/
theorem liveCount_upd (f : Nat → Option σ) (s : Nat) (v : Option σ)
    {n : Nat} (h : s < n) :
    liveCount (upd f s v) n + (if (f s).isSome then 1 else 0)
      = liveCount f n + (if v.isSome then 1 else 0) := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hs : s = n
    · subst hs
      have hcong : liveCount (upd f s v) s = liveCount f s :=
        liveCount_congr (fun i hi => upd_ne f v (by omega))
      simp only [liveCount, hcong, upd_self]
      omega
    · have hne : n ≠ s := by omega
      simp only [liveCount, upd_ne f v hne]
      have := ih (by omega)
      omega

theorem liveCount_upd_ge (f : Nat → Option σ) (v : Option σ) {s n : Nat}
    (h : n ≤ s) : liveCount (upd f s v) n = liveCount f n :=
  liveCount_congr fun _ hi => upd_ne f v (by omega)

theorem liveCount_upd_none {f : Nat → Option σ} {s n : Nat}
    (h : s < n) (hs : (f s).isSome) :
    liveCount (upd f s none) n + 1 = liveCount f n := by
  have := liveCount_upd f s none h
  simp [hs] at this
  omega

theorem liveCount_upd_some_of_none {f : Nat → Option σ} {s n : Nat} (v : σ)
    (h : s < n) (hs : f s = none) :
    liveCount (upd f s (some v)) n = liveCount f n + 1 := by
  have := liveCount_upd f s (some v) h
  simp [hs] at this
  omega

theorem liveCount_upd_some_of_some {f : Nat → Option σ} {s n : Nat} (v : σ)
    (h : s < n) (hs : (f s).isSome) :
    liveCount (upd f s (some v)) n = liveCount f n := by
  have := liveCount_upd f s (some v) h
  simp [hs] at this
  omega

theorem liveCount_pos {f : Nat → Option σ} {s n : Nat}
    (h : s < n) (hs : (f s).isSome) : 0 < liveCount f n := by
  induction n with
  | zero => omega
  | succ n ih =>
    by_cases hsn : s = n
    · subst hsn
      simp only [liveCount, hs, if_true]
      omega
    · have := ih (by omega)
      simp only [liveCount]
      omega

/-! ### The table -/

/-- The concrete slab: two-level fd→slot indirection over a dense slot store,
with a LIFO free list.  Refines the abstract partial map `fd ⇀ σ` (see
`Slab.Table.abs`). -/
structure Table (σ : Type u) where
  /-- Direct-indexed fd → slot map (`none` = empty). -/
  fdIndex : Nat → Option Nat
  /-- Number of slots allocated so far (dense store length). -/
  nSlots : Nat
  /-- Dense slot store; slots at or past `nSlots` are `none`. -/
  slots : Nat → Option σ
  /-- Reverse map slot → fd; meaningful only for live slots. -/
  slotFd : Nat → Nat
  /-- LIFO free list of dead slots (head = most recently freed). -/
  free : List Nat
  /-- Cached number of live connections. -/
  count : Nat

namespace Table

/-- The empty table. -/
def empty : Table σ where
  fdIndex := fun _ => none
  nSlots := 0
  slots := fun _ => none
  slotFd := fun _ => 0
  free := []
  count := 0

/-- Look up a connection by fd: follow the indirection, then read the slot. -/
def lookup (t : Table σ) (fd : Nat) : Option σ :=
  (t.fdIndex fd).bind t.slots

/-- The abstraction function: the partial map `fd ⇀ σ` this table denotes.
`lookup` *is* the abstraction — the refinement theorems say `insert` and
`remove` commute with it. -/
def abs (t : Table σ) : Nat → Option σ :=
  fun fd => t.lookup fd

/-- Membership test (reads only the indirection level). -/
def contains (t : Table σ) (fd : Nat) : Bool :=
  (t.fdIndex fd).isSome

/-- Number of live connections (cached). -/
def len (t : Table σ) : Nat :=
  t.count

/-- Insert (or replace) the state for `fd`.  A fresh binding takes a slot
from the head of the free list, or extends the dense store when the free
list is empty; a rebinding overwrites in place. -/
def insert (t : Table σ) (fd : Nat) (v : σ) : Table σ :=
  match t.fdIndex fd with
  | some s =>
    -- Replace in place: the slot is already allocated to this fd.
    { t with slots := upd t.slots s (some v) }
  | none =>
    match t.free with
    | s :: rest =>
      -- Recycle the most recently freed slot (LIFO, cache-warm).
      { fdIndex := upd t.fdIndex fd (some s)
        nSlots := t.nSlots
        slots := upd t.slots s (some v)
        slotFd := upd t.slotFd s fd
        free := rest
        count := t.count + 1 }
    | [] =>
      -- No free slot: extend the dense store.
      { fdIndex := upd t.fdIndex fd (some t.nSlots)
        nSlots := t.nSlots + 1
        slots := upd t.slots t.nSlots (some v)
        slotFd := upd t.slotFd t.nSlots fd
        free := []
        count := t.count + 1 }

/-- Remove the binding for `fd`, returning the removed state (if any) and
pushing the freed slot onto the free list. -/
def remove (t : Table σ) (fd : Nat) : Option σ × Table σ :=
  match t.fdIndex fd with
  | none => (none, t)
  | some s =>
    (t.slots s,
     { t with
        fdIndex := upd t.fdIndex fd none
        slots := upd t.slots s none
        free := s :: t.free
        count := t.count - 1 })

/-- `remove`, keeping only the table. -/
def erase (t : Table σ) (fd : Nat) : Table σ :=
  (t.remove fd).2

/-! ### Case-shape lemmas (the only place the `match`es are unfolded) -/

theorem insert_replace {t : Table σ} {fd s : Nat} (h : t.fdIndex fd = some s)
    (v : σ) : t.insert fd v = { t with slots := upd t.slots s (some v) } := by
  simp [insert, h]

theorem insert_pop {t : Table σ} {fd : Nat} {s : Nat} {rest : List Nat}
    (h : t.fdIndex fd = none) (hf : t.free = s :: rest) (v : σ) :
    t.insert fd v =
      { fdIndex := upd t.fdIndex fd (some s)
        nSlots := t.nSlots
        slots := upd t.slots s (some v)
        slotFd := upd t.slotFd s fd
        free := rest
        count := t.count + 1 } := by
  simp [insert, h, hf]

theorem insert_fresh {t : Table σ} {fd : Nat}
    (h : t.fdIndex fd = none) (hf : t.free = []) (v : σ) :
    t.insert fd v =
      { fdIndex := upd t.fdIndex fd (some t.nSlots)
        nSlots := t.nSlots + 1
        slots := upd t.slots t.nSlots (some v)
        slotFd := upd t.slotFd t.nSlots fd
        free := []
        count := t.count + 1 } := by
  simp [insert, h, hf]

theorem remove_none {t : Table σ} {fd : Nat} (h : t.fdIndex fd = none) :
    t.remove fd = (none, t) := by
  simp [remove, h]

theorem remove_some {t : Table σ} {fd s : Nat} (h : t.fdIndex fd = some s) :
    t.remove fd =
      (t.slots s,
       { t with
          fdIndex := upd t.fdIndex fd none
          slots := upd t.slots s none
          free := s :: t.free
          count := t.count - 1 }) := by
  simp [remove, h]

/-! ### The coupling invariant -/

/-- Well-formedness: the coupling invariant between the concrete table and
the abstract map.

* `index_live` / `live_indexed` together are the fd ↔ slot bijection between
  bound fds and live slots (with `slotFd` as the inverse direction).
* `free_dead` is free-list soundness: no live slot is ever on the free list.
* `free_nodup` rules out double frees.
* `dead_free` is free-list completeness: every dead slot below the bound is
  recorded, so allocation never clobbers a live slot.
* `count_eq` pins the cached count to the true number of live slots. -/
structure WF (t : Table σ) : Prop where
  index_live : ∀ fd s, t.fdIndex fd = some s →
      s < t.nSlots ∧ (t.slots s).isSome ∧ t.slotFd s = fd
  live_indexed : ∀ s, s < t.nSlots → (t.slots s).isSome →
      t.fdIndex (t.slotFd s) = some s
  slots_bounded : ∀ s, t.nSlots ≤ s → t.slots s = none
  free_dead : ∀ s ∈ t.free, s < t.nSlots ∧ t.slots s = none
  free_nodup : t.free.Nodup
  dead_free : ∀ s, s < t.nSlots → t.slots s = none → s ∈ t.free
  count_eq : t.count = liveCount t.slots t.nSlots

/-- Two distinct fds never share a slot (via the reverse map). -/
theorem WF.index_inj {t : Table σ} (h : t.WF) {fd fd' s : Nat}
    (h1 : t.fdIndex fd = some s) (h2 : t.fdIndex fd' = some s) : fd = fd' := by
  have a1 := (h.index_live fd s h1).2.2
  have a2 := (h.index_live fd' s h2).2.2
  omega

end Table

end Slab

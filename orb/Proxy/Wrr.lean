/-
Wrr — weighted round-robin selection, with an exact window-fairness theorem.

The policy: give the round counter `k`, reduce it modulo the total weight `W`
of the candidate list, and walk the list's cumulative-weight intervals — a
backend with weight `w` owns `w` consecutive residues. One atomic round
counter is the only state; selection is a pure function of `(candidates, k)`.

The headline theorem is `wrr_window_weight`: over ANY window of `W`
consecutive rounds — aligned to the cycle or not — a backend with weight `w`
is selected EXACTLY `w` times (candidate list held fixed across the window).
That is strictly stronger than the usual "within its weight proportion ± 1"
fairness bound, and it makes the ±1 bound trivial for sub-window prefixes.

The counting is done with a self-contained counter `cnt p n` = |{ j < n |
p j }| rather than a library fold, so every lemma is a plain induction:

  * `cnt_mod_window` — counting a predicate of `(start + j) % W` over a window
    of length `W` is independent of `start` (sliding the window by one swaps
    out residue `start % W` and swaps the same residue back in);
  * `cnt_pick`       — over the base cycle `[0, W)`, the residues that select
    a given backend are exactly its cumulative-weight interval, so the count
    is its weight (summed over duplicate occurrences: `occWeight`).

`wrr_total` (a healthy candidate with positive weight exists ⇒ a backend is
selected) and `wrr_mem` (the selection is drawn from the candidate list) are
the totality/soundness pair used by the tiered selector in `Proxy.Balance`.
-/

import Proxy.Basic

namespace Proxy

/-- Walk the cumulative-weight intervals: residue `r` selects the first
backend whose interval contains it. -/
def pickByResidue : List Backend → Nat → Option Backend
  | [], _ => none
  | b :: bs, r => if r < b.weight then some b else pickByResidue bs (r - b.weight)

/-- Weighted round-robin: reduce the round counter modulo the total weight,
then walk the intervals. `none` only when the total weight is zero (empty
candidate list, or all weights zero). -/
def wrr (bs : List Backend) (round : Nat) : Option Backend :=
  if totalWeight bs = 0 then none
  else pickByResidue bs (round % totalWeight bs)

/-! ### Totality and membership -/

theorem pickByResidue_isSome {bs : List Backend} {r : Nat}
    (h : r < totalWeight bs) : (pickByResidue bs r).isSome := by
  induction bs generalizing r with
  | nil => simp at h
  | cons b rest ih =>
    simp only [pickByResidue]
    split
    · rfl
    · rename_i hlt
      apply ih
      simp at h
      omega

theorem pickByResidue_mem {bs : List Backend} {r : Nat} {b : Backend}
    (h : pickByResidue bs r = some b) : b ∈ bs := by
  induction bs generalizing r with
  | nil => simp [pickByResidue] at h
  | cons c rest ih =>
    simp only [pickByResidue] at h
    split at h
    · cases h; exact List.mem_cons_self ..
    · exact List.mem_cons_of_mem _ (ih h)

/-- Selection totality: positive total weight (in particular: some candidate
has positive weight) means a backend is always chosen. -/
theorem wrr_total {bs : List Backend} (h : 0 < totalWeight bs) (round : Nat) :
    (wrr bs round).isSome := by
  unfold wrr
  rw [if_neg (by omega)]
  exact pickByResidue_isSome (Nat.mod_lt _ h)

/-- The selection is always drawn from the candidate list. -/
theorem wrr_mem {bs : List Backend} {round : Nat} {b : Backend}
    (h : wrr bs round = some b) : b ∈ bs := by
  unfold wrr at h
  split at h
  · cases h
  · exact pickByResidue_mem h

/-! ### The window counter -/

/-- `cnt p n` = the number of `j < n` with `p j`. -/
def cnt (p : Nat → Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt p n + (if p n then 1 else 0)

theorem cnt_congr {p q : Nat → Bool} {n : Nat} (h : ∀ j, j < n → p j = q j) :
    cnt p n = cnt q n := by
  induction n with
  | zero => rfl
  | succ n ih =>
    simp only [cnt]
    rw [ih (fun j hj => h j (Nat.lt_succ_of_lt hj)), h n (Nat.lt_succ_self n)]

@[simp] theorem cnt_false (n : Nat) : cnt (fun _ => false) n = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cnt, ih]

@[simp] theorem cnt_true (n : Nat) : cnt (fun _ => true) n = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [cnt, ih]

/-- Split a count over `[0, a + b)` at `a`. -/
theorem cnt_split (p : Nat → Bool) (a b : Nat) :
    cnt p (a + b) = cnt p a + cnt (fun j => p (a + j)) b := by
  induction b with
  | zero => simp [cnt]
  | succ b ih =>
    show cnt p (a + b + 1) = _
    simp only [cnt, ih]
    omega

/-- Peel the first element of a count instead of the last. -/
theorem cnt_shift_one (p : Nat → Bool) (n : Nat) :
    cnt p (n + 1) = (if p 0 then 1 else 0) + cnt (fun j => p (j + 1)) n := by
  induction n with
  | zero => simp [cnt]
  | succ n ih =>
    have h1 : cnt p (n + 1 + 1) = cnt p (n + 1) + (if p (n + 1) then 1 else 0) := rfl
    have h2 : cnt (fun j => p (j + 1)) (n + 1)
        = cnt (fun j => p (j + 1)) n + (if p (n + 1) then 1 else 0) := rfl
    rw [h1, h2, ih]
    omega

/-- Sliding-window invariance: over a window of length `W`, a count of any
predicate of `(start + j) % W` does not depend on `start`. Sliding the window
by one removes residue `start % W` at the front and appends the same residue
`(start + W) % W` at the back. -/
theorem cnt_mod_window (p : Nat → Bool) (W : Nat) (start : Nat) :
    cnt (fun j => p ((start + j) % W)) W = cnt (fun j => p (j % W)) W := by
  induction start with
  | zero => simp
  | succ n ih =>
    have hpeel := cnt_shift_one (fun j => p ((n + j) % W)) W
    have hlast : cnt (fun j => p ((n + j) % W)) (W + 1)
        = cnt (fun j => p ((n + j) % W)) W
          + (if p ((n + W) % W) then 1 else 0) := rfl
    have hwrap : (n + W) % W = (n + 0) % W := by
      rw [Nat.add_mod_right, Nat.add_zero]
    rw [hwrap] at hlast
    have harg : ∀ j, j < W →
        (fun j => p ((n + (j + 1)) % W)) j = (fun j => p ((n + 1 + j) % W)) j := by
      intro j _
      have : n + (j + 1) = n + 1 + j := by omega
      simp [this]
    calc cnt (fun j => p ((n + 1 + j) % W)) W
        = cnt (fun j => p ((n + (j + 1)) % W)) W := (cnt_congr harg).symm
      _ = cnt (fun j => p ((n + j) % W)) W := by
            rw [hpeel] at hlast; omega
      _ = cnt (fun j => p (j % W)) W := ih

/-! ### The base-cycle count -/

/-- Total weight of the occurrences of `b` in the list (a backend appearing
twice owns two intervals). Under `idsNodup` this is just `b.weight`
(`occWeight_eq_weight`). -/
def occWeight : List Backend → Backend → Nat
  | [], _ => 0
  | c :: rest, b => (if c = b then c.weight else 0) + occWeight rest b

theorem occWeight_of_not_mem {bs : List Backend} {b : Backend} (h : b ∉ bs) :
    occWeight bs b = 0 := by
  induction bs with
  | nil => rfl
  | cons c rest ih =>
    have hne : c ≠ b := by
      intro hc
      exact h (by rw [← hc]; exact List.mem_cons_self c rest)
    have hnm : b ∉ rest := fun hmem => h (List.mem_cons_of_mem _ hmem)
    simp only [occWeight, if_neg hne, ih hnm]

theorem occWeight_eq_weight {bs : List Backend} {b : Backend}
    (hnd : idsNodup bs) (hmem : b ∈ bs) : occWeight bs b = b.weight := by
  induction bs with
  | nil => cases hmem
  | cons c rest ih =>
    have hnd' : c.id ∉ rest.map Backend.id ∧ idsNodup rest := by
      simpa [idsNodup] using hnd
    simp only [occWeight]
    rcases List.mem_cons.mp hmem with hb | hb
    · subst hb
      rw [if_pos rfl, occWeight_of_not_mem
        (fun hmem' => hnd'.1 (List.mem_map_of_mem Backend.id hmem'))]
      omega
    · have hne : c ≠ b := by
        intro hc
        apply hnd'.1
        rw [hc]
        exact List.mem_map_of_mem Backend.id hb
      rw [if_neg hne, ih hnd'.2 hb]
      omega

theorem occWeight_of_totalWeight_eq_zero {bs : List Backend} {b : Backend}
    (h : totalWeight bs = 0) : occWeight bs b = 0 := by
  induction bs with
  | nil => rfl
  | cons c rest ih =>
    simp at h
    simp only [occWeight, ih h.2]
    split <;> omega

/-- Over the base cycle `[0, totalWeight bs)`, the residues selecting `b` are
exactly its cumulative-weight interval(s): the count is `occWeight bs b`. -/
theorem cnt_pick (bs : List Backend) (b : Backend) :
    cnt (fun r => decide (pickByResidue bs r = some b)) (totalWeight bs)
      = occWeight bs b := by
  induction bs with
  | nil => rfl
  | cons c rest ih =>
    rw [totalWeight_cons, cnt_split, occWeight]
    have hhead : cnt (fun r => decide (pickByResidue (c :: rest) r = some b))
        c.weight = if c = b then c.weight else 0 := by
      by_cases hc : c = b
      · subst hc
        rw [if_pos rfl]
        rw [cnt_congr (q := fun _ => true)
          (fun j hj => by simp [pickByResidue, hj])]
        exact cnt_true _
      · rw [if_neg hc]
        rw [cnt_congr (q := fun _ => false)
          (fun j hj => by simp [pickByResidue, hj, hc])]
        exact cnt_false _
    have htail : cnt (fun j =>
          decide (pickByResidue (c :: rest) (c.weight + j) = some b))
        (totalWeight rest)
        = cnt (fun r => decide (pickByResidue rest r = some b))
          (totalWeight rest) := by
      apply cnt_congr
      intro j _
      have hge : ¬ (c.weight + j < c.weight) := by omega
      simp only [pickByResidue, if_neg hge, Nat.add_sub_cancel_left]
    rw [hhead, htail, ih]

/-! ### The fairness theorems -/

/-- **Exact window fairness (general form).** Over any window of
`W = totalWeight bs` consecutive rounds, starting anywhere, backend `b` is
selected exactly `occWeight bs b` times. -/
theorem wrr_window_exact (bs : List Backend) (b : Backend) (start : Nat) :
    cnt (fun j => decide (wrr bs (start + j) = some b)) (totalWeight bs)
      = occWeight bs b := by
  by_cases hW : totalWeight bs = 0
  · rw [hW, occWeight_of_totalWeight_eq_zero hW]; rfl
  · have hsel : ∀ j, (fun j => decide (wrr bs (start + j) = some b)) j
        = (fun j => (fun r => decide (pickByResidue bs r = some b))
            ((start + j) % totalWeight bs)) j := by
      intro j; simp only [wrr, if_neg hW]
    rw [cnt_congr (fun j _ => hsel j),
      cnt_mod_window (fun r => decide (pickByResidue bs r = some b))
        (totalWeight bs) start,
      cnt_congr (q := fun r => decide (pickByResidue bs r = some b))
        (fun j hj => by rw [Nat.mod_eq_of_lt hj]),
      cnt_pick]

/-- **Exact window fairness.** With pairwise-distinct backend identities, any
window of `totalWeight bs` consecutive rounds selects each member exactly its
weight's worth of times — the "±1 of its weight proportion" fairness bound
holds with slack zero at full-cycle windows. The candidate list (the healthy
set and the weights) is held fixed across the window; a health flip mid-window
restarts the fairness clock, as it must. -/
theorem wrr_window_weight {bs : List Backend} {b : Backend}
    (hnd : idsNodup bs) (hmem : b ∈ bs) (start : Nat) :
    cnt (fun j => decide (wrr bs (start + j) = some b)) (totalWeight bs)
      = b.weight := by
  rw [wrr_window_exact, occWeight_eq_weight hnd hmem]

end Proxy

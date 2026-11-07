/-
# Dregg2.Policy.Factor — the absence automaton by a checked factor (subset) construction.

Compiling `absenceOf R = neg (any* · R · any*)` by derivatives is correct but impractical: the
derivative terms of a factor search are `≅`-distinct for every SET of partial matches, and ACI
similarity does not identify them by language. Measured on the compiled `policyc`: `"{{"` 9 ms,
but the 10-byte literal `"-----BEGIN"`, the alternation `"password=" | "secret=" | "api_key="`
and `"AKIA" [A-Z]{2}` each exceeded 60 s [MEASURED].

So the absence automaton is built from the WHOLE-WORD table `D` of `R` (fast by derivatives, then
minimized): its states are pairs `(S, found)` where `S` is the set of `D`-states reached by the
suffixes of the input read so far. `absRun_spec` proves, for every byte word, that `found` holds
iff some factor is accepted by `D` (and, while not found, `S` is exactly the suffix-run set).
The explored, numbered table `E` is then certified by `labCheck`, an enumeration that every
numbered state's successor carries the abstract successor's label; `labCheck_run` transfers the
abstract theorem to `E`. Exploration itself needs no proof.

The end-to-end statement `absence_decides`: `E` accepts `w` iff no factor of `w` matches the
surface regex, i.e. `Certified (absenceOf (elabRe r))`.
-/
import Dregg2.Policy.Compile

namespace Dregg2.Policy

open Dregg2.Crypto.Deriv
open Dregg2.Crypto.Deriv.PredRE

set_option autoImplicit false

/-! ## The abstract factor automaton over a table `D`. -/

/-- A set of `D`-states as a bitmap of length `D.n`. -/
abbrev Bits := List Bool

def memB (S : Bits) (q : Nat) : Bool := S.getD q false

/-- Membership read from the array copy of the bitmap (constant time, not `O(q)`). -/
theorem memB_toArray (S : Bits) (q : Nat) : S.toArray.getD q false = memB S q := by
  simp [memB, Array.getD, List.getD]
  by_cases h : q < S.length <;> simp [h]

/-- One source's contribution to the successor image. -/
def imgStep (D : Table) (Sa : Array Bool) (b : Nat) (acc : Array Bool) (p : Nat) : Array Bool :=
  if Sa.getD p false then acc.setIfInBounds (D.step p b) true else acc

theorem imgStep_size (D : Table) (Sa : Array Bool) (b : Nat) (acc : Array Bool) (p : Nat) :
    (imgStep D Sa b acc p).size = acc.size := by
  unfold imgStep; split <;> simp

theorem imgStep_getD (D : Table) (S : Bits) (b q p : Nat) (acc : Array Bool) (hq : q < acc.size) :
    (imgStep D S.toArray b acc p).getD q false = (acc.getD q false || (memB S p && D.step p b == q)) := by
  unfold imgStep
  rw [memB_toArray S p]
  cases memB S p
  · simp
  · by_cases he : D.step p b = q
    · subst he; simp [Array.getD, hq]
    · simp [Array.getD, Array.getElem_setIfInBounds, he, hq]

theorem img_getD (D : Table) (S : Bits) (b q : Nat) :
    ∀ (L : List Nat) (acc : Array Bool), q < acc.size →
      (L.foldl (imgStep D S.toArray b) acc).getD q false =
        (acc.getD q false || L.any (fun p => memB S p && D.step p b == q)) := by
  intro L
  induction L with
  | nil => intro acc _; simp
  | cons p L ih =>
    intro acc hq
    simp only [List.foldl_cons, List.any_cons]
    rw [ih _ (by rw [imgStep_size]; exact hq), imgStep_getD D S b q p acc hq, Bool.or_assoc]

/-- Successor set: every state stepped by `b`, plus `D.start` (the empty suffix). The image is
collected into an array in one pass over the active sources. -/
def nextSet (D : Table) (S : Bits) (b : Nat) : Bits :=
  let img := (List.range D.n).foldl (imgStep D S.toArray b) (Array.replicate D.n false)
  (List.range D.n).map fun q => q == D.start || img.getD q false

/-- The array image is exactly the original pointwise set semantics, for every table, bitmap
and byte. Membership and stepping are computed once per source, rather than once per destination. -/
theorem nextSet_spec (D : Table) (S : Bits) (b : Nat) :
    nextSet D S b = (List.range D.n).map (fun q => q == D.start ||
      (List.range D.n).any (fun p => memB S p && D.step p b == q)) := by
  unfold nextSet
  apply List.map_congr_left
  intro q hq
  rw [List.mem_range] at hq
  rw [img_getD D S b q _ _ (by simpa using hq)]
  simp [Array.getD, hq]

/-- Some state of the bitmap accepts (the bitmap read through its array copy). -/
def anyAcc (D : Table) (S : Bits) : Bool :=
  let Sa := S.toArray
  (List.range D.n).any (fun q => Sa.getD q false && D.acc q)

theorem anyAcc_spec (D : Table) (S : Bits) :
    anyAcc D S = (List.range D.n).any (fun q => memB S q && D.acc q) := by
  simp only [anyAcc, memB_toArray]

def absInit (D : Table) : Bits × Bool :=
  let S := (List.range D.n).map (· == D.start)
  (S, anyAcc D S)

/-- Once found, the state collapses to the sink `([], true)`. -/
def absStep (D : Table) (x : Bits × Bool) (b : Nat) : Bits × Bool :=
  if x.2 then ([], true) else
    let S := nextSet D x.1 b
    (S, anyAcc D S)

def absRun (D : Table) (w : List Nat) : Bits × Bool := w.foldl (absStep D) (absInit D)

/-- `D` is closed on bytes. -/
def closedB (D : Table) : Bool :=
  decide (D.start < D.n) && (List.range D.n).all (fun s => (List.range 256).all (fun b => decide (D.step s b < D.n)))

theorem memB_map_range (n : Nat) (f : Nat → Bool) (q : Nat) :
    memB ((List.range n).map f) q = (decide (q < n) && f q) := by
  unfold memB
  by_cases h : q < n
  · simp [List.getD, h]
  · simp [List.getD, h]

theorem closed_run {D : Table} (hD : closedB D = true) :
    ∀ (v : List Nat), v.all (· < 256) = true → ∀ s, s < D.n → D.run s v < D.n := by
  simp only [closedB, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hD
  intro v
  induction v with
  | nil => intro _ s hs; exact hs
  | cons b v ih =>
    intro hv s hs
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hv
    exact ih hv.2 _ (hD.2 s hs b hv.1)

theorem run_append_single (D : Table) (s : Nat) (v : List Nat) (b : Nat) :
    D.run s (v ++ [b]) = D.step (D.run s v) b := by
  simp [Table.run, List.foldl_append]

/-! ## List facts: suffixes and factors of `w ++ [b]`. -/

theorem suffix_snoc {α : Type} (w : List α) (b : α) (v : List α) :
    (∃ u, w ++ [b] = u ++ v) ↔ v = [] ∨ ∃ v', v = v' ++ [b] ∧ ∃ u, w = u ++ v' := by
  constructor
  · rintro ⟨u, hu⟩
    rcases List.eq_nil_or_concat v with rfl | ⟨v', c, rfl⟩
    · left; rfl
    · right
      rw [List.concat_eq_append, ← List.append_assoc] at hu
      obtain ⟨h1, h2⟩ := List.append_inj' hu rfl
      simp only [List.cons.injEq, and_true] at h2
      subst h2
      exact ⟨v', by simp, u, h1⟩
  · rintro (rfl | ⟨v', rfl, u, rfl⟩)
    · exact ⟨w ++ [b], by simp⟩
    · exact ⟨u, by simp⟩

theorem factor_snoc {α : Type} (P : List α → Prop) (w : List α) (b : α) :
    (∃ x y z, w ++ [b] = x ++ y ++ z ∧ P y) ↔
      (∃ x y z, w = x ++ y ++ z ∧ P y) ∨ (∃ u v, w ++ [b] = u ++ v ∧ P v) := by
  constructor
  · rintro ⟨x, y, z, h, hp⟩
    rcases List.eq_nil_or_concat z with rfl | ⟨z', c, rfl⟩
    · right; exact ⟨x, y, by simpa using h, hp⟩
    · left
      have : w ++ [b] = (x ++ y ++ z') ++ [c] := by rw [h]; simp
      obtain ⟨h1, -⟩ := List.append_inj' this rfl
      exact ⟨x, y, z', h1, hp⟩
  · rintro (⟨x, y, z, rfl, hp⟩ | ⟨u, v, h, hp⟩)
    · exact ⟨x, y, z ++ [b], by simp, hp⟩
    · exact ⟨u, v, [], by simpa using h, hp⟩

/-! ## ⚑ The abstract invariant. -/

/-- After reading `w`: `found` iff some factor of `w` is accepted by `D`; while not found, `S` is
exactly the set of `D`-states reached by the suffixes of `w`. -/
theorem absRun_spec (D : Table) (hD : closedB D = true) :
    ∀ (w : List Nat), w.all (· < 256) = true →
      ((absRun D w).2 = true ↔ ∃ x y z, w = x ++ y ++ z ∧ D.acc (D.run D.start y) = true) ∧
      ((absRun D w).2 = false → ∀ q, memB (absRun D w).1 q = true ↔ ∃ u v, w = u ++ v ∧ D.run D.start v = q) := by
  have hst : D.start < D.n := by
    simp only [closedB, Bool.and_eq_true, decide_eq_true_eq] at hD; exact hD.1
  intro w
  induction w using List.reverseRecOn with
  | nil =>
    intro _
    have hS : ∀ q, memB (absInit D).1 q = true ↔ ∃ u v, ([] : List Nat) = u ++ v ∧ D.run D.start v = q := by
      intro q
      simp only [absInit, memB_map_range, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
      constructor
      · rintro ⟨-, rfl⟩; exact ⟨[], [], rfl, rfl⟩
      · rintro ⟨u, v, h, rfl⟩
        obtain ⟨-, rfl⟩ := List.append_eq_nil_iff.mp h.symm
        exact ⟨hst, rfl⟩
    refine ⟨?_, fun _ => hS⟩
    simp only [absRun, List.foldl_nil, absInit, anyAcc_spec, List.any_eq_true, List.mem_range,
      Bool.and_eq_true]
    constructor
    · rintro ⟨q, hq, hm, ha⟩
      have := (hS q).mp (by simpa [absInit] using hm)
      obtain ⟨u, v, h, rfl⟩ := this
      obtain ⟨rfl, rfl⟩ := List.append_eq_nil_iff.mp h.symm
      exact ⟨[], [], [], rfl, ha⟩
    · rintro ⟨x, y, z, h, ha⟩
      have hy : y = [] := by
        have := congrArg List.length h; simp at this; exact List.length_eq_zero_iff.mp (by omega)
      subst hy
      refine ⟨D.start, hst, ?_, ha⟩
      simp [memB_map_range, hst]
  | append_singleton w b ih =>
    intro hw
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_true] at hw
    obtain ⟨ih1, ih2⟩ := ih hw.1
    have hrun : absRun D (w ++ [b]) = absStep D (absRun D w) b := by
      simp [absRun, List.foldl_append]
    rw [hrun]
    cases hf : (absRun D w).2 with
    | true =>
      have hfac := ih1.mp hf
      refine ⟨?_, ?_⟩
      · simp only [absStep, hf, if_true, true_iff]
        obtain ⟨x, y, z, h, ha⟩ := hfac
        exact ⟨x, y, z ++ [b], by simp [h], ha⟩
      · intro h; simp [absStep, hf] at h
    | false =>
      have hS := ih2 hf
      -- the successor set is the suffix-run set of `w ++ [b]`
      have hS' : ∀ q, memB (nextSet D (absRun D w).1 b) q = true ↔
          ∃ u v, w ++ [b] = u ++ v ∧ D.run D.start v = q := by
        intro q
        simp only [nextSet_spec, memB_map_range, Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true,
          beq_iff_eq, List.any_eq_true, List.mem_range]
        constructor
        · rintro ⟨-, rfl | ⟨p, hp, hm, rfl⟩⟩
          · exact ⟨w ++ [b], [], by simp, rfl⟩
          · obtain ⟨u, v, rfl, rfl⟩ := (hS p).mp hm
            exact ⟨u, v ++ [b], by simp, run_append_single _ _ _ _⟩
        · rintro ⟨u, v, h, rfl⟩
          have hv := (suffix_snoc w b v).mp ⟨u, h⟩
          have hvb : v.all (· < 256) = true := by
            have : (w ++ [b]).all (· < 256) = true := by simp [hw.1, hw.2]
            rw [h] at this; simp only [List.all_append, Bool.and_eq_true] at this; exact this.2
          refine ⟨closed_run hD v hvb _ hst, ?_⟩
          rcases hv with rfl | ⟨v', rfl, u', rfl⟩
          · left; rfl
          · right
            refine ⟨D.run D.start v', ?_, (hS _).mpr ⟨u', v', rfl, rfl⟩, by rw [run_append_single]⟩
            have : v'.all (· < 256) = true := by
              simp only [List.all_append, Bool.and_eq_true] at hw; exact hw.1.2
            exact closed_run hD v' this _ hst
      refine ⟨?_, fun _ => by simpa [absStep, hf] using hS'⟩
      simp only [absStep, hf, Bool.false_eq_true, if_false, anyAcc_spec, List.any_eq_true,
        List.mem_range, Bool.and_eq_true]
      rw [factor_snoc (fun y => D.acc (D.run D.start y) = true)]
      constructor
      · rintro ⟨q, -, hm, ha⟩
        obtain ⟨u, v, h, rfl⟩ := (hS' q).mp hm
        exact Or.inr ⟨u, v, h, ha⟩
      · rintro (hfac | ⟨u, v, h, ha⟩)
        · rw [← ih1, hf] at hfac; exact absurd hfac (by simp)
        · have hvb : v.all (· < 256) = true := by
            have : (w ++ [b]).all (· < 256) = true := by simp [hw.1, hw.2]
            rw [h] at this; simp only [List.all_append, Bool.and_eq_true] at this; exact this.2
          refine ⟨D.run D.start v, ?_, (hS' _).mpr ⟨u, v, h, rfl⟩, ha⟩
          have hst' := hst
          exact closed_run hD v hvb _ hst'

/-! ## Numbering the explored states, certified by enumeration. -/

/-- `lab` labels each numbered state with its abstract state; `labCheck` enumerates that the
numbering commutes with the abstract step on every byte and that acceptance is `¬ found`. -/
def labCheck (D : Table) (E : Table) (lab : Nat → Bits × Bool) : Bool :=
  decide (E.start < E.n) && lab E.start == absInit D &&
  (List.range E.n).all (fun k => E.acc k == !(lab k).2 &&
    (List.range 256).all (fun b => decide (E.step k b < E.n) && lab (E.step k b) == absStep D (lab k) b))

theorem labCheck_run {D E : Table} {lab : Nat → Bits × Bool} (h : labCheck D E lab = true) :
    ∀ (w : List Nat), w.all (· < 256) = true →
      lab (E.run E.start w) = absRun D w ∧ E.run E.start w < E.n := by
  simp only [labCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at h
  obtain ⟨⟨hs, hl⟩, hall⟩ := h
  intro w
  induction w using List.reverseRecOn with
  | nil => intro _; exact ⟨hl, hs⟩
  | append_singleton w b ih =>
    intro hw
    simp only [List.all_append, List.all_cons, List.all_nil, Bool.and_eq_true, decide_eq_true_eq,
      Bool.and_true] at hw
    obtain ⟨i1, i2⟩ := ih hw.1
    obtain ⟨h1, h2⟩ := (hall _ i2).2 b hw.2
    refine ⟨?_, ?_⟩
    · rw [run_append_single, h2, i1]; simp [absRun, List.foldl_append]
    · rw [run_append_single]; exact h1

/-! ## Byte classes: checking one byte per column class. -/

/-- Bytes with equal `D`-columns have equal abstract successors. -/
theorem absStep_col (D : Table) (x : Bits × Bool) (b c : Nat)
    (h : ∀ p, p < D.n → D.step p b = D.step p c) : absStep D x b = absStep D x c := by
  have hs : nextSet D x.1 b = nextSet D x.1 c := by
    rw [nextSet_spec, nextSet_spec]
    apply List.map_congr_left
    intro q _
    congr 1
    apply Bool.eq_iff_iff.mpr
    simp only [List.any_eq_true, List.mem_range, Bool.and_eq_true, beq_iff_eq]
    constructor
    · rintro ⟨p, hp, hm, he⟩; exact ⟨p, hp, hm, by rw [← h p hp]; exact he⟩
    · rintro ⟨p, hp, hm, he⟩; exact ⟨p, hp, hm, by rw [h p hp]; exact he⟩
  unfold absStep
  rw [hs]

/-- `rep` maps every byte to a byte `< 256` with the same `D`-column, and is idempotent. -/
def colCheck (D : Table) (rep : Nat → Nat) : Bool :=
  (List.range 256).all fun b => decide (rep b < 256) && rep (rep b) == rep b &&
    (List.range D.n).all fun p => D.step p b == D.step p (rep b)

/-- `labCheck`, comparing labels only at class representatives: any other byte must step to the
same numbered state as its representative. -/
def labCheckRep (D : Table) (E : Table) (lab : Nat → Bits × Bool) (rep : Nat → Nat) : Bool :=
  colCheck D rep && decide (E.start < E.n) && lab E.start == absInit D &&
  (List.range E.n).all (fun k => E.acc k == !(lab k).2 &&
    (List.range 256).all (fun b => decide (E.step k b < E.n) &&
      if rep b == b then lab (E.step k b) == absStep D (lab k) b
      else E.step k b == E.step k (rep b)))

/-- The representative check implies the full check. -/
theorem labCheckRep_sound {D E : Table} {lab : Nat → Bits × Bool} {rep : Nat → Nat}
    (h : labCheckRep D E lab rep = true) : labCheck D E lab = true := by
  simp only [labCheckRep, colCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq,
    List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨hcol, hs⟩, hl⟩, hall⟩ := h
  simp only [labCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range]
  refine ⟨⟨hs, hl⟩, fun k hk => ⟨(hall k hk).1, fun b hb => ?_⟩⟩
  obtain ⟨hlt, hb'⟩ := (hall k hk).2 b hb
  refine ⟨hlt, ?_⟩
  obtain ⟨⟨hr, hrr⟩, hc⟩ := hcol b hb
  by_cases he : rep b = b
  · simpa [he] using hb'
  · simp only [he, if_false, beq_iff_eq] at hb'
    have hrep := ((hall k hk).2 (rep b) hr).2
    simp only [hrr, if_true, beq_iff_eq, beq_self_eq_true] at hrep
    rw [hb', hrep]
    exact (absStep_col D (lab k) b (rep b) (fun p hp => hc p hp)).symm

/-- ⚑ **`factor_decides`** — a label-checked table accepts exactly the words with no factor
accepted by `D`. -/
theorem factor_decides {D E : Table} {lab : Nat → Bits × Bool} (hD : closedB D = true)
    (h : labCheck D E lab = true) (w : List Nat) (hw : w.all (· < 256) = true) :
    E.acc (E.run E.start w) = true ↔ ¬ ∃ x y z, w = x ++ y ++ z ∧ D.acc (D.run D.start y) = true := by
  have hh := h
  simp only [labCheck, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, List.all_eq_true,
    List.mem_range] at hh
  obtain ⟨i1, i2⟩ := labCheck_run h w hw
  have hacc := (hh.2 _ i2).1
  rw [hacc, i1, ← (absRun_spec D hD w hw).1]
  cases (absRun D w).2 <;> simp

/-- ⚑⚑ **`absence_decides`** — from a certified whole-word table for `elabRe r`, a label-checked
factor table decides the absence semantics of `r` on every byte word. -/
theorem absence_decides (r : Re) (D : Certified (elabRe r)) (hD : closedB D.t = true) {E : Table}
    {lab : Nat → Bits × Bool} (h : labCheck D.t E lab = true) (w : List Nat) (hw : w.all (· < 256) = true) :
    E.acc (E.run E.start w) = true ↔ ¬ ∃ x y z, w = x ++ y ++ z ∧ ReSem r y := by
  rw [factor_decides hD h w hw]
  apply not_congr
  constructor
  · rintro ⟨x, y, z, rfl, ha⟩
    have hy : y.all (· < 256) = true := by
      simp only [List.all_append, Bool.and_eq_true] at hw; exact hw.1.2
    exact ⟨x, y, z, rfl, (elabRe_derives r y).mp ((D.hdec y hy).mp ha)⟩
  · rintro ⟨x, y, z, rfl, hs⟩
    have hy : y.all (· < 256) = true := by
      simp only [List.all_append, Bool.and_eq_true] at hw; exact hw.1.2
    exact ⟨x, y, z, rfl, (D.hdec y hy).mpr ((elabRe_derives r y).mpr hs)⟩

/-- The same table as a `Certified (absenceOf (elabRe r))`, so it flows through minimization. -/
def Certified.ofFactor (r : Re) (D : Certified (elabRe r)) (hD : closedB D.t = true) (E : Table)
    (lab : Nat → Bits × Bool) (h : labCheck D.t E lab = true) : Certified (absenceOf (elabRe r)) :=
  ⟨E, fun w hw => by
    rw [absence_decides r D hD h w hw, correctness, absenceOf_semantics]⟩

/-! ## Exploration (unproved; its output is checked). -/

/-- Breadth-first exploration of the reachable abstract states; returns the labels and the
numbered transition rows, or `none` when `limit` states are exceeded. -/
def explore (D : Table) (limit : Nat) : Option (Array (Bits × Bool) × Array (Array Nat)) :=
  exploreStatesRep (absInit D) (absStep D) (byteReps D) limit

/-- Checked absence construction from any certified whole-word table. This lets compositional
compilers reuse the factor theorem without repeating derivative determinization. -/
def certifyAbsenceFrom (r : Re) (D : Certified (elabRe r)) (notes : List String := [])
    (limit : Nat := 100000) : Except String (Certified (absenceOf (elabRe r)) × List String) := do
  if hD : closedB D.t = true then
    let reps := byteReps D.t
    match exploreStatesRep (absInit D.t) (absStep D.t) reps limit with
    | none => .error s!"factor construction exceeded {limit} states"
    | some (labels, rows) =>
      let E : Table := ⟨labels.size, fun k b => (rows.getD k #[]).getD b 0,
        fun k => !(labels.getD k ([], false)).2, 0⟩
      let lab := fun k => labels.getD k ([], false)
      if h : labCheckRep D.t E lab (fun b => reps.getD b b) = true then
        let c0 := Certified.ofFactor r D hD E lab (labCheckRep_sound h)
        pure (c0.optimize notes)
      else .error "factor table failed its label check"
  else .error "whole-word table is not closed"

/-- Whole-word compilation followed by the checked factor construction. -/
def certifyAbsence (r : Re) (limit : Nat := 100000) :
    Except String (Certified (absenceOf (elabRe r)) × List String) := do
  let (D, notes) ← certify (elabRe r)
  certifyAbsenceFrom r D notes limit

/-- The image includes active successors and excludes inactive ones. -/
theorem nextSet_discriminates :
    nextSet ⟨3, fun s _ => if s = 0 then 1 else 2, fun _ => false, 0⟩
      [true, false, false] 7 = [true, true, false] ∧
    nextSet ⟨3, fun s _ => if s = 0 then 1 else 2, fun _ => false, 0⟩
      [false, true, false] 7 = [true, false, true] := by constructor <;> rfl

/-- info: 'Dregg2.Policy.nextSet_discriminates' does not depend on any axioms -/
#guard_msgs in
#print axioms nextSet_discriminates

/-- info: 'Dregg2.Policy.nextSet_spec' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms nextSet_spec

#assert_all_clean [absStep_col, labCheckRep_sound, nextSet_spec, anyAcc_spec, imgStep_getD, img_getD, memB_toArray, nextSet_discriminates, suffix_snoc, factor_snoc, absRun_spec, labCheck_run, factor_decides, absence_decides,
  closed_run]

end Dregg2.Policy

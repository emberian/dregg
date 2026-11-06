/-
The generated eight-lane route's semantic refinement. The only acceptance premise
is its added row constraints, shared by scalar and full-map denotations. Canonical
field cells and an admitted trace height below the characteristic turn congruences
into exact equalities; no hash injectivity premise occurs.
-/
import Dregg2.Circuit.Emit.RouteChain8
import Dregg2.Circuit.Emit.RouteChain8Binding
namespace Dregg2.Circuit.Emit.RouteChain8Refine
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (envAt_loc envAt_nxt)
open Dregg2.Circuit.Emit.RouteChain8
open Dregg2.Circuit.Emit.RouteChain8Binding (preimage fold)
set_option autoImplicit false

/-- Only generated route constraints, so both scalar and lanes8 acceptance can supply it. -/
def RowsHold (c : Config) (hash : List ℤ → ℤ) (t : VmTrace) : Prop :=
  ∀ i < t.rows.length, ∀ x ∈ constraints c,
    x.holdsAt hash t.tf (envAt t i) (i == 0) (i + 1 == t.rows.length)

/-- BabyBear representatives: guaranteed by the field type on the served path. -/
structure Canonical (t : VmTrace) : Prop where
  row : ∀ i (hi : i < t.rows.length) j, 0 ≤ t.rows[i] j ∧ t.rows[i] j < 2013265921
  pub : ∀ j, 0 ≤ t.pub j ∧ t.pub j < 2013265921

def seed (c : Config) (t : VmTrace) : List ℤ :=
  lanes.map fun j => match c.seed with | none => 0 | some k => t.pub (k+j)
def output (c : Config) (a : Assignment) : List ℤ := lanes.map fun j => a (out c j)
def previous (c : Config) (a : Assignment) : List ℤ := lanes.map fun j => a (acc c j)
def publicRoute (c : Config) (t : VmTrace) : List ℤ := lanes.map fun j => t.pub (routePi c j)
def payload (c : Config) (a : Assignment) : List ℤ :=
  [c.domain, a (index c), a c.current, a c.symbol, a c.next]
def payloads (c : Config) (t : VmTrace) : List (List ℤ) := t.rows.map (payload c)

theorem payload_width (c : Config) (t : VmTrace) : ∀ p ∈ payloads c t, p.length = 5 := by
  intro p hp
  obtain ⟨a, _, rfl⟩ := List.mem_map.mp hp
  rfl

theorem canonical_eq {a b : ℤ} (hm : a ≡ b [ZMOD 2013265921])
    (ha : 0 ≤ a ∧ a < 2013265921) (hb : 0 ≤ b ∧ b < 2013265921) : a = b := by
  obtain ⟨k, hk⟩ := hm.dvd
  omega

section Extraction
variable {c : Config} {hash : List ℤ → ℤ} {t : VmTrace}

theorem row_hash (H : List ℤ → List ℤ) (hs : ChipTableSoundN H (t.tf .poseidon2))
    (h : RowsHold c hash t) {i : Nat} (hi : i < t.rows.length) :
    output c t.rows[i] = H (preimage (previous c t.rows[i]) (payload c t.rows[i])) := by
  have hc := h i hi (chip c) (by simp [constraints])
  have hm : (chipLookupTupleN (inputs c) (lanes.map (out c))).map
      (·.eval t.rows[i]) ∈ t.tf .poseidon2 := by
    simpa only [chip, VmConstraint2.holdsAt, Lookup.holdsAt, envAt_loc hi] using hc
  have he := chip_lookup_sound_N H (t.tf .poseidon2) hs t.rows[i] (inputs c)
    (lanes.map (out c)) (by chip_arity_admitted) hm
  simpa [output, previous, payload, preimage, inputs, lanes, EmittedExpr.eval] using he

theorem index_exact (h : RowsHold c hash t) (hc : Canonical t)
    (hheight : t.rows.length < 2013265921) :
    ∀ i (hi : i < t.rows.length), t.rows[i] (index c) = (i+1 : Nat) := by
  intro i
  induction i with
  | zero =>
    intro hi
    have hh := h 0 hi (indexFirst c) (by simp [constraints])
    have hm : t.rows[0] (index c) + (-1) ≡ 0 [ZMOD 2013265921] := by
      simpa [indexFirst, VmConstraint2.holdsAt, VmConstraint.holdsVm, EmittedExpr.eval,
        envAt_loc hi] using hh
    obtain ⟨k, hk⟩ := hm.dvd
    have hn := hc.row 0 hi (index c)
    omega
  | succ i ih =>
    intro hi
    have hi0 : i < t.rows.length := by omega
    have hp := ih hi0
    have hh := h i hi0 (indexStep c) (by simp [constraints])
    have hlast : (i+1 == t.rows.length) = false := by simp; omega
    have hm : t.rows[i+1] (index c) + (-1) * t.rows[i] (index c) + (-1) ≡
        0 [ZMOD 2013265921] := by
      simpa [indexStep, VmConstraint2.holdsAt, WindowConstraint.holdsAt, hlast,
        WindowExpr.eval, envAt_loc hi0, envAt_nxt hi] using hh
    obtain ⟨k, hk⟩ := hm.dvd
    have hn := hc.row (i+1) hi (index c)
    have hb : (i+1 : ℤ) + 1 < 2013265921 := by omega
    simp only [Nat.cast_add, Nat.cast_one] at hp ⊢
    omega

/-- Public length is derived from the AIR and admitted height, never an arbitrary caller equality. -/
theorem length_exact (h : RowsHold c hash t) (hc : Canonical t)
    (hne : t.rows ≠ []) (hheight : t.rows.length < 2013265921) :
    t.pub (lengthPi c) = (t.rows.length : ℤ) := by
  have hp : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hi : t.rows.length-1 < t.rows.length := by omega
  have hh := h (t.rows.length-1) hi (indexLast c) (by simp [constraints])
  have hm : t.rows[t.rows.length-1] (index c) ≡ t.pub (lengthPi c) [ZMOD 2013265921] := by
    simpa [indexLast, VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt_loc hi,
      show t.rows.length - 1 + 1 = t.rows.length by omega] using hh
  have he := canonical_eq hm (hc.row _ hi _) (hc.pub _)
  rw [← he, index_exact h hc hheight _ hi]
  congr 1
  omega

theorem seed_exact (h : RowsHold c hash t) (hc : Canonical t)
    (hi : 0 < t.rows.length) : previous c t.rows[0] = seed c t := by
  apply List.map_congr_left
  intro j hj
  have hh := h 0 hi (seedPin c j) (by simp [constraints]; aesop)
  cases hs : c.seed with
  | none =>
    have hm : t.rows[0] (acc c j) ≡ 0 [ZMOD 2013265921] := by
      simpa [seedPin, hs, VmConstraint2.holdsAt, VmConstraint.holdsVm, EmittedExpr.eval,
        envAt_loc hi] using hh
    change t.rows[0] (acc c j) = 0
    exact canonical_eq hm (hc.row 0 hi _) (by omega)
  | some k =>
    have hm : t.rows[0] (acc c j) ≡ t.pub (k+j) [ZMOD 2013265921] := by
      simpa [seedPin, hs, VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt_loc hi] using hh
    exact canonical_eq hm (hc.row 0 hi _) (hc.pub _)

theorem copy_exact (h : RowsHold c hash t) (hc : Canonical t)
    {i : Nat} (hi : i+1 < t.rows.length) : previous c t.rows[i+1] = output c t.rows[i] := by
  apply List.map_congr_left
  intro j hj
  have hi0 : i < t.rows.length := by omega
  have hh := h i hi0 (copy c j) (by simp [constraints]; aesop)
  have hlast : (i+1 == t.rows.length) = false := by simp; omega
  have hm : t.rows[i+1] (acc c j) + (-1) * t.rows[i] (out c j) ≡ 0 [ZMOD 2013265921] := by
    simpa [copy, VmConstraint2.holdsAt, WindowConstraint.holdsAt, WindowExpr.eval,
      hlast, envAt_loc hi0, envAt_nxt hi] using hh
  obtain ⟨k, hk⟩ := hm.dvd
  have hca := hc.row (i+1) hi (acc c j)
  have hco := hc.row i hi0 (out c j)
  omega

theorem last_exact (h : RowsHold c hash t) (hc : Canonical t)
    (hne : t.rows ≠ []) : output c (t.rows.getLast hne) = publicRoute c t := by
  have hp : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hi : t.rows.length-1 < t.rows.length := by omega
  rw [List.getLast_eq_getElem hne]
  apply List.map_congr_left
  intro j hj
  have hh := h (t.rows.length-1) hi (outputPin c j) (by simp [constraints]; aesop)
  have hm : t.rows[t.rows.length-1] (out c j) ≡ t.pub (routePi c j) [ZMOD 2013265921] := by
    simpa [outputPin, VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt_loc hi,
      show t.rows.length - 1 + 1 = t.rows.length by omega] using hh
  exact canonical_eq hm (hc.row _ hi _) (hc.pub _)
end Extraction

private theorem fold_append (H : List ℤ → List ℤ) (s : List ℤ)
    (xs ys : List (List ℤ)) : fold H s (xs ++ ys) = fold H (fold H s xs) ys := by
  induction xs generalizing s with
  | nil => rfl
  | cons a as ih => exact ih _

/-- The public eight-lane route is the fold of the actual ordered payloads. -/
theorem route_eq_fold {c : Config} {hash : List ℤ → ℤ} {t : VmTrace}
    (H : List ℤ → List ℤ) (hs : ChipTableSoundN H (t.tf .poseidon2))
    (h : RowsHold c hash t) (hc : Canonical t) (hne : t.rows ≠ []) :
    publicRoute c t = fold H (seed c t) (payloads c t) := by
  have hprefix : ∀ i (hi : i < t.rows.length),
      fold H (seed c t) ((t.rows.take (i+1)).map (payload c)) = output c t.rows[i] := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [List.take_succ_eq_append_getElem hi]
      simp only [List.take_zero, List.nil_append, List.map_cons, List.map_nil, fold]
      rw [← seed_exact h hc hi]
      exact (row_hash H hs h hi).symm
    | succ i ih =>
      intro hi
      have hi0 : i < t.rows.length := by omega
      rw [List.take_succ_eq_append_getElem hi, List.map_append, fold_append, ih hi0]
      simp only [List.map_cons, List.map_nil, fold]
      rw [← copy_exact h hc hi]
      exact (row_hash H hs h hi).symm
  have hp : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hi : t.rows.length-1 < t.rows.length := by omega
  have he := hprefix (t.rows.length-1) hi
  rw [show t.rows.length - 1 + 1 = t.rows.length by omega, List.take_length] at he
  rw [← last_exact h hc hne, List.getLast_eq_getElem hne]
  exact he.symm

/-- info: 'Dregg2.Circuit.Emit.RouteChain8Refine.index_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms index_exact
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Refine.length_exact' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms length_exact
/-- info: 'Dregg2.Circuit.Emit.RouteChain8Refine.route_eq_fold' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms route_eq_fold
end Dregg2.Circuit.Emit.RouteChain8Refine

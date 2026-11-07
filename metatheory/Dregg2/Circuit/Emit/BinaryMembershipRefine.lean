/-
The generated binary-membership descriptor certifies an arbitrary dir-ordered
binary authentication path. All rows, including the final row, enforce direction
and child order. The depth argument labels the descriptor; it does not constrain
the trace height. The theorem intentionally identifies only the actual row count.
-/
import Dregg2.Circuit.Emit.BinaryMembershipEmit
import Dregg2.Circuit.Emit.AdjacencyMembershipRefine
import Dregg2.Circuit.Emit.DfaRoutingTableEmit
namespace Dregg2.Circuit.Emit.BinaryMembershipRefine
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.Emit.DfaRoutingTableEmit (envAt_loc envAt_nxt)
open Dregg2.Circuit.Emit.AdjacencyMembershipRefine
  (Canon combine foldNode foldNode_concat eq_of_modEq_canon bit_of_modEq_canon)
open Dregg2.Circuit.Emit.EffectVmEmitTransfer (gate_modEq_iff)
open Dregg2.Circuit.Emit.BinaryMembershipEmit
set_option autoImplicit false

/-- Canonical representatives supplied by the deployed field-valued witness. -/
structure Canonical (t : VmTrace) : Prop where
  row : ∀ i (hi : i < t.rows.length) j, Canon (t.rows[i] j)
  pub : ∀ j, Canon (t.pub j)

/-- The complete authentication path, lowest level first; no row is dropped. -/
def path (t : VmTrace) : List (ℤ × ℤ) := t.rows.map fun a => (a DIR, a SIB)

section Extract
variable {hash : List ℤ → ℤ} {depth : Nat} {minit : ℤ → ℤ}
variable {mfin : ℤ → ℤ × Nat} {maddrs : List ℤ} {t : VmTrace}

/-- The paired transition and final-boundary gates jointly cover every trace row. -/
theorem gate_all_rows (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (body : EmittedExpr)
    (hgate : VmConstraint2.base (.gate body) ∈ (membershipDesc depth).constraints)
    (hlast : VmConstraint2.base (.boundary .last body) ∈ (membershipDesc depth).constraints)
    {i : Nat} (hi : i < t.rows.length) : body.eval t.rows[i] ≡ 0 [ZMOD 2013265921] := by
  by_cases he : i+1 = t.rows.length
  · have hh := h.rowConstraints i hi _ hlast
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, he, envAt_loc hi] using hh
  · have hh := h.rowConstraints i hi _ hgate
    have hb : (i+1 == t.rows.length) = false := by simp [he]
    simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, hb, envAt_loc hi] using hh

theorem row_bits (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (hc : Canonical t) {i : Nat} (hi : i < t.rows.length) :
    t.rows[i] DIR = 0 ∨ t.rows[i] DIR = 1 := by
  apply bit_of_modEq_canon (hc.row i hi DIR)
  have hd := gate_all_rows h dirBody (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT])
    (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT]) hi
  convert hd using 1
  simp [dirBody, EmittedExpr.eval, sub_eq_add_neg]

theorem row_hash (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (hchip : ChipTableSound hash (t.tf .poseidon2))
    {i : Nat} (hi : i < t.rows.length) :
    t.rows[i] PAR = hash [t.rows[i] LEFT, t.rows[i] RIGHT] := by
  have hh := h.rowConstraints i hi
    (.lookup ⟨.poseidon2, chipLookupTuple [.var LEFT, .var RIGHT] PAR [6,7,8,9,10,11,12]⟩)
    (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT])
  have hm : (chipLookupTuple [.var LEFT, .var RIGHT] PAR [6,7,8,9,10,11,12]).map
      (·.eval t.rows[i]) ∈ t.tf .poseidon2 := by
    simpa only [VmConstraint2.holdsAt, Lookup.holdsAt, envAt_loc hi] using hh
  have he := chip_lookup_sound hash (t.tf .poseidon2) hchip t.rows[i]
    [.var LEFT, .var RIGHT] PAR [6,7,8,9,10,11,12] (by chip_arity_admitted) hm
  simpa [EmittedExpr.eval] using he

/-- Every row computes a genuine binary combine, including the last row. -/
theorem row_combine (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (hchip : ChipTableSound hash (t.tf .poseidon2)) (hc : Canonical t)
    {i : Nat} (hi : i < t.rows.length) :
    t.rows[i] PAR = combine hash (t.rows[i] DIR) (t.rows[i] CUR) (t.rows[i] SIB) := by
  have hl := gate_all_rows h leftBody (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT])
    (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT]) hi
  have hr := gate_all_rows h rightBody (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT])
    (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT]) hi
  have hlc : t.rows[i] LEFT ≡ t.rows[i] CUR + t.rows[i] DIR * t.rows[i] SIB -
      t.rows[i] DIR * t.rows[i] CUR [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [leftBody, neg, EmittedExpr.eval]; ring)).mp hl
  have hrc : t.rows[i] RIGHT ≡ t.rows[i] SIB + t.rows[i] DIR * t.rows[i] CUR -
      t.rows[i] DIR * t.rows[i] SIB [ZMOD 2013265921] :=
    (gate_modEq_iff (by simp only [rightBody, neg, EmittedExpr.eval]; ring)).mp hr
  rcases row_bits h hc hi with hd | hd
  · have heL : t.rows[i] LEFT = t.rows[i] CUR :=
      eq_of_modEq_canon (hc.row i hi LEFT) (hc.row i hi CUR) (by simpa [hd] using hlc)
    have heR : t.rows[i] RIGHT = t.rows[i] SIB :=
      eq_of_modEq_canon (hc.row i hi RIGHT) (hc.row i hi SIB) (by simpa [hd] using hrc)
    rw [row_hash h hchip hi, heL, heR]
    simp [combine, hd]
  · have heL : t.rows[i] LEFT = t.rows[i] SIB :=
      eq_of_modEq_canon (hc.row i hi LEFT) (hc.row i hi SIB) (by simpa [hd] using hlc)
    have heR : t.rows[i] RIGHT = t.rows[i] CUR :=
      eq_of_modEq_canon (hc.row i hi RIGHT) (hc.row i hi CUR) (by simpa [hd] using hrc)
    rw [row_hash h hchip hi, heL, heR]
    simp [combine, hd]

theorem initial_exact (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (hc : Canonical t) (hi : 0 < t.rows.length) : t.rows[0] CUR = t.pub 0 := by
  have hh := h.rowConstraints 0 hi (.base (.piBinding .first CUR 0))
    (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT])
  apply eq_of_modEq_canon (hc.row 0 hi CUR) (hc.pub 0)
  simp [VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt_loc hi,
    (fun _ => rfl : ∀ j, (envAt t j).pub = t.pub)] at hh
  exact hh

theorem continuity_exact (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (hc : Canonical t) {i : Nat} (hi : i+1 < t.rows.length) :
    t.rows[i+1] CUR = t.rows[i] PAR := by
  have hi0 : i < t.rows.length := by omega
  have hh := h.rowConstraints i hi0 (.windowGate continuity) (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT])
  have hb : (i+1 == t.rows.length) = false := by simp; omega
  have hm : t.rows[i+1] CUR + (-1) * t.rows[i] PAR ≡ 0 [ZMOD 2013265921] := by
    simpa [VmConstraint2.holdsAt, WindowConstraint.holdsAt, continuity, WindowExpr.eval,
      hb, envAt_loc hi0, envAt_nxt hi] using hh
  apply eq_of_modEq_canon (hc.row (i+1) hi CUR) (hc.row i hi0 PAR)
  exact (gate_modEq_iff (by ring)).mp hm

theorem final_exact (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (hc : Canonical t) (hne : t.rows ≠ []) : (t.rows.getLast hne) PAR = t.pub 1 := by
  have hp : 0 < t.rows.length := List.length_pos_of_ne_nil hne
  have hi : t.rows.length-1 < t.rows.length := by omega
  have hh := h.rowConstraints (t.rows.length-1) hi (.base (.piBinding .last PAR 1))
    (by simp [membershipDesc, constraints, parentLookup, PI_LEAF, PI_ROOT])
  rw [List.getLast_eq_getElem hne]
  apply eq_of_modEq_canon (hc.row _ hi PAR) (hc.pub 1)
  simp [VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt_loc hi,
    (fun _ => rfl : ∀ j, (envAt t j).pub = t.pub),
    show t.rows.length-1+1=t.rows.length by omega] at hh
  exact hh

/-- Acceptance binds the published leaf and root through every level of the
actual trace. `depth` is a descriptor label, never a hidden height premise. -/
theorem membership_sat_refines
    (h : Satisfied2 hash (membershipDesc depth) minit mfin maddrs t)
    (hchip : ChipTableSound hash (t.tf .poseidon2)) (hc : Canonical t) (hne : t.rows ≠ []) :
    foldNode hash (t.pub 0) (path t) = t.pub 1 ∧
    (∀ step ∈ path t, step.1 = 0 ∨ step.1 = 1) ∧ (path t).length = t.rows.length := by
  have hprefix : ∀ i (hi : i < t.rows.length),
      foldNode hash (t.pub 0) ((t.rows.take (i+1)).map (fun a => (a DIR, a SIB))) =
        t.rows[i] PAR := by
    intro i
    induction i with
    | zero =>
      intro hi
      rw [List.take_succ_eq_append_getElem hi]
      simp only [List.take_zero, List.nil_append, List.map_cons, List.map_nil,
        foldNode, List.foldl_cons, List.foldl_nil]
      rw [← initial_exact h hc hi]
      exact (row_combine h hchip hc hi).symm
    | succ i ih =>
      intro hi
      have hi0 : i < t.rows.length := by omega
      rw [List.take_succ_eq_append_getElem hi, List.map_append]
      simp only [List.map_cons, List.map_nil]
      rw [foldNode_concat, ih hi0, ← continuity_exact h hc hi]
      exact (row_combine h hchip hc hi).symm
  refine ⟨?_, ?_, by simp [path]⟩
  · have hp : 0 < t.rows.length := List.length_pos_of_ne_nil hne
    have hi : t.rows.length-1 < t.rows.length := by omega
    have he := hprefix (t.rows.length-1) hi
    rw [show t.rows.length-1+1=t.rows.length by omega, List.take_length] at he
    rw [← final_exact h hc hne, List.getLast_eq_getElem hne]
    exact he
  · intro step hstep
    obtain ⟨a, ha, rfl⟩ := List.mem_map.mp hstep
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
    exact row_bits h hc hi
end Extract

/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipRefine.row_combine' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms row_combine
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipRefine.membership_sat_refines' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms membership_sat_refines
end Dregg2.Circuit.Emit.BinaryMembershipRefine

/-
# Binary membership: inhabited refinement and last-row refusal

A two-level path uses BOTH directions under a nonconstant scalar compression:
leaf 3, sibling 5 on the right -> 13; sibling 7 on the left -> root 33.
The seven auxiliary chip output lanes remain auxiliary: this is a ONE-FELT
commitment. The attack changes only the top ordered children (and its consistent
chip output/root) while keeping the path and continuity. A deliberately weakened
seven-constraint control accepts it; the existing ten-constraint shape rejects it.
-/
import Dregg2.Circuit.Emit.BinaryMembershipRefine

namespace Dregg2.Circuit.Emit.BinaryMembershipWitness
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.EffectVmEmit
open Dregg2.Circuit.Emit.BinaryMembershipEmit
open Dregg2.Circuit.Emit.BinaryMembershipRefine
open Dregg2.Circuit.Emit.AdjacencyMembershipRefine (Canon foldNode)
set_option autoImplicit false

/-- Nonconstant reference compression with canonical field output. Not Poseidon2. -/
def referenceHash (ins : List ℤ) : ℤ := (ins.getD 0 0 + 2 * ins.getD 1 0) % 2013265921

theorem referenceHash_nonconstant : referenceHash [0,0] ≠ referenceHash [1,0] := by decide

def row (cur sib dir left right parent : ℤ) : Assignment := fun c =>
  ([cur,sib,dir,left,right,parent,0,0,0,0,0,0,0] : List ℤ).getD c 0

def firstRow : Assignment := row 3 5 0 3 5 13
def lastRow : Assignment := row 13 7 1 7 13 33
/-- Same cur/sibling/direction as lastRow, but the child pair is reversed. -/
def attackRow : Assignment := row 13 7 1 13 7 27

def publicInputs (root : ℤ) : Assignment := fun c => ([3,root] : List ℤ).getD c 0

def chipTable (left right : ℤ) : Table :=
  [chipRow referenceHash [3,5] [0,0,0,0,0,0,0],
   chipRow referenceHash [left,right] [0,0,0,0,0,0,0]]

def tables (left right : ℤ) : TraceFamily := fun id =>
  if id = .poseidon2 then chipTable left right else []

def witness : VmTrace :=
  { rows := [firstRow,lastRow], pub := publicInputs 33, tf := tables 7 13 }
def attack : VmTrace :=
  { rows := [firstRow,attackRow], pub := publicInputs 27, tf := tables 13 7 }

/-- Deliberately weakened control, no source mutation: remove the three last-row gates.
The Rust descriptor being migrated already had all ten constraints. -/
def weakDesc (depth : Nat) : EffectVmDescriptor2 :=
  { membershipDesc depth with constraints := constraints.take 7 }

theorem chip_sound (left right : ℤ) : ChipTableSound referenceHash (tables left right .poseidon2) := by
  intro r hr
  change r ∈ chipTable left right at hr
  simp only [chipTable, List.mem_cons, List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[3,5], [0,0,0,0,0,0,0], by decide, rfl, rfl⟩
  · exact ⟨[left,right], [0,0,0,0,0,0,0], by chip_arity_admitted, rfl, rfl⟩

theorem memLog_empty (depth : Nat) (t : VmTrace) : memLog (membershipDesc depth) t = [] := by
  simp [memLog, memOpsOf, membershipDesc, constraints, parentLookup]
theorem mapLog_empty (depth : Nat) (t : VmTrace) : mapLog (membershipDesc depth) t = [] := by
  simp [mapLog, mapOpsOf, membershipDesc, constraints, parentLookup]
theorem weak_memLog_empty (depth : Nat) (t : VmTrace) : memLog (weakDesc depth) t = [] := by
  simp [memLog, memOpsOf, weakDesc, membershipDesc, constraints, parentLookup]
theorem weak_mapLog_empty (depth : Nat) (t : VmTrace) : mapLog (weakDesc depth) t = [] := by
  simp [mapLog, mapOpsOf, weakDesc, membershipDesc, constraints, parentLookup]

/-- A complete satisfying trace, uniformly in the descriptor's depth LABEL. -/
theorem witness_satisfies (depth : Nat) :
    Satisfied2 referenceHash (membershipDesc depth) (fun _ => 0) (fun _ => (0,0)) [] witness where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    simp only [membershipDesc, constraints, List.mem_cons, List.not_mem_nil, or_false] at hc
    interval_cases i <;> rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        WindowConstraint.holdsAt, envAt, witness, firstRow, lastRow, row, publicInputs,
        tables, chipTable, chipRow, referenceHash, chipLookupTuple, padTo, padToE, CHIP_RATE,
        dirBody, leftBody, rightBody, neg, parentLookup, continuity, WindowExpr.eval,
        EmittedExpr.eval, CUR, SIB, DIR, LEFT, RIGHT, PAR, PI_LEAF, PI_ROOT] <;> trivial
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp [membershipDesc] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [memLog_empty]; simp
  memDisciplined := by rw [memLog_empty]; trivial
  memBalanced := by rw [memLog_empty]; exact memCheck_nil _ _
  memTableFaithful := by rw [memLog_empty]; rfl
  mapTableFaithful := by rw [mapLog_empty]; rfl

/-- The weakened transition-only ordering gates leave the last row free. The chip
is nevertheless genuine, and both public boundaries and continuity are met. -/
theorem weak_attack_satisfies (depth : Nat) :
    Satisfied2 referenceHash (weakDesc depth) (fun _ => 0) (fun _ => (0,0)) [] attack where
  rowConstraints := by
    intro i hi c hc
    have hi2 : i < 2 := hi
    simp only [weakDesc, membershipDesc, constraints, List.take_succ_cons, List.take_zero,
      List.mem_cons, List.not_mem_nil, or_false] at hc
    interval_cases i <;> rcases hc with (rfl | rfl | rfl | rfl | rfl | rfl | rfl) <;>
      norm_num [VmConstraint2.holdsAt, VmConstraint.holdsVm, Lookup.holdsAt,
        WindowConstraint.holdsAt, envAt, attack, firstRow, attackRow, row, publicInputs,
        tables, chipTable, chipRow, referenceHash, chipLookupTuple, padTo, padToE, CHIP_RATE,
        dirBody, leftBody, rightBody, neg, parentLookup, continuity, WindowExpr.eval,
        EmittedExpr.eval, CUR, SIB, DIR, LEFT, RIGHT, PAR, PI_LEAF, PI_ROOT] <;> trivial
  rowHashes := by intro i _; trivial
  rowRanges := by intro i _ r hr; simp [weakDesc, membershipDesc] at hr
  memAddrsNodup := List.nodup_nil
  memClosed := by rw [weak_memLog_empty]; simp
  memDisciplined := by rw [weak_memLog_empty]; trivial
  memBalanced := by rw [weak_memLog_empty]; exact memCheck_nil _ _
  memTableFaithful := by rw [weak_memLog_empty]; rfl
  mapTableFaithful := by rw [weak_mapLog_empty]; rfl

private theorem list_canon : ∀ (xs : List ℤ),
    (∀ x ∈ xs, Canon x) → ∀ j, Canon (xs.getD j 0)
  | [], _, _ => by simp [Canon]
  | a :: _, h, 0 => h a List.mem_cons_self
  | _ :: xs, h, j+1 => list_canon xs (fun x hx => h x (List.mem_cons_of_mem _ hx)) j

theorem witness_canonical : Canonical witness where
  row := by
    intro i hi j
    have hi2 : i < 2 := hi
    interval_cases i
    · exact list_canon _ (by unfold Canon; decide) j
    · exact list_canon _ (by unfold Canon; decide) j
  pub := fun j => list_canon _ (by unfold Canon; decide) j

theorem attack_canonical : Canonical attack where
  row := by
    intro i hi j
    have hi2 : i < 2 := hi
    interval_cases i
    · exact list_canon _ (by unfold Canon; decide) j
    · exact list_canon _ (by unfold Canon; decide) j
  pub := fun j => list_canon _ (by unfold Canon; decide) j

/-- All premises of the whole-path refinement are met by this ONE witness. -/
theorem jointly_inhabited :
    Satisfied2 referenceHash (membershipDesc 2) (fun _ => 0) (fun _ => (0,0)) [] witness ∧
    ChipTableSound referenceHash (witness.tf .poseidon2) ∧ Canonical witness ∧ witness.rows ≠ [] :=
  ⟨witness_satisfies 2, chip_sound 7 13, witness_canonical, by decide⟩

/-- The actual-fold theorem fires on a mixed-direction two-level path. -/
theorem witness_refines :
    foldNode referenceHash (witness.pub PI_LEAF) (path witness) = witness.pub PI_ROOT ∧
    path witness = [(0,5),(1,7)] ∧ witness.pub PI_ROOT = 33 :=
  ⟨(membership_sat_refines (witness_satisfies 2) (chip_sound 7 13) witness_canonical
    (by decide)).1, rfl, rfl⟩

/-- The last-row attack changes neither the described path nor the leaf. -/
theorem attack_same_path : path attack = path witness ∧ attack.pub PI_LEAF = witness.pub PI_LEAF := by
  constructor <;> rfl

/-- Genuine path folding gives 33, whereas the accepted weak attack advertises 27. -/
theorem weak_attack_wrong_root : foldNode referenceHash (attack.pub PI_LEAF) (path attack) ≠
    attack.pub PI_ROOT := by decide

/-- The existing last-row ordering boundary rejects that exact weakened-control witness. -/
theorem strong_attack_refused (depth : Nat) :
    ¬ Satisfied2 referenceHash (membershipDesc depth) (fun _ => 0) (fun _ => (0,0)) [] attack := by
  intro h
  have hh := h.rowConstraints 1 (by decide) (.base (.boundary .last leftBody))
    (by simp [membershipDesc, constraints])
  have hn : ¬ (VmConstraint2.base (.boundary .last leftBody)).holdsAt referenceHash attack.tf
      (envAt attack 1) (1 == 0) (1+1 == attack.rows.length) := by
    norm_num [VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt, attack, firstRow,
      attackRow, row, leftBody, neg, EmittedExpr.eval, CUR, SIB, DIR, LEFT]
  exact hn hh

/-- The same concrete attack jointly has genuine chip rows, canonical cells,
weakened-control acceptance, a false path claim, and refusal by the full descriptor. -/
theorem last_row_separation :
    Satisfied2 referenceHash (weakDesc 2) (fun _ => 0) (fun _ => (0,0)) [] attack ∧
    ChipTableSound referenceHash (attack.tf .poseidon2) ∧ Canonical attack ∧
    foldNode referenceHash (attack.pub PI_LEAF) (path attack) ≠ attack.pub PI_ROOT ∧
    ¬ Satisfied2 referenceHash (membershipDesc 2) (fun _ => 0) (fun _ => (0,0)) [] attack :=
  ⟨weak_attack_satisfies 2, chip_sound 13 7, attack_canonical, weak_attack_wrong_root,
    strong_attack_refused 2⟩

/-- Depth is a label, not a length theorem: the same two rows satisfy depth eight. -/
theorem depth_label_does_not_bind_height :
    Satisfied2 referenceHash (membershipDesc 8) (fun _ => 0) (fun _ => (0,0)) [] witness ∧
    witness.rows.length ≠ 8 := ⟨witness_satisfies 8, by decide⟩

/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.referenceHash_nonconstant' depends on axioms: [propext] -/
#guard_msgs in
#print axioms referenceHash_nonconstant
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.last_row_separation' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms last_row_separation
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.jointly_inhabited' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms jointly_inhabited
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.witness_refines' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms witness_refines
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.witness_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms witness_satisfies
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.weak_attack_satisfies' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms weak_attack_satisfies
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.strong_attack_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms strong_attack_refused
/-- info: 'Dregg2.Circuit.Emit.BinaryMembershipWitness.depth_label_does_not_bind_height' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms depth_label_does_not_bind_height
end Dregg2.Circuit.Emit.BinaryMembershipWitness

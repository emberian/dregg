/-
# TupleBindingEmit — one author for public tuple carriers

Four recursion adapters require the tuple constant on every row. Delegation
requires only its first row pinned: the flag preserves that weaker contract.
These carriers bind tuples, not their off-AIR validation. No hashing,
authorization, membership, or derivation validity is asserted here.
-/
import Dregg2.Circuit.DescriptorIR2
namespace Dregg2.Circuit.Emit.TupleBindingEmit
open Dregg2.Circuit (Assignment)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRowEnv VmConstraint)
open Dregg2.Circuit.DescriptorIR2
set_option autoImplicit false

def pin (c : Nat) : VmConstraint2 := .base (.piBinding .first c c)
def copy (c : Nat) : VmConstraint2 :=
  .windowGate ⟨.add (.nxt c) (.mul (.const (-1)) (.loc c)), true⟩

def tupleDesc (name : String) (width : Nat) (constantRows : Bool) : EffectVmDescriptor2 :=
  { name, traceWidth := width, piCount := width, tables := [], hashSites := [], ranges := []
    constraints := (List.range width).map pin ++
      if constantRows then (List.range width).map copy else [] }

/-- Linear constraint count; every emitted gate has degree one. -/
theorem constraint_count (name : String) (width : Nat) (constantRows : Bool) :
    (tupleDesc name width constantRows).constraints.length =
      width + if constantRows then width else 0 := by
  cases constantRows <;> simp [tupleDesc]

theorem copy_semantics (env : VmRowEnv) (hash : List Int → Int) (tf : TraceFamily)
    (first last : Bool) (c : Nat) :
    (copy c).holdsAt hash tf env first last ↔
      (last = false → env.nxt c ≡ env.loc c [ZMOD 2013265921]) := by
  simp only [copy, VmConstraint2.holdsAt, WindowConstraint.holdsAt,
    ↓reduceIte, WindowExpr.eval, neg_one_mul]
  simp only [Int.modEq_iff_dvd]
  ring_nf

/-- Exact semantics of the emitted constraints, including inactive row selectors. -/
theorem tuple_semantics (name : String) (width : Nat) (constantRows : Bool)
    (env : VmRowEnv) (hash : List Int → Int) (tf : TraceFamily) (first last : Bool) :
    (∀ c ∈ (tupleDesc name width constantRows).constraints,
      c.holdsAt hash tf env first last) ↔
    (∀ c < width, first = true → env.loc c ≡ env.pub c [ZMOD 2013265921]) ∧
    (constantRows = true → ∀ c < width,
      last = false → env.nxt c ≡ env.loc c [ZMOD 2013265921]) := by
  cases constantRows <;>
    simp only [tupleDesc, Bool.false_eq_true, ↓reduceIte, List.forall_mem_append,
      List.forall_mem_map, List.mem_range, and_true,
      false_implies, true_implies, copy_semantics]
  all_goals simp [pin, VmConstraint2.holdsAt, VmConstraint.holdsVm]

/-- Every public tuple inhabits the constraints at every selector combination. -/
theorem honest_tuple (name : String) (width : Nat) (constantRows : Bool)
    (a : Assignment) (hash : List Int → Int) (tf : TraceFamily) (first last : Bool) :
    ∀ c ∈ (tupleDesc name width constantRows).constraints,
      c.holdsAt hash tf {loc := a, nxt := a, pub := a} first last := by
  rw [tuple_semantics]
  exact ⟨fun _ _ _ => Int.ModEq.refl _, fun _ _ _ _ => Int.ModEq.refl _⟩

/-- A changed public limb is refused, for every valid column. -/
theorem changed_public_refused (name : String) (width : Nat) (constantRows : Bool)
    (env : VmRowEnv) (hash : List Int → Int) (tf : TraceFamily) (last : Bool)
    (c : Nat) (hc : c < width) (hbad : ¬ env.loc c ≡ env.pub c [ZMOD 2013265921]) :
    ¬ (∀ k ∈ (tupleDesc name width constantRows).constraints,
      k.holdsAt hash tf env true last) := by
  intro h
  exact hbad ((tuple_semantics _ _ _ _ _ _ _ _).mp h |>.1 c hc rfl)

/-- A changed next-row limb is refused by the constant-row variant. -/
theorem changed_next_refused (name : String) (width : Nat)
    (env : VmRowEnv) (hash : List Int → Int) (tf : TraceFamily) (first : Bool)
    (c : Nat) (hc : c < width) (hbad : ¬ env.nxt c ≡ env.loc c [ZMOD 2013265921]) :
    ¬ (∀ k ∈ (tupleDesc name width true).constraints,
      k.holdsAt hash tf env first false) := by
  intro h
  exact hbad ((tuple_semantics _ _ _ _ _ _ _ _).mp h |>.2 rfl c hc rfl)

/-- The constant-row carrier binds every row, not just the first window. -/
theorem all_rows_bound (name : String) (width : Nat) (hash : List Int → Int)
    (minit : Int → Int) (mfin : Int → Int × Nat) (maddrs : List Int) (t : VmTrace)
    (h : Satisfied2 hash (tupleDesc name width true) minit mfin maddrs t)
    (i : Nat) (hi : i < t.rows.length) (c : Nat) (hc : c < width) :
    t.rows.getD i zeroAsg c ≡ t.pub c [ZMOD 2013265921] := by
  induction i with
  | zero =>
    exact ((tuple_semantics _ _ _ _ _ _ _ _).mp (h.rowConstraints 0 hi)).1 c hc rfl
  | succ i ih =>
    have hi' : i < t.rows.length := by omega
    have hs := ((tuple_semantics _ _ _ _ _ _ _ _).mp
      (h.rowConstraints i hi')).2 rfl c hc
    have hlast : (i + 1 == t.rows.length) = false := by simp; omega
    exact (hs hlast).trans (ih hi')

/-- Two genuine rows, arbitrary public data, and empty auxiliary tables. -/
def honestTrace (a : Assignment) : VmTrace :=
  { rows := [a, a], pub := a, tf := fun _ => [] }

theorem no_mem_ops (name : String) (width : Nat) (constantRows : Bool) :
    memOpsOf (tupleDesc name width constantRows) = [] := by
  cases constantRows <;> simp [memOpsOf, tupleDesc, List.filterMap_map, pin, copy]

theorem no_map_ops (name : String) (width : Nat) (constantRows : Bool) :
    mapOpsOf (tupleDesc name width constantRows) = [] := by
  cases constantRows <;> simp [mapOpsOf, tupleDesc, List.filterMap_map, pin, copy]

/-- The full deployed denotation is inhabited for all widths and all tuples. -/
theorem honest_satisfies (name : String) (width : Nat) (constantRows : Bool)
    (a : Assignment) (hash : List Int → Int) :
    Satisfied2 hash (tupleDesc name width constantRows)
      (fun _ => 0) (fun _ => (0, 0)) [] (honestTrace a) := by
  constructor
  · intro i hi
    have hi' : i < 2 := hi
    rw [tuple_semantics]
    interval_cases i <;> simp [honestTrace, envAt]
  · intro i hi
    simp [tupleDesc, EffectVmEmit.siteHoldsAll, EffectVmEmit.siteHoldsAll.go]
  · intro i hi r hr; cases hr
  · exact List.nodup_nil
  · intro op hop; simp [memLog, no_mem_ops] at hop
  · simp [memLog, no_mem_ops, honestTrace, Dregg2.Crypto.MemoryChecking.Disciplined,
      Dregg2.Crypto.MemoryChecking.DisciplinedFrom]
  · simp only [memLog, no_mem_ops, List.filterMap_nil]
    exact memCheck_nil _ _
  · simp [honestTrace, memLog, no_mem_ops]
  · simp [honestTrace, mapLog, no_map_ops]

/-- A concrete falsifier supplies the premise of both refusal theorems. -/
theorem zero_ne_one_mod : ¬ (0 : Int) ≡ 1 [ZMOD 2013265921] := by decide

/-- The intentionally weaker delegation variant permits a distinct next row. -/
theorem first_only_allows_distinct_next (name : String) (width : Nat) :
    ∀ k ∈ (tupleDesc name width false).constraints,
      k.holdsAt (fun _ => 0) (fun _ => [])
        {loc := fun _ => 0, nxt := fun _ => 1, pub := fun _ => 0} true false := by
  rw [tuple_semantics]
  simp

/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.constraint_count' depends on axioms: [propext] -/
#guard_msgs in
#print axioms constraint_count
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.copy_semantics' depends on axioms: [propext] -/
#guard_msgs in
#print axioms copy_semantics
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.tuple_semantics' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms tuple_semantics
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.honest_tuple' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms honest_tuple
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.changed_public_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms changed_public_refused
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.changed_next_refused' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms changed_next_refused
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.all_rows_bound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms all_rows_bound
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.no_mem_ops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_mem_ops
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.no_map_ops' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms no_map_ops
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.honest_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honest_satisfies
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.zero_ne_one_mod' does not depend on any axioms -/
#guard_msgs in
#print axioms zero_ne_one_mod
/-- info: 'Dregg2.Circuit.Emit.TupleBindingEmit.first_only_allows_distinct_next' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms first_only_allows_distinct_next

def factoryDesc := tupleDesc "factory-backing-leaf::factory_backing_v1" 24 true
def hatcheryDesc := tupleDesc "hatchery-attestation-leaf::hatchery_attestation_v1" 16 true
def sovereignDesc := tupleDesc "sovereign-authority-leaf::sovereign_authority_v1" 21 true
def membershipDesc := tupleDesc "membership-leaf::sender_membership_v1" 2 true
def delegateDesc := tupleDesc "dregg-delegate::v2" 24 false

end Dregg2.Circuit.Emit.TupleBindingEmit

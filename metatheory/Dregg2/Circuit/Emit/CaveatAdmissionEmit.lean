/- Lean-authored u128-capable caveat admission, using generic field-safe borrow chains. -/
import Dregg2.Circuit.Emit.BorrowChainEmit
import Dregg2.Circuit.Emit.TupleBindingEmit
namespace Dregg2.Circuit.Emit.CaveatAdmissionEmit
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.FieldDeltaRangeEmit (Canon eq_of_modEq_canon)
open BorrowChainEmit (value bodies)
set_option autoImplicit false
set_option maxRecDepth 2000

def BASE : Int := 67108864
def opCol (o j : Nat) : Nat := o * 5 + j
def diffCol (c j : Nat) : Nat := 40 + c * 5 + j
def borrowCol (c j : Nat) : Nat := 55 + c * 4 + (j-1)
def borrow (c j : Nat) (init : Int) : EmittedExpr :=
  if j = 0 then .const init else if j = 5 then .const 0 else .var (borrowCol c j)
def first (e : EmittedExpr) : VmConstraint2 := .base (.boundary .first e)
def bit (col : Nat) : EmittedExpr := .mul (.var col) (.add (.var col) (.const (-1)))
def comparison (c x y : Nat) (init : Int) : List VmConstraint2 :=
  (bodies BASE 5 (opCol x) (opCol y) (diffCol c) (fun j => borrow c j init)).map first ++
  (List.range 4).map (fun j => first (bit (borrowCol c (j+1))))
def asset (j : Nat) : EmittedExpr :=
  .add (.var (opCol 6 j)) (.mul (.const (-1)) (.var (opCol 7 j)))
def rangeLookup (c : Nat) : VmConstraint2 := .lookup ⟨.range, [.var c]⟩
def descriptor : EffectVmDescriptor2 :=
  { name := "caveat-admission-leaf::bignum_decidable_atoms_v1"
    traceWidth := 67, piCount := 40
    tables := [⟨.range, "range", 1, .rangeLimb 26⟩]
    constraints := (List.range 40).map TupleBindingEmit.pin ++
      comparison 0 0 1 0 ++ comparison 1 2 3 1 ++ comparison 2 4 5 0 ++
      (List.range 5).map (fun j => first (asset j)) ++
      (List.range 67).map TupleBindingEmit.copy ++
      (List.range 55).map rangeLookup
    hashSites := [], ranges := [] }

theorem constraint_count : descriptor.constraints.length = 194 := by decide

def amount (a : Assignment) (o : Nat) : Int := value BASE 5 (fun j => a (opCol o j))

private theorem row_range {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hrange : t.tf .range = rangeRows 26)
    (hs : Satisfied2 hash descriptor initial bounds mem t) (c : Nat) (hc : c < 55) :
    0 ≤ (envAt t 0).loc c ∧ (envAt t 0).loc c < BASE := by
  have hh := hs.rowConstraints 0 ht (rangeLookup c) (by
    simp only [descriptor, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inr ⟨c, hc, rfl⟩)
  have hv := lookup_replaces_range 26 t.tf hrange (envAt t 0) c hh
  simpa [EffectVmEmit.VmRange.holds, BASE] using hv

private theorem first_vanishes {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hs : Satisfied2 hash descriptor initial bounds mem t)
    (e : EmittedExpr) (he : first e ∈ descriptor.constraints) :
    e.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
  have hh := hs.rowConstraints 0 ht (first e) he
  simpa [first, VmConstraint2.holdsAt, VmConstraint.holdsVm] using hh

/-- One generated comparison means the exact integer comparison, including strictness. -/
theorem comparison_sound {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hrange : t.tf .range = rangeRows 26)
    (hc : ∀ k, Canon ((envAt t 0).loc k))
    (hs : Satisfied2 hash descriptor initial bounds mem t)
    (c x y : Nat) (hcx : c < 3) (hx : x < 8) (hy : y < 8)
    (init : Int) (hi : init = 0 ∨ init = 1)
    (hm : ∀ e ∈ comparison c x y init, e ∈ descriptor.constraints) :
    amount (envAt t 0).loc x + init ≤ amount (envAt t 0).loc y := by
  have hb : ∀ j ≤ 5, (borrow c j init).eval (envAt t 0).loc = 0 ∨
      (borrow c j init).eval (envAt t 0).loc = 1 := by
    intro j hj
    by_cases hz : j = 0
    · simp [borrow, hz, hi]
    by_cases hf : j = 5
    · simp [borrow, hf]
    have hh := first_vanishes ht hs (bit (borrowCol c j)) (hm _ (by
      apply List.mem_append_right
      apply List.mem_map.mpr
      refine ⟨j-1, List.mem_range.mpr (by omega), ?_⟩
      congr 2))
    have he : (BoundedFactEmit.boolean (borrowCol c j)).eval (envAt t 0).loc ≡
        0 [ZMOD 2013265921] := by
      simpa [BoundedFactEmit.boolean, BoundedFactEmit.sub, bit, EmittedExpr.eval] using hh
    simpa [borrow, hz, hf, EmittedExpr.eval] using BoundedFactEmit.boolean_forces he (hc _)
  have hh := BorrowChainEmit.bodies_sound BASE 5 (opCol x) (opCol y) (diffCol c)
    (fun j => borrow c j init) (envAt t 0).loc (by decide) (by decide)
    (by
      intro j hj
      exact ⟨row_range ht hrange hs _ (by unfold opCol; omega),
        row_range ht hrange hs _ (by unfold opCol; omega),
        row_range ht hrange hs _ (by unfold diffCol; omega)⟩) hb
    (by simp [borrow])
    (fun e he => first_vanishes ht hs e (hm _
      (List.mem_append_left _ (List.mem_map.mpr ⟨e, he, rfl⟩))))
  simpa [amount, borrow, EmittedExpr.eval] using hh

/-- Main statement: the actual descriptor enforces all three bounded integer atoms
and asset equality, over the same row carrying the public limbs. The range-table
faithfulness premise is explicit; Satisfied2 alone does not assert public table semantics. -/
theorem caveat_emit_sound {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hrange : t.tf .range = rangeRows 26)
    (hc : ∀ k, Canon ((envAt t 0).loc k))
    (hs : Satisfied2 hash descriptor initial bounds mem t) :
    let a := (envAt t 0).loc
    amount a 0 ≤ amount a 1 ∧ amount a 2 < amount a 3 ∧
      amount a 4 ≤ amount a 5 ∧ amount a 6 = amount a 7 := by
  have h0 := comparison_sound ht hrange hc hs 0 0 1 (by decide) (by decide) (by decide)
    0 (Or.inl rfl) (by intro e he; simp only [descriptor, List.mem_append]; tauto)
  have h1 := comparison_sound ht hrange hc hs 1 2 3 (by decide) (by decide) (by decide)
    1 (Or.inr rfl) (by intro e he; simp only [descriptor, List.mem_append]; tauto)
  have h2 := comparison_sound ht hrange hc hs 2 4 5 (by decide) (by decide) (by decide)
    0 (Or.inl rfl) (by intro e he; simp only [descriptor, List.mem_append]; tauto)
  have ha : ∀ j < 5, (envAt t 0).loc (opCol 6 j) = (envAt t 0).loc (opCol 7 j) := by
    intro j hj
    have he := first_vanishes ht hs (asset j) (by
      simp only [descriptor, List.mem_append, List.mem_map, List.mem_range]
      exact Or.inl (Or.inl (Or.inr ⟨j, hj, rfl⟩)))
    have hm : (envAt t 0).loc (opCol 6 j) ≡ (envAt t 0).loc (opCol 7 j) [ZMOD 2013265921] := by
      simp only [asset, EmittedExpr.eval] at he
      obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp he
      exact Int.modEq_iff_dvd.mpr ⟨-k, by linear_combination -hk⟩
    exact eq_of_modEq_canon hm (hc _) (hc _)
  refine ⟨by omega, by omega, by omega, ?_⟩
  simp only [amount, value]
  rw [ha 0 (by decide), ha 1 (by decide), ha 2 (by decide), ha 3 (by decide), ha 4 (by decide)]

/-- Every public operand limb is the row used by the comparison. -/
theorem public_limbs_bound {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hc : ∀ k, Canon ((envAt t 0).loc k))
    (hp : ∀ k < 40, Canon (t.pub k))
    (hs : Satisfied2 hash descriptor initial bounds mem t) (k : Nat) (hk : k < 40) :
    t.pub k = (envAt t 0).loc k := by
  have hh := hs.rowConstraints 0 ht (TupleBindingEmit.pin k) (by
    simp only [descriptor, List.mem_append, List.mem_map, List.mem_range]
    exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨k, hk, rfl⟩))))))
  have he : (envAt t 0).loc k ≡ t.pub k [ZMOD 2013265921] := by
    simpa [TupleBindingEmit.pin, VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt] using hh
  exact (eq_of_modEq_canon he (hc k) (hp k hk)).symm

/-- Externally visible statement over the canonical public limb tuple. -/
theorem caveat_public_sound {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hrange : t.tf .range = rangeRows 26)
    (hc : ∀ k, Canon ((envAt t 0).loc k)) (hp : ∀ k < 40, Canon (t.pub k))
    (hs : Satisfied2 hash descriptor initial bounds mem t) :
    amount t.pub 0 ≤ amount t.pub 1 ∧ amount t.pub 2 < amount t.pub 3 ∧
      amount t.pub 4 ≤ amount t.pub 5 ∧ amount t.pub 6 = amount t.pub 7 := by
  have hpv : ∀ o < 8, amount t.pub o = amount (envAt t 0).loc o := by
    intro o ho
    simp only [amount, value]
    rw [public_limbs_bound ht hc hp hs (opCol o 0) (by unfold opCol; omega),
      public_limbs_bound ht hc hp hs (opCol o 1) (by unfold opCol; omega),
      public_limbs_bound ht hc hp hs (opCol o 2) (by unfold opCol; omega),
      public_limbs_bound ht hc hp hs (opCol o 3) (by unfold opCol; omega),
      public_limbs_bound ht hc hp hs (opCol o 4) (by unfold opCol; omega)]
  simpa only [hpv 0 (by decide), hpv 1 (by decide), hpv 2 (by decide), hpv 3 (by decide),
    hpv 4 (by decide), hpv 5 (by decide), hpv 6 (by decide), hpv 7 (by decide)] using
    caveat_emit_sound ht hrange hc hs

/-- The strict height atom is inhabited: height0 < ceiling1; other operands zero. -/
def honestRow (c : Nat) : Int := if c = 15 then 1 else 0
def honestTable : TraceFamily := fun id => if id = .range then rangeRows 26 else []
def honestTrace : VmTrace :=
  { rows := [honestRow], pub := honestRow, tf := honestTable }

theorem honest_canonical : ∀ c, Canon (honestRow c) := by
  intro c; unfold honestRow Canon; split <;> norm_num

theorem honest_constraints :
    ∀ c ∈ descriptor.constraints, c.holdsAt (fun _ => 0) honestTable
      {loc := honestRow, nxt := zeroAsg, pub := honestRow} true true := by
  simp only [descriptor, List.forall_mem_append, List.forall_mem_map, and_assoc]
  constructor
  · intro c hc
    simp [TupleBindingEmit.pin, VmConstraint2.holdsAt, VmConstraint.holdsVm]
  constructor
  · simp only [comparison, List.forall_mem_append, List.forall_mem_map,
      first, VmConstraint2.holdsAt, VmConstraint.holdsVm]
    decide
  constructor
  · simp only [comparison, List.forall_mem_append, List.forall_mem_map,
      first, VmConstraint2.holdsAt, VmConstraint.holdsVm]
    decide
  constructor
  · simp only [comparison, List.forall_mem_append, List.forall_mem_map,
      first, VmConstraint2.holdsAt, VmConstraint.holdsVm]
    decide
  constructor
  · simp only [comparison, List.forall_mem_append, List.forall_mem_map,
      first, VmConstraint2.holdsAt, VmConstraint.holdsVm]
    decide
  constructor
  · intro c hc
    rw [TupleBindingEmit.copy_semantics]
    intro h; cases h
  · intro c hc
    change [honestRow c] ∈ rangeRows 26
    rw [range_row_mem_iff]
    unfold honestRow
    split <;> norm_num

@[simp] theorem honest_loc (i : Nat) (hi : i < 1) : (envAt honestTrace i).loc = honestRow := by
  interval_cases i <;> rfl

theorem honest_satisfies : Satisfied2 (fun _ => 0) descriptor
    (fun _ => 0) (fun _ => (0, 0)) [] honestTrace := by
  constructor
  · intro i hi c hc
    have hi' : i < 1 := hi
    have hz : i = 0 := by omega
    subst i
    exact honest_constraints c hc
  · intro i hi; simp [descriptor, EffectVmEmit.siteHoldsAll, EffectVmEmit.siteHoldsAll.go]
  · intro i hi r hr; cases hr
  · exact List.nodup_nil
  · intro op hop
    simp [memLog, memOpsOf, descriptor, comparison, bodies, first, rangeLookup,
      TupleBindingEmit.pin, TupleBindingEmit.copy] at hop
  · simp [memLog, memOpsOf, descriptor, comparison, bodies, first, rangeLookup,
      TupleBindingEmit.pin, TupleBindingEmit.copy, honestTrace,
      Dregg2.Crypto.MemoryChecking.Disciplined, Dregg2.Crypto.MemoryChecking.DisciplinedFrom]
  · simp [Dregg2.Crypto.MemoryChecking.MemCheck, memLog, memOpsOf, descriptor,
      comparison, bodies, first, rangeLookup, TupleBindingEmit.pin, TupleBindingEmit.copy,
      honestTrace, Dregg2.Crypto.MemoryChecking.initSet, Dregg2.Crypto.MemoryChecking.finalSet]
  · simp [honestTrace, honestTable, memLog, memOpsOf, descriptor, comparison, bodies,
      first, rangeLookup, TupleBindingEmit.pin, TupleBindingEmit.copy]
  · simp [honestTrace, honestTable, mapLog, mapOpsOf, descriptor, comparison, bodies,
      first, rangeLookup, TupleBindingEmit.pin, TupleBindingEmit.copy]

/-- Equal heights pass the weak inclusive chain and fail the emitted strict chain. -/
theorem strict_boundary_falsifier :
    (bodies BASE 5 (opCol 2) (opCol 3) (diffCol 1) (fun j => borrow 1 j 0)).all
      (fun e => decide (e.eval (fun _ => 0) ≡ 0 [ZMOD 2013265921])) = true ∧
    (bodies BASE 5 (opCol 2) (opCol 3) (diffCol 1) (fun j => borrow 1 j 1)).all
      (fun e => decide (e.eval (fun _ => 0) ≡ 0 [ZMOD 2013265921])) = false := by decide

/-- info: 'Dregg2.Circuit.Emit.CaveatAdmissionEmit.caveat_emit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms caveat_emit_sound
/-- info: 'Dregg2.Circuit.Emit.CaveatAdmissionEmit.honest_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honest_satisfies
/-- info: 'Dregg2.Circuit.Emit.CaveatAdmissionEmit.caveat_public_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms caveat_public_sound
#assert_all_clean [constraint_count, comparison_sound, caveat_emit_sound, public_limbs_bound, caveat_public_sound,
  honest_canonical, honest_constraints, honest_satisfies, strict_boundary_falsifier]
end Dregg2.Circuit.Emit.CaveatAdmissionEmit

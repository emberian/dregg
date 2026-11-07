/-
# SolvencyLeafEmit — bounded integer solvency, authored in Lean

The former Rust constructor checked only `(R-L) mod p < 2^30`; even `(0,2^30-1)`
passed. This emitter ranges both amounts and uses two 15-bit borrow limbs. Each
modular limb equation lifts to an integer identity before assembly. Supported
amounts remain `[0,2^30)`. `rangeBodies` generates reusable bit-range constraints.
All arithmetic is first-row-boundary constrained, including at trace height one.
The scalar fact-hash interface is unchanged; these arithmetic theorems assert no
cryptographic binding or hiding guarantee.
-/
import Dregg2.Circuit.Emit.BoundedFactEmit
namespace Dregg2.Circuit.Emit.SolvencyLeafEmit
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRow)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.FieldDeltaRangeEmit (Canon eq_of_modEq_canon)
open BoundedFactEmit (sub boolean rangeBodies boolean_forces rangeBodies_sound)
set_option autoImplicit false

-- First seven columns preserve the witness/commitment interface.
def R : Nat := 0
def L : Nat := 1
def SR : Nat := 2
def SL : Nat := 3
def RC : Nat := 4
def LC : Nat := 5
def D : Nat := 6
-- Six 15-bit limbs: reserve, liability, difference (little endian).
def limb (k : Nat) : Nat := 7 + k
def bitsBase (k : Nat) : Nat := 13 + 15 * k
def BORROW : Nat := 103
def BASE_WIDTH : Nat := 104
def WIDTH : Nat := 118

def assembled (lo : Nat) : EmittedExpr :=
  .add (.var (limb lo)) (.mul (.const 32768) (.var (limb (lo + 1))))
def assembly (value lo : Nat) : EmittedExpr := sub (.var value) (assembled lo)
def borrowLow : EmittedExpr :=
  sub (.add (sub (.var (limb 0)) (.var (limb 2)))
    (.mul (.const 32768) (.var BORROW))) (.var (limb 4))
def borrowHigh : EmittedExpr :=
  sub (sub (sub (.var (limb 1)) (.var (limb 3))) (.var BORROW)) (.var (limb 5))
def arithmeticBodies : List EmittedExpr :=
  (List.range 6).flatMap (fun k => rangeBodies 15 (limb k) (bitsBase k)) ++
    [boolean BORROW, assembly R 0, assembly L 2, assembly D 4, borrowLow, borrowHigh]
def firstGate (e : EmittedExpr) : VmConstraint2 := .base (.boundary .first e)

/-- One fact-hash opening, including the seven remaining permutation lanes. -/
def factSite (value salt output lanes : Nat) : VmConstraint2 :=
  BoundedFactEmit.factSite ![.var value, .var salt, .const 0, .const 0, .const 0] output lanes

def solvencyDescriptor : EffectVmDescriptor2 :=
  { name := "solvency-leaf::dregg-reserve-covers-liabilities-v2"
    traceWidth := WIDTH
    piCount := 2
    tables := []
    constraints := [factSite R SR RC BASE_WIDTH, factSite L SL LC (BASE_WIDTH + 7)] ++
      arithmeticBodies.map firstGate ++
      [.base (.piBinding .first RC 0), .base (.piBinding .first LC 1)]
    hashSites := []
    ranges := [] }

private theorem bounded_zero {x : Int} (h : x ≡ 0 [ZMOD 2013265921])
    (hlo : -2013265921 < x) (hhi : x < 2013265921) : x = 0 := by
  obtain ⟨k, hk⟩ := Int.modEq_zero_iff_dvd.mp h
  omega

/-- The emitted arithmetic forces exact, non-wrapping integer subtraction. -/
theorem arithmetic_sound (a : Assignment) (hc : ∀ c, Canon (a c))
    (h : ∀ e ∈ arithmeticBodies, e.eval a ≡ 0 [ZMOD 2013265921]) :
    0 ≤ a R ∧ a R < 2^30 ∧ 0 ≤ a L ∧ a L < 2^30 ∧
      a L ≤ a R ∧ a D = a R - a L := by
  have hr : ∀ k < 6, 0 ≤ a (limb k) ∧ a (limb k) < 32768 := by
    intro k hk
    have := rangeBodies_sound a 15 (limb k) (bitsBase k) (by norm_num) hc
      (fun e he => h e (List.mem_append_left _ (List.mem_flatMap.mpr
        ⟨k, List.mem_range.mpr hk, he⟩)))
    norm_num at this
    exact this
  have br := boolean_forces (h _ (by simp [arithmeticBodies])) (hc BORROW)
  have ha (v k : Nat) (hm : assembly v k ∈ arithmeticBodies)
      (hk : k < 5) : a v = a (limb k) + 32768 * a (limb (k + 1)) := by
    have hh := h _ hm
    simp only [assembly, assembled, sub, EmittedExpr.eval] at hh
    have he : a v - (a (limb k) + 32768 * a (limb (k + 1))) ≡ 0 [ZMOD 2013265921] := by
      convert hh using 1 <;> ring
    have hm' : a v ≡ a (limb k) + 32768 * a (limb (k + 1)) [ZMOD 2013265921] := by
      obtain ⟨q, hq⟩ := Int.modEq_zero_iff_dvd.mp he
      exact Int.modEq_iff_dvd.mpr ⟨-q, by linear_combination -hq⟩
    exact eq_of_modEq_canon hm' (hc v)
      ⟨by have := hr k (by omega); have := hr (k+1) (by omega); omega,
       by have := hr k (by omega); have := hr (k+1) (by omega); omega⟩
  have hR := ha R 0 (by simp [arithmeticBodies]) (by omega)
  have hL := ha L 2 (by simp [arithmeticBodies]) (by omega)
  have hD := ha D 4 (by simp [arithmeticBodies]) (by omega)
  have h0 := h borrowLow (by simp [arithmeticBodies])
  have h1 := h borrowHigh (by simp [arithmeticBodies])
  simp only [borrowLow, borrowHigh, sub, EmittedExpr.eval] at h0 h1
  have r0 := hr 0 (by omega); have r1 := hr 1 (by omega)
  have l0 := hr 2 (by omega); have l1 := hr 3 (by omega)
  have d0 := hr 4 (by omega); have d1 := hr 5 (by omega)
  have e0 := bounded_zero h0 (by rcases br with hb | hb <;> omega)
    (by rcases br with hb | hb <;> omega)
  have e1 := bounded_zero h1 (by rcases br with hb | hb <;> omega)
    (by rcases br with hb | hb <;> omega)
  norm_num at hR hL hD ⊢
  omega

/-- Descriptor soundness at the PI-pinned first row, including one-row traces. -/
theorem solvency_emit_sound {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length)
    (hc : ∀ c, Canon ((envAt t 0).loc c))
    (hs : Satisfied2 hash solvencyDescriptor initial bounds mem t) :
    let a := (envAt t 0).loc
    0 ≤ a R ∧ a R < 2^30 ∧ 0 ≤ a L ∧ a L < 2^30 ∧
      a L ≤ a R ∧ a D = a R - a L := by
  apply arithmetic_sound _ hc
  intro e he
  have hm : firstGate e ∈ solvencyDescriptor.constraints := by
    simp only [solvencyDescriptor, List.mem_append, List.mem_map]
    exact Or.inl (Or.inr ⟨e, he, rfl⟩)
  have hh := hs.rowConstraints 0 ht (firstGate e) hm
  simpa [firstGate, VmConstraint2.holdsAt, VmConstraint.holdsVm] using hh

/-- The same row opened by each chip site is the row constrained by arithmetic. -/
theorem factSite_sound (permOut : List Int → List Int) (tf : TraceFamily)
    (hchip : ChipTableSoundN permOut (tf .poseidon2))
    (env : EffectVmEmit.VmRowEnv) (value salt output lanes : Nat)
    (h : (factSite value salt output lanes).holdsAt (fun _ => 0) tf env true false) :
    env.loc output = (permOut [env.loc value, env.loc salt, 0, 0, 0, 64207, 1]).headD 0 := by
  have hh := chip_lookup_sound_N permOut (tf .poseidon2) hchip env.loc
    [.var value, .var salt, .const 0, .const 0, .const 0, .const 64207, .const 1]
    (output :: (List.range 7).map (fun j => lanes + j)) (by change ChipArityAdmitted 7; decide) h
  have := congrArg (fun xs : List Int => xs.headD 0) hh
  simpa [List.map_cons, List.map_nil, EmittedExpr.eval] using this

/-- Exported PIs are the fact-hash heads of the very same compared amounts.
The cryptographic/table correctness assumption is explicit; no injectivity is assumed. -/
theorem solvency_commitments_sound {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (permOut : List Int → List Int) (ht : 0 < t.rows.length)
    (hc : ∀ c, Canon ((envAt t 0).loc c)) (hp : ∀ k < 2, Canon (t.pub k))
    (hchip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hs : Satisfied2 hash solvencyDescriptor initial bounds mem t) :
    let a := (envAt t 0).loc
    t.pub 0 = (permOut [a R, a SR, 0, 0, 0, 64207, 1]).headD 0 ∧
    t.pub 1 = (permOut [a L, a SL, 0, 0, 0, 64207, 1]).headD 0 := by
  have hsite (v s o lanes : Nat) (hm : factSite v s o lanes ∈ solvencyDescriptor.constraints) :
      (envAt t 0).loc o =
        (permOut [(envAt t 0).loc v, (envAt t 0).loc s, 0, 0, 0, 64207, 1]).headD 0 := by
    apply factSite_sound permOut t.tf hchip
    exact hs.rowConstraints 0 ht _ hm
  have hpin (o k : Nat) (hk : k < 2)
      (hm : VmConstraint2.base (.piBinding .first o k) ∈ solvencyDescriptor.constraints) :
      t.pub k = (envAt t 0).loc o := by
    have hh := hs.rowConstraints 0 ht _ hm
    have he : (envAt t 0).loc o ≡ t.pub k [ZMOD 2013265921] := by
      simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt] using hh
    exact (eq_of_modEq_canon he (hc o) (hp k hk)).symm
  constructor
  · rw [hpin RC 0 (by decide) (by simp [solvencyDescriptor])]
    exact hsite R SR RC BASE_WIDTH (by simp [solvencyDescriptor])
  · rw [hpin LC 1 (by decide) (by simp [solvencyDescriptor])]
    exact hsite L SL LC (BASE_WIDTH + 7) (by simp [solvencyDescriptor])

/-- Old check accepts an insolvent canonical pair. -/
theorem old_modular_difference_accepts_insolvent :
    (0 : Int) < 2013265920 ∧
    ((0 : Int) - 2013265920) % 2013265921 = 1 ∧ (1 : Int) < 2^30 := by decide
/-- The attack also fits the advertised 30-bit amount domain. -/
theorem old_modular_difference_accepts_30bit_insolvent :
    (0 : Int) < 1073741823 ∧ 1073741823 < (2 : Int)^30 ∧
    ((0 : Int) - 1073741823) % 2013265921 = 939524098 ∧ 939524098 < (2 : Int)^30 := by decide

theorem arithmetic_refuses_insolvent (a : Assignment) (hc : ∀ c, Canon (a c))
    (hbad : a R < a L) :
    ¬ (∀ e ∈ arithmeticBodies, e.eval a ≡ 0 [ZMOD 2013265921]) := by
  intro h
  have hs := arithmetic_sound a hc h
  omega

/-- An honest nonzero subtraction that exercises a low-limb borrow. -/
def honestRow (c : Nat) : Int :=
  if c = R then 32768 else if c = L then 1 else if c = D then 32767 else
  if c = limb 1 ∨ c = limb 2 ∨ c = BORROW ∨ c = bitsBase 1 ∨ c = bitsBase 2 then 1 else
  if c = limb 4 then 32767 else if bitsBase 4 ≤ c ∧ c < bitsBase 4 + 15 then 1 else 0

theorem honest_arithmetic_check :
    arithmeticBodies.all (fun e => decide (e.eval honestRow = 0)) = true := by decide

theorem honest_arithmetic :
    ∀ e ∈ arithmeticBodies, e.eval honestRow ≡ 0 [ZMOD 2013265921] := by
  intro e he
  have hh := (List.all_eq_true.mp honest_arithmetic_check) e he
  have hz : e.eval honestRow = 0 := of_decide_eq_true hh
  rw [hz]

theorem honest_canonical : ∀ c, Canon (honestRow c) := by
  intro c
  unfold honestRow Canon
  split <;> try norm_num
  split <;> try norm_num
  split <;> try norm_num
  split <;> try norm_num
  split <;> try norm_num
  split <;> norm_num

def honestTable : TraceFamily := fun id => if id = .poseidon2 then
  [chipRowN (fun _ => List.replicate 8 0) [32768, 0, 0, 0, 0, 64207, 1],
   chipRowN (fun _ => List.replicate 8 0) [1, 0, 0, 0, 0, 64207, 1]] else []
/-- The extra chip-table premise of the commitment theorem is inhabited too. -/
theorem honest_chip_sound :
    ChipTableSoundN (fun _ => List.replicate 8 0) (honestTable .poseidon2) := by
  intro row hr
  change row ∈ [chipRowN (fun _ => List.replicate 8 0) [32768, 0, 0, 0, 0, 64207, 1],
    chipRowN (fun _ => List.replicate 8 0) [1, 0, 0, 0, 0, 64207, 1]] at hr
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[32768, 0, 0, 0, 0, 64207, 1], by decide, rfl⟩
  · exact ⟨[1, 0, 0, 0, 0, 64207, 1], by decide, rfl⟩

def honestTrace : VmTrace :=
  { rows := [honestRow, honestRow], pub := fun _ => 0, tf := honestTable }

@[simp] theorem honest_loc (i : Nat) (hi : i < 2) :
    (envAt honestTrace i).loc = honestRow := by
  interval_cases i <;> rfl

theorem honest_satisfies : Satisfied2 (fun _ => 0) solvencyDescriptor
    (fun _ => 0) (fun _ => (0, 0)) [] honestTrace := by
  constructor
  · intro i hi c hc
    have hi' : i < 2 := hi
    simp only [solvencyDescriptor, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false, List.mem_map] at hc
    rcases hc with (hc | hc) | hc
    · rcases hc with rfl | rfl <;>
        simp only [VmConstraint2.holdsAt, factSite, BoundedFactEmit.factSite, Lookup.holdsAt, honest_loc i hi'] <;>
        decide
    · obtain ⟨e, he, rfl⟩ := hc
      simp only [firstGate, VmConstraint2.holdsAt, VmConstraint.holdsVm, honest_loc i hi']
      intro _
      exact honest_arithmetic e he
    · rcases hc with rfl | rfl <;>
        simp only [VmConstraint2.holdsAt, VmConstraint.holdsVm, honest_loc i hi'] <;>
        intro _ <;> change (0 : Int) ≡ 0 [ZMOD 2013265921] <;> rfl
  · intro i hi; simp [solvencyDescriptor, EffectVmEmit.siteHoldsAll, EffectVmEmit.siteHoldsAll.go]
  · intro i hi r hr; cases hr
  · exact List.nodup_nil
  · intro op hop; simp [memLog, memOpsOf, solvencyDescriptor, arithmeticBodies,
      firstGate, factSite, BoundedFactEmit.factSite, rangeBodies] at hop
  · simp [memLog, memOpsOf, solvencyDescriptor, arithmeticBodies, firstGate, factSite, BoundedFactEmit.factSite,
      rangeBodies, honestTrace, Dregg2.Crypto.MemoryChecking.Disciplined,
      Dregg2.Crypto.MemoryChecking.DisciplinedFrom, Function.comp_def]
  · simp [Dregg2.Crypto.MemoryChecking.MemCheck, memLog, memOpsOf, solvencyDescriptor,
      arithmeticBodies, firstGate, factSite, BoundedFactEmit.factSite, rangeBodies, honestTrace,
      Dregg2.Crypto.MemoryChecking.initSet, Dregg2.Crypto.MemoryChecking.finalSet, Function.comp_def]
  · simp [honestTrace, honestTable, memLog, memOpsOf, solvencyDescriptor,
      arithmeticBodies, firstGate, factSite, BoundedFactEmit.factSite, rangeBodies]
  · simp [honestTrace, honestTable, mapLog, mapOpsOf, solvencyDescriptor,
      arithmeticBodies, firstGate, factSite, BoundedFactEmit.factSite, rangeBodies]

#assert_all_clean [arithmetic_sound, solvency_emit_sound, factSite_sound, solvency_commitments_sound, old_modular_difference_accepts_insolvent,
  old_modular_difference_accepts_30bit_insolvent, arithmetic_refuses_insolvent,
  honest_arithmetic_check, honest_arithmetic, honest_canonical, honest_chip_sound, honest_satisfies]
/-- info: 'Dregg2.Circuit.Emit.SolvencyLeafEmit.solvency_emit_sound' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms solvency_emit_sound
/-- info: 'Dregg2.Circuit.Emit.SolvencyLeafEmit.solvency_commitments_sound' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms solvency_commitments_sound
/-- info: 'Dregg2.Circuit.Emit.SolvencyLeafEmit.honest_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honest_satisfies
end Dregg2.Circuit.Emit.SolvencyLeafEmit

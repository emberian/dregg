/-
# DecoLeafEmit — fact identity and bounded amount, not transcript authentication

The public tuple is [amount,currency,recipient,intent,paymentHash]. Three chip
lookups compute the two-stage identity and an unexposed salt opening. Because the
transcript commitment is existential witness data, this does not authenticate TLS,
Stripe, a server key, or a transcript. Those are separate executor obligations.
The amount contract is the existing inclusive range 1 ≤ amount ≤ 2^30. Its gates
now use the first-row boundary so even a height-one trace cannot skip the range.
-/
import Dregg2.Circuit.Emit.BoundedFactEmit
namespace Dregg2.Circuit.Emit.DecoLeafEmit
open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint VmRowEnv)
open Dregg2.Circuit.DescriptorIR2
open Dregg2.Circuit.Emit.BoundedFactEmit
open Dregg2.Circuit.Emit.FieldDeltaRangeEmit (Canon eq_of_modEq_canon)
set_option autoImplicit false

def m1Inputs : FactInputs := ![.var 0, .var 1, .var 2, .const 0, .const 0]
def identityInputs : FactInputs := ![.var 5, .var 3, .const 0, .const 0, .const 0]
def transcriptInputs : FactInputs := ![.var 6, .var 4, .const 0, .const 0, .const 0]
def firstGate (e : EmittedExpr) : VmConstraint2 := .base (.boundary .first e)
def pin (col pi : Nat) : VmConstraint2 := .base (.piBinding .first col pi)
def decoDescriptor : EffectVmDescriptor2 :=
  { name := "deco-commitment-leaf::dregg-deco-stripe-v2"
    traceWidth := 59, piCount := 5, tables := [], hashSites := [], ranges := []
    constraints := [pin 0 0, pin 1 1, pin 2 2, pin 3 3,
      factSite m1Inputs 5 38, factSite identityInputs 6 45,
      factSite transcriptInputs 7 52, pin 6 4] ++
      (rangeBodiesOffset 30 0 8 1).map firstGate }

theorem descriptor_count : decoDescriptor.constraints.length = 39 := by decide

/-- Exact inclusive range, derived from the emitted first-row arithmetic. -/
theorem amount_range {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hc : ∀ c, Canon ((envAt t 0).loc c))
    (hs : Satisfied2 hash decoDescriptor initial bounds mem t) :
    1 ≤ (envAt t 0).loc 0 ∧ (envAt t 0).loc 0 ≤ 2^30 := by
  have hh := offset_range_sound (envAt t 0).loc 30 0 8 1 (by norm_num) (by norm_num) hc
  have he : ∀ e ∈ rangeBodiesOffset 30 0 8 1,
      e.eval (envAt t 0).loc ≡ 0 [ZMOD 2013265921] := by
    intro e he
    have hm : firstGate e ∈ decoDescriptor.constraints := by
      exact List.mem_append_right _ (List.mem_map.mpr ⟨e, he, rfl⟩)
    have hp := hs.rowConstraints 0 ht _ hm
    simpa [firstGate, VmConstraint2.holdsAt, VmConstraint.holdsVm] using hp
  have hb := hh he
  constructor <;> omega

def paymentIdentity (permOut : List Int → List Int) (amount currency recipient intent : Int) : Int :=
  (permOut [(permOut [amount, currency, recipient, 0, 0, 64207, 1]).headD 0,
    intent, 0, 0, 0, 64207, 1]).headD 0

/-- Public facts and public identity are connected through the genuine chip outputs.
No hash injectivity or transcript-authentication premise is smuggled into this result. -/
theorem payment_identity {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (permOut : List Int → List Int) (ht : 0 < t.rows.length)
    (hc : ∀ c, Canon ((envAt t 0).loc c)) (hp : ∀ k < 5, Canon (t.pub k))
    (hchip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hs : Satisfied2 hash decoDescriptor initial bounds mem t) :
    t.pub 4 = paymentIdentity permOut (t.pub 0) (t.pub 1) (t.pub 2) (t.pub 3) := by
  have hpin (col k : Nat) (hk : k < 5) (hm : pin col k ∈ decoDescriptor.constraints) :
      (envAt t 0).loc col = t.pub k := by
    have he := hs.rowConstraints 0 ht _ hm
    have hh : (envAt t 0).loc col ≡ t.pub k [ZMOD 2013265921] := by
      simpa [pin, VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt] using he
    exact eq_of_modEq_canon hh (hc col) (hp k hk)
  have hm1 := factSite_sound permOut t.tf hchip (envAt t 0) hash true
    (1 == t.rows.length) m1Inputs 5 38
    (hs.rowConstraints 0 ht _ (by simp [decoDescriptor]))
  have hid := factSite_sound permOut t.tf hchip (envAt t 0) hash true
    (1 == t.rows.length) identityInputs 6 45
    (hs.rowConstraints 0 ht _ (by simp [decoDescriptor]))
  simp only [factAbsorb, m1Inputs, identityInputs, List.map_cons, List.map_nil,
    EmittedExpr.eval, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two,
    Matrix.cons_val_three, Matrix.cons_val_four] at hm1 hid
  rw [hm1] at hid
  have h0 := hpin 0 0 (by decide) (by simp [decoDescriptor])
  have h1 := hpin 1 1 (by decide) (by simp [decoDescriptor])
  have h2 := hpin 2 2 (by decide) (by simp [decoDescriptor])
  have h3 := hpin 3 3 (by decide) (by simp [decoDescriptor])
  have h4 := hpin 6 4 (by decide) (by simp [decoDescriptor])
  simpa [paymentIdentity, h0, h1, h2, h3, h4] using hid

/-- The third lookup binds a private commitment to a private salt. It is not a
binding to an externally supplied authenticated transcript commitment. -/
theorem transcript_opening {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (permOut : List Int → List Int) (ht : 0 < t.rows.length)
    (hchip : ChipTableSoundN permOut (t.tf .poseidon2))
    (hs : Satisfied2 hash decoDescriptor initial bounds mem t) :
    (envAt t 0).loc 7 = (permOut [(envAt t 0).loc 6,
      (envAt t 0).loc 4, 0, 0, 0, 64207, 1]).headD 0 := by
  have hh := factSite_sound permOut t.tf hchip (envAt t 0) hash true
    (1 == t.rows.length) transcriptInputs 7 52
    (hs.rowConstraints 0 ht _ (by simp [decoDescriptor]))
  simpa [factAbsorb, transcriptInputs] using hh


/-- The range statement rejects out-of-domain amounts even at height one. -/
theorem invalid_amount_refused {hash : List Int → Int} {t : VmTrace}
    {initial : Int → Int} {bounds : Int → Int × Nat} {mem : List Int}
    (ht : 0 < t.rows.length) (hc : ∀ c, Canon ((envAt t 0).loc c))
    (hbad : (envAt t 0).loc 0 < 1 ∨ 2^30 < (envAt t 0).loc 0) :
    ¬ Satisfied2 hash decoDescriptor initial bounds mem t := by
  intro hs
  have hh := amount_range ht hc hs
  omega

def honestRow (c : Nat) : Int := if c = 0 then 1 else 0
def honestTable : TraceFamily := fun id => if id = .poseidon2 then
  [chipRowN (fun _ => List.replicate 8 0) [1, 0, 0, 0, 0, 64207, 1],
   chipRowN (fun _ => List.replicate 8 0) [0, 0, 0, 0, 0, 64207, 1]] else []
def honestTrace : VmTrace := {rows := [honestRow], pub := honestRow, tf := honestTable}

theorem honest_arithmetic_check :
    (rangeBodiesOffset 30 0 8 1).all (fun e => decide (e.eval honestRow = 0)) = true := by decide

theorem honest_arithmetic : ∀ e ∈ rangeBodiesOffset 30 0 8 1,
    e.eval honestRow ≡ 0 [ZMOD 2013265921] := by
  intro e he
  have hh := (List.all_eq_true.mp honest_arithmetic_check) e he
  have hz : e.eval honestRow = 0 := of_decide_eq_true hh
  rw [hz]

theorem honest_canonical : ∀ c, Canon (honestRow c) := by
  intro c
  unfold honestRow Canon
  split <;> norm_num

/-- The chip-soundness premise is inhabited, with the same permutation and table
as the full witness below. The theorem is parametric in the genuine permutation. -/
theorem honest_chip_sound : ChipTableSoundN (fun _ => List.replicate 8 0)
    (honestTrace.tf .poseidon2) := by
  intro r hr
  simp only [honestTrace, honestTable, ↓reduceIte, List.mem_cons,
    List.not_mem_nil, or_false] at hr
  rcases hr with rfl | rfl
  · exact ⟨[1, 0, 0, 0, 0, 64207, 1], by decide, rfl⟩
  · exact ⟨[0, 0, 0, 0, 0, 64207, 1], by decide, rfl⟩

/-- A full height-one witness exercises the first-row range on the final row. -/
theorem honest_satisfies : Satisfied2 (fun _ => 0) decoDescriptor
    (fun _ => 0) (fun _ => (0, 0)) [] honestTrace := by
  constructor
  · intro i hi c hc
    have hi' : i = 0 := by change i < 1 at hi; omega
    subst i
    simp only [decoDescriptor, List.mem_append, List.mem_cons, List.mem_nil_iff,
      or_false, List.mem_map] at hc
    rcases hc with hc | ⟨e, he, rfl⟩
    · rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
        simp [pin, VmConstraint2.holdsAt, VmConstraint.holdsVm, envAt,
          honestTrace, honestRow, factSite, Lookup.holdsAt, honestTable,
          factAbsorb, m1Inputs, identityInputs, transcriptInputs,
          chipLookupTupleN, padToE, chipRowN, padTo, EmittedExpr.eval] <;> decide
    · simp only [firstGate, VmConstraint2.holdsAt, VmConstraint.holdsVm]
      intro _
      exact honest_arithmetic e he
  · intro i hi; simp [decoDescriptor, EffectVmEmit.siteHoldsAll, EffectVmEmit.siteHoldsAll.go]
  · intro i hi r hr; cases hr
  · exact List.nodup_nil
  · intro op hop; simp [memLog, memOpsOf, decoDescriptor, rangeBodiesOffset, firstGate,
      factSite, pin] at hop
  · simp [memLog, memOpsOf, decoDescriptor, rangeBodiesOffset, firstGate, factSite, pin,
      honestTrace, Dregg2.Crypto.MemoryChecking.Disciplined,
      Dregg2.Crypto.MemoryChecking.DisciplinedFrom]
  · simp [Dregg2.Crypto.MemoryChecking.MemCheck, memLog, memOpsOf, decoDescriptor,
      rangeBodiesOffset, firstGate, factSite, pin, honestTrace,
      Dregg2.Crypto.MemoryChecking.initSet, Dregg2.Crypto.MemoryChecking.finalSet]
  · simp [honestTrace, honestTable, memLog, memOpsOf, decoDescriptor,
      rangeBodiesOffset, firstGate, factSite, pin]
  · simp [honestTrace, honestTable, mapLog, mapOpsOf, decoDescriptor,
      rangeBodiesOffset, firstGate, factSite, pin]


/-- The old transition gate has no arithmetic content on a height-one trace. -/
theorem old_final_row_range_vacuous (env : VmRowEnv) :
    ∀ e ∈ rangeBodiesOffset 30 0 8 1,
      (VmConstraint2.base (.gate e)).holdsAt (fun _ => 0) (fun _ => []) env true true := by
  intro e _
  trivial

/-- The corrected range refuses the concrete zero-amount witness. -/
theorem zero_amount_arithmetic_refused :
    ¬ (∀ e ∈ rangeBodiesOffset 30 0 8 1,
      e.eval (fun _ => 0) ≡ 0 [ZMOD 2013265921]) := by
  intro h
  have hh := offset_range_sound (fun _ => 0) 30 0 8 1 (by norm_num) (by norm_num)
    (fun _ => by norm_num [Canon]) h
  norm_num at hh

/-- The preexisting upper endpoint is included, not silently narrowed. -/
def upperRow (c : Nat) : Int :=
  if c = 0 then 1073741824 else if 8 ≤ c ∧ c < 38 then 1 else 0
theorem upper_endpoint_arithmetic :
    (rangeBodiesOffset 30 0 8 1).all (fun e => decide (e.eval upperRow = 0)) = true := by decide

/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.descriptor_count' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms descriptor_count
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.amount_range' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms amount_range
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.payment_identity' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms payment_identity
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.transcript_opening' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms transcript_opening
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.invalid_amount_refused' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms invalid_amount_refused
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.honest_arithmetic_check' depends on axioms: [propext] -/
#guard_msgs in
#print axioms honest_arithmetic_check
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.honest_arithmetic' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms honest_arithmetic
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.honest_canonical' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honest_canonical
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.honest_chip_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs in
#print axioms honest_chip_sound
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.honest_satisfies' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs in
#print axioms honest_satisfies
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.old_final_row_range_vacuous' depends on axioms: [propext] -/
#guard_msgs in
#print axioms old_final_row_range_vacuous
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.zero_amount_arithmetic_refused' depends on axioms: [propext,
 Classical.choice,
 Quot.sound] -/
#guard_msgs in
#print axioms zero_amount_arithmetic_refused
/-- info: 'Dregg2.Circuit.Emit.DecoLeafEmit.upper_endpoint_arithmetic' depends on axioms: [propext] -/
#guard_msgs in
#print axioms upper_endpoint_arithmetic
end Dregg2.Circuit.Emit.DecoLeafEmit

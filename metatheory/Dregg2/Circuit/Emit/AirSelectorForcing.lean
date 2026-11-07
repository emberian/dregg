/-
# `Dregg2.Circuit.Emit.AirSelectorForcing` — ⚑⚑⚑ THE TWO SELECTOR PREMISES, DISCHARGED.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Nothing here is a Rust gate, a Rust builder, or a Rust
`air_accepts`. Every leg cashed below is a member of `PastaCurveScheduled.pallasScheduledAir.legs`
— the list the emit lowers — reached by list membership, never re-typed. House Law #1.

## ⚑ WHAT THIS CLOSES

`AirCrossRow` §6 proved that the SCHEDULED trace forces the RCB formula **conditional on two
premises**, and both were named as selector plumbing rather than theorems of the model:

> `PhaseIndicator` (row `t` reads phase `i` as `[i = t]`) and `RowsSat` (row `i` satisfies op `i`'s
> core gates). Until they land, quote §6 as FORCING CONDITIONAL ON THE SELECTOR READING HONESTLY.

Both are theorems here, from the emitted block's own legs:

* `phaseIndicator_of_selectorLegs` — from `selBooleanLegs` + `selOneHotLeg` + `selShiftLegs`.
* `rowsSat_of_scheduleLegs` — from `scheduleLegs`, whose every gate is `gateBy (SEL i)` of a core
  gate, at the row where `PhaseIndicator` says the selector reads `1`.

and `pallasScheduledBlock_forces_the_rcb_formula` / `vestaScheduledBlock_forces_the_rcb_formula`
are §6 **with no selector premise left**. ⚠ Quote them, not the conditional form.

## ⚑⚑ THE PREMISE WAS NOT MERELY UNDONE — ITS OLD STATEMENT WAS FALSE OF THE DESCRIPTOR

`AirCrossRow.PhaseIndicator` read, until 2026-08-08:

    ∀ t < 33, ∀ i < 34, tr t (SEL i) = if i = t then 1 else 0        -- over ℤ

**No leg can force that.** `AirLeg.forces` on a `window` is `body ≡ 0 [ZMOD PMOD]`, so a trace with
`tr 0 (SEL 0) = 1 + P` satisfies booleanity, the one-hot sum and every shift leg, and refutes the
ℤ-equality. The premise was not a target waiting for a proof; it was a statement about a **different
object** than the one the descriptor constrains, and the honest fix is to restate it mod `P` — which
is what `AirCrossRow` now does, and which pulled `indicator_sum_modEq`, `carryMask_is_one` and
`carried_of_carryLeg` into the same reading. ⚑ **Nothing is relaxed by that**: the congruence is the
reading `prove_vm_descriptor2` performs, and every other lemma in the cone was already in it.

## ⚑ WHERE THE PRIME FIELD ACTUALLY ENTERS, AND IT IS ONE PLACE

The shift half of the register is a plain induction and needs no field theory: `nxt(sᵢ₊₁) = loc(sᵢ)`
walks the indicator forward, `nxt(s₀) = 0` kills the return, and the idle leg absorbs phase 32. The
step that needs an argument is **row 0**: `sᵢ ≡ 0` for `i ≥ 1`, which is booleanity plus sum-to-one.

* `bit_of_boolean` — `x·(x−1) ≡ 0 [ZMOD P]` ⇒ `x ≡ 0 ∨ x ≡ 1`. This is exactly `Prime (P : ℤ)`; over
  a composite modulus it is FALSE and a prover would have a third residue to sit on.
* `bits_sum_is_a_count` — a list of bits sums to a NATURAL NUMBER `n ≤ length`, mod `P`.
* `bits_onehot` — with `length < P` and one entry reading `1`, every other entry reads `0`. The
  `length < P` side condition is not decoration: it is what turns `n ≡ 0 [ZMOD P]` into `n = 0`, and
  a register with `P` or more phases would satisfy the sum with every phase live.

⚠ **`SEL` IS THE IDENTITY ON COLUMN INDICES** (`PastaCurveScheduled.SEL i = i`), so "phase column
`i`" and "column `i`" are the same object; the statements below are written at `tr t i` and the two
readings coincide by `rfl`. That is a property of THIS layout, not a convention.

## ⚠ WHICH OBJECT EACH THEOREM IS ABOUT — this cone has two schedules with similar names

Everything here is about **`AirColumnAlloc.rcbOpsScheduled`**, the emitted hand schedule, through
`PastaCurveScheduled.rcbSchedule` (`rcbSchedule_is_the_scheduled_dag` pins the two equal). ⚠ It is
**NOT** about `AirSchedule.rcbOpsOptimal`: `1 307` is a width result no forcing theorem mentions,
and moving to the optimal schedule would move `rcbSchedule`, `carryPhases`, `loOf`/`hiOf` and every
`by decide` in `AirCrossRow` §5b with it.

## ⚠ WHAT IS STILL A PREMISE, AND IT IS A DIFFERENT KIND

`AirCrossRow.PoolsRanged` — that the values the trace presents really are byte/16-bit/1-bit ranged.
§5 below still takes it, exactly as `AirCrossRow` §6 did and exactly as the 3 048-column one-row
block does. ⚠ It is **not** selector plumbing and it is **not** discharged here: `valuePoolLegs` and
`witnessPoolLegs` put every pooled column in a declared range table on every row, but turning that
into a numeric bound needs *"the table the family supplies for `rangeTidW 8` contains only
byte-valued singletons"* — a statement about the TRACE FAMILY the lookup argument produces, one rail
below any leg. That is the lookup argument's own meaning, it is the SAME floor the one-row block
stands on, and it is UNDONE WORK rather than a theorem of the model: the thing worth building is a
`RangeTablesHonest tf → PoolsRanged tr` lemma serving every descriptor in this cone, not one.

⚑ **Nothing about the scheduled layout weakens it.** The pooled legs assert on all 64 rows what the
one-row block asserted once (`PastaCurveScheduled` §3b), so the hypotheses the forcing lemmas take
are strictly more available here, not less.

## Axiom hygiene

`#assert_axioms`-clean; no `sorry`/`admit`/`native_decide`; zero `#guard`s.
Nothing is emitted by name; no VK rotates; nothing re-emits.
-/
import Dregg2.Circuit.Emit.AirCrossRow
import Dregg2.Circuit.BabyBearFriField

namespace Dregg2.Circuit.Emit.AirSelectorForcing

open Dregg2.Circuit (Assignment Expr)
open Dregg2.Circuit.Emit.EffectLower (P)
open Dregg2.Circuit.DescriptorIR2 (TraceFamily WindowExpr)
open Dregg2.Circuit.EffectAirIR (AirLeg)
open Dregg2.Circuit.Emit.PastaFieldSound (SK sVal pLimb qLimb)
open Dregg2.Circuit.Emit.PastaCurveSound (IN_BASE vBase)
open Dregg2.Circuit.Emit.PastaCurveComplete (curveB3 rcbTraceZ)
open Dregg2.Circuit.Emit.PastaCurve (CZp CZq)
open Dregg2.Circuit.Emit.PastaCurveScheduled
  (OpKind SEL SEL_IDLE sumLoc rcbSchedule rcbSchedule_length
   carryLegs valuePoolLegs witnessPoolLegs scheduleLegs opLegs gateBy
   selBooleanLegs selOneHotLeg selShiftLegs
   pallasScheduledAir vestaScheduledAir)
open Dregg2.Circuit.Emit.AirCrossRow
  (RowTrace rowEnv PhaseIndicator RowsSat SlotsCarry PoolsRanged sumLoc_eval
   slotsCarry_of_carryLegs scheduledRows_force_the_rcb_formula
   vestaScheduledRows_force_the_rcb_formula gather)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §1 — ⚑⚑ THE PRIME FIELD, WHERE IT IS NEEDED AND NOWHERE ELSE.

The deployed modulus is `P = 2 013 265 921` = BabyBear, and its primality is the ONE fact that makes
"a selector column is a bit" mean anything. Reused from `BabyBearFriField.babyBearP_prime` (a
`norm_num` Pratt certificate) rather than re-proved, so this file adds no new primality claim. -/

/-- ⚑ **THE DEPLOYED MODULUS IS PRIME, AS AN INTEGER.** -/
theorem pPrimeInt : Prime (P : ℤ) := by
  exact_mod_cast Nat.prime_iff_prime_int.mp Dregg2.Circuit.BabyBearFriField.babyBearP_prime

/-- ⚑⚑ **BOOLEANITY IS A BIT — AND ONLY OVER A PRIME MODULUS.** `x·(x−1) ≡ 0` factors because `P`
is prime; over a composite modulus the same gate admits residues that are neither `0` nor `1`, and
a prover would sit on one to turn a phase half-on. -/
theorem bit_of_boolean {x : ℤ} (h : x * (x + (-1)) ≡ 0 [ZMOD P]) :
    x ≡ 0 [ZMOD P] ∨ x ≡ 1 [ZMOD P] := by
  have hdvd : (P : ℤ) ∣ x * (x + (-1)) := Int.modEq_zero_iff_dvd.mp h
  rcases pPrimeInt.2.2 _ _ hdvd with h0 | h1
  · exact Or.inl (Int.modEq_zero_iff_dvd.mpr h0)
  · refine Or.inr (Int.modEq_iff_dvd.mpr ?_)
    have h2 := dvd_neg.mpr h1
    have he : -(x + (-1)) = 1 - x := by ring
    rwa [he] at h2

/-- ⚑⚑ **A LIST OF BITS SUMS TO A NATURAL NUMBER, MOD `P` — AND THE COUNT BOUNDS ITS LENGTH.**
This is the whole content of "sum-to-one over a prime field": the residue the one-hot leg pins is
not an arbitrary field element but the CARDINALITY of the live set, which is why a bound on the
number of phases can then pin it exactly. -/
theorem bits_sum_is_a_count (f : Nat → ℤ) :
    ∀ l : List Nat, (∀ i ∈ l, f i ≡ 0 [ZMOD P] ∨ f i ≡ 1 [ZMOD P]) →
      ∃ n : Nat, n ≤ l.length ∧ (l.map f).sum ≡ (n : ℤ) [ZMOD P]
        ∧ (n = 0 → ∀ i ∈ l, f i ≡ 0 [ZMOD P]) := by
  intro l
  induction l with
  | nil => intro _; exact ⟨0, le_refl _, by simp, by simp⟩
  | cons c cs ih =>
      intro hb
      obtain ⟨n, hn, hns, hz⟩ := ih (fun i hi => hb i (List.mem_cons_of_mem _ hi))
      rcases hb c (List.mem_cons_self ..) with h0 | h1
      · refine ⟨n, by simp; omega, ?_, ?_⟩
        · rw [List.map_cons, List.sum_cons]
          simpa using h0.add hns
        · intro hn0 i hi
          rcases List.mem_cons.mp hi with h | h
          · exact h ▸ h0
          · exact hz hn0 i h
      · refine ⟨n + 1, by simp; omega, ?_, ?_⟩
        · rw [List.map_cons, List.sum_cons]
          have hcast : ((n + 1 : Nat) : ℤ) = 1 + (n : ℤ) := by push_cast; ring
          rw [hcast]
          exact h1.add hns
        · intro hn0; exact absurd hn0 (Nat.succ_ne_zero n)

/-- ⚑⚑⚑ **ONE-HOT OVER A PRIME FIELD: booleanity + sum-to-one + one entry reading `1` forces every
OTHER entry to read `0`.**

⚠ `hlen` is load-bearing. `n ≡ 0 [ZMOD P]` pins `n = 0` only because `n < P`; a register with `P`
or more phase columns would satisfy booleanity AND the sum with every phase live, and the whole
schedule discipline would be vacuous. The scheduled block has 34 columns against 2 013 265 921. -/
theorem bits_onehot (f : Nat → ℤ) (l : List Nat)
    (hb : ∀ i ∈ l, f i * (f i + (-1)) ≡ 0 [ZMOD P])
    (hlen : l.length < 2013265921)
    (hs : (l.map f).sum ≡ 1 [ZMOD P])
    {a : Nat} (ha : a ∈ l) (h1 : f a ≡ 1 [ZMOD P]) :
    ∀ i ∈ l, i ≠ a → f i ≡ 0 [ZMOD P] := by
  have hperm : l.Perm (a :: l.erase a) := List.perm_cons_erase ha
  have hmapsum : (l.map f).sum = f a + ((l.erase a).map f).sum := by
    rw [(hperm.map f).sum_eq, List.map_cons, List.sum_cons]
  have htail : ((l.erase a).map f).sum ≡ 0 [ZMOD P] := by
    rw [hmapsum] at hs
    have hd := hs.sub h1
    simpa using hd
  have hbits : ∀ i ∈ l.erase a, f i ≡ 0 [ZMOD P] ∨ f i ≡ 1 [ZMOD P] :=
    fun i hi => bit_of_boolean (hb i (List.mem_of_mem_erase hi))
  obtain ⟨n, hn, hns, hz⟩ := bits_sum_is_a_count f (l.erase a) hbits
  have hlen' : (l.erase a).length ≤ l.length := List.length_erase_le
  have hn0 : (n : ℤ) ≡ 0 [ZMOD P] := hns.symm.trans htail
  have hdvd : (P : ℤ) ∣ (n : ℤ) := Int.modEq_zero_iff_dvd.mp hn0
  have hdvd' : (2013265921 : ℕ) ∣ n := by exact_mod_cast hdvd
  have hzero : n = 0 := Nat.eq_zero_of_dvd_of_lt hdvd' (by omega)
  intro i hi hne
  exact hz hzero i ((List.mem_erase_of_ne hne).mpr hi)

/-! ## §2 — ⚑ THE HYPOTHESIS: THE EMITTED BLOCK'S LEGS, FORCED ON THE 33 OP ROWS.

One predicate, over a leg LIST rather than an AIR, so the extraction is list membership and the
pallas/vesta split is one `rfl` rather than two proofs.

⚑ **The flags are the real ones, not `false false`.** Row 0 carries `isFirst`; and no row `t < 33`
is the LAST row of the block, because `prove_vm_descriptor2` refuses a non-power-of-two trace height
(`descriptor_ir2.rs:6987`) so the 33 op rows sit inside 64 with the idle phase absorbing the tail.
A `.first` leg that never fired would leave the register unpinned at row 0 and `PhaseIndicator`
unprovable, so the flag is where the argument lives. -/

/-- ⚑ **THE 33 OP ROWS OF THE SCHEDULED BLOCK SATISFY `legs`.** -/
def LegsHold (tr : RowTrace) (tf : TraceFamily) (pub chal : Assignment)
    (legs : List AirLeg) : Prop :=
  ∀ t, t < 33 → ∀ l ∈ legs, l.forces tf (rowEnv tr pub chal t) (decide (t = 0)) false

theorem LegsHold.mono {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}
    {a b : List AirLeg} (hsub : ∀ l ∈ a, l ∈ b) (h : LegsHold tr tf pub chal b) :
    LegsHold tr tf pub chal a :=
  fun t ht l hl => h t ht l (hsub l hl)

/-- The phase register's three leg families, as one block. -/
def selectorLegs : List AirLeg := selBooleanLegs ++ [selOneHotLeg] ++ selShiftLegs

/-- ⚑ **THE SCHEDULED BLOCK'S LEG LIST**, as a function of the modulus limbs — literally
`pallasScheduledAir.legs` at `pLimb` and `vestaScheduledAir.legs` at `qLimb`, which is what
`pallas_legs_eq` / `vesta_legs_eq` pin. -/
def scheduledLegs (pl : Nat → ℤ) : List AirLeg :=
  selectorLegs ++ valuePoolLegs ++ witnessPoolLegs ++ carryLegs ++ scheduleLegs pl

theorem pallas_legs_eq : pallasScheduledAir.legs = scheduledLegs pLimb := rfl
theorem vesta_legs_eq : vestaScheduledAir.legs = scheduledLegs qLimb := rfl

theorem selectorLegs_sub {pl : Nat → ℤ} : ∀ l ∈ selectorLegs, l ∈ scheduledLegs pl :=
  fun _ hl =>
    List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_left _ hl)))

theorem carryLegs_sub {pl : Nat → ℤ} : ∀ l ∈ carryLegs, l ∈ scheduledLegs pl :=
  fun _ hl => List.mem_append_left _ (List.mem_append_right _ hl)

theorem scheduleLegs_sub {pl : Nat → ℤ} : ∀ l ∈ scheduleLegs pl, l ∈ scheduledLegs pl :=
  fun _ hl => List.mem_append_right _ hl

theorem valuePoolLegs_sub {pl : Nat → ℤ} : ∀ l ∈ valuePoolLegs, l ∈ scheduledLegs pl :=
  fun _ hl =>
    List.mem_append_left _ (List.mem_append_left _
      (List.mem_append_left _ (List.mem_append_right _ hl)))

theorem witnessPoolLegs_sub {pl : Nat → ℤ} : ∀ l ∈ witnessPoolLegs, l ∈ scheduledLegs pl :=
  fun _ hl =>
    List.mem_append_left _ (List.mem_append_left _ (List.mem_append_right _ hl))

/-! ### §2a — the six selector facts, cashed off the leg list. -/

section Selectors

variable {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}

/-- Booleanity, on every row and every one of the 34 phase columns. `.all` scope, so there is no
flag to discharge — a prover cannot pick a row where the bit constraint sleeps. -/
theorem sel_boolean (h : LegsHold tr tf pub chal selectorLegs) {t : Nat} (ht : t < 33)
    {i : Nat} (hi : i < 34) :
    tr t i * (tr t i + (-1)) ≡ 0 [ZMOD P] :=
  h t ht _ (List.mem_append_left _ (List.mem_append_left _
    (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩)))

/-- Sum-to-one, on every row. -/
theorem sel_onehot (h : LegsHold tr tf pub chal selectorLegs) {t : Nat} (ht : t < 33) :
    ((List.range 34).map (tr t)).sum ≡ 1 [ZMOD P] := by
  have hb : (WindowExpr.add (sumLoc (List.range 34)) (.const (-1))).eval (rowEnv tr pub chal t)
      ≡ 0 [ZMOD P] :=
    h t ht _ (List.mem_append_left _ (List.mem_append_right _ (List.mem_singleton.mpr rfl)))
  simp only [WindowExpr.eval, sumLoc_eval, rowEnv] at hb
  have h1 := hb.add_right 1
  have e1 : ((List.range 34).map (tr t)).sum + -1 + 1 = ((List.range 34).map (tr t)).sum := by ring
  have e2 : (0 : ℤ) + 1 = 1 := by ring
  rwa [e1, e2] at h1

/-- Phase 0 is live on the FIRST row. This is the only `.first` leg in the block and the only place
`isFirst` is read; a trace whose row 0 did not carry it would leave the register unpinned. -/
theorem sel_first (h : LegsHold tr tf pub chal selectorLegs) : tr 0 0 ≡ 1 [ZMOD P] := by
  have hb : (WindowExpr.add (.loc (SEL 0)) (.const (-1))).eval (rowEnv tr pub chal 0)
      ≡ 0 [ZMOD P] :=
    h 0 (by omega) _
      (List.mem_append_right _ (List.mem_cons_self ..)) rfl
  simp only [WindowExpr.eval, rowEnv, SEL] at hb
  have h1 := hb.add_right 1
  have e1 : tr 0 0 + -1 + 1 = tr 0 0 := by ring
  have e2 : (0 : ℤ) + 1 = 1 := by ring
  rwa [e1, e2] at h1

/-- Phase 0 never returns. -/
theorem sel_zero_never_returns (h : LegsHold tr tf pub chal selectorLegs) {t : Nat} (ht : t < 33) :
    tr (t + 1) 0 ≡ 0 [ZMOD P] := by
  have hb : (WindowExpr.nxt (SEL 0)).eval (rowEnv tr pub chal t) ≡ 0 [ZMOD P] :=
    h t ht _
      (List.mem_append_right _ (List.mem_cons_of_mem _ (List.mem_cons_self ..))) rfl
  simpa [WindowExpr.eval, rowEnv, SEL] using hb

/-- The idle phase absorbs phase 32 and itself. -/
theorem sel_idle (h : LegsHold tr tf pub chal selectorLegs) {t : Nat} (ht : t < 33) :
    tr (t + 1) 33 + -1 * (tr t 32 + tr t 33) ≡ 0 [ZMOD P] := by
  have hb : (WindowExpr.add (.nxt SEL_IDLE)
      (.mul (.const (-1)) (.add (.loc (SEL 32)) (.loc SEL_IDLE)))).eval (rowEnv tr pub chal t)
      ≡ 0 [ZMOD P] :=
    h t ht _
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_self ..)))) rfl
  exact hb

/-- The shift: phase `i` at row `t` becomes phase `i+1` at row `t+1`, for `i < 32`. -/
theorem sel_shift (h : LegsHold tr tf pub chal selectorLegs) {t : Nat} (ht : t < 33)
    {i : Nat} (hi : i < 32) :
    tr (t + 1) (i + 1) + -1 * tr t i ≡ 0 [ZMOD P] := by
  have hb : (WindowExpr.add (.nxt (SEL (i + 1))) (.mul (.const (-1)) (.loc (SEL i)))).eval
      (rowEnv tr pub chal t) ≡ 0 [ZMOD P] :=
    h t ht _
      (List.mem_append_right _
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ (List.mem_cons_of_mem _
          (List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩))))) rfl
  exact hb

/-- ⚠⚑ **THE HYPOTHESIS IS REFUTABLE, AND HERE IS A TRACE IT REFUSES.** A premise nothing can
falsify proves nothing; `LegsHold … selectorLegs` is a real constraint on the trace, and the
constant-`5` trace — which satisfies no phase discipline at all — is refused by the ONE `.first` leg.
⚑ Read with `phaseIndicator_of_selectorLegs`: its conclusion is false of that same trace, so the
implication could not have been holding for the empty reason. -/
theorem legsHold_refuses_a_constant_trace (tf : TraceFamily) (pub chal : Assignment) :
    ¬ LegsHold (fun _ _ => 5) tf pub chal selectorLegs := by
  intro h
  have h5 : (5 : ℤ) ≡ 1 [ZMOD P] := sel_first h
  exact absurd h5 (by decide)

end Selectors

/-! ## §3 — ⚑⚑⚑ `PhaseIndicator` IS A THEOREM.

Row 0 is the prime-field argument; every other row is the shift, walked forward. The two halves are
separated on purpose: if the register ever changes shape, the induction is where the change lands
and §1 is untouched. -/

/-- ⚑⚑ **ROW 0: EXACTLY PHASE 0 IS LIVE.** `hfirst` gives `s₀ ≡ 1`; `bits_onehot` gives `sᵢ ≡ 0`
for every other `i`, and it is here and only here that primality is spent. -/
theorem phase_row_zero {tr : RowTrace}
    (hbool : ∀ t, t < 33 → ∀ i, i < 34 → tr t i * (tr t i + (-1)) ≡ 0 [ZMOD P])
    (honehot : ∀ t, t < 33 → ((List.range 34).map (tr t)).sum ≡ 1 [ZMOD P])
    (hfirst : tr 0 0 ≡ 1 [ZMOD P]) :
    ∀ i, i < 34 → tr 0 i ≡ (if i = 0 then 1 else 0) [ZMOD P] := by
  have hb : ∀ i ∈ List.range 34, tr 0 i * (tr 0 i + (-1)) ≡ 0 [ZMOD P] :=
    fun i hi => hbool 0 (by omega) i (List.mem_range.mp hi)
  have hzero := bits_onehot (tr 0) (List.range 34) hb (by simp)
    (honehot 0 (by omega)) (List.mem_range.mpr (by omega)) hfirst
  intro i hi
  by_cases hi0 : i = 0
  · subst hi0; simpa using hfirst
  · rw [if_neg hi0]
    exact hzero i (List.mem_range.mpr hi) hi0

/-- ⚑⚑⚑ **THE PHASE REGISTER READS AS THE ONE-HOT ROW INDICATOR, FROM SIX FACTS.**

⚑ Parametric in the register's own legs on purpose. `PastaCurveScheduled`'s register is ONE-SHOT
(`nxt(s₀) ≡ 0` outright) and a CHAIN's is cyclic (`nxt(s₀) ≡ loc(s₃₂)·loc(GO)`) — but over the first
block, rows `0 … 32`, the two agree, because `hnoReturn` and `hidle` are handed `tr t 32 ≡ 0` and
that is what a cyclic register needs to collapse to the one-shot one. Stating the induction over the
FACTS rather than over one leg list is what lets a second register reuse it instead of copying it.

⚠ Mod `P`, which is the only reading a window leg can supply. -/
theorem phaseIndicator_of_phaseFacts {tr : RowTrace}
    (hbool : ∀ t, t < 33 → ∀ i, i < 34 → tr t i * (tr t i + (-1)) ≡ 0 [ZMOD P])
    (honehot : ∀ t, t < 33 → ((List.range 34).map (tr t)).sum ≡ 1 [ZMOD P])
    (hfirst : tr 0 0 ≡ 1 [ZMOD P])
    (hnoReturn : ∀ t, t < 32 → tr t 32 ≡ 0 [ZMOD P] → tr (t + 1) 0 ≡ 0 [ZMOD P])
    (hidle : ∀ t, t < 32 → tr t 32 ≡ 0 [ZMOD P] → tr t 33 ≡ 0 [ZMOD P] →
              tr (t + 1) 33 ≡ 0 [ZMOD P])
    (hshift : ∀ t, t < 33 → ∀ i, i < 32 → tr (t + 1) (i + 1) + -1 * tr t i ≡ 0 [ZMOD P]) :
    PhaseIndicator tr := by
  intro t
  induction t with
  | zero => intro _ i hi; exact phase_row_zero hbool honehot hfirst i hi
  | succ n ih =>
      intro hn i hi
      have hn33 : n < 33 := by omega
      have hn32 : n < 32 := by omega
      have ihn := ih (by omega)
      have h32 : tr n 32 ≡ 0 [ZMOD P] := by
        have := ihn 32 (by omega)
        rwa [if_neg (by omega : ¬ ((32 : Nat) = n))] at this
      rcases Nat.eq_zero_or_pos i with rfl | hipos
      · rw [if_neg (by omega : ¬ ((0 : Nat) = n + 1))]
        exact hnoReturn n hn32 h32
      obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      by_cases hj33 : j = 32
      · subst hj33
        have h33 : tr n 33 ≡ 0 [ZMOD P] := by
          have := ihn 33 (by omega)
          rwa [if_neg (by omega : ¬ ((33 : Nat) = n))] at this
        rw [if_neg (by omega : ¬ ((32 : Nat) + 1 = n + 1))]
        exact hidle n hn32 h32 h33
      · have hj32 : j < 32 := by omega
        have hstep : tr (n + 1) (j + 1) ≡ tr n j [ZMOD P] := by
          have := (hshift n hn33 j hj32).add_right (tr n j)
          simpa using this
        have hcomb := hstep.trans (ihn j (by omega))
        by_cases hje : j = n
        · rw [if_pos (by omega : j + 1 = n + 1)]
          rwa [if_pos hje] at hcomb
        · rw [if_neg (by omega : ¬ (j + 1 = n + 1))]
          rwa [if_neg hje] at hcomb

/-- ⚑⚑⚑ **`PhaseIndicator` DISCHARGED FOR THE ONE-SHOT REGISTER** — the premise `AirCrossRow` §5 and
§7 consumed, from `PastaCurveScheduled`'s own selector legs. `sel_zero_never_returns` and `sel_idle`
do not need the `tr t 32 ≡ 0` they are handed; a cyclic register does, and that is the only
difference. -/
theorem phaseIndicator_of_selectorLegs {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}
    (h : LegsHold tr tf pub chal selectorLegs) : PhaseIndicator tr := by
  refine phaseIndicator_of_phaseFacts
    (fun t ht i hi => sel_boolean h ht hi) (fun t ht => sel_onehot h ht) (sel_first h)
    (fun t ht _ => sel_zero_never_returns h (by omega)) (fun t ht h32 h33 => ?_)
    (fun t ht i hi => sel_shift h ht hi)
  have hidle := sel_idle h (by omega : t < 33)
  have hs : tr t 32 + tr t 33 ≡ 0 [ZMOD P] := by simpa using h32.add h33
  have hc : tr (t + 1) 33 + -1 * (tr t 32 + tr t 33) ≡ tr (t + 1) 33 + -1 * 0 [ZMOD P] :=
    (Int.ModEq.refl _).add ((Int.ModEq.refl (-1 : ℤ)).mul hs)
  have := hc.symm.trans hidle
  simpa using this

/-! ## §4 — ⚑⚑⚑ `RowsSat` IS A THEOREM.

`opLegs pl i t` is `((coreOf pl t.1).legs … |>.filter isGate).map (gateBy (SEL i))`, so a core gate's
phase-gated image is one `List.mem_map` / `List.mem_filter` / `List.mem_append_left` away from the
emitted list. With the selector reading `1` at row `i`, the gate is the core gate. -/

/-- ⚑⚑ **A PHASE-GATED GATE, CASHED ON ITS OWN ROW.** `gateBy (SEL i)` multiplies the body by the
selector; at row `i` the selector is congruent to `1`, so the body vanishes on its own.

⚠ This is where a prover would attack a schedule that only had booleanity: with `sᵢ` free to be `0`
at row `i`, EVERY gate would be satisfiable by turning the phase off. `sel_onehot` plus the shift is
what makes `sᵢ ≡ 1` at row `i` rather than merely `sᵢ ∈ {0,1}`. -/
theorem gate_of_gateBy {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}
    (hp : PhaseIndicator tr) {i : Nat} (hi : i < 33) {e : Expr}
    (hleg : (gateBy (SEL i) (AirLeg.gate ⟨e, .const 0⟩)).forces tf (rowEnv tr pub chal i)
              (decide (i = 0)) false) :
    P ∣ e.eval (tr i) := by
  have hb : (Expr.mul (.var (SEL i)) e).eval (tr i) ≡ (Expr.const 0).eval (tr i) [ZMOD P] :=
    hleg rfl
  rw [Expr.eval, Expr.eval, Expr.eval] at hb
  have hsel : tr i i ≡ 1 [ZMOD P] := by
    have := hp i hi i (by omega)
    simpa [SEL] using this
  have h1 : (1 : ℤ) * e.eval (tr i) ≡ tr i i * e.eval (tr i) [ZMOD P] :=
    Int.ModEq.mul_right _ hsel.symm
  rw [one_mul] at h1
  exact Int.modEq_zero_iff_dvd.mp (h1.trans hb)

/-- Row `i`'s own legs are legs of the block. `rcbSchedule[i]? = some t` is what keeps a caller from
supplying a row for an op the schedule does not have. -/
theorem opLegs_sub {pl : Nat → ℤ} {i : Nat} (hi : i < 33) {t : OpKind × Nat × Nat × Nat}
    (hti : rcbSchedule[i]? = some t) : ∀ l ∈ opLegs pl i t, l ∈ scheduleLegs pl := by
  intro l hl
  refine List.mem_flatMap.mpr ⟨i, List.mem_range.mpr ?_, ?_⟩
  · rw [rcbSchedule_length]; exact hi
  · rw [hti]; exact hl

/-- ⚑⚑⚑ **EVERY SCHEDULED ROW SATISFIES ITS OWN OP'S GATES — `RowsSat` DISCHARGED.**

⚠ The `b3` the conclusion carries is `curveB3`, because `coreOf … .smul` bakes it into the emitted
legs. A theorem at a free `b3` would be a theorem about an AIR this file does not emit. -/
theorem rowsSat_of_scheduleLegs {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}
    {pl : Nat → ℤ} (hp : PhaseIndicator tr) (h : LegsHold tr tf pub chal (scheduleLegs pl)) :
    RowsSat tr pl (curveB3 : ℤ) := by
  intro i t hti
  have hi : i < 33 := by
    have hlt := List.getElem?_eq_some_iff.mp hti
    obtain ⟨hlt', _⟩ := hlt
    rw [rcbSchedule_length] at hlt'
    exact hlt'
  have hrow : ∀ l ∈ opLegs pl i t, l.forces tf (rowEnv tr pub chal i) (decide (i = 0)) false :=
    fun l hl => h i hi l (opLegs_sub hi hti l hl)
  obtain ⟨k, d, s1, s2⟩ := t
  cases k with
  | mul =>
      intro m hm
      exact gate_of_gateBy hp hi (hrow _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr
        ⟨List.mem_append_left _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩), rfl⟩, rfl⟩))
  | add =>
      intro m hm
      exact gate_of_gateBy hp hi (hrow _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr
        ⟨List.mem_append_left _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩), rfl⟩, rfl⟩))
  | sub =>
      intro m hm
      exact gate_of_gateBy hp hi (hrow _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr
        ⟨List.mem_append_left _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩), rfl⟩, rfl⟩))
  | smul =>
      intro m hm
      exact gate_of_gateBy hp hi (hrow _ (List.mem_map.mpr ⟨_, List.mem_filter.mpr
        ⟨List.mem_append_left _ (List.mem_map.mpr ⟨m, List.mem_range.mpr hm, rfl⟩), rfl⟩, rfl⟩))

/-! ## §5 — ⚑⚑⚑ §6, UNCONDITIONAL.

`AirCrossRow.scheduledRows_force_the_rcb_formula` took three premises; two of them are now theorems
of the same hypothesis that supplies the carry legs. What remains is `PoolsRanged`, and §6 below
says where that comes from. -/

/-- ⚑ Both selector premises and the carry premise, from ONE hypothesis: the emitted block's legs
hold on its 33 op rows. -/
theorem slotsCarry_of_legs {tr : RowTrace} {tf : TraceFamily} {pub chal : Assignment}
    {pl : Nat → ℤ} (hp : PhaseIndicator tr) (h : LegsHold tr tf pub chal (scheduledLegs pl)) :
    SlotsCarry tr :=
  slotsCarry_of_carryLegs tr tf pub chal hp
    (fun t ht l hl => h t ht l (carryLegs_sub l hl))

/-- ⚑⚑⚑ **THE SCHEDULED PALLAS BLOCK FORCES `(X3, Y3, Z3) ≡ rcbTraceZ 15 (P, Q)` MOD THE
PALLAS-BASE PRIME — WITH NO SELECTOR PREMISE.**

⚠ **Which object:** `pallasScheduledAir`, the block emitted as
`dregg-pasta-pallas-complete-add-scheduled::v1` at 481 declared / 1 499 committed columns, on the
hand schedule `rcbOpsScheduled`. NOT `AirSchedule.rcbOpsOptimal`. -/
theorem pallasScheduledBlock_forces_the_rcb_formula (tr : RowTrace) (tf : TraceFamily)
    (pub chal : Assignment) (h : LegsHold tr tf pub chal pallasScheduledAir.legs)
    (hr : PoolsRanged tr) :
    CZp (sVal (gather tr) (vBase IN_BASE 26))
        (rcbTraceZ (curveB3 : ℤ)
          (sVal (gather tr) 0)
          (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK))
          (sVal (gather tr) (3*SK))
          (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).X3g
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 29))
        (rcbTraceZ (curveB3 : ℤ)
          (sVal (gather tr) 0)
          (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK))
          (sVal (gather tr) (3*SK))
          (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Y3f
    ∧ CZp (sVal (gather tr) (vBase IN_BASE 32))
        (rcbTraceZ (curveB3 : ℤ)
          (sVal (gather tr) 0)
          (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK))
          (sVal (gather tr) (3*SK))
          (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Z3c := by
  rw [pallas_legs_eq] at h
  have hp : PhaseIndicator tr :=
    phaseIndicator_of_selectorLegs (h.mono selectorLegs_sub)
  exact scheduledRows_force_the_rcb_formula tr (slotsCarry_of_legs hp h) hr
    (rowsSat_of_scheduleLegs hp (h.mono scheduleLegs_sub))

/-- ⚑⚑ **…AND THE VESTA TWIN**, because the accumulator leg is Step/Tick on Vesta and a Pallas-only
discharge would leave half the recursion boundary conditional. -/
theorem vestaScheduledBlock_forces_the_rcb_formula (tr : RowTrace) (tf : TraceFamily)
    (pub chal : Assignment) (h : LegsHold tr tf pub chal vestaScheduledAir.legs)
    (hr : PoolsRanged tr) :
    CZq (sVal (gather tr) (vBase IN_BASE 26))
        (rcbTraceZ (curveB3 : ℤ)
          (sVal (gather tr) 0)
          (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK))
          (sVal (gather tr) (3*SK))
          (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).X3g
    ∧ CZq (sVal (gather tr) (vBase IN_BASE 29))
        (rcbTraceZ (curveB3 : ℤ)
          (sVal (gather tr) 0)
          (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK))
          (sVal (gather tr) (3*SK))
          (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Y3f
    ∧ CZq (sVal (gather tr) (vBase IN_BASE 32))
        (rcbTraceZ (curveB3 : ℤ)
          (sVal (gather tr) 0)
          (sVal (gather tr) SK)
          (sVal (gather tr) (2*SK))
          (sVal (gather tr) (3*SK))
          (sVal (gather tr) (4*SK))
          (sVal (gather tr) (5*SK))).Z3c := by
  rw [vesta_legs_eq] at h
  have hp : PhaseIndicator tr :=
    phaseIndicator_of_selectorLegs (h.mono selectorLegs_sub)
  exact vestaScheduledRows_force_the_rcb_formula tr (slotsCarry_of_legs hp h) hr
    (rowsSat_of_scheduleLegs hp (h.mono scheduleLegs_sub))

#assert_axioms pPrimeInt
#assert_axioms bit_of_boolean
#assert_axioms bits_sum_is_a_count
#assert_axioms bits_onehot
#assert_axioms sel_boolean
#assert_axioms sel_onehot
#assert_axioms sel_first
#assert_axioms legsHold_refuses_a_constant_trace
#assert_axioms sel_shift
#assert_axioms phase_row_zero
#assert_axioms phaseIndicator_of_phaseFacts
#assert_axioms phaseIndicator_of_selectorLegs
#assert_axioms gate_of_gateBy
#assert_axioms rowsSat_of_scheduleLegs
#assert_axioms slotsCarry_of_legs
#assert_axioms pallasScheduledBlock_forces_the_rcb_formula
#assert_axioms vestaScheduledBlock_forces_the_rcb_formula

end Dregg2.Circuit.Emit.AirSelectorForcing

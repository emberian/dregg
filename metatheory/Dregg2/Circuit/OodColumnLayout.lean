/-
# `Dregg2.Circuit.OodColumnLayout` — the GENERAL (∀-descriptor) COLUMN-LAYOUT MODELER.

## What this closes

Both the OOD/hood reduction (`AlgoStarkSoundTransferV3`) and the LogUp reduction bottom out at the
same named residual: "the column layout is unmodeled" — the map from `verifyAlgo`'s single batched
`TableOpening.constraintEval` onto the per-arith-constraint residual family was exhibited by hand for
`transferV3` (`arithList transferV3` / `Rfam transferV3`). This module states the modeler ONCE, over
`∀ d : EffectVmDescriptor2`, and proves the COLUMN-LAYOUT LAW for any descriptor:

  * `oodArithList d`   — the descriptor's ACTUAL arith-constraint layout (`d.constraints.filter isArithB`);
  * `oodRfam d t ζ qp` — its per-constraint residual family `R_j = C_j(ζ) − Z(ζ)·q_j(ζ)`, indexed by
        that layout;
  * `oodBatchResidual d t ζ qp` — the RLC batching polynomial `Σ_j Λ^j · R_j` (in the challenge Λ),
        whose value at the sampled Λ is `verifyAlgo`'s batched `constraintEval` residual;
  * `oodColumnLayout_law` — **the law, ∀ d**: `(oodBatchResidual d t ζ qp).coeff j = R_j`, the `j`-th
        coefficient IS the `j`-th arith constraint's residual (via `batchResidual_coeff`). The batched
        opening therefore genuinely carries every per-constraint residual — the plumbing residual is a
        THEOREM, not a per-descriptor hand-model;
  * `oodLayout_debatch` / `mainAirAcceptF_of_oodLayout` / `hood_of_oodColumnLayout` — the discharge
        wired through: batched residual `= 0` at a non-exceptional Λ forces every per-constraint OOD
        identity, hence `MainAirAcceptF d t`, for ANY `d`;
  * `transferV3_columnLayout_law` — the hand-modeled `transferV3` layout RE-DERIVED as the
        specialization `oodColumnLayout_law transferV3` (subsumption, not a re-proof).

## Non-vacuity

The modeler reads real descriptors: `#guard (oodArithList transferV3).length == 155` (of 295 total —
a PROPER subset, so `isArithB` genuinely discriminates), the kernel-checked
`oodArithList_transferV3_length`, and `oodColumnLayout_law_fires` (the coefficient law at the concrete
first column of the deployed `transferV3` layout). `transferV3_rlc_bound` discharges outright the
nonemptiness hypothesis the hand-model's `rlc_lambda_is_bounded_fs_form` had to carry.

## What stays per-descriptor

Nothing structural: layout, residual family, batching polynomial, coefficient law, de-batch, and the
`MainAirAcceptF` derivation are all `∀ d`. Only the FRI extraction bundle's per-effect assembly (which
descriptor the deployed slice runs, e.g. `FriLdtExtractV3` at `transferV3`) remains per-effect — a
deployment fact, not layout plumbing.

## Discipline

Sorry-free; no carrier; no `Fintype`/`decide` over `|F|`-sized objects (the only `decide` is a
295-element constraint-list length; degree bounds are `< #constraints`, a small Nat). New file;
imports read-only; builds targeted (`lake build Dregg2.Circuit.OodColumnLayout`).
-/
import Dregg2.Circuit.AlgoStarkSoundTransferV3

namespace Dregg2.Circuit.OodColumnLayout

open Polynomial
open Dregg2.Circuit.FriVerifier
  (verifyAlgo BatchProofData WrapPublics FriParams RecursionVk FriCore FieldArith
   TableOpening fullChecks)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith)
open Dregg2.Circuit.RotatedKernelRefinement (transferV3)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly ood_forces_mainAirAccept_field_of_residuals)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet)
open Dregg2.Circuit.OodSoundnessGame
  (batchResidual batchResidual_coeff batchResidual_eval rlc_debatch
   batchResidual_natDegree_lt batchResidual_exceptionalSet_card_lt)
open Dregg2.Circuit.OodCommitmentBinding (merkleRecomputeZ OpeningColl)
open Dregg2.Circuit.Poseidon2Binding (Poseidon2SpongeCR)
open Dregg2.Circuit.BabyBearFriField (BabyBear)
open Dregg2.Circuit.AlgoStarkSoundTransferV3
  (isArithB isArithB_iff arithList Rfam hood_of_reductions)

/-! ## §1 — THE GENERAL MODELER: layout, residual family, batching polynomial, for ANY descriptor. -/

/-- **The column layout of ANY descriptor** — its actual arithmetic (main-table) constraint list,
`d.constraints.filter isArithB`. This is what `verifyAlgo`'s RLC batches: the `j`-th power of the
batching challenge Λ carries the `j`-th element of THIS list. Interaction-bus arms are excluded
(their residual is the separate LogUp AIR). -/
def oodArithList (d : EffectVmDescriptor2) : List VmConstraint2 := d.constraints.filter isArithB

/-- `oodArithList d` IS the descriptor's filtered constraint list (definitional). -/
theorem oodArithList_eq (d : EffectVmDescriptor2) :
    oodArithList d = d.constraints.filter isArithB := rfl

/-- The general modeler coincides definitionally with the template's `arithList` — the hand-model's
layout was already an instance of this shape. -/
theorem oodArithList_eq_arithList (d : EffectVmDescriptor2) :
    oodArithList d = arithList d := rfl

/-- Membership in the layout ⟺ a declared constraint that is arithmetic. -/
theorem mem_oodArithList_iff (d : EffectVmDescriptor2) (c : VmConstraint2) :
    c ∈ oodArithList d ↔ c ∈ d.constraints ∧ isArith c := by
  simp [oodArithList, List.mem_filter, isArithB_iff]

/-- **The per-constraint residual family of ANY descriptor**, indexed by its column layout:
`oodRfam d t ζ qp j = C_j(ζ) − Z(ζ)·q_j(ζ)` for the `j`-th arith constraint of `d`. This is the
`R : Fin n → BabyBear` that `batchResidual` weights by `Λ^j` and `rlc_debatch` de-batches. -/
noncomputable def oodRfam (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) : Fin (oodArithList d).length → BabyBear :=
  fun j => (constraintPoly d t ((oodArithList d).get j)).eval ζ
             - (vanishingPoly t).eval ζ * (qp ((oodArithList d).get j)).eval ζ

/-- The general residual family coincides definitionally with the template's `Rfam`. -/
theorem oodRfam_eq_Rfam (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    oodRfam d t ζ qp = Rfam d t ζ qp := rfl

/-- **The RLC batching polynomial of ANY descriptor** — `Σ_j Λ^j · R_j` over `d`'s actual layout,
as a polynomial in the batching challenge. Its value at the sampled Λ is `verifyAlgo`'s batched
`constraintEval` residual for the `d`-slice; its degree is `< #(oodArithList d)` (a small Nat). -/
noncomputable def oodBatchResidual (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) : Polynomial BabyBear :=
  batchResidual (oodRfam d t ζ qp)

/-- The general batching polynomial IS the template's `batchResidual (Rfam …)` (definitional) — so
`FriLdtExtractV3`'s hand-stated layout equation is literally an equation about
`oodBatchResidual transferV3`. -/
theorem oodBatchResidual_eq_template (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    oodBatchResidual d t ζ qp = batchResidual (Rfam d t ζ qp) := rfl

/-- Its value at a challenge Λ is the batched sum `Σ_j R_j · Λ^j` — the shape `verifyAlgo` opens. -/
theorem oodBatchResidual_eval_eq (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (Λ : BabyBear) :
    (oodBatchResidual d t ζ qp).eval Λ
      = ∑ j : Fin (oodArithList d).length, oodRfam d t ζ qp j * Λ ^ (j : ℕ) :=
  batchResidual_eval (oodRfam d t ζ qp) Λ

/-! ## §2 — THE COLUMN-LAYOUT LAW, `∀ d`: coefficient `j` of the batched residual IS the `j`-th arith
constraint's residual. This is the recurring "column-layout plumbing" residual, DISCHARGED as a
theorem for any descriptor (the equation `transferV3` exhibited by hand, now general). -/

/-- **THE GENERAL COLUMN-LAYOUT LAW.** For ANY descriptor `d`, the `j`-th coefficient of the batched
residual polynomial is exactly the `j`-th arith constraint's OOD residual
`C_j(ζ) − Z(ζ)·q_j(ζ)`. The batched opening therefore CARRIES every per-constraint residual of `d`'s
actual layout — distinct constraints land in distinct powers of Λ (via `batchResidual_coeff`), which
is why a single nonzero constraint forces a nonzero batch and Schwartz–Zippel de-batching works. -/
theorem oodColumnLayout_law (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (j : Fin (oodArithList d).length) :
    (oodBatchResidual d t ζ qp).coeff (j : ℕ)
      = (constraintPoly d t ((oodArithList d).get j)).eval ζ
          - (vanishingPoly t).eval ζ * (qp ((oodArithList d).get j)).eval ζ :=
  batchResidual_coeff (oodRfam d t ζ qp) j

/-- The law in MEMBERSHIP form: every declared arithmetic constraint of ANY `d` occupies a column —
some coefficient of the batched residual is exactly ITS residual. (No constraint is dropped by the
batching; the layout is surjective onto `d`'s arith constraints.) -/
theorem oodColumnLayout_law_mem (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (c : VmConstraint2)
    (hc : c ∈ d.constraints) (harith : isArith c) :
    ∃ j : Fin (oodArithList d).length,
      (oodArithList d).get j = c ∧
      (oodBatchResidual d t ζ qp).coeff (j : ℕ)
        = (constraintPoly d t c).eval ζ - (vanishingPoly t).eval ζ * (qp c).eval ζ := by
  have hcf : c ∈ oodArithList d := (mem_oodArithList_iff d c).mpr ⟨hc, harith⟩
  obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
  refine ⟨⟨i, hlt⟩, ?_, ?_⟩
  · simpa [List.get_eq_getElem] using hget
  · rw [oodColumnLayout_law d t ζ qp ⟨i, hlt⟩]
    simp only [List.get_eq_getElem, hget]

/-- The batched residual's degree is `< #(oodArithList d)` — the small-Nat Schwartz–Zippel degree the
RLC exceptional set rides, for ANY descriptor. -/
theorem oodBatchResidual_natDegree_lt (d : EffectVmDescriptor2)
    (hn : 0 < (oodArithList d).length) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    (oodBatchResidual d t ζ qp).natDegree < (oodArithList d).length :=
  batchResidual_natDegree_lt hn (oodRfam d t ζ qp)

/-- The RLC bad-Λ set is small (`< #(oodArithList d)`) for ANY descriptor — a uniform batching
challenge misses it except with probability `≤ (n−1)/|F|`. -/
theorem oodBatchResidual_exceptionalSet_card_lt (d : EffectVmDescriptor2)
    (hn : 0 < (oodArithList d).length) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    (exceptionalSet (oodBatchResidual d t ζ qp)).card < (oodArithList d).length :=
  batchResidual_exceptionalSet_card_lt hn (oodRfam d t ζ qp)

/-! ## §3 — THE DISCHARGE WIRED THROUGH, `∀ d`: batched-zero at a non-exceptional Λ ⟹ every
per-constraint OOD identity ⟹ `MainAirAcceptF d t`. -/

/-- **De-batch through the general layout.** If the batched residual of ANY descriptor vanishes at a
NON-exceptional Λ, then EVERY declared arithmetic constraint of `d` satisfies its per-constraint OOD
identity `C_c(ζ) = Z(ζ)·q_c(ζ)`. The read-off from batch to constraint goes through the column-layout
law: `rlc_debatch` kills every coefficient, and each arith constraint of `d` IS a coefficient. -/
theorem oodLayout_debatch (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (Λ : BabyBear)
    (heval : (oodBatchResidual d t ζ qp).eval Λ = 0)
    (hLam : Λ ∉ exceptionalSet (oodBatchResidual d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ := by
  have hRzero : ∀ j, oodRfam d t ζ qp j = 0 :=
    rlc_debatch (oodRfam d t ζ qp) Λ heval hLam
  intro c hc harith
  have hcf : c ∈ oodArithList d := (mem_oodArithList_iff d c).mpr ⟨hc, harith⟩
  obtain ⟨i, hlt, hget⟩ := List.mem_iff_getElem.mp hcf
  have hj0 : oodRfam d t ζ qp ⟨i, hlt⟩ = 0 := hRzero ⟨i, hlt⟩
  simp only [oodRfam, List.get_eq_getElem, hget] at hj0
  exact sub_eq_zero.mp hj0

/-- **`MainAirAcceptF d t` from the general column layout**, for ANY descriptor: the batched residual
vanishing at a non-exceptional Λ (what acceptance + commitment binding deliver), plus the carried FS
non-exceptionality of ζ, forces the full per-row AIR accept. The column-layout input is now the
GENERAL modeler — no per-descriptor hand-model is consumed anywhere on this path. -/
theorem mainAirAcceptF_of_oodLayout (d : EffectVmDescriptor2) (t : VmTrace)
    (hcap : t.rows.length ≤ domainSize) (ζ Λ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear)
    (heval : (oodBatchResidual d t ζ qp).eval Λ = 0)
    (hLam : Λ ∉ exceptionalSet (oodBatchResidual d t ζ qp))
    (hnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet (constraintPoly d t c - vanishingPoly t * qp c)) :
    MainAirAcceptF d t :=
  ood_forces_mainAirAccept_field_of_residuals d t hcap ζ qp
    (oodLayout_debatch d t ζ qp Λ heval hLam) hnonexc

/-- **`hood` from the general column layout, at the deployed verifier** — `hood_of_reductions` with
its layout inputs restated over the GENERAL modeler: for ANY descriptor `d`, acceptance by the
specified `verifyAlgo` + the Poseidon2-CR commitment binding + the layout equation over
`oodBatchResidual d` + Λ non-exceptional force every per-constraint OOD identity of `d`. The template
consumes the general modeler with no per-descriptor plumbing. -/
theorem hood_of_oodColumnLayout
    (d : EffectVmDescriptor2)
    (sponge : List ℤ → ℤ)
    (perm : List ℤ → List ℤ) (RATE : Nat) (toNat : ℤ → Nat)
    (params : FriParams) (vk : RecursionVk ℤ) (core : FriCore ℤ) (A : FieldArith ℤ)
    (initState : List ℤ) (logN : Nat)
    (proof : BatchProofData ℤ) (pub : WrapPublics ℤ)
    (hacc : verifyAlgo perm RATE toNat params vk (fullChecks core A toNat params.powBits)
        initState logN proof pub = true)
    (t : VmTrace) (ζ Λ : BabyBear) (qp : VmConstraint2 → Polynomial BabyBear)
    (topen : TableOpening ℤ) (ood vCommitted root : ℤ) (idx : Nat) (siblings : List ℤ)
    (hoodPt : proof.oodPoint = [ood])
    (hmem : topen ∈ proof.tableOpenings)
    (hCommitted : merkleRecomputeZ sponge idx vCommitted siblings = root)
    (hOpened : merkleRecomputeZ sponge idx topen.constraintEval siblings = root)
    (hno : ¬ OpeningColl sponge idx topen.constraintEval vCommitted siblings)
    (hlayout : (oodBatchResidual d t ζ qp).eval Λ
        = ((vCommitted : ℤ) : BabyBear)
            - ((A.mul topen.vanishingAtZeta topen.quotientAtZeta : ℤ) : BabyBear))
    (hLam : Λ ∉ exceptionalSet (oodBatchResidual d t ζ qp)) :
    ∀ c ∈ d.constraints, isArith c →
      (constraintPoly d t c).eval ζ = (vanishingPoly t).eval ζ * (qp c).eval ζ :=
  hood_of_reductions d sponge perm RATE toNat params vk core A initState logN proof pub hacc
    t ζ Λ qp topen ood vCommitted root idx siblings hoodPt hmem hCommitted hOpened hno hlayout
    hLam

/-! ## §4 — transferV3 RE-DERIVED: the hand-modeled layout is the SPECIALIZATION
`oodColumnLayout_law transferV3` (subsumption, not a re-proof). -/

/-- `oodColumnLayout_law` restated over the template's `arithList`/`Rfam`, at a generic
descriptor (so the definitional unfolding never meets a concrete descriptor's body). -/
private theorem columnLayout_law_template (d : EffectVmDescriptor2) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (j : Fin (arithList d).length) :
    (batchResidual (Rfam d t ζ qp)).coeff (j : ℕ) = Rfam d t ζ qp j :=
  oodColumnLayout_law d t ζ qp j

/-- **The hand-model, subsumed.** The `transferV3` column-layout equation the template exhibits by
hand — coefficient `j` of `batchResidual (Rfam transferV3 …)` is `Rfam transferV3 … j` — is exactly
`oodColumnLayout_law` specialized at `d := transferV3`. (The statement is over the template's OWN
`arithList`/`Rfam`; the proof term is the general law.) -/
theorem transferV3_columnLayout_law (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) (j : Fin (arithList transferV3).length) :
    (batchResidual (Rfam transferV3 t ζ qp)).coeff (j : ℕ) = Rfam transferV3 t ζ qp j :=
  columnLayout_law_template transferV3 t ζ qp j

/-! ## §5 — NON-VACUITY: the modeler reads the REAL deployed descriptor. -/

-- transferV3 declares 295 constraints; its column layout selects EXACTLY the 155 arithmetic ones —
-- a proper subset, so `isArithB` genuinely discriminates (neither vacuously true nor false).
--
-- ⚑ 283/147 -> 295/155 at the 2026-07-31 ninth-lane flag day (`rotatedNumPreLimbs` 178 -> 184).
-- The +8 ARITHMETIC constraints are exactly the eight new `fields[slot]` lane-8 completion freezes
-- (`colEq(before, after)` on columns 176..183, one per slot); the other +4 are the two extra chip
-- absorption sites per block, which are lookups and so do NOT enter the arithmetic layout. MEASURED
-- by `#eval` against the deployed descriptor, not derived — and the delta being 8-and-only-8 is
-- itself the check that the nonet reached this member exactly once per slot.
--
-- ⚑ 295 -> 297 at the rc-FOLD flag day: the caveat region gained the TWO chip sites that absorb the
-- DFA route-commitment carrier into the published caveat commitment. Both are LOOKUPS, so the
-- arithmetic layout is UNCHANGED at 155 — which is itself the check that the fold added absorption
-- and not a new algebraic gate.
--
-- ⚑ 297 -> 299 at the 2026-08-01 KEY-NONET flag day (`rotatedNumPreLimbs` 184 -> 187). The three
-- carrier octets got their ninth lane, so each rotated block's absorption walk gained ONE 3-wide
-- body site (62 -> 63 sites per block, 136 -> 138 appendix sites). Both new constraints are chip
-- SITES, i.e. lookups, so the arithmetic layout is UNCHANGED at 155 — which is itself the check
-- that the widening added absorption and not a new algebraic gate. Contrast the 178 -> 184 row
-- above, where +8 of the delta WAS arithmetic (the eight fields lane-8 completion freezes): the
-- key nonet's lanes are welded by no `colEq` at all, which is the hole `zzz_e10_freeze_owner_
-- falsifier` exercises and which this flag day does NOT close.
#guard transferV3.constraints.length == 299
#guard (oodArithList transferV3).length == 155
#guard (oodArithList transferV3).length < transferV3.constraints.length

set_option maxRecDepth 4096 in
/-- Kernel-checked (not just `#guard`-evaluated): the deployed `transferV3` layout has EXACTLY 155
columns. (A 295-element list filter — a small computation, nothing `|F|`-sized.) -/
theorem oodArithList_transferV3_length : (oodArithList transferV3).length = 155 := by decide

/-- The deployed layout is nonempty — the RLC batch genuinely carries columns. -/
theorem oodArithList_transferV3_pos : 0 < (oodArithList transferV3).length := by
  rw [oodArithList_transferV3_length]; omega

/-- Coefficient `0` of the batched residual, at a generic descriptor with a nonempty layout. -/
private theorem oodBatchResidual_coeff_zero (d : EffectVmDescriptor2)
    (h : 0 < (oodArithList d).length) (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    (oodBatchResidual d t ζ qp).coeff 0 = oodRfam d t ζ qp ⟨0, h⟩ :=
  batchResidual_coeff (oodRfam d t ζ qp) ⟨0, h⟩

/-- **The law FIRES on the deployed descriptor**: coefficient `0` of `transferV3`'s batched residual
is the residual of the FIRST column of its actual 155-column layout — the general law applied at a
concrete real descriptor and a concrete index. -/
theorem oodColumnLayout_law_fires (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    (oodBatchResidual transferV3 t ζ qp).coeff 0
      = oodRfam transferV3 t ζ qp ⟨0, oodArithList_transferV3_pos⟩ :=
  oodBatchResidual_coeff_zero transferV3 oodArithList_transferV3_pos t ζ qp

/-- The RLC bad-Λ bound at the deployed descriptor, with the nonemptiness hypothesis DISCHARGED
outright (the template's `rlc_lambda_is_bounded_fs_form` had to carry it): fewer than 155 bad
challenges, so ε_RLC ≤ 154/2013265921. -/
theorem transferV3_rlc_bound (t : VmTrace) (ζ : BabyBear)
    (qp : VmConstraint2 → Polynomial BabyBear) :
    (exceptionalSet (oodBatchResidual transferV3 t ζ qp)).card < 155 := by
  have h := oodBatchResidual_exceptionalSet_card_lt transferV3
    oodArithList_transferV3_pos t ζ qp
  rwa [oodArithList_transferV3_length] at h

/-! ## Kernel-clean keystones (0 sorries; axiom floor is Lean's own). -/

#assert_axioms oodArithList_eq_arithList
#assert_axioms mem_oodArithList_iff
#assert_axioms oodRfam_eq_Rfam
#assert_axioms oodBatchResidual_eq_template
#assert_axioms oodBatchResidual_eval_eq
#assert_axioms oodColumnLayout_law
#assert_axioms oodColumnLayout_law_mem
#assert_axioms oodBatchResidual_natDegree_lt
#assert_axioms oodBatchResidual_exceptionalSet_card_lt
#assert_axioms oodLayout_debatch
#assert_axioms mainAirAcceptF_of_oodLayout
#assert_axioms hood_of_oodColumnLayout
#assert_axioms transferV3_columnLayout_law
#assert_axioms oodArithList_transferV3_length
#assert_axioms oodArithList_transferV3_pos
#assert_axioms oodColumnLayout_law_fires
#assert_axioms transferV3_rlc_bound

end Dregg2.Circuit.OodColumnLayout

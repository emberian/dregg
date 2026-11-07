/-
# `Dregg2.Circuit.ExtOpeningRecordWidth` — the OPENED-VALUE RECORDS at the deployed quartic width.

## The gap this file is about

Recent work retyped the deployed FRI CHALLENGES to the quartic extension where they belong (the
constraint-RLC `α`, the OOD `ζ`, every commit-phase fold `β`: `ExtFieldChallenge.lean:8-15`). It did
NOT widen the serialized RECORDS. `BatchTablesSingleAir.SingleAirOpening.alpha` and
`FriVerifier.TableOpening.constraintEval` / `vanishingAtZeta` / `quotientAtZeta` / `logupCumSum` are
still ONE felt each. This file supplies the widened records ADDITIVELY, proves what actually holds
between them and the narrow ones, and delivers the downstream payoff.

## ⚑ WHAT THE DEPLOYED SYSTEM ACTUALLY HOLDS (read in the sources, not inferred)

`Challenge = BinomialExtensionField<BabyBear, 4>` (`circuit-prove/src/dregg_outer_config.rs:153`),
and a `Challenge` reaches the transcript as FOUR base felts — `obs_ext` observes
`e.as_basis_coefficients_slice()` (`circuit-prove/src/apex_shrink_gnark_export.rs:743`).

  * `alpha` is **NOT SERIALIZED AT ALL** — it is squeezed:
    `let _alpha_constraints = rec.sample_ext()` (`apex_shrink_gnark_export.rs:1008`), and in the FRI
    layer `let alpha: Challenge = challenger.sample_algebra_element()`
    (`vendor/plonky3-fri-82cfad73/src/verifier.rs:143`). So is `zeta`
    (`apex_shrink_gnark_export.rs:1011`, `let zeta = rec.sample_ext()`).
  * `constraintEval` / `quotientAtZeta` / `vanishingAtZeta` are **NOT ON THE WIRE AS SUCH EITHER** —
    they are DERIVED `Challenge` values: the folded constraint from the serialized `trace_local` /
    `trace_next` openings (all `Challenge`: `ps_at_z` at `verifier.rs:623-640`) and `alpha`; the
    quotient by recomposition from the serialized `quotient_chunks` (`Challenge`); the vanishing and
    its inverse computed from `zeta`.
  * `logupCumSum` IS carried by the proof and IS a `Challenge`:
    `rec.obs_ext(&data.cumulative_sum)` (`apex_shrink_gnark_export.rs:1005`).

So every field-typed slot of both records is a four-lane `Challenge` in deployment, and every one of
them is one BabyBear felt in Lean.

## ⚑ PER-FIELD VERDICT — LOAD-BEARING or INERT, with evidence

**`SingleAirOpening.alpha` — INERT at the apex, and honestly retired here.** The widened single-AIR
record ALREADY EXISTS (`ExtFieldChallenge.ExtSingleAirOpening`) and is ALREADY CONJOINED: the
apex-facing `verifyAlgoUnifiedFaithfulExt` requires
`batchTablesCheckExt extA W params.extDeg ⟨d.constraintAlpha⟩ ⟨d.ζ⟩ view.singleAirOpenings`, which
consumes the COMPLETE four-lane transcript `α` and `ζ`. §9's `faithfulExt_forces_fullWidth_alpha`
proves acceptance forces exactly that. The narrow scalar conjunct
(`singleAirChallengesBound`: `o.alpha = d.constraintAlpha.headD default`) is a redundant
strengthening target retained so `DeployedRefines` transports — it does not carry a soundness claim
the wide conjunct does not already carry. It is nevertheless an unfaithful DESCRIPTION, and §6 says
how unfaithful: `lane0_alpha_does_not_determine_the_fold` exhibits two `Challenge`s agreeing on the
pinned lane whose deployed Horner RLC folds DIFFER.

**`TableOpening.constraintEval` / `vanishingAtZeta` / `quotientAtZeta` (+ `logupCumSum`) —
LOAD-BEARING, and there is NO widened counterpart anywhere in the tree.** `batchTablesCheckExt`
covers `ExtSingleAirOpening` only; nothing carries a widened `TableOpening`. Meanwhile the narrow
identity `topen.constraintEval = A.mul topen.vanishingAtZeta topen.quotientAtZeta` is a HYPOTHESIS of
every extraction bundle that lands `MainAirAcceptF` — `StarkSoundReduce:114/159/193`,
`OodColumnLayout:235`, `ApexOodLaneRepair:257/306/425/691`, `FriDecodedTraceWitness:481`,
`FriLdtExtractDeployed`, `DeployedRefinesProof:105`, `OodSingletonRepair`, `FriFsDecodedOodRepair`.
That is the site this file widens.

## ⚑ THE TRUE RELATION FOUND (investigated, not assumed) — it is the expected shape, sharpened

  * **Base records LIFT, completely** (`wideOfTable_ok_of_tableOk`,
    `wideOfSingleAir_ok_of_singleAirOk`, `wideBusSum_map`, `wideFolded_wideOfSingleAir`,
    `wideRecomposed_wideOfSingleAir`): every tooth — the degree pin, the vanishing recompute, the
    genuine-inverse pin, the Horner RLC, the chunk recomposition, the bus sum — transports along
    `algebraMap BabyBear E`. The widened hypothesis is strictly WEAKER.
  * **The wide record does NOT descend** (`wide_table_beyond_base`): at a `Challenge`-valued OOD
    point there is a widened opening that PASSES, whose recomputed vanishing AND opened quotient are
    both outside `Set.range (algebraMap BabyBear E)` — the lift of no narrow record.
  * **⚑ AND THE NARROW RECORD CANNOT EXPRESS THE DEPLOYED VALUE — sharper than a cardinality
    remark.** `lifted_narrow_forces_base_ood_power`: a LIFTED NARROW record satisfies the widened
    check ONLY at an OOD point whose `2^degreeBits` power lies in the base image. The deployed `ζ` is
    a `Challenge`. So a narrow `TableOpening` that PASSES `tableOk` is passing at a base OOD point —
    a different run from the deployed one, not a coarse view of it. The vanishing recompute is what
    forces this: `Z_H(ζ)` is not a free value, it IS `ζ^{2^db} − 1`.
    This compounds, and explains, the tree's own measurement that `tableOpenings = []` on the only
    exhibited accepting pole (`PremiseInhabitabilitySweep`
    `at_the_only_exhibited_pole_the_repair_is_half_realized`): widening is a PREREQUISITE for that
    conjunct ever being witnessed on a deployed run.
  * **And the lane-0 squeeze cannot rescue the narrow equation**
    (`lane0_square_not_multiplicative`, `lane_product_not_multiplicative`): neither the vanishing
    recompute nor the quotient identity is lane-wise, at any lane of the deployed quartic basis.

## ⚑ THE PAYOFF — weaker-but-achievable hypothesis, IDENTICAL conclusion

`mainAirAcceptF_of_wideTableOpening` and `mainAirAcceptF_of_wideSingleAirOpening`: the widened
record's quotient identity, at an extension `ζ` and an extension batching `α`, still forces the same
BASE-field per-row AIR acceptance `MainAirAcceptF d t`, through the landed
`kprime_compose_of_tableIdentityExt`. `tableOfWideSingleAir_ok` is the bridge: the deployed
acceptance test `folded · inv_vanishing = quotient` plus the genuine-inverse pin FORCES the widened
table identity, at full width.

## ⚑ PRICING — say which, precisely

The lane-0 squeeze has a three-dimensional kernel (`lane0_ker_finrank`); `p^3 > 2^92`
(`squeeze_factor_gt_two_pow_92`, `bb4_card_split`). What that number IS:

  * For `alpha`: **an unfaithful description, NOT a soundness loss.** The deployed `α` is bound at
    full width by the conjunct §9 exhibits; the narrow felt does not weaken any check the deployed
    verifier performs. What it loses is the ability to DENOTE the deployed fold at all.
  * For `TableOpening`: **neither a soundness loss nor a benign relabel — an UNWITNESSABLE
    hypothesis.** Nothing at the apex derives from those three felts (the legacy conjunct passes on
    the default `tableOpenings := []`), so no deployed check is weakened by their narrowness; but
    every soundness chain that CONSUMES them consumes an equation a deployed run does not satisfy.
    `p^3` measures the distance between the described object and the deployed one — it is not an
    attack budget, and nobody should quote it as one.

## WHAT REMAINS NARROW, and why

  * The landed `TableOpening` / `SingleAirOpening` structures and `tableOk` / `singleAirOk` /
    `batchTablesCheck` / `batchTablesCheckUnified` are UNTOUCHED — this file is additive, by the
    coordination rule. Migrating `FriVerifier.BatchProofData.tableOpenings` to the widened record is
    a shared-struct change and is NOT taken here.
  * The extraction bundles listed above still hypothesize the narrow identity, over `ℤ` at `opaque`
    deployed arguments. Retargeting them onto `WideTableOpening` is the follow-on, and it is where
    the `ℤ`-vs-field typing gap has to be crossed as well.
  * `verifyAlgoUnifiedFaithfulExt` takes the narrow `proof` and the wide `view` as two independent
    arguments and asserts NO relation between `proof.singleAirOpenings` and
    `view.singleAirOpenings`. At the deployed apex both are decodes of the same bytes
    (`cfgView` / `cfgExtView`, `CircuitSoundness.lean`), so this is not an exploitable hole — but the
    Lean model does not SAY they agree, and that consistency conjunct is not supplied here either.
  * The FRI soundness floor is unchanged. Widening a record moves no FRI/STARK assumption.

Sorry-free; no `axiom`; no carrier; additive new module; every keystone `#assert_axioms`-checked.
-/
import Dregg2.Circuit.ExtChallengeOodSites
import Dregg2.Tactics

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Circuit.ExtOpeningRecordWidth

open Polynomial
open Dregg2.Circuit.BabyBearFriField (BabyBear babyBearP)
open Dregg2.Circuit.FriVerifier (FieldArith TableOpening tableOk busSum)
open Dregg2.Circuit.BatchTablesSingleAir
  (SingleAirOpening singleAirOk foldedConstraints recomposedQuotient busSumSA)
open Dregg2.Circuit.DescriptorIR2 (VmTrace EffectVmDescriptor2 VmConstraint2)
open Dregg2.Circuit.AirChecksSatisfied (MainAirAcceptF isArith dArith tHonest)
open Dregg2.Circuit.TraceColumnInterp (constraintPoly domainSize)
open Dregg2.Circuit.FieldIntegerLift (vanishingPoly)
open Dregg2.Circuit.OodQuotientConsistency (exceptionalSet rlcResidualPoly)
open Dregg2.Circuit.OodExtChallengeLayout
  (liftPoly coordLin coordFunctional_not_multiplicative constraintPoly_dArith_tHonest_zero)
open Dregg2.Circuit.OodInterpFieldExt
  (BB4 bb4Basis bb4_finrank bb4_card exists_not_mem_range_algebraMap exists_nonbase_bb4)
open Dregg2.Circuit.ExtChallengeOodSites
  (mul_algebraMap_notMem_range constraintResidualAtZetaExt kprime_compose_of_tableIdentityExt
   constraintResidualAtZetaExt_dArith_tHonest)

/-! ## §0 — the narrow records' checks at REAL field arithmetic.

`FriVerifier.tableOk` / `BatchTablesSingleAir.singleAirOk` are stated over an opaque
`FieldArith F` op bundle.  To relate them to anything algebraic the bundle has to be the genuine
field operations; `fieldArithOf` is that instantiation and nothing below reasons about any other
bundle. -/

/-- The genuine-field `FieldArith` bundle. -/
def fieldArithOf (K : Type) [Field K] : FieldArith K where
  add := (· + ·)
  mul := (· * ·)
  pow := fun b n => b ^ n
  zero := 0
  one := 1

@[simp] theorem fieldArithOf_add {K : Type} [Field K] (a b : K) :
    (fieldArithOf K).add a b = a + b := rfl

@[simp] theorem fieldArithOf_mul {K : Type} [Field K] (a b : K) :
    (fieldArithOf K).mul a b = a * b := rfl

@[simp] theorem fieldArithOf_pow {K : Type} [Field K] (a : K) (n : Nat) :
    (fieldArithOf K).pow a n = a ^ n := rfl

@[simp] theorem fieldArithOf_zero {K : Type} [Field K] : (fieldArithOf K).zero = (0 : K) := rfl

@[simp] theorem fieldArithOf_one {K : Type} [Field K] : (fieldArithOf K).one = (1 : K) := rfl

/-! ## §1 — THE WIDENED RECORDS.

The deployed opened values are `Challenge` — elements of the quartic extension, FOUR ordered
BabyBear lanes (`ExtFieldChallenge.lean:8-15`; `vendor/plonky3-fri-82cfad73/src/verifier.rs:623-640`).
The widened records below carry each opened value as ONE element of an abstract extension `E`;
§2 pins that this is exactly four base lanes at the deployed `BB4`, losslessly, and that the narrow
record carries one.  Typing the value as an `E` rather than as a lane list is what lets the payoff
(§5) reuse the landed extension-typed consumer verbatim; by `deployed_quartic_ext_canonical` the
deployed `BabyBear[X]/(X^4 − 11)` IS `BB4` up to a BabyBear-algebra isomorphism, so nothing depends
on the binomial presentation. -/

/-- **`FriVerifier.TableOpening` at the deployed challenge width.** Same fields; the three opened
values and the bus contribution are extension elements instead of single felts. -/
structure WideTableOpening (E : Type*) where
  degreeBits : Nat
  expectedDegreeBits : Nat
  constraintEval : E
  quotientAtZeta : E
  vanishingAtZeta : E
  logupCumSum : E

/-- **`FriVerifier.tableOk` at the deployed challenge width**, as a `Prop` over genuine field
arithmetic: the VK degree pin, the vanishing recompute `Z_H(ζ) + 1 = ζ^{2^db}`, and the quotient
identity `C(ζ) = Z_H(ζ)·q(ζ)` — every value, and the OOD point, an extension element. -/
def WideTableOpening.Ok {E : Type*} [Field E] (ζ : E) (t : WideTableOpening E) : Prop :=
  t.degreeBits = t.expectedDegreeBits
    ∧ t.vanishingAtZeta + 1 = ζ ^ (2 ^ t.degreeBits)
    ∧ t.constraintEval = t.vanishingAtZeta * t.quotientAtZeta

/-- `FriVerifier.busSum` at the deployed width. -/
def wideBusSum {E : Type*} [Field E] (ts : List (WideTableOpening E)) : E :=
  (ts.map (fun t => t.logupCumSum)).foldr (· + ·) 0

/-- `FriVerifier.batchTablesCheck` at the deployed width. -/
def WideBatchOk {E : Type*} [Field E] (ζ : E) (ts : List (WideTableOpening E)) : Prop :=
  (∀ t ∈ ts, t.Ok ζ) ∧ wideBusSum ts = 0

/-- **`BatchTablesSingleAir.SingleAirOpening` at the deployed challenge width.** -/
structure WideSingleAirOpening (E : Type*) where
  zeta : E
  degreeBits : Nat
  expectedDegreeBits : Nat
  alpha : E
  constraintEvals : List E
  zps : List E
  quotientChunks : List E
  vanishing : E
  invVanishing : E
  logupCumSum : E

/-- The deployed Horner RLC fold `Σᵢ cᵢ·α^{n−1−i}` (`uni-stark/src/folder.rs:215-217`) at the
deployed challenge width — `α` an extension element, so the fold is extension arithmetic. -/
def wideFolded {E : Type*} [Field E] (o : WideSingleAirOpening E) : E :=
  o.constraintEvals.foldl (fun acc c => acc * o.alpha + c) 0

/-- `recompose_quotient_from_chunks` at the deployed challenge width. -/
def wideRecomposed {E : Type*} [Field E] (o : WideSingleAirOpening E) : E :=
  (o.zps.zip o.quotientChunks).foldr (fun p acc => p.1 * p.2 + acc) 0

/-- **`BatchTablesSingleAir.singleAirOk` at the deployed challenge width** — the same four teeth. -/
def WideSingleAirOpening.Ok {E : Type*} [Field E] (o : WideSingleAirOpening E) : Prop :=
  o.degreeBits = o.expectedDegreeBits
    ∧ o.vanishing + 1 = o.zeta ^ (2 ^ o.degreeBits)
    ∧ o.vanishing * o.invVanishing = 1
    ∧ wideFolded o * o.invVanishing = wideRecomposed o

/-! ## §2 — WIDTH, exactly: the wide record holds FOUR base felts per opened value, the narrow one
holds ONE, and the map from wide to narrow is the lane-0 squeeze. -/

section Width

/-- The deployed four-lane view of a `Challenge`: its ordered coordinates on the deployed quartic
basis.  This is the `[F; 4]` array `from_basis_coefficients_fn` fills. -/
noncomputable def lanes (x : BB4) : Fin 4 → BabyBear := fun i => bb4Basis.repr x i

/-- **The wide value is exactly four base felts, LOSSLESSLY** — the lane view is injective, so the
widened record carries neither more nor less than the deployed `[Val; 4]`. -/
theorem lanes_injective : Function.Injective lanes := by
  intro x y hxy
  have : bb4Basis.repr x = bb4Basis.repr y := by
    ext i
    exact congrFun hxy i
  exact bb4Basis.repr.injective this

/-- The lane-0 squeeze — the operation `FriChallengerUnified.projBeta` /
`singleAirChallengesBound`'s `headD default` performs, in algebraic form. -/
noncomputable def lane0 : BB4 →ₗ[BabyBear] BabyBear := coordLin bb4Basis 0

@[simp] theorem lane0_apply (x : BB4) : lane0 x = bb4Basis.repr x 0 := rfl

end Width

/-! ## §3 — THE TRUE RELATION, half one: **the narrow record LIFTS, completely.**

Everything transports along `algebraMap BabyBear E`: the degree pin is a `Nat` equation, and the
vanishing recompute and the quotient identity are ring equations, so a narrow record that PASSES
`tableOk` / `singleAirOk` becomes a wide record that satisfies the widened check at the embedded
OOD point.  The widened hypothesis is therefore strictly WEAKER — retyping loses nothing. -/

section Lift

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-- Embed a narrow `TableOpening` into the widened record. -/
noncomputable def wideOfTable (E : Type*) [Field E] [Algebra BabyBear E]
    (t : TableOpening BabyBear) : WideTableOpening E where
  degreeBits := t.degreeBits
  expectedDegreeBits := t.expectedDegreeBits
  constraintEval := algebraMap BabyBear E t.constraintEval
  quotientAtZeta := algebraMap BabyBear E t.quotientAtZeta
  vanishingAtZeta := algebraMap BabyBear E t.vanishingAtZeta
  logupCumSum := algebraMap BabyBear E t.logupCumSum

/-- **THE LIFT at the table record**: a narrow opening that passes the deployed-shell `tableOk` at
a base OOD point satisfies the WIDENED check at the embedded OOD point. -/
theorem wideOfTable_ok_of_tableOk (E : Type*) [Field E] [Algebra BabyBear E]
    (ζ₀ : BabyBear) (t : TableOpening BabyBear)
    (h : tableOk (fieldArithOf BabyBear) ζ₀ t = true) :
    (wideOfTable E t).Ok (algebraMap BabyBear E ζ₀) := by
  unfold tableOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, fieldArithOf_add, fieldArithOf_mul,
    fieldArithOf_pow, fieldArithOf_one] at h
  obtain ⟨⟨hdeg, hvan⟩, hquot⟩ := h
  refine ⟨hdeg, ?_, ?_⟩
  · show algebraMap BabyBear E t.vanishingAtZeta + 1
      = algebraMap BabyBear E ζ₀ ^ (2 ^ t.degreeBits)
    rw [← map_one (algebraMap BabyBear E), ← map_add, ← map_pow, of_decide_eq_true hvan]
  · show algebraMap BabyBear E t.constraintEval
      = algebraMap BabyBear E t.vanishingAtZeta * algebraMap BabyBear E t.quotientAtZeta
    rw [← map_mul, of_decide_eq_true hquot]

/-- The bus sum transports too, so the whole batch check lifts. -/
theorem wideBusSum_map (E : Type*) [Field E] [Algebra BabyBear E]
    (ts : List (TableOpening BabyBear)) :
    wideBusSum (ts.map (wideOfTable E)) = algebraMap BabyBear E (busSum (fieldArithOf BabyBear) ts) := by
  unfold wideBusSum busSum
  induction ts with
  | nil => simp
  | cons a t ih =>
      simp only [List.map_cons, List.foldr_cons, fieldArithOf_add]
      rw [ih, show (wideOfTable E a).logupCumSum = algebraMap BabyBear E a.logupCumSum from rfl,
        ← map_add]

/-- Embed a narrow `SingleAirOpening` into the widened record. -/
noncomputable def wideOfSingleAir (E : Type*) [Field E] [Algebra BabyBear E]
    (o : SingleAirOpening BabyBear) : WideSingleAirOpening E where
  zeta := algebraMap BabyBear E o.zeta
  degreeBits := o.degreeBits
  expectedDegreeBits := o.expectedDegreeBits
  alpha := algebraMap BabyBear E o.alpha
  constraintEvals := o.constraintEvals.map (algebraMap BabyBear E)
  zps := o.zps.map (algebraMap BabyBear E)
  quotientChunks := o.quotientChunks.map (algebraMap BabyBear E)
  vanishing := algebraMap BabyBear E o.vanishing
  invVanishing := algebraMap BabyBear E o.invVanishing
  logupCumSum := algebraMap BabyBear E o.logupCumSum

/-- The Horner RLC fold commutes with the embedding, at every accumulator. -/
theorem foldl_horner_map (E : Type*) [Field E] [Algebra BabyBear E] (a : BabyBear) :
    ∀ (l : List BabyBear) (acc : BabyBear),
      (l.map (algebraMap BabyBear E)).foldl
          (fun x c => x * algebraMap BabyBear E a + c) (algebraMap BabyBear E acc)
        = algebraMap BabyBear E (l.foldl (fun x c => x * a + c) acc) := by
  intro l
  induction l with
  | nil => intro acc; simp
  | cons c t ih =>
      intro acc
      simp only [List.map_cons, List.foldl_cons]
      rw [show algebraMap BabyBear E acc * algebraMap BabyBear E a + algebraMap BabyBear E c
            = algebraMap BabyBear E (acc * a + c) by rw [map_add, map_mul]]
      exact ih _

/-- **The deployed Horner RLC is the embedding of the narrow one**, at an embedded `α`. -/
theorem wideFolded_wideOfSingleAir (E : Type*) [Field E] [Algebra BabyBear E]
    (o : SingleAirOpening BabyBear) :
    wideFolded (wideOfSingleAir E o)
      = algebraMap BabyBear E (foldedConstraints (fieldArithOf BabyBear) o) := by
  unfold wideFolded foldedConstraints wideOfSingleAir
  simp only [fieldArithOf_add, fieldArithOf_mul, fieldArithOf_zero]
  have := foldl_horner_map E o.alpha o.constraintEvals 0
  simpa using this

/-- The chunk recomposition commutes with the embedding. -/
theorem foldr_recompose_map (E : Type*) [Field E] [Algebra BabyBear E] :
    ∀ (l : List (BabyBear × BabyBear)),
      (l.map (Prod.map (algebraMap BabyBear E) (algebraMap BabyBear E))).foldr
          (fun p acc => p.1 * p.2 + acc) 0
        = algebraMap BabyBear E (l.foldr (fun p acc => p.1 * p.2 + acc) 0) := by
  intro l
  induction l with
  | nil => simp
  | cons p t ih =>
      simp only [List.map_cons, List.foldr_cons, Prod.map_fst, Prod.map_snd]
      rw [ih, ← map_mul, ← map_add]

/-- **The deployed quotient recomposition is the embedding of the narrow one.** -/
theorem wideRecomposed_wideOfSingleAir (E : Type*) [Field E] [Algebra BabyBear E]
    (o : SingleAirOpening BabyBear) :
    wideRecomposed (wideOfSingleAir E o)
      = algebraMap BabyBear E (recomposedQuotient (fieldArithOf BabyBear) o) := by
  unfold wideRecomposed recomposedQuotient wideOfSingleAir
  simp only [fieldArithOf_add, fieldArithOf_mul, fieldArithOf_zero]
  rw [List.zip_map]
  exact foldr_recompose_map E _

/-- **THE LIFT at the single-AIR record**: a narrow opening that passes the deployed faithful
`singleAirOk` satisfies the WIDENED check.  All four teeth transport. -/
theorem wideOfSingleAir_ok_of_singleAirOk (E : Type*) [Field E] [Algebra BabyBear E]
    (o : SingleAirOpening BabyBear) (h : singleAirOk (fieldArithOf BabyBear) o = true) :
    (wideOfSingleAir E o).Ok := by
  unfold singleAirOk at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, fieldArithOf_add, fieldArithOf_mul,
    fieldArithOf_pow, fieldArithOf_one] at h
  obtain ⟨⟨⟨hdeg, hvan⟩, hinv⟩, hid⟩ := h
  refine ⟨hdeg, ?_, ?_, ?_⟩
  · show algebraMap BabyBear E o.vanishing + 1
      = algebraMap BabyBear E o.zeta ^ (2 ^ o.degreeBits)
    rw [← map_one (algebraMap BabyBear E), ← map_add, ← map_pow, of_decide_eq_true hvan]
  · show algebraMap BabyBear E o.vanishing * algebraMap BabyBear E o.invVanishing = 1
    rw [← map_mul, of_decide_eq_true hinv, map_one]
  · rw [wideFolded_wideOfSingleAir, wideRecomposed_wideOfSingleAir]
    show algebraMap BabyBear E _ * algebraMap BabyBear E o.invVanishing = _
    rw [← map_mul, of_decide_eq_true hid]

end Lift

/-! ## §4 — THE TRUE RELATION, half two: **the wide record does NOT descend, and the narrow record
cannot EXPRESS the deployed value.**

The vanishing recompute is what makes this sharp and not merely a cardinality remark.  `Z_H(ζ)` is
FORCED to be `ζ^{2^db} − 1`; the OOD point is by construction a `Challenge`, so as soon as
`ζ^{2^db}` is outside the base image, `Z_H(ζ)` is too — and every narrow record's lift has all four
values inside it.  So at a genuinely extension-valued OOD point NO narrow record satisfies the
widened check at all.  It is not that the narrow record is a coarse description of the deployed
one; it describes a value the deployed verifier never holds. -/

section NoDescent

variable {E : Type*} [Field E] [Algebra BabyBear E]

/-- Every value a lifted narrow record can hold is inside the base image. -/
theorem wideOfTable_values_mem_range (t : TableOpening BabyBear) :
    (wideOfTable E t).constraintEval ∈ Set.range (algebraMap BabyBear E)
      ∧ (wideOfTable E t).vanishingAtZeta ∈ Set.range (algebraMap BabyBear E)
      ∧ (wideOfTable E t).quotientAtZeta ∈ Set.range (algebraMap BabyBear E) :=
  ⟨⟨_, rfl⟩, ⟨_, rfl⟩, ⟨_, rfl⟩⟩

/-- **⚑ NO NARROW RECORD AT A GENUINELY EXTENSION-VALUED OOD POINT.** If `ζ^{2^db}` is outside the
base image — which is the deployed regime, `ζ` being a `Challenge` — then no lifted narrow
`TableOpening` satisfies the widened check, because the vanishing recompute forces
`Z_H(ζ) = ζ^{2^db} − 1` and a lifted record's `vanishingAtZeta` is in the base image.  This is the
precise sense in which the single-felt record cannot EXPRESS the deployed value. -/
theorem no_narrow_table_at_nonbase_ood (ζ : E) (t : TableOpening BabyBear)
    (hζ : ζ ^ (2 ^ t.degreeBits) ∉ Set.range (algebraMap BabyBear E)) :
    ¬ (wideOfTable E t).Ok ζ := by
  rintro ⟨-, hvan, -⟩
  refine hζ ⟨t.vanishingAtZeta + 1, ?_⟩
  rw [map_add, map_one]
  exact hvan

/-- **⚑ THE POSITIVE FORM — a narrow record only ever describes a BASE OOD point.** If a lifted
narrow `TableOpening` satisfies the widened check at `ζ`, then `ζ^{2^degreeBits}` is in the base
image.  Contrapositive of `no_narrow_table_at_nonbase_ood`, stated the way the consumer needs it: the
deployed `ζ` is a `Challenge`, so a narrow record that PASSES `tableOk` is passing about a different
run, not about a lane of the deployed one.  The vanishing recompute is what forces this — `Z_H(ζ)` is
not a free value, it IS `ζ^{2^db} − 1`. -/
theorem lifted_narrow_forces_base_ood_power (ζ : E) (t : TableOpening BabyBear)
    (h : (wideOfTable E t).Ok ζ) :
    ζ ^ (2 ^ t.degreeBits) ∈ Set.range (algebraMap BabyBear E) := by
  by_contra hcon
  exact no_narrow_table_at_nonbase_ood ζ t hcon h

/-- The same for a narrow record that genuinely PASSES the deployed shell check at a base OOD point:
its widened reading is pinned to base OOD points, so it never denotes a deployed run. -/
theorem tableOk_pass_does_not_describe_nonbase_ood (ζ₀ : BabyBear) (ζ : E)
    (t : TableOpening BabyBear) (_hpass : tableOk (fieldArithOf BabyBear) ζ₀ t = true)
    (hζ : ζ ^ (2 ^ t.degreeBits) ∉ Set.range (algebraMap BabyBear E)) :
    ¬ (wideOfTable E t).Ok ζ :=
  no_narrow_table_at_nonbase_ood ζ t hζ

/-- The same at the single-AIR record, positively: a lifted narrow opening's `zeta` AND `alpha` are
always in the base image, so a lifted record can never carry the deployed `Challenge`-valued OOD
point or the deployed `Challenge`-valued constraint-RLC challenge. -/
theorem wideOfSingleAir_challenges_mem_range (o : SingleAirOpening BabyBear) :
    (wideOfSingleAir E o).zeta ∈ Set.range (algebraMap BabyBear E)
      ∧ (wideOfSingleAir E o).alpha ∈ Set.range (algebraMap BabyBear E) :=
  ⟨⟨o.zeta, rfl⟩, ⟨o.alpha, rfl⟩⟩

/-- **⚑ THE WIDE RECORD ATTAINS VALUES NO NARROW RECORD CAN.** At a `Challenge`-valued OOD point
`ζ` outside the base image there is a widened table opening that PASSES the widened check, whose
recomputed vanishing AND whose opened quotient are both outside the base image — hence it is the
lift of no narrow record whatsoever. -/
theorem wide_table_beyond_base {ζ : E} (hζ : ζ ∉ Set.range (algebraMap BabyBear E)) :
    ∃ w : WideTableOpening E,
      w.Ok ζ
      ∧ w.vanishingAtZeta ∉ Set.range (algebraMap BabyBear E)
      ∧ w.quotientAtZeta ∉ Set.range (algebraMap BabyBear E)
      ∧ ∀ t : TableOpening BabyBear, wideOfTable E t ≠ w := by
  refine ⟨{ degreeBits := 0, expectedDegreeBits := 0, constraintEval := (ζ - 1) * ζ,
            quotientAtZeta := ζ, vanishingAtZeta := ζ - 1, logupCumSum := 0 },
          ⟨rfl, by show ζ - 1 + 1 = ζ ^ (2 ^ 0); ring, rfl⟩, ?_, hζ, ?_⟩
  · rintro ⟨s, hs⟩
    exact hζ ⟨s + 1, by rw [map_add, map_one, hs]; ring⟩
  · intro t hteq
    refine hζ ⟨t.quotientAtZeta, ?_⟩
    exact congrArg WideTableOpening.quotientAtZeta hteq

/-! ### §4.1 — and the lane-0 squeeze cannot rescue the narrow equation.

`batchTablesCheck` reads `proof.oodPoint`'s HEAD lane and `singleAirChallengesBound` pins
`o.alpha` to `d.constraintAlpha.headD default`.  Both of the narrow record's equations are
MULTIPLICATIVE in the squeezed value, and no basis-coordinate functional of a nontrivial extension
is multiplicative — so the base-typed equation is not the lane-0 image of the deployed one. -/

/-- **The vanishing recompute is not lane-wise.**  There is a `Challenge` whose lane-0 square
differs from the square of its lane 0, so `tableOk`'s `Z_H + 1 = ζ₀^{2^db}` at `degreeBits = 1` is
NOT the lane-0 projection of the deployed `Z_H(ζ) + 1 = ζ^{2}`. Derived from
`coordFunctional_not_multiplicative` by polarization (BabyBear has odd characteristic). -/
theorem lane0_square_not_multiplicative :
    ∃ ζ : BB4, bb4Basis.repr (ζ ^ 2) 0 ≠ (bb4Basis.repr ζ 0) ^ 2 := by
  by_contra hcon0
  have hcon : ∀ ζ : BB4, bb4Basis.repr (ζ ^ 2) 0 = (bb4Basis.repr ζ 0) ^ 2 := by
    intro ζ
    by_contra h
    exact hcon0 ⟨ζ, h⟩
  obtain ⟨x, y, hxy⟩ :=
    coordFunctional_not_multiplicative bb4Basis 0 (by rw [bb4_finrank]; norm_num)
  apply hxy
  have hr : bb4Basis.repr (x + y) 0 = bb4Basis.repr x 0 + bb4Basis.repr y 0 := by simp
  have key : bb4Basis.repr ((x + y) ^ 2) 0
      = bb4Basis.repr (x ^ 2) 0
        + (bb4Basis.repr (x * y) 0 + bb4Basis.repr (x * y) 0)
        + bb4Basis.repr (y ^ 2) 0 := by
    rw [show (x + y) ^ 2 = x ^ 2 + (x * y + x * y) + y ^ 2 by ring]
    simp
  have e1 : bb4Basis.repr (x ^ 2) 0
        + (bb4Basis.repr (x * y) 0 + bb4Basis.repr (x * y) 0)
        + bb4Basis.repr (y ^ 2) 0
      = (bb4Basis.repr x 0 + bb4Basis.repr y 0) ^ 2 := by
    rw [← key, hcon (x + y), hr]
  rw [hcon x, hcon y] at e1
  have h2 : (2 : BabyBear) * bb4Basis.repr (x * y) 0
      = 2 * (bb4Basis.repr x 0 * bb4Basis.repr y 0) := by linear_combination e1
  have hne2 : (2 : BabyBear) ≠ 0 := by decide
  exact mul_left_cancel₀ hne2 h2

/-- **The quotient identity is not lane-wise either** — the same obstruction at the deployed
quartic basis, for EVERY lane. -/
theorem lane_product_not_multiplicative (i : Fin 4) :
    ∃ x y : BB4, bb4Basis.repr (x * y) i ≠ bb4Basis.repr x i * bb4Basis.repr y i :=
  coordFunctional_not_multiplicative bb4Basis i (by rw [bb4_finrank]; norm_num)

end NoDescent

/-! ## §5 — THE PAYOFF: the widened record forces the IDENTICAL downstream conclusion.

The whole point of the retyping is that it is not merely more faithful but FREE: the widened
record's quotient identity still lands the base-field per-row AIR acceptance `MainAirAcceptF d t`
through the landed extension-typed composition, so the repair replaces an unachievable hypothesis
(a single felt where the deployed verifier holds a `Challenge`) with an achievable one at the same
conclusion. -/

section Payoff

variable {E : Type*} [Field E] [Algebra BabyBear E] [DecidableEq E]

/-- **⚑ THE PAYOFF AT THE WIDENED TABLE RECORD.** From the widened check at an extension OOD point
`ζ`, an extension batching challenge `α`, the honest RLC identification, and the two
non-exceptionality side conditions, conclude the very same BASE-field `MainAirAcceptF d t`. -/
theorem mainAirAcceptF_of_wideTableOpening (E : Type*) [Field E] [Algebra BabyBear E]
    [DecidableEq E] (d : EffectVmDescriptor2) (tr : VmTrace)
    (hcap : tr.rows.length ≤ domainSize)
    (ζ α : E) (qp : VmConstraint2 → Polynomial E) (w : WideTableOpening E)
    (hOk : w.Ok ζ)
    (hCombinedIsRlc : w.constraintEval - w.vanishingAtZeta * w.quotientAtZeta
        = ∑ i ∈ Finset.range d.constraints.length,
            constraintResidualAtZetaExt E d tr ζ qp i * α ^ i)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZetaExt E d tr ζ qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        ζ ∉ exceptionalSet
          (liftPoly E (constraintPoly d tr c) - liftPoly E (vanishingPoly tr) * qp c)) :
    MainAirAcceptF d tr :=
  kprime_compose_of_tableIdentityExt E d tr hcap ζ α qp
    w.constraintEval w.vanishingAtZeta w.quotientAtZeta hOk.2.2 hCombinedIsRlc hαnonexc hζnonexc

/-- The widened single-AIR record's DERIVED table opening: its `constraintEval` is the Horner RLC
and its `quotientAtZeta` is the chunk recomposition, both computed rather than carried — exactly the
shape `BatchTablesSingleAir` retargets the free-field model to. -/
def tableOfWideSingleAir {E : Type*} [Field E] (o : WideSingleAirOpening E) : WideTableOpening E where
  degreeBits := o.degreeBits
  expectedDegreeBits := o.expectedDegreeBits
  constraintEval := wideFolded o
  quotientAtZeta := wideRecomposed o
  vanishingAtZeta := o.vanishing
  logupCumSum := o.logupCumSum

/-- **The widened single-AIR check FORCES the widened table identity** — the deployed acceptance
test `folded · inv_vanishing = quotient` plus the genuine-inverse pin gives
`C(ζ) = Z_H(ζ) · q(ζ)` at the full challenge width. -/
theorem tableOfWideSingleAir_ok {E : Type*} [Field E] (o : WideSingleAirOpening E) (h : o.Ok) :
    (tableOfWideSingleAir o).Ok o.zeta := by
  obtain ⟨hdeg, hvan, hinv, hid⟩ := h
  refine ⟨hdeg, hvan, ?_⟩
  show wideFolded o = o.vanishing * wideRecomposed o
  calc wideFolded o = wideFolded o * (o.vanishing * o.invVanishing) := by rw [hinv, mul_one]
    _ = o.vanishing * (wideFolded o * o.invVanishing) := by ring
    _ = o.vanishing * wideRecomposed o := by rw [hid]

/-- **⚑ THE PAYOFF AT THE WIDENED SINGLE-AIR RECORD**, composed: the deployed faithful quotient
check at the full challenge width still lands the base-field `MainAirAcceptF d t`. -/
theorem mainAirAcceptF_of_wideSingleAirOpening (E : Type*) [Field E] [Algebra BabyBear E]
    [DecidableEq E] (d : EffectVmDescriptor2) (tr : VmTrace)
    (hcap : tr.rows.length ≤ domainSize)
    (α : E) (qp : VmConstraint2 → Polynomial E) (o : WideSingleAirOpening E)
    (hOk : o.Ok)
    (hCombinedIsRlc : wideFolded o - o.vanishing * wideRecomposed o
        = ∑ i ∈ Finset.range d.constraints.length,
            constraintResidualAtZetaExt E d tr o.zeta qp i * α ^ i)
    (hαnonexc : α ∉ exceptionalSet
        (rlcResidualPoly d.constraints.length (constraintResidualAtZetaExt E d tr o.zeta qp)))
    (hζnonexc : ∀ c ∈ d.constraints, isArith c →
        o.zeta ∉ exceptionalSet
          (liftPoly E (constraintPoly d tr c) - liftPoly E (vanishingPoly tr) * qp c)) :
    MainAirAcceptF d tr :=
  mainAirAcceptF_of_wideTableOpening E d tr hcap o.zeta α qp (tableOfWideSingleAir o)
    (tableOfWideSingleAir_ok o hOk) hCombinedIsRlc hαnonexc hζnonexc

end Payoff

/-! ## §6 — PRICING THE SQUEEZE.

Two independent facts, and they say DIFFERENT things:

  * the value space collapses by a factor `p^3 > 2^92` (`lane0_ker_finrank`, `bb4_card_split`);
  * and the collapse is not harmless bookkeeping — the RLC fold, which is what the record's `alpha`
    is FOR, genuinely differs between two challenges that agree on the squeezed lane
    (`lane0_alpha_does_not_determine_the_fold`). -/

section Pricing

/-- `|BabyBear| = p`. -/
theorem babyBear_card : Fintype.card BabyBear = babyBearP := ZMod.card babyBearP

/-- The deployed challenge space is `p^3` times the narrow record's value space. -/
theorem bb4_card_split : Fintype.card BB4 = Fintype.card BabyBear * babyBearP ^ 3 := by
  rw [bb4_card, babyBear_card]; ring

/-- `p^3 > 2^92` — the order of the loss the single-felt record describes. -/
theorem squeeze_factor_gt_two_pow_92 : 2 ^ 92 < babyBearP ^ 3 := by norm_num

/-- The lane-0 squeeze is surjective onto the base field. -/
theorem lane0_surjective : Function.Surjective lane0 := by
  intro a
  refine ⟨a • bb4Basis 0, ?_⟩
  show bb4Basis.repr (a • bb4Basis 0) 0 = a
  simp

/-- **⚑ THE SQUEEZE HAS A THREE-DIMENSIONAL KERNEL.** Every squeezed felt is shared by a
`BabyBear`-subspace of dimension 3 — `p^3` distinct `Challenge` values — so the narrow record's
single felt determines `1/p^3` of the deployed value. -/
theorem lane0_ker_finrank : Module.finrank BabyBear (LinearMap.ker lane0) = 3 := by
  have h := LinearMap.finrank_range_add_finrank_ker lane0
  rw [LinearMap.range_eq_top.mpr lane0_surjective] at h
  rw [finrank_top, Module.finrank_self, bb4_finrank] at h
  omega

/-- A widened single-AIR opening whose Horner RLC fold is exactly its `alpha` (constraint
evaluations `[1, 0]`): the minimal probe that makes the fold depend on the challenge. -/
noncomputable def alphaProbe (a : BB4) : WideSingleAirOpening BB4 where
  zeta := 0
  degreeBits := 0
  expectedDegreeBits := 0
  alpha := a
  constraintEvals := [1, 0]
  zps := []
  quotientChunks := []
  vanishing := 0
  invVanishing := 0
  logupCumSum := 0

@[simp] theorem wideFolded_alphaProbe (a : BB4) : wideFolded (alphaProbe a) = a := by
  show ((0 * a + 1) * a + 0) = a
  ring

/-- **⚑ THE NARROW BIND DOES NOT DETERMINE THE DEPLOYED VALUE.**
`FriChallengerUnified.singleAirChallengesBound` pins `o.alpha` to `d.constraintAlpha.headD default`
— lane 0 of the four-lane transcript squeeze. Two `Challenge` values agreeing on that lane produce
DIFFERENT deployed Horner RLC folds. So the narrow record's single felt is not a coarse description
of the deployed `alpha`: it fails to fix the very quantity the deployed check consumes. -/
theorem lane0_alpha_does_not_determine_the_fold :
    ∃ a₁ a₂ : BB4,
      bb4Basis.repr a₁ 0 = bb4Basis.repr a₂ 0
      ∧ a₁ ≠ a₂
      ∧ wideFolded (alphaProbe a₁) ≠ wideFolded (alphaProbe a₂) := by
  refine ⟨bb4Basis 0, bb4Basis 0 + bb4Basis 1, by simp, ?_, ?_⟩
  · intro h
    have h1 : bb4Basis 1 = 0 := by
      have := h
      nth_rewrite 1 [← add_zero (bb4Basis 0)] at this
      exact (add_left_cancel this).symm
    exact bb4Basis.ne_zero 1 h1
  · rw [wideFolded_alphaProbe, wideFolded_alphaProbe]
    intro h
    have h1 : bb4Basis 1 = 0 := by
      nth_rewrite 1 [← add_zero (bb4Basis 0)] at h
      exact (add_left_cancel h).symm
    exact bb4Basis.ne_zero 1 h1

end Pricing

/-! ## §7 — NON-VACUITY: the widened hypothesis bundle is INHABITED, at values drawn from OUTSIDE
the base image, and it DELIVERS.

Following the methodological correction that an inhabitation witness recording only the CONCLUSION
is weaker than it looks: the statements below carry EVERY value-dependent hypothesis of the §5
payoff, plus the §4 separation clauses at the very same witness. -/

section Fire

/-- Any nonzero base scalar away from a non-base element stays non-base. -/
theorem sub_one_notMem_range {E : Type*} [Field E] [Algebra BabyBear E] {ξ : E}
    (hξ : ξ ∉ Set.range (algebraMap BabyBear E)) :
    ξ - 1 ∉ Set.range (algebraMap BabyBear E) := by
  rintro ⟨s, hs⟩
  exact hξ ⟨s + 1, by rw [map_add, map_one, hs]; ring⟩

/-- **⚑ FIRE — the §5 payoff bundle at the WIDENED TABLE RECORD, all values NON-BASE.**
Every challenge-and-value-dependent hypothesis is recorded, so this cannot be met by a vacuous
witness: the OOD point and the batching challenge are both drawn from `BB4 ∖ image(BabyBear)`, the
widened record's recomputed vanishing AND opened quotient are both outside the base image, NO narrow
`TableOpening` (at the same degree pin) can satisfy the widened check at this OOD point, the widened
check HOLDS, the RLC identification HOLDS, both non-exceptionality conditions HOLD, and the
composition produces the real base-field `MainAirAcceptF dArith tHonest`. -/
theorem fire_wideTableOpening_nonbase :
    ∃ (ζ α : BB4) (w : WideTableOpening BB4),
      ζ ∉ Set.range (algebraMap BabyBear BB4)
      ∧ α ∉ Set.range (algebraMap BabyBear BB4)
      ∧ w.vanishingAtZeta ∉ Set.range (algebraMap BabyBear BB4)
      ∧ w.quotientAtZeta ∉ Set.range (algebraMap BabyBear BB4)
      ∧ (∀ t : TableOpening BabyBear, wideOfTable BB4 t ≠ w)
      ∧ (∀ t : TableOpening BabyBear, t.degreeBits = 0 → ¬ (wideOfTable BB4 t).Ok ζ)
      ∧ w.Ok ζ
      ∧ (w.constraintEval - w.vanishingAtZeta * w.quotientAtZeta
          = ∑ i ∈ Finset.range dArith.constraints.length,
              constraintResidualAtZetaExt BB4 dArith tHonest ζ (fun _ => 0) i * α ^ i)
      ∧ α ∉ exceptionalSet (rlcResidualPoly dArith.constraints.length
            (constraintResidualAtZetaExt BB4 dArith tHonest ζ (fun _ => 0)))
      ∧ (∀ c ∈ dArith.constraints, isArith c →
            ζ ∉ exceptionalSet (liftPoly BB4 (constraintPoly dArith tHonest c)
              - liftPoly BB4 (vanishingPoly tHonest) * 0))
      ∧ MainAirAcceptF dArith tHonest := by
  obtain ⟨ξ, hξ⟩ := exists_nonbase_bb4
  refine ⟨ξ, ξ,
    { degreeBits := 0, expectedDegreeBits := 0, constraintEval := (ξ - 1) * ξ,
      quotientAtZeta := ξ, vanishingAtZeta := ξ - 1, logupCumSum := 0 },
    hξ, hξ, sub_one_notMem_range hξ, hξ, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hteq
    exact hξ ⟨t.quotientAtZeta, congrArg WideTableOpening.quotientAtZeta hteq⟩
  · intro t hdb
    refine no_narrow_table_at_nonbase_ood ξ t ?_
    rw [hdb]
    simpa using hξ
  · exact ⟨rfl, by show ξ - 1 + 1 = ξ ^ (2 ^ 0); ring, rfl⟩
  · show (ξ - 1) * ξ - (ξ - 1) * ξ = _
    rw [sub_self, constraintResidualAtZetaExt_dArith_tHonest]
    simp
  · rw [constraintResidualAtZetaExt_dArith_tHonest]
    simp [exceptionalSet, rlcResidualPoly]
  · intro c hc _
    simp only [dArith, List.mem_singleton] at hc
    subst hc
    rw [constraintPoly_dArith_tHonest_zero]
    simp [liftPoly, exceptionalSet]
  · refine mainAirAcceptF_of_wideTableOpening BB4 dArith tHonest (by simp [tHonest, domainSize])
      ξ ξ (fun _ => 0)
      { degreeBits := 0, expectedDegreeBits := 0, constraintEval := (ξ - 1) * ξ,
        quotientAtZeta := ξ, vanishingAtZeta := ξ - 1, logupCumSum := 0 }
      ⟨rfl, by show ξ - 1 + 1 = ξ ^ (2 ^ 0); ring, rfl⟩ ?_ ?_ ?_
    · show (ξ - 1) * ξ - (ξ - 1) * ξ = _
      rw [sub_self, constraintResidualAtZetaExt_dArith_tHonest]
      simp
    · rw [constraintResidualAtZetaExt_dArith_tHonest]
      simp [exceptionalSet, rlcResidualPoly]
    · intro c hc _
      simp only [dArith, List.mem_singleton] at hc
      subst hc
      rw [constraintPoly_dArith_tHonest_zero]
      simp [liftPoly, exceptionalSet]

/-- A widened single-AIR opening whose `alpha`, `zeta`, recomputed vanishing and Horner fold are
ALL genuine `Challenge` values outside the base image, with a real inverse tooth. -/
noncomputable def nonbaseSingleAir (ξ : BB4) : WideSingleAirOpening BB4 where
  zeta := ξ
  degreeBits := 0
  expectedDegreeBits := 0
  alpha := ξ
  constraintEvals := [1, 0]
  zps := [1]
  quotientChunks := [(ξ - 1)⁻¹ * ξ]
  vanishing := ξ - 1
  invVanishing := (ξ - 1)⁻¹
  logupCumSum := 0

/-- **⚑ FIRE — the widened SINGLE-AIR record is inhabited at a genuinely non-base `alpha`.**
The deployed RLC challenge, the OOD point, the recomputed vanishing, and the resulting folded
constraint value are all outside the base image; the genuine-inverse tooth is real (the vanishing is
invertible); the widened check HOLDS; and no narrow `SingleAirOpening` lifts to it. -/
theorem fire_wideSingleAir_nonbase :
    ∃ ξ : BB4,
      ξ ∉ Set.range (algebraMap BabyBear BB4)
      ∧ (nonbaseSingleAir ξ).alpha ∉ Set.range (algebraMap BabyBear BB4)
      ∧ (nonbaseSingleAir ξ).vanishing ∉ Set.range (algebraMap BabyBear BB4)
      ∧ wideFolded (nonbaseSingleAir ξ) ∉ Set.range (algebraMap BabyBear BB4)
      ∧ (nonbaseSingleAir ξ).Ok
      ∧ (∀ o : SingleAirOpening BabyBear, wideOfSingleAir BB4 o ≠ nonbaseSingleAir ξ) := by
  obtain ⟨ξ, hξ⟩ := exists_nonbase_bb4
  have hne : ξ - 1 ≠ 0 := by
    intro h
    exact hξ ⟨1, by rw [map_one]; linear_combination -h⟩
  have hfold : wideFolded (nonbaseSingleAir ξ) = ξ := by
    show ((0 * ξ + 1) * ξ + 0) = ξ
    ring
  refine ⟨ξ, hξ, hξ, sub_one_notMem_range hξ, by rw [hfold]; exact hξ, ⟨rfl, ?_, ?_, ?_⟩, ?_⟩
  · show ξ - 1 + 1 = ξ ^ (2 ^ 0)
    ring
  · show (ξ - 1) * (ξ - 1)⁻¹ = 1
    field_simp
  · rw [hfold]
    show ξ * (ξ - 1)⁻¹ = 1 * ((ξ - 1)⁻¹ * ξ) + 0
    ring
  · intro o hoeq
    exact hξ ⟨o.alpha, congrArg WideSingleAirOpening.alpha hoeq⟩

end Fire

/-! ## §9 — THE EVIDENCE FOR THE `alpha` VERDICT: the FULL four-lane challenge IS bound at the apex.

This is what makes `SingleAirOpening.alpha`'s single felt a redundant description rather than a
soundness hole.  The apex-facing predicate does not merely pin the scalar lane; it separately
requires the widened single-AIR check against the COMPLETE four-lane transcript `α` and `ζ`. -/

section ApexBinding

open Dregg2.Circuit.FriVerifier (BatchProofData WrapPublics FriParams RecursionVk FriCore)
open Dregg2.Circuit.ExtFieldChallenge
  (ExtFriCore ExtFriArith ExtVerifierView verifyAlgoUnifiedFaithfulExt batchTablesCheckExt ExtElem)

/-- **⚑ ACCEPTANCE FORCES THE FULL-WIDTH SINGLE-AIR CHECK.** Whatever the apex-facing
`verifyAlgoUnifiedFaithfulExt` accepts, the widened single-AIR OOD identity holds against the
complete `params.extDeg`-lane transcript `α` and `ζ` — not their head lanes.  So the deployed
constraint-RLC challenge IS bound at full width by the verifier the apex consumes. -/
theorem faithfulExt_forces_fullWidth_alpha {F : Type} [Inhabited F] [DecidableEq F]
    (perm : List F → List F) (RATE : Nat) (toNat : F → Nat) (params : FriParams)
    (vk : RecursionVk F) (core : FriCore F) (A : FieldArith F)
    (extCore : ExtFriCore F) (extA : ExtFriArith F) (W : F)
    (initState : List F) (logN : Nat) (proof : BatchProofData F) (pub : WrapPublics F)
    (view : ExtVerifierView F)
    (hacc : verifyAlgoUnifiedFaithfulExt perm RATE toNat params vk core A extCore extA W
      initState logN proof pub view = true) :
    batchTablesCheckExt extA W params.extDeg
        (⟨(Dregg2.Circuit.FriChallengerUnified.deriveTranscript
            perm RATE toNat params initState logN proof pub).constraintAlpha⟩ : ExtElem F)
        (⟨(Dregg2.Circuit.FriChallengerUnified.deriveTranscript
            perm RATE toNat params initState logN proof pub).ζ⟩ : ExtElem F)
        view.singleAirOpenings = true := by
  unfold verifyAlgoUnifiedFaithfulExt at hacc
  simp only [Bool.and_eq_true] at hacc
  exact hacc.2.2

end ApexBinding

/-! ## §8 — Axiom hygiene. -/

#assert_all_clean [
  wideOfTable_ok_of_tableOk,
  wideBusSum_map,
  wideOfSingleAir_ok_of_singleAirOk,
  wideFolded_wideOfSingleAir,
  wideRecomposed_wideOfSingleAir
]

#assert_all_clean [
  faithfulExt_forces_fullWidth_alpha,
  lifted_narrow_forces_base_ood_power,
  tableOk_pass_does_not_describe_nonbase_ood
]

#assert_all_clean [
  no_narrow_table_at_nonbase_ood,
  wide_table_beyond_base,
  lane0_square_not_multiplicative,
  lane_product_not_multiplicative,
  lanes_injective
]

#assert_all_clean [
  mainAirAcceptF_of_wideTableOpening,
  tableOfWideSingleAir_ok,
  mainAirAcceptF_of_wideSingleAirOpening
]

#assert_all_clean [
  bb4_card_split,
  squeeze_factor_gt_two_pow_92,
  lane0_ker_finrank,
  lane0_alpha_does_not_determine_the_fold
]

#assert_all_clean [
  fire_wideTableOpening_nonbase,
  fire_wideSingleAir_nonbase
]

end Dregg2.Circuit.ExtOpeningRecordWidth

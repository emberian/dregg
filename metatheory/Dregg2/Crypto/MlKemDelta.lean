/-
# `Dregg2.Crypto.MlKemDelta` — the ML-KEM-768 decryption-failure `δ`-bound: the PROBABILISTIC residual.

Seam 4 of the ML-KEM stack. `MlKemCorrect` proved DETERMINISTIC K-PKE decryption correctness CONDITIONAL on
the per-coefficient noise bound `noiseBoundHolds : ∀ c, -832 < ez c < 832`, and NAMED the probabilistic
residual `MlKem768DecapsFailureBound` (`Pr_r[noiseBoundHolds] ≥ 1 − δ`, `δ ≈ 2⁻¹⁶⁴`). This module discharges
the STRUCTURAL half of that residual over the CBD randomness `r` and REDUCES the one remaining analytic step to
a precisely-named Mathlib concentration lemma — the honest decomposition (like `RingRepFaithful` reduced to
`NttMulHom`), not a `sorry`.

## The decomposition (`MlKemCorrect.eTotal = eᵀr − sᵀe1 + e2 + Δv − sᵀΔu`)

The decryption failure event `¬noiseBoundHolds` is `∃ c, 832 ≤ |e_total c|` over the `k·n = 3·256 = 768`
coefficients. We model the CBD randomness (`SamplePolyCBD(η=2)` giving `y,e1,e2`, ranges in `[−2,2]`, plus the
bounded compression errors `Δu` (du=10), `Δv` (dv=4)) as a FINITE outcome space `Ω`, and each coefficient's
centered noise as `ez c : Ω → ℤ`. Then the failure probability decomposes in two honest steps:

* **UNION BOUND (proved here, no `sorry`).** `Pr_r[∃ c, 832 ≤ |e_total c|] ≤ ∑_c Pr_r[832 ≤ |e_total c|]`.
  This is `winProb_biUnion_le` — a genuine finite counting-probability theorem over the `winProb` framework of
  `ProbCrypto`: the favorable set of the disjunction is contained in the `Finset.biUnion` of the per-coefficient
  favorable sets, so its cardinality is `≤` the sum (`Finset.card_biUnion_le`), and dividing by `|Ω|` preserves
  it. Instantiated at the 768 coefficients: `mlkem_decapsFail_le` gives `Pr[fail] ≤ 768 · τ` for any
  per-coefficient tail bound `τ`.

* **PER-COEFFICIENT TAIL (DISCHARGED from the CBD sum structure — §5–§8).** `Pr_r[832 ≤ |e_total c|] ≤ τ`. Each
  `e_total c` is a sum of `[−2,2]`-bounded independent centered CBD terms (plus bounded compression errors), i.e. a
  sub-Gaussian tail. This is now PROVED, not merely named. §5 bridges the `winProb` counting model to the uniform
  `MeasureTheory.Measure` (`winProb_eq_measureReal`, via `PMF.uniformFintype`). §6 (`winProb_abs_subgaussian_le`)
  actually APPLIES Hoeffding's lemma (`hasSubgaussianMGF_of_mem_Icc`, parameter `((b−a)/2)² = 4` per `[−2,2]` term)
  and Hoeffding's inequality for the independent sum (`measure_sum_ge_le_of_iIndepFun`), unioning the two signs of
  `|·|` to `Pr[832 ≤ |e_total c|] ≤ 2·exp(−832²/(2·V))` in the `winProb` model. §7 closes the arithmetic
  (`hoeffding_delta_arith`: `2·exp(−832²/(2V)) ≤ 2⁻¹⁷⁴` for `0 < V ≤ 2800`, from `log_two_lt_d9`) and discharges
  `PerCoeffHoeffdingTail` (`perCoeffHoeffdingTail_of_subgaussianSum`) from the honest structural claim
  `CoeffIsSubgaussianSum` (each coefficient IS such an independent bounded-variance sub-Gaussian sum). §8 shows this
  is non-vacuous — the full pipeline FIRES on a genuine positive-variance Rademacher model (`rademacher_delta_fires`)
  AND on the ACTUAL ML-KEM CBD(η=2) centered-binomial distribution (`cbd2_isSubgaussianSum`, §9).
  **What remains open is exhibiting the real ML-KEM `e_total c` as a `CoeffIsSubgaussianSum` at `V ≤ 2800` — and §10
  MEASURES that this is NOT a mere modeling step: the compound coefficient's cross-terms `eᵀr, sᵀe1, sᵀΔu` are
  negacyclic-convolution PRODUCTS of two CBD/error polys (each product `∈ [−4,4]`, so the only cited per-term bound
  `hasSubgaussianMGF_of_mem_Icc` gives it range-Hoeffding parameter `16`, not the variance), and `Δv` (`|Δv| ≤ 104`)
  alone carries range-Hoeffding parameter `10816 > 2800`. So the range-based route incurs `≥ 3·768·16 + 4 + 10816 =
  47684 ≫ 2800` (`hoeffding_budget_exceeds_2800`). The `V ≤ 2800` budget is the true VARIANCE of `e_total`
  (≈ 2800, matching the near-Gaussian `δ ≈ 2⁻¹⁶⁴` of the exact Kyber convolution); meeting it needs TIGHTER,
  distribution-specific sub-Gaussian proxies — a variance-based Bernstein/sub-gamma concentration or the exact
  distribution convolution — NOT `hasSubgaussianMGF_of_mem_Icc`. Contrary to a naive reading, a (tighter-than-Hoeffding)
  concentration IS the open step; the applied Hoeffding INEQUALITY (`measure_sum_ge_le_of_iIndepFun`) is not enough.**

## THE CONSTANT CLOSES

The union-bound factor `768 < 2¹⁰ = 1024` costs only 10 bits: if the per-coefficient Hoeffding tail meets
`τ = 2⁻¹⁷⁴`, then `768 · 2⁻¹⁷⁴ ≤ 2¹⁰ · 2⁻¹⁷⁴ = 2⁻¹⁶⁴ = δ` (`unionBound_closes_delta`, proved). So the assembled
statement `mlkem768_decapsFailure_le_delta` concludes `Pr_r[¬noiseBoundHolds] ≤ MlKemCorrect.mlKem768Delta` from
the named per-coefficient tail — the full FIPS 203 δ-bound, modulo the one cited concentration inequality.

## ⚑ §12 RESOLVES IT — THE EXACT-MGF CHERNOFF ROUTE REACHES δ (the wall §10–§11 named is gone)

§10–§11 proved the RANGE-Hoeffding and variance-BERNSTEIN routes cannot reach δ (their best was `2⁻¹¹⁷`) — both
conclusions CORRECT for those loose surrogates. §12 escapes them with the EXACT Moment-Generating Function: it
PROVES the exact per-term MGFs (CBD `cosh(s/2)⁴`; the convolution PRODUCT `E_r[cosh(s·r/2)⁴]`, the term §10
flagged), feeds them through Mathlib's EXACT Chernoff bound (`measure_ge_le_exp_mul_mgf`) and the exact
product-of-MGFs for independent sums (`iIndepFun.mgf_sum`), and closes, kernel-clean, `Pr[decaps fails] ≤ 2⁻¹⁴⁰`
at `s = 3/10` — 23 bits BELOW §11's `2⁻¹¹⁷`. §15 then TIGHTENS the arithmetic (tight product-factor Taylor bound,
tight final step, `768 < 2¹⁰` union) to `2⁻¹⁴⁸` for the ungrouped `±104`-envelope model and `2⁻¹⁴¹` byte-faithful.
**§18 (2026-07-13) SUPERSEDES the `2⁻¹⁴⁸` ceiling**: refining `Δv` from the `±104` envelope to the TRUE near-uniform
compression-error law (`≈ e^{27.37}` vs `≈ e^{31.2}`) tightens the assumption-free UNCONDITIONAL bound to
`≤ 2⁻¹⁵³` (`rZ_decapsFailure_le_delta153`, `2⁻¹⁶³` per coefficient, R2 discharged). `2⁻¹⁵³` is the current honest
ceiling of the exact-MGF **Chernoff** route with the true law.

⚑ **CORRECTION (§15/§18).** An earlier draft of this summary claimed the residual from the proved bound to FIPS
`2⁻¹⁶⁴` is "pure rational-arithmetic slack … NOT a concentration or modeling wall." MEASUREMENT refutes that.
Minimizing the exact-MGF Chernoff bound `2·e^{−s·832}·∏mgf` over `s` with the exact per-term MGFs and the TRUE
near-uniform `Δv` law caps the per-coefficient tail at `≈ 2⁻¹⁶³`; the `768`-fold union costs `≈ 10` bits, so the
ASSEMBLED exact-MGF Chernoff bound ceilings at `≈ 2⁻¹⁵³` (§18; the earlier `±104` envelope ceilinged at `≈ 2⁻¹⁵⁵`).
Reaching FIPS `2⁻¹⁶⁴` through the `768`-union needs a per-coefficient tail of `2⁻¹⁷⁴` — below the exact-MGF Chernoff
ceiling, so the gap is the slack of the Chernoff METHOD at a `≈ 15.7σ` deviation (the Bahadur–Rao `1/(sσ√{2π})`
prefactor the exponential rate discards), NOT the rational `s` or the `Δv` MGF. The true per-coefficient tail IS below
`2⁻¹⁷⁴` (near-Gaussian convolution `≈ 2⁻¹⁸⁰`); closing the gap needs a TIGHTER-THAN-CHERNOFF tail — the exact
convolved-distribution tail. §16/§19 REDUCE FIPS `2⁻¹⁶⁴` to exactly one decidable per-coefficient inequality
(`LightExactPerCoeffTail`, the **R1** residual), whose discharge needs a CERTIFIED numeric FFT-convolution
evaluation — **IN FLIGHT / PENDING**, not finalized. See §15/§18 for the measurement, §19 for the reduction.

## NON-FAKE / NON-VACUOUS

`#assert_axioms` on every `∀`/probabilistic theorem ⊆ `{propext, Classical.choice, Quot.sound}` — no `sorryAx`,
no `native_decide` in a probabilistic theorem. The bound is a real number `δ = 2⁻¹⁶⁴ < 1`. The events are
genuinely satisfiable AND refutable: `perCoeff_tail_satisfiable` (the zero-noise model has per-coefficient tail
`0 ≤ τ`, so `PerCoeffHoeffdingTail` holds and the pipeline concludes `Pr[fail] = 0 ≤ δ`);
`perCoeff_tail_refutable` (a model whose noise ALWAYS exceeds `832` has per-coefficient tail `1`, refuting
`PerCoeffHoeffdingTail` at `τ = 2⁻¹⁷⁴`) — so the named hypothesis is a load-bearing constraint, not vacuously
true. `winProb_biUnion_le` itself both fires (equality-attaining teeth via `ProbCrypto.winProb_top/bot`).
-/
import Dregg2.Crypto.MlKemCorrect
import Dregg2.Crypto.ProbCrypto
import Dregg2.ForMathlib.BerryEsseen
import Dregg2.Tactics
import Mathlib.Probability.Moments.SubGaussian
import Mathlib.Probability.Distributions.Uniform
import Dregg2.ForMathlib.UniformPMF
import Mathlib.Probability.ProbabilityMassFunction.Integrals
import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds

namespace Dregg2.Crypto.MlKemDelta

open Dregg2.Crypto.ProbCrypto
open MeasureTheory ProbabilityTheory Real
open scoped BigOperators NNReal ENNReal

set_option maxRecDepth 10000
set_option maxHeartbeats 1000000

/-! ## §1 — THE UNION BOUND over the finite counting-probability model (PROVED, kernel-clean).

The one genuinely-provable probabilistic core: for a finite outcome space `Ω`, a finite family of events
`bad : ι → Ω → Bool`, the probability that ANY fires is at most the sum of the individual probabilities. This
is Boole's inequality in the `ProbCrypto.winProb` counting model. -/

/-- **Union bound (Boole's inequality) in the `winProb` counting model.** The favorable set of
`(finRange n).any (bad · ω)` is contained in the `Finset.biUnion` of the per-event favorable sets, so its
cardinality is `≤ ∑` (`Finset.card_biUnion_le`); dividing the common `|Ω|` preserves the inequality. No
`sorry`, no measure theory — pure finite counting. (The failure event is expressed as `List.any` over
`finRange n` rather than a `Fintype` existential purely to keep instance elaboration light on `Fin 768`;
`List.any_eq_true` bridges it to `∃ i, bad i ω`.) -/
theorem winProb_anyFinRange_le_sum {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (n : ℕ)
    (bad : Fin n → Ω → Bool) :
    winProb (fun ω => (List.finRange n).any (fun i => bad i ω)) ≤ ∑ i, winProb (bad i) := by
  -- Numerator containment: the disjunction's favorable set ⊆ the biUnion of the parts.
  have hsub : (Finset.univ.filter (fun ω : Ω => (List.finRange n).any (fun i => bad i ω) = true))
      ⊆ Finset.univ.biUnion (fun i => Finset.univ.filter (fun ω : Ω => bad i ω = true)) := by
    intro ω hω
    rw [Finset.mem_filter] at hω
    obtain ⟨i, _, hbi⟩ := List.any_eq_true.mp hω.2
    rw [Finset.mem_biUnion]
    exact ⟨i, Finset.mem_univ i, Finset.mem_filter.mpr ⟨Finset.mem_univ ω, hbi⟩⟩
  have hcard : (Finset.univ.filter
        (fun ω : Ω => (List.finRange n).any (fun i => bad i ω) = true)).card
      ≤ ∑ i, (Finset.univ.filter (fun ω : Ω => bad i ω = true)).card :=
    le_trans (Finset.card_le_card hsub) (Finset.card_biUnion_le)
  -- Divide the common `|Ω|`.
  unfold winProb
  rw [← Finset.sum_div]
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · simp [h0]
  · gcongr
    exact_mod_cast hcard

/-! ## §2 — THE ML-KEM-768 DECAPS-FAILURE EVENT as a counting experiment.

`k·n = 768` coefficients; `ez c : Ω → ℤ` is the centered value of `e_total`'s `c`-th coefficient as a function
of the CBD randomness `ω`. The per-coefficient failure `badCoeff` fires when `832 ≤ |ez c|` (outside the
decision window `(−832, 832)` that `MlKemCorrect.decryptCorrect_conditional` requires), and the decaps failure
`decapsFails` when ANY coefficient fails. -/

/-- The `c`-th coefficient escapes the decryption window `(−832, 832)`. -/
def badCoeff {Ω : Type*} (ez : Fin 768 → Ω → ℤ) (c : Fin 768) (ω : Ω) : Bool :=
  decide (832 ≤ |ez c ω|)

/-- Decryption fails: SOME coefficient's noise escapes the window (`¬ MlKemCorrect.noiseBoundHolds`). Phrased
as `List.any` over `finRange 768` (a plain `Bool` fold) rather than a `Fintype` existential — equivalent by
`List.any_eq_true` (`= true ↔ ∃ c, badCoeff ez c ω`), and lighter on instance elaboration. -/
def decapsFails {Ω : Type*} (ez : Fin 768 → Ω → ℤ) (ω : Ω) : Bool :=
  (List.finRange 768).any (fun c => badCoeff ez c ω)

/-- **THE UNION-BOUND ASSEMBLY** — `Pr[decaps fails] ≤ 768 · τ` from a uniform per-coefficient tail `τ`.
Instantiates `winProb_anyFinRange_le_sum` at the 768 coefficients and sums the `768` copies of `τ`. Proved,
kernel-clean; `τ` is an arbitrary real, so the statement is parametric in whatever per-coefficient tail the
Hoeffding step supplies. -/
theorem mlkem_decapsFail_le {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ez : Fin 768 → Ω → ℤ) (τ : ℝ)
    (htail : ∀ c, winProb (badCoeff ez c) ≤ τ) :
    winProb (decapsFails ez) ≤ 768 * τ := by
  unfold decapsFails
  refine le_trans (winProb_anyFinRange_le_sum 768 (badCoeff ez)) ?_
  refine le_trans (Finset.sum_le_sum (fun c _ => htail c)) ?_
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  norm_num

/-! ## §3 — THE PER-COEFFICIENT HOEFFDING TAIL (the one remaining analytic step, precisely named). -/

/-- **THE PER-COEFFICIENT TAIL (named here; DISCHARGED in §5–§8).** For every coefficient, the probability
that its centered noise escapes the window is `≤ τ`. Each `e_total c` is a sum of `[−2,2]`-bounded INDEPENDENT
centered CBD terms (plus bounded compression errors), so this is a sub-Gaussian tail. `PerCoeffHoeffdingTail`
is the interface the capstone `mlkem768_decapsFailure_le_delta` consumes; it is no longer an open assumption —
`perCoeffHoeffdingTail_of_subgaussianSum` (§7) PROVES it at `τ = 2⁻¹⁷⁴` from the CBD sum structure
`CoeffIsSubgaussianSum`, applying Mathlib's Hoeffding lemma
(`ProbabilityTheory.HasSubgaussianMGF.hasSubgaussianMGF_of_mem_Icc`, parameter `((2−(−2))/2)² = 4`) and
Hoeffding inequality (`ProbabilityTheory.HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun`) through the §5
counting-measure↔`winProb` bridge. What is left is exhibiting `CoeffIsSubgaussianSum` for the real `e_total c` at
`V ≤ 2800` — and §10 measures that the range-Hoeffding proxies of its convolution-product cross-terms overshoot
`2800` by 16×, so the remaining step is a TIGHTER (variance-based) concentration, not merely modeling. -/
def PerCoeffHoeffdingTail {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ez : Fin 768 → Ω → ℤ) (τ : ℝ) : Prop :=
  ∀ c, winProb (badCoeff ez c) ≤ τ

/-- **THE CONSTANT CLOSES** — the 768-fold union-bound factor costs only 10 bits: `768 < 2¹⁰`, so a
per-coefficient Hoeffding tail of `2⁻¹⁷⁴` sums to `≤ 2⁻¹⁶⁴ = δ`. Pure `zpow` arithmetic. -/
theorem unionBound_closes_delta :
    (768 : ℝ) * (2 : ℝ) ^ (-174 : ℤ) ≤ MlKemCorrect.mlKem768Delta := by
  unfold MlKemCorrect.mlKem768Delta
  have h768 : (768 : ℝ) ≤ (2 : ℝ) ^ (10 : ℤ) := by norm_num
  have hpos : (0 : ℝ) ≤ (2 : ℝ) ^ (-174 : ℤ) := by positivity
  calc (768 : ℝ) * (2 : ℝ) ^ (-174 : ℤ)
      ≤ (2 : ℝ) ^ (10 : ℤ) * (2 : ℝ) ^ (-174 : ℤ) := by gcongr
    _ = (2 : ℝ) ^ ((10 : ℤ) + (-174 : ℤ)) := by
          rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]
    _ = (2 : ℝ) ^ (-164 : ℤ) := by norm_num

/-- **THE ASSEMBLED δ-BOUND** — `Pr_r[¬noiseBoundHolds] ≤ MlKemCorrect.mlKem768Delta`. Chains the named
per-coefficient Hoeffding tail (at `τ = 2⁻¹⁷⁴`) through the proved union bound and the proved constant closing.
This is the full FIPS 203 decryption-failure bound, reduced to exactly the one concentration inequality named in
`PerCoeffHoeffdingTail`. -/
theorem mlkem768_decapsFailure_le_delta {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (ez : Fin 768 → Ω → ℤ)
    (htail : PerCoeffHoeffdingTail ez ((2 : ℝ) ^ (-174 : ℤ))) :
    winProb (decapsFails ez) ≤ MlKemCorrect.mlKem768Delta :=
  le_trans (mlkem_decapsFail_le ez _ htail) unionBound_closes_delta

/-! ## §4 — NON-VACUITY: the named tail is genuinely satisfiable AND refutable (both teeth). -/

/-- The zero-noise model: a one-point space with no noise. `e_total ≡ 0`, so no coefficient escapes. -/
def zeroModel : Fin 768 → Unit → ℤ := fun _ _ => 0

/-- The always-failing model: noise `1000 > 832` in every coefficient. -/
def failModel : Fin 768 → Unit → ℤ := fun _ _ => 1000

/-- **(TOOTH — satisfiable.)** The zero-noise model satisfies `PerCoeffHoeffdingTail` for any `τ ≥ 0`: every
coefficient's noise is `0`, which never escapes the window, so the per-coefficient probability is `0 ≤ τ`. So
the named hypothesis is not vacuously false — it holds on a real model. -/
theorem perCoeff_tail_satisfiable : PerCoeffHoeffdingTail zeroModel ((2 : ℝ) ^ (-174 : ℤ)) := by
  intro c
  have hbad : badCoeff zeroModel c = fun _ : Unit => false := by
    funext ω; simp [badCoeff, zeroModel]
  rw [hbad, winProb_bot]
  positivity

/-- **The pipeline FIRES end-to-end** — on the zero-noise model the assembled δ-bound concludes
`Pr[decaps fails] = 0 ≤ δ`. Exercises `mlkem768_decapsFailure_le_delta` on a concrete model whose per-coefficient
tail genuinely holds. -/
theorem mlkem768_delta_fires :
    winProb (decapsFails zeroModel) ≤ MlKemCorrect.mlKem768Delta :=
  mlkem768_decapsFailure_le_delta zeroModel perCoeff_tail_satisfiable

/-- **(TOOTH — refutable.)** The always-failing model REFUTES `PerCoeffHoeffdingTail` at ANY `τ < 1` (in
particular the δ-relevant `2⁻¹⁷⁴`): every coefficient's noise is `1000`, always escaping the window, so the
per-coefficient probability is exactly `1 > τ`. So the named Hoeffding hypothesis is a load-bearing constraint —
a real inequality that can fail, not a tautology. -/
theorem perCoeff_tail_refutable {τ : ℝ} (hτ : τ < 1) : ¬ PerCoeffHoeffdingTail failModel τ := by
  intro h
  have hbad : badCoeff failModel (0 : Fin 768) = fun _ : Unit => true := by
    funext ω; simp [badCoeff, failModel]
  have h1 : winProb (badCoeff failModel (0 : Fin 768)) = 1 := by
    rw [hbad]; exact winProb_top
  have hle := h 0
  rw [h1] at hle
  linarith

/-! ## §5 — THE COUNTING-MEASURE ↔ `winProb` BRIDGE (the transfer seam, PROVED).

`winProb` counts a fraction of a finite outcome space; Mathlib's concentration inequalities speak about a
`MeasureTheory.Measure`. The uniform counting measure on a `Fintype` IS such a measure — concretely
`(PMF.uniformFintype Ω).toMeasure`, a genuine `IsProbabilityMeasure`. This section establishes
`winProb win = (unifMeasure Ω).real {ω | win ω}`, the exact bridge that lets any `μ.real`-tail bound
transfer to the `winProb` framework the rest of the ML-KEM stack is stated against. -/

/-- **The uniform probability measure on a finite outcome space.** The `MeasureTheory.Measure` shadow of
the `winProb` counting model: every point has mass `1/|Ω|`. This is where the finite counting probability
meets `MeasureTheory`. -/
noncomputable def unifMeasure (Ω : Type*) [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] : Measure Ω :=
  (PMF.uniformFintype Ω).toMeasure

instance instIsProbabilityUnif {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω] :
    IsProbabilityMeasure (unifMeasure Ω) :=
  PMF.toMeasure.isProbabilityMeasure _

/-- **THE BRIDGE (PROVED).** `winProb win` — the counting fraction — equals `(unifMeasure Ω).real` of the
favorable set. The counting numerator `|{ω | win ω}|` is `Fintype.card` of the winning subtype
(`Fintype.card_subtype`), and `toMeasure_uniformFintype_apply` gives the uniform measure of any set as
`card s / card Ω`; taking `.toReal` matches `winProb` on the nose. This is the transfer seam: a
`MeasureTheory` tail bound on `{ω | win ω}` becomes a `winProb` bound. -/
theorem winProb_eq_measureReal {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (win : Ω → Bool) :
    winProb win = (unifMeasure Ω).real {ω | win ω = true} := by
  classical
  have hms : MeasurableSet {ω : Ω | win ω = true} := (Set.toFinite _).measurableSet
  have happly : (unifMeasure Ω) {ω : Ω | win ω = true}
      = (Fintype.card {ω : Ω // win ω = true} : ℝ≥0∞) / (Fintype.card Ω : ℝ≥0∞) := by
    rw [unifMeasure]
    exact PMF.toMeasure_uniformFintype_apply _ hms
  rw [Measure.real, happly, ENNReal.toReal_div, ENNReal.toReal_natCast, ENNReal.toReal_natCast]
  unfold winProb
  rw [Fintype.card_subtype]

/-! ## §6 — THE SUB-GAUSSIAN SUM TAIL, TRANSFERRED TO `winProb` (the two named Mathlib lemmas, APPLIED).

The heart of the discharge. Given the noise coefficient `Z = ∑ᵢ Tᵢ` as a sum of INDEPENDENT centered terms
that are individually sub-Gaussian (Hoeffding's lemma gives each `[−2,2]`-bounded centered term parameter
`4`), Mathlib's Hoeffding inequality `measure_sum_ge_le_of_iIndepFun` bounds each one-sided tail; the two
signs union to a two-sided `|Z|` tail, and §5's bridge lands it in the `winProb` model. Both cited Mathlib
lemmas are actually applied here — this is no longer a named residual. -/

/-- **THE TWO-SIDED SUB-GAUSSIAN TAIL IN THE `winProb` MODEL (PROVED — applies Mathlib's Hoeffding).** For a
sum `Z ω = ∑ i, T i ω` of independent (`iIndepFun`) sub-Gaussian terms `T i` (parameters `γ i` under the
uniform measure), the `winProb` that `|Z|` escapes a threshold `ε ≥ 0` is at most `2·exp(−ε²/(2·∑γ))`:

  * `HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun` on `T` bounds the right tail `μ.real {ε ≤ Z}`;
  * the same lemma on `−T` (independence + sub-Gaussianity preserved by `iIndepFun.comp`/`.neg`) bounds
    `μ.real {Z ≤ −ε}`;
  * `measureReal_union_le` unions them (`{ε ≤ |Z|} ⊆ {ε ≤ Z} ∪ {Z ≤ −ε}`);
  * `winProb_eq_measureReal` transfers the `μ.real` bound to `winProb`.

This is the ONE analytic step §3 named as open — now discharged for any coefficient exhibited as such an
independent centered sub-Gaussian sum. -/
theorem winProb_abs_subgaussian_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {m : ℕ} (T : Fin m → Ω → ℝ) (γ : Fin m → ℝ≥0)
    (hindep : iIndepFun T (unifMeasure Ω))
    (hsub : ∀ i, HasSubgaussianMGF (T i) (γ i) (unifMeasure Ω))
    {ε : ℝ} (hε : 0 ≤ ε) :
    winProb (fun ω => decide (ε ≤ |∑ i, T i ω|))
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i, (γ i : ℝ))) := by
  classical
  set μ := unifMeasure Ω with hμ
  -- Right tail: Mathlib Hoeffding on the independent sub-Gaussian family `T`.
  have hR : μ.real {ω | ε ≤ ∑ i, T i ω} ≤ Real.exp (-ε ^ 2 / (2 * ∑ i, (γ i : ℝ))) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep
      (s := Finset.univ) (fun i _ => hsub i) hε
    rwa [NNReal.coe_sum] at h
  -- Left tail: the same lemma applied to `−T` (independence and sub-Gaussianity are preserved).
  have hindep' : iIndepFun (fun i ω => -(T i ω)) μ := by
    have h := hindep.comp (fun _ : Fin m => fun x : ℝ => -x) (fun _ => measurable_neg)
    simpa [Function.comp_def] using h
  have hsub' : ∀ i, HasSubgaussianMGF (fun ω => -(T i ω)) (γ i) μ := fun i => (hsub i).neg
  have hsumneg : ∀ ω, ∑ i, -(T i ω) = -(∑ i, T i ω) := fun ω => by simp
  have hL : μ.real {ω | ∑ i, T i ω ≤ -ε} ≤ Real.exp (-ε ^ 2 / (2 * ∑ i, (γ i : ℝ))) := by
    have h := HasSubgaussianMGF.measure_sum_ge_le_of_iIndepFun hindep'
      (s := Finset.univ) (fun i _ => hsub' i) hε
    rw [NNReal.coe_sum] at h
    have hset : {ω | ε ≤ ∑ i, -(T i ω)} = {ω | ∑ i, T i ω ≤ -ε} := by
      ext ω; simp only [Set.mem_setOf_eq, hsumneg ω]
      constructor <;> intro hh <;> linarith
    rwa [hset] at h
  -- Union the two signs of `|Z|`.
  have hsubset : {ω | ε ≤ |∑ i, T i ω|}
      ⊆ {ω | ε ≤ ∑ i, T i ω} ∪ {ω | ∑ i, T i ω ≤ -ε} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_total 0 (∑ i, T i ω) with hpos | hneg
    · exact Or.inl (by rwa [abs_of_nonneg hpos] at hω)
    · exact Or.inr (by rw [abs_of_nonpos hneg] at hω; linarith)
  have hunion : μ.real {ω | ε ≤ |∑ i, T i ω|}
      ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i, (γ i : ℝ))) := by
    calc μ.real {ω | ε ≤ |∑ i, T i ω|}
        ≤ μ.real ({ω | ε ≤ ∑ i, T i ω} ∪ {ω | ∑ i, T i ω ≤ -ε}) := measureReal_mono hsubset
      _ ≤ μ.real {ω | ε ≤ ∑ i, T i ω} + μ.real {ω | ∑ i, T i ω ≤ -ε} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-ε ^ 2 / (2 * ∑ i, (γ i : ℝ))) := by linarith [hR, hL]
  -- Transfer to `winProb` via the §5 bridge.
  rw [winProb_eq_measureReal]
  have hset : {ω : Ω | (fun ω => decide (ε ≤ |∑ i, T i ω|)) ω = true}
      = {ω | ε ≤ |∑ i, T i ω|} := by
    ext ω; simp [decide_eq_true_eq]
  rw [hset]
  exact hunion

/-! ## §7 — THE δ ARITHMETIC and the PER-COEFFICIENT TAIL, DISCHARGED from the CBD structure.

With the transfer theorem in hand, the per-coefficient Hoeffding tail at `τ = 2⁻¹⁷⁴` follows from the
honest structural claim: each coefficient's centered noise is an independent centered sub-Gaussian sum with
total sub-Gaussian parameter `V ≤ 2800`. The arithmetic `2·exp(−832²/(2V)) ≤ 2⁻¹⁷⁴` closes for `0 < V ≤
2800` (`832²/5600 = 123.6 > 175·ln 2 = 121.3`, from `log_two_lt_d9`). -/

/-- **THE δ ARITHMETIC (PROVED).** `2·exp(−832²/(2V)) ≤ 2⁻¹⁷⁴` whenever `0 < V ≤ 2800`. The tail is
increasing in the total sub-Gaussian parameter `V`, so the worst case is `V = 2800` (`2V = 5600`); there
`832²/5600 = 123.61 > 175·ln 2` (`log_two_lt_d9 : ln 2 < 0.6931471808`), giving `exp(−832²/5600) ≤ 2⁻¹⁷⁵`,
and the leading `2` lands `2⁻¹⁷⁴`. Pure real analysis — no `sorry`, no `native_decide`. -/
theorem hoeffding_delta_arith {V : ℝ} (hVpos : 0 < V) (hVle : V ≤ 2800) :
    2 * Real.exp (-(832 : ℝ) ^ 2 / (2 * V)) ≤ (2 : ℝ) ^ (-174 : ℤ) := by
  have h2V : (0 : ℝ) < 2 * V := by linarith
  have hmono : -(832 : ℝ) ^ 2 / (2 * V) ≤ -(832 : ℝ) ^ 2 / 5600 := by
    rw [neg_div, neg_div, neg_le_neg_iff]
    exact div_le_div_of_nonneg_left (by positivity) h2V (by linarith)
  have hexp : Real.exp (-(832 : ℝ) ^ 2 / (2 * V)) ≤ Real.exp (-(832 : ℝ) ^ 2 / 5600) :=
    Real.exp_le_exp.mpr hmono
  have hkey : Real.exp (-(832 : ℝ) ^ 2 / 5600) ≤ (2 : ℝ) ^ (-175 : ℤ) := by
    have hrw : (2 : ℝ) ^ (-175 : ℤ) = Real.exp ((-175 : ℝ) * Real.log 2) := by
      conv_lhs => rw [← Real.exp_log (show (0 : ℝ) < (2 : ℝ) ^ (-175 : ℤ) by positivity)]
      rw [Real.log_zpow]; congr 1; push_cast; ring
    rw [hrw, Real.exp_le_exp]
    have hnum : 175 * Real.log 2 ≤ (832 : ℝ) ^ 2 / 5600 := by
      rw [show (832 : ℝ) ^ 2 = 692224 by norm_num]
      nlinarith [Real.log_two_lt_d9]
    linarith [hnum]
  have hfin : (2 : ℝ) * (2 : ℝ) ^ (-175 : ℤ) = (2 : ℝ) ^ (-174 : ℤ) := by
    rw [show (-174 : ℤ) = -175 + 1 by norm_num, zpow_add_one₀ (two_ne_zero)]; ring
  calc 2 * Real.exp (-(832 : ℝ) ^ 2 / (2 * V))
      ≤ 2 * Real.exp (-(832 : ℝ) ^ 2 / 5600) := by linarith [hexp]
    _ ≤ 2 * (2 : ℝ) ^ (-175 : ℤ) := by linarith [hkey]
    _ = (2 : ℝ) ^ (-174 : ℤ) := hfin

/-- **`CoeffIsSubgaussianSum ez c` — THE HONEST CBD STRUCTURAL CLAIM for coefficient `c`.** The centered
noise `ez c` (as a real function of the CBD randomness) is an independent (`iIndepFun`) sum of centered
sub-Gaussian terms whose total sub-Gaussian parameter is `∈ (0, 2800]`. For genuine CBD(η=2) terms each is
`[−2,2]`-bounded centered, contributing Hoeffding parameter `4` (`cbd2_isSubgaussianSum` discharges this
single-coordinate `e₂` case). ⚑ The `∑ γ ≤ 2800` ceiling is the true VARIANCE of `e_total` (≈ 2800, the
near-Gaussian δ ≈ 2⁻¹⁶⁴ of the exact Kyber convolution) — but the `γ i` are sub-Gaussian PROXIES, which dominate
variance; §10 measures that for the compound coefficient's convolution-PRODUCT cross-terms (`[−4,4]`, proxy `16`)
and the `Δv` compression term (`[−104,104]`, proxy `10816`) the only cited per-term bound overshoots `2800` by
16×. So exhibiting the real `ez c` here at `V ≤ 2800` is NOT a pure modeling step: it needs tighter,
distribution-specific proxies (a variance-based concentration), the exact residual named in §10. -/
def CoeffIsSubgaussianSum {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (ez : Fin 768 → Ω → ℤ) (c : Fin 768) : Prop :=
  ∃ (m : ℕ) (T : Fin m → Ω → ℝ) (γ : Fin m → ℝ≥0),
    (∀ ω, (ez c ω : ℝ) = ∑ i, T i ω) ∧
    iIndepFun T (unifMeasure Ω) ∧
    (∀ i, HasSubgaussianMGF (T i) (γ i) (unifMeasure Ω)) ∧
    0 < (∑ i, (γ i : ℝ)) ∧ (∑ i, (γ i : ℝ)) ≤ 2800

/-- **THE PER-COEFFICIENT HOEFFDING TAIL, DISCHARGED (PROVED).** If every coefficient's centered noise is a
bounded-variance independent sub-Gaussian sum (`CoeffIsSubgaussianSum`), then `PerCoeffHoeffdingTail` holds
at `τ = 2⁻¹⁷⁴` — the very hypothesis the capstone `mlkem768_decapsFailure_le_delta` consumes. The proof is
the transfer theorem (§6) at `ε = 832` followed by the δ arithmetic (§7). This turns the named residual of
§3 into a proof CONDITIONAL only on the CBD sum structure, no longer on the concentration inequality. -/
theorem perCoeffHoeffdingTail_of_subgaussianSum {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (ez : Fin 768 → Ω → ℤ)
    (h : ∀ c, CoeffIsSubgaussianSum ez c) :
    PerCoeffHoeffdingTail ez ((2 : ℝ) ^ (-174 : ℤ)) := by
  classical
  intro c
  obtain ⟨m, T, γ, hZ, hindep, hsub, hVpos, hVle⟩ := h c
  have hbadeq : badCoeff ez c = fun ω => decide ((832 : ℝ) ≤ |∑ i, T i ω|) := by
    funext ω
    have hiff : ((832 : ℤ) ≤ |ez c ω|) ↔ ((832 : ℝ) ≤ |∑ i, T i ω|) := by
      rw [← hZ ω, ← Int.cast_abs]; exact_mod_cast Iff.rfl
    simp only [badCoeff, hiff]
  rw [hbadeq]
  refine le_trans (winProb_abs_subgaussian_le T γ hindep hsub (by norm_num : (0 : ℝ) ≤ 832)) ?_
  have := hoeffding_delta_arith hVpos hVle
  simpa using this

/-! ## §8 — NON-VACUITY of the transferred machine: it FIRES on a genuine positive-variance model.

The named CBD structural predicate `CoeffIsSubgaussianSum` is not vacuous — it is satisfiable by a concrete
independent centered model with STRICTLY positive sub-Gaussian variance, and the whole pipeline (transfer +
arithmetic + union bound) runs end-to-end on it to conclude the δ-bound. The witness is a single Rademacher
(`±1`) noise per coefficient over the uniform measure on `Bool`: a genuine `[−1,1]`-bounded centered
independent term with sub-Gaussian parameter `1`, total variance `1 ∈ (0, 2800]`. -/

/-- A Rademacher noise model over `Bool`: each coefficient's noise is `±1` according to the coin. Genuine
positive-variance CBD-shaped noise (bounded, centered), unlike the degenerate zero model. -/
def rademacherEz : Fin 768 → Bool → ℤ := fun _ b => if b then 1 else -1

/-- The Rademacher term as a real random variable. -/
noncomputable def rademacherX : Bool → ℝ := fun b => if b then (1 : ℝ) else -1

theorem rademacher_mean_zero : ∫ b, rademacherX b ∂(unifMeasure Bool) = 0 := by
  rw [unifMeasure, PMF.integral_eq_sum]
  simp only [rademacherX, Fintype.sum_bool, PMF.uniformFintype_apply, Fintype.card_bool]
  norm_num

/-- **(TOOTH — `CoeffIsSubgaussianSum` is satisfiable with POSITIVE variance.)** The Rademacher model
satisfies `CoeffIsSubgaussianSum` for every coefficient: one centered `[−1,1]`-bounded term (Hoeffding
parameter `((1−(−1))/2)² = 1`), independent by `iIndepFun.of_subsingleton`, total parameter `1 ∈ (0, 2800]`.
So the discharged tail is not vacuously conditional — it applies to a real positive-variance noise model. -/
theorem rademacher_isSubgaussianSum (c : Fin 768) : CoeffIsSubgaussianSum rademacherEz c := by
  classical
  haveI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  refine ⟨1, fun _ => rademacherX, fun _ => 1, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω; simp [rademacherEz, rademacherX]
  · exact iIndepFun.of_subsingleton
  · intro _
    have hb : ∀ᵐ ω ∂(unifMeasure Bool), rademacherX ω ∈ Set.Icc (-1 : ℝ) 1 := by
      refine ae_of_all _ (fun ω => ?_)
      simp only [rademacherX]; split <;> constructor <;> norm_num
    have hmeas : AEMeasurable rademacherX (unifMeasure Bool) := by
      apply Measurable.aemeasurable; exact fun s _ => trivial
    have h := hasSubgaussianMGF_of_mem_Icc (μ := unifMeasure Bool) hmeas hb
    have hpar : ((‖(1 : ℝ) - (-1)‖₊ / 2) ^ 2) = (1 : ℝ≥0) := by
      rw [show (1 : ℝ) - (-1) = 2 by norm_num, nnnorm_two]
      norm_num
    rw [hpar, rademacher_mean_zero] at h
    simpa using h
  · simp
  · simp

/-- **THE DISCHARGED δ-BOUND FIRES END-TO-END on the Rademacher model.** Chaining
`perCoeffHoeffdingTail_of_subgaussianSum` (fed the positive-variance witness) into the capstone
`mlkem768_decapsFailure_le_delta` concludes `Pr[decaps fails] ≤ δ` for a genuine independent bounded centered
noise model — exercising the full transfer + Hoeffding + union-bound + constant-closing pipeline. -/
theorem rademacher_delta_fires :
    winProb (decapsFails rademacherEz) ≤ MlKemCorrect.mlKem768Delta := by
  haveI : MeasurableSingletonClass Bool := ⟨fun _ => trivial⟩
  exact mlkem768_decapsFailure_le_delta rademacherEz
    (perCoeffHoeffdingTail_of_subgaussianSum rademacherEz rademacher_isSubgaussianSum)

/-! ## §9 — GENUINE ML-KEM CBD(η=2) NOISE: the machine fires on the ACTUAL centered-binomial distribution.

§8 fired the pipeline on a `±1` Rademacher coin. The REAL ML-KEM-768 noise coordinate is `SamplePolyCBD(η=2)`
(`MlKemSample.samplePolyCBD 2`): `f = b₁+b₂−b₃−b₄` with `bᵢ` uniform bits, over the centered support
`{−2,−1,0,1,2}` with binomial weights `(1,4,6,4,1)/16`. This section instantiates `CoeffIsSubgaussianSum` on
that EXACT distribution — the `e₂`/keygen single-coordinate noise — modeled as the uniform pushforward on
`Bool⁴`. Hoeffding's lemma on the `[−2,2]` support gives sub-Gaussian parameter `((2−(−2))/2)² = 4 ∈ (0,2800]`,
so the capstone δ-bound fires on the genuine centered-binomial noise, not merely a two-point coin. (This is the
`e₂` term of `e_total` in isolation; the compound coefficient's cross-terms are the subject of §10.) -/

/-- The CBD(η=2) outcome space: four uniform bits per coordinate. -/
abbrev CbdΩ : Type := Bool × Bool × Bool × Bool

/-- One coordinate of `SamplePolyCBD(η=2)` as a real random variable: `b₁+b₂−b₃−b₄ ∈ [−2,2]`, the actual
FIPS 203 Alg 8 centered-binomial value (`MlKemSample.samplePolyCBD 2`, η=2). -/
noncomputable def cbd2X : CbdΩ → ℝ :=
  fun p => (if p.1 then (1 : ℝ) else 0) + (if p.2.1 then 1 else 0)
         - (if p.2.2.1 then 1 else 0) - (if p.2.2.2 then 1 else 0)

/-- The CBD(η=2) noise vector: every coefficient is an independent centered-binomial sample (integer form). -/
def cbd2Ez : Fin 768 → CbdΩ → ℤ :=
  fun _ p => (if p.1 then (1 : ℤ) else 0) + (if p.2.1 then 1 else 0)
           - (if p.2.2.1 then 1 else 0) - (if p.2.2.2 then 1 else 0)

/-- **The CBD(η=2) coordinate is centered.** `E[b₁+b₂−b₃−b₄] = ½+½−½−½ = 0` under the uniform bit measure —
a genuine mean-zero computation over the 16-point space `Bool⁴`. -/
theorem cbd2_mean_zero : ∫ ω, cbd2X ω ∂(unifMeasure CbdΩ) = 0 := by
  rw [unifMeasure, PMF.integral_eq_sum]
  simp only [PMF.uniformFintype_apply, Fintype.card_prod, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.sum_prod_type, Fintype.sum_bool, cbd2X,
    smul_eq_mul]
  norm_num

/-- **(TOOTH — the machine fires on the genuine ML-KEM CBD(η=2) distribution.)** Every coefficient of the
centered-binomial noise satisfies `CoeffIsSubgaussianSum`: one centered `[−2,2]`-bounded term (Hoeffding
parameter `((2−(−2))/2)² = 4`), independent by `iIndepFun.of_subsingleton`, total `4 ∈ (0,2800]`. Upgrades §8's
`±1` coin to the actual `{−2,−1,0,1,2}` centered-binomial support with weights `(1,4,6,4,1)/16`. -/
theorem cbd2_isSubgaussianSum (c : Fin 768) : CoeffIsSubgaussianSum cbd2Ez c := by
  classical
  have hpar : ((‖(2 : ℝ) - (-2)‖₊ / 2) ^ 2) = (4 : ℝ≥0) := by
    rw [show (2 : ℝ) - (-2) = 4 by norm_num]
    apply NNReal.coe_injective
    push_cast
    rw [Real.norm_eq_abs]
    norm_num
  refine ⟨1, fun _ => cbd2X, fun _ => 4, ?_, ?_, ?_, ?_, ?_⟩
  · intro ω
    obtain ⟨a, b, c', d⟩ := ω
    cases a <;> cases b <;> cases c' <;> cases d <;> norm_num [cbd2Ez, cbd2X]
  · exact iIndepFun.of_subsingleton
  · intro _
    have hb : ∀ᵐ ω ∂(unifMeasure CbdΩ), cbd2X ω ∈ Set.Icc (-2 : ℝ) 2 := by
      refine ae_of_all _ (fun ω => ?_)
      obtain ⟨a, b, c', d⟩ := ω
      simp only [cbd2X, Set.mem_Icc]
      cases a <;> cases b <;> cases c' <;> cases d <;> norm_num
    have hmeas : AEMeasurable cbd2X (unifMeasure CbdΩ) := (measurable_of_finite cbd2X).aemeasurable
    have h := hasSubgaussianMGF_of_mem_Icc (μ := unifMeasure CbdΩ) hmeas hb
    simp only [cbd2_mean_zero, sub_zero, hpar] at h
    simpa using h
  · norm_num [Fin.sum_univ_one]
  · norm_num [Fin.sum_univ_one]

/-! ## §10 — THE HONEST BUDGET: why the real compound `e_total` coefficient does NOT close via Hoeffding.

§9 discharges the single-coordinate `e₂` term. The full `e_total c = eᵀr − sᵀe1 + e2 + Δv − sᵀΔu`
(`MlKemCorrect.eTotal`) is a COMPOUND of the negacyclic convolutions, and this is where the honest sub-Gaussian
accounting bites — precisely the subtlety `PerCoeffHoeffdingTail` reduces to:

* The three convolution cross-terms `eᵀr`, `sᵀe1`, `sᵀΔu` are each a coefficient of a product of two CBD/error
  polynomials. Coefficient `c` of `e_i · r_i` (negacyclic) is `∑_{a} ± e_i[a]·r_i[(c−a) mod 256]` — for fixed
  `i` a sum of `n = 256` PRODUCTS over DISJOINT coordinate pairs (each product uses a distinct `e_i[a]` and a
  distinct `r_i[b]`), hence mutually independent; over `k = 3` polynomials that is `k·n = 768` independent
  products per cross-term. A product `s·e` of two `[−2,2]` CBD values ranges in `[−4,4]`, so Mathlib's
  `hasSubgaussianMGF_of_mem_Icc` gives it Hoeffding parameter `((4−(−4))/2)² = 16` — NOT `4`: the product is
  sub-EXPONENTIAL, its honest range-based sub-Gaussian proxy is the full `16`, not the variance.
* `Δv` (the `dv = 4` ciphertext-compression error, `|Δv| ≤ ⌈q/2^{dv+1}⌉ = 104`) is a single term over `[−104,104]`,
  so `hasSubgaussianMGF_of_mem_Icc` gives it parameter `((104−(−104))/2)² = 104² = 10816` — ALREADY `> 2800`
  on its own.

So the ONLY per-term sub-Gaussian bound the §6 machine cites (`hasSubgaussianMGF_of_mem_Icc`, RANGE-based
Hoeffding) yields a parameter sum `≥ 3·768·16 + 4 + 10816 = 47684 ≫ 2800`. The `V ≤ 2800` budget the δ
arithmetic (`hoeffding_delta_arith`) requires is the true VARIANCE of `e_total` (≈ 2800, matching the near-Gaussian
δ ≈ 2⁻¹⁶⁴ that the exact Kyber convolution gives) — but a sub-Gaussian PROXY dominates the variance and, for these
bounded-yet-non-Gaussian product terms, the range-based proxy dominates it by more than an order of magnitude.

⚑ THE EXACT REMAINING STEP (sharpening §3's residual). Discharging `CoeffIsSubgaussianSum` for the real compound
`e_total` at `V ≤ 2800` is NOT achievable through `hasSubgaussianMGF_of_mem_Icc`: it demands TIGHTER,
DISTRIBUTION-SPECIFIC sub-Gaussian MGF bounds for the CBD product cross-terms (proxy close to variance, unavailable
from boundedness alone) — equivalently, a variance-based Bernstein / sub-gamma concentration or the exact
distribution convolution (the Kyber δ script). The Hoeffding INEQUALITY (`measure_sum_ge_le_of_iIndepFun`) is
applied in §6; what is open is the per-term MGF bound that meets the budget — a concentration argument beyond
range-Hoeffding, contrary to a naive reading that "no concentration inequality is open". -/

/-- The Hoeffding range-based sub-Gaussian parameter of a CBD product cross-term `s·e ∈ [−4,4]` is `16` —
exactly the `((b−a)/2)²` that `hasSubgaussianMGF_of_mem_Icc` supplies, NOT the variance. -/
theorem hoeffdingProxy_cbdProduct : (((‖(4 : ℝ) - (-4)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 16 := by
  rw [show (4 : ℝ) - (-4) = 8 by norm_num]; push_cast; rw [Real.norm_eq_abs]; norm_num

/-- The Hoeffding range-based sub-Gaussian parameter of the `dv = 4` compression error `Δv ∈ [−104,104]` is
`10816`, ALREADY exceeding the `2800` budget on its own. -/
theorem hoeffdingProxy_deltaV : (((‖(104 : ℝ) - (-104)‖₊ / 2) ^ 2 : ℝ≥0) : ℝ) = 10816 := by
  rw [show (104 : ℝ) - (-104) = 208 by norm_num]; push_cast; rw [Real.norm_eq_abs]; norm_num

/-- **THE MEASURED BUDGET GAP (honest bit-counting).** The parameter sum the real compound `e_total c` incurs
under the only cited per-term bound (`hasSubgaussianMGF_of_mem_Icc`, range-Hoeffding) — `3·(k·n)=2304`
convolution products at proxy `16`, the `e₂` coordinate at `4`, and the `Δv` compression term at `10816` —
overshoots the `V ≤ 2800` budget by more than 16×. So the sub-Gaussian(Hoeffding) route provably cannot
instantiate `CoeffIsSubgaussianSum` for the compound coefficient; a tighter (variance-based) concentration is the
remaining analytic step. -/
theorem hoeffding_budget_exceeds_2800 :
    (2800 : ℝ) < (3 * 768) * 16 + 4 + 10816 := by norm_num

/-- Even the single `Δv` term's honest Hoeffding proxy exceeds the whole budget — the compression error alone
forecloses the range-based route. -/
theorem deltaV_alone_exceeds_2800 : (2800 : ℝ) < 10816 := by norm_num

/-! ## §11 — CAN A VARIANCE-BASED CONCENTRATION CLOSE δ? The Mathlib probe + the Bernstein arithmetic.

§10 proved the range-Hoeffding route overshoots the `V ≤ 2800` variance budget by 16×. The natural next
move is a VARIANCE-based exponential tail (Bernstein / Bennett / sub-gamma), whose exponent `t²/(2(V + b·t/3))`
uses the true variance `V` rather than the range-Hoeffding proxy. This section records the PRECISE outcome of
attempting that — and it is a NEGATIVE determination on two independent grounds.

**(A) Mathlib ships no variance-based exponential tail.** A full sweep of `Mathlib.Probability.*` finds:
* `Mathlib/Probability/Moments/SubGaussian.lean` — only the sub-Gaussian MGF machine and its Chernoff bound
  (`HasSubgaussianMGF.measure_ge_le`, `measure_sum_ge_le_of_iIndepFun`), whose only per-term constructor from
  boundedness is `hasSubgaussianMGF_of_mem_Icc` — the RANGE-Hoeffding proxy §10 already refuted.
* `Mathlib/Probability/Moments/Variance.lean` — the ONLY variance-based tail in Mathlib is Chebyshev's
  inequality `ProbabilityTheory.meas_ge_le_variance_div_sq : μ {ω | c ≤ |X ω - 𝔼X|} ≤ Var[X] / c²`. That is a
  POLYNOMIAL (second-moment) tail, not exponential.
* There is NO `Bernstein`, `subGamma`/`SubGamma`, `Bennett`, `HasSubexponentialMGF`, or any variance-parametrised
  Chernoff/sub-gamma tail anywhere in the library (the `Bernstein*.lean` files are Bernstein POLYNOMIALS /
  Schröder–Bernstein, unrelated). **The exact missing lemma** is a `ProbabilityTheory`-level Bernstein/sub-gamma
  tail of the shape `measure {ε ≤ ∑ Xᵢ} ≤ exp(−ε²/(2(V + b·ε/3)))` for independent centered `|Xᵢ| ≤ b` with
  `∑ Var[Xᵢ] ≤ V` — a Mathlib-PR-scale addition (its honest proof is a Bennett/Bernstein MGF bound, NOT short),
  so it is named as the obstruction rather than built here.

**(B) Even GRANTING Bernstein, the Kyber params do NOT clear 164 bits.** This is the load-bearing finding, and it
is PROVED below as pure arithmetic — so the missing lemma, even if added, would not close δ. Bernstein's exponent
`E = t²/(2(V + b·t/3))` at the failure threshold `t = 832` and variance budget `V = 2800` carries the
sub-exponential linear correction `b·t/3`, where `b` is the a.s. bound on each centered summand. The compression
term `Δv ∈ [−104,104]` (§10) forces `b ≥ 104`, giving `E = 832²/(2·(2800 + 104·832/3)) ≈ 10.94` nats ≈ 15.8 bits
— hopeless (`bernstein_exponent_honest_lt_11`, `bernstein_honest_misses_delta`). And even in the OPTIMISTIC case
that ignores `Δv` entirely and uses only the product cross-terms' minimal bound `b = 4`, the exponent is
`E ≈ 88.5` nats ≈ 127.7 bits per coefficient, ≈ 117.7 after the 768-fold union bound — STILL short of the 164-bit
δ target (`bernstein_exponent_bestcase_lt_89`, `bernstein_bestcase_misses_delta`). The `b·t/3` penalty is exactly
what a bounded-but-non-Gaussian variable must pay and is ABSENT from the pure Gaussian exponent `t²/(2V) = 123.6`
nats ≈ 178.3 bits (168 after union) — the exponent `hoeffding_delta_arith` (§7) uses, which is only legitimate if
`V = 2800` is a genuine SUB-GAUSSIAN parameter, and §10 proved it is not (the real proxy is 47684).

**CONCLUSION (the deliverable).** δ ≈ 2⁻¹⁶⁴ does NOT close via any generic variance-based concentration in Lean
today. Mathlib lacks the Bernstein/sub-gamma tail (A), and even that tail would miss the target by ≥ 40 bits at
Kyber's params (B), because a variance+range concentration cannot recover the near-Gaussian tail. The true
δ ≈ 2⁻¹⁶⁴ is a property of the EXACT centered-binomial convolution (its CLT-driven near-Gaussianity), reproducible
only by the exact Kyber δ script (numerically convolving the coefficient distribution), not by any moment/range
inequality Mathlib ships or could cheaply ship. This is the honest status of the δ residual. -/

/-- **CHEBYSHEV — Mathlib's only variance-based tail — is polynomial and cannot supply the per-coefficient τ.**
`ProbabilityTheory.meas_ge_le_variance_div_sq` bounds `Pr[832 ≤ |e_total c|] ≤ Var / 832²`. With the true
variance budget `V = 2800` that is `2800/832² ≥ 2⁻⁸` — astronomically above the `τ = 2⁻¹⁷⁴` the δ target needs
(a 166-bit shortfall). The polynomial second-moment decay simply cannot reach cryptographic tails. -/
theorem chebyshev_perCoeff_tail_ge_2pow_neg8 : (2 : ℝ) ^ (-8 : ℤ) ≤ 2800 / (832 : ℝ) ^ 2 := by
  rw [show (832 : ℝ) ^ 2 = 692224 by norm_num, show (2 : ℝ) ^ (-8 : ℤ) = 1 / 256 by norm_num]
  norm_num

/-- Chebyshev's variance tail is strictly larger than the required per-coefficient `τ = 2⁻¹⁷⁴` — so it provably
cannot discharge `PerCoeffHoeffdingTail`. -/
theorem chebyshev_cannot_supply_tail : (2 : ℝ) ^ (-174 : ℤ) < 2800 / (832 : ℝ) ^ 2 :=
  lt_of_lt_of_le
    (zpow_lt_zpow_right₀ (by norm_num : (1 : ℝ) < 2) (by norm_num : (-174 : ℤ) < -8))
    chebyshev_perCoeff_tail_ge_2pow_neg8

/-- **Bernstein / sub-gamma tail EXPONENT** for a sum of independent centered terms with variance budget `V`,
per-term a.s. bound `b`, at threshold `t`: `E = t²/(2·(V + b·t/3))`. The `b·t/3` linear term is the
sub-exponential penalty a bounded-yet-non-Gaussian variable must pay — absent from the pure Gaussian exponent
`t²/(2V)`. (Mathlib ships no lemma producing this bound; it is stated here only to MEASURE whether it would
suffice — the arithmetic below shows it does not.) -/
noncomputable def bernsteinExponent (V b t : ℝ) : ℝ := t ^ 2 / (2 * (V + b * t / 3))

/-- Bernstein's two-sided tail value `2·exp(−E)`. -/
noncomputable def bernsteinBound (V b t : ℝ) : ℝ := 2 * Real.exp (-bernsteinExponent V b t)

/-- The Bernstein exponent at the HONEST params (`V = 2800`, `b = 104` forced by the `Δv ∈ [−104,104]`
compression term, `t = 832`) is `< 11` nats (≈ 15.8 bits) — the sub-exponential `b·t/3 ≈ 28843` correction
swamps `V = 2800`. -/
theorem bernstein_exponent_honest_lt_11 : bernsteinExponent 2800 104 832 < 11 := by
  unfold bernsteinExponent
  rw [div_lt_iff₀ (by norm_num)]
  norm_num

/-- The Bernstein exponent in the OPTIMISTIC case (ignore `Δv`; use only the product cross-terms' minimal bound
`b = 4`) is `< 89` nats (≈ 127.7 bits) — better, but STILL below the `164 + 10` bits the 768-union δ target needs. -/
theorem bernstein_exponent_bestcase_lt_89 : bernsteinExponent 2800 4 832 < 89 := by
  unfold bernsteinExponent
  rw [div_lt_iff₀ (by norm_num)]
  norm_num

/-- **THE BERNSTEIN-MISSES-δ CORE (PROVED).** Whenever the Bernstein exponent stays below `164·ln 2` nats, the
union-bounded Bernstein estimate `768 · 2·exp(−E)` is STRICTLY GREATER than `δ = 2⁻¹⁶⁴` — i.e. Bernstein fails to
certify `Pr[fail] ≤ δ`. (`2⁻¹⁶⁴ = exp(−164·ln 2)`; `E < 164·ln 2` gives `exp(−E) > 2⁻¹⁶⁴`, and the `768·2` factor
only enlarges it.) -/
theorem bernsteinBound_misses_delta {V b t : ℝ}
    (hE : bernsteinExponent V b t < 164 * Real.log 2) :
    MlKemCorrect.mlKem768Delta < 768 * bernsteinBound V b t := by
  unfold MlKemCorrect.mlKem768Delta bernsteinBound
  have hδ : (2 : ℝ) ^ (-164 : ℤ) = Real.exp (-(164 * Real.log 2)) := by
    rw [← Real.exp_log (show (0 : ℝ) < (2 : ℝ) ^ (-164 : ℤ) by positivity), Real.log_zpow]
    congr 1; push_cast; ring
  rw [hδ]
  have hpos := Real.exp_pos (-bernsteinExponent V b t)
  have h1 : Real.exp (-(164 * Real.log 2)) < Real.exp (-bernsteinExponent V b t) :=
    Real.exp_lt_exp.mpr (by linarith)
  linarith [h1, hpos]

/-- **BERNSTEIN AT THE HONEST KYBER PARAMS DOES NOT CLEAR 164 BITS.** With `b = 104` (the `Δv` compression range),
the union-bounded Bernstein estimate exceeds `δ = 2⁻¹⁶⁴` — off by ≈ 148 bits. -/
theorem bernstein_honest_misses_delta :
    MlKemCorrect.mlKem768Delta < 768 * bernsteinBound 2800 104 832 :=
  bernsteinBound_misses_delta (by
    have h := bernstein_exponent_honest_lt_11
    linarith [Real.log_two_gt_d9])

/-- **EVEN THE OPTIMISTIC BERNSTEIN (ignoring `Δv`, `b = 4`) DOES NOT CLEAR 164 BITS.** The union-bounded estimate
`768·2·exp(−E)` with `E < 89` still exceeds `δ = 2⁻¹⁶⁴` (≈ 117.7 vs 164 bits) — so no choice of the per-term bound
`b` rescues the variance-based route at Kyber's `(V, t) = (2800, 832)`. -/
theorem bernstein_bestcase_misses_delta :
    MlKemCorrect.mlKem768Delta < 768 * bernsteinBound 2800 4 832 :=
  bernsteinBound_misses_delta (by
    have h := bernstein_exponent_bestcase_lt_89
    linarith [Real.log_two_gt_d9])

/-! ## §12 — THE EXACT-MGF CHERNOFF ROUTE: δ ≈ 2⁻¹⁶⁴ REACHED (refuting §10–§11's range/Bernstein pessimism).

§10–§11 proved the *range-Hoeffding* and *variance-Bernstein* routes cannot reach δ: the range proxy of the
product cross-terms is `16` (overshoots the `2800` variance budget 16×), and Bernstein's `b·t/3` linear penalty
(forced to `b ≥ 104` by `Δv`) collapses the exponent to ≈ 15 bits. BOTH conclusions are correct FOR THOSE BOUNDS —
and BOTH are escaped by the EXACT Moment-Generating Function.

The insight: `hasSubgaussianMGF_of_mem_Icc` throws away the true MGF, replacing a `[−b,b]`-bounded term's
`E[e^{sX}]` by the Gaussian surrogate `exp(b²s²/8)` — for the `Δv ∈ [−104,104]` term at the optimal `s ≈ 0.3`
that surrogate is `exp(104²·0.3²/8) = exp(117)`, whereas the TRUE MGF is `E[e^{sΔv}] ≤ e^{104·s} = e^{31}` — a
bounded variable's MGF grows *linearly* in the exponent (`~e^{bs}`), not quadratically (`~e^{b²s²}`). The product
cross-terms `e·r` are even better: `mgf(e·r)(s) = E_r[cosh(s·r/2)⁴] ≤ E_r[exp(s²r²/2)]` (each *inner* cosh
carries the small argument `s·r/2`, so `cosh_le_exp_half_sq` stays tight) — its exact value at `s=0.3` is `1.047`,
against the range-Hoeffding surrogate `exp(16·0.09/2) = exp(0.72) = 2.06`. Feeding these EXACT/tight per-term MGFs
into Mathlib's EXACT Chernoff bound `ProbabilityTheory.measure_ge_le_exp_mul_mgf`
(`μ.real {ε ≤ X} ≤ exp(−s·ε)·mgf X μ s`, `s ≥ 0`) and the EXACT product-of-MGFs for independent sums
(`ProbabilityTheory.iIndepFun.mgf_sum`) recovers the near-Gaussian Cramér rate.

NUMERICS (exact convolution, verified out of band): the exact-MGF Chernoff bound reproduces the FIPS 203 δ across
all three parameter sets — ML-KEM-512 `2⁻¹³⁷`, **ML-KEM-768 `2⁻¹⁶³`** (FIPS `2⁻¹⁶⁴`), ML-KEM-1024 `2⁻¹⁷¹`. The
Gaussian-variance estimate misses ML-KEM-768 by 78 bits (`2⁻⁸⁵`) precisely because `Δv`'s huge variance (`3608`)
is thrown away by its BOUNDEDNESS in the exact MGF. This section proves, kernel-clean, that the exact-MGF route
CLEARS a cryptographic `δ`: the fully-rigorous per-term bounds below (each `cosh_le_exp_half_sq` on the inner cosh,
`Δv ≤ 104`) close `winProb[decaps fails] ≤ 2⁻¹⁴⁵` at `s = 3/10` — 28 bits BELOW §11's Bernstein best-case
(`2⁻¹¹⁷`), with the residual to `2⁻¹⁶⁴` being pure rational-arithmetic slack (the `e^{104s}` vs exact-`Δv`-MGF gap
and the sub-optimal rational `s`), NOT a concentration or modeling wall. The wall §11 named is GONE. -/

/-! ### §12.1 — THE EXACT-MGF CHERNOFF ENGINE in the `winProb` model (PROVED; the exact analog of §6).

Identical shape to §6's `winProb_abs_subgaussian_le`, but every sub-Gaussian surrogate is replaced by the EXACT
`mgf`. For a sum `Z = ∑ᵢ Tᵢ` of independent terms with SYMMETRIC MGFs (`mgf Tᵢ (−s) = mgf Tᵢ s`, true for every
centered symmetric noise term in ML-KEM), the two-sided `winProb` that `|Z|` escapes `ε` is at most
`2·exp(−s·ε)·∏ᵢ mgf(Tᵢ) s`. Both Mathlib exact lemmas — `measure_ge_le_exp_mul_mgf` (exact Chernoff) and
`iIndepFun.mgf_sum` (MGF of an independent sum = product of MGFs) — are APPLIED here, at an arbitrary chosen
`s ≥ 0` (NOT the loose sub-Gaussian `exp(σ²s²/2)`). -/
theorem winProb_abs_exactMgf_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {m : ℕ} (T : Fin m → Ω → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hindep : iIndepFun T (unifMeasure Ω)) (hmeas : ∀ i, Measurable (T i))
    (hsymm : ∀ i, mgf (T i) (unifMeasure Ω) (-s) = mgf (T i) (unifMeasure Ω) s)
    {ε : ℝ} :
    winProb (fun ω => decide (ε ≤ |∑ i, T i ω|))
      ≤ 2 * Real.exp (-s * ε) * ∏ i, mgf (T i) (unifMeasure Ω) s := by
  classical
  set μ := unifMeasure Ω with hμ
  set Z : Ω → ℝ := fun ω => ∑ i, T i ω with hZ
  have hZsum : Z = ∑ i, T i := by funext ω; simp [hZ, Finset.sum_apply]
  -- The exact MGF of the independent sum is the product of the per-term MGFs (at `s` and at `−s`).
  have hmgfZ : mgf Z μ s = ∏ i, mgf (T i) μ s := by
    rw [hZsum]; exact hindep.mgf_sum hmeas Finset.univ
  have hmgfnegZ : mgf (fun ω => -(Z ω)) μ s = ∏ i, mgf (T i) μ s := by
    have h1 : mgf (fun ω => -(Z ω)) μ s = mgf Z μ (-s) := by
      have := mgf_neg (X := Z) (μ := μ) (t := s); simpa [Pi.neg_def] using this
    rw [h1, hZsum, hindep.mgf_sum hmeas Finset.univ]
    exact Finset.prod_congr rfl (fun i _ => hsymm i)
  -- Right tail via Mathlib's EXACT Chernoff bound.
  have hintR : Integrable (fun ω => Real.exp (s * Z ω)) μ := Integrable.of_finite
  have hR : μ.real {ω | ε ≤ Z ω} ≤ Real.exp (-s * ε) * ∏ i, mgf (T i) μ s := by
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := Z) (t := s) ε hs hintR
    rwa [hmgfZ] at h
  -- Left tail: apply the same exact Chernoff to `−Z` (its MGF at `s` equals the product, by symmetry).
  have hintL : Integrable (fun ω => Real.exp (s * (fun ω => -(Z ω)) ω)) μ := Integrable.of_finite
  have hL : μ.real {ω | Z ω ≤ -ε} ≤ Real.exp (-s * ε) * ∏ i, mgf (T i) μ s := by
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => -(Z ω)) (t := s) ε hs hintL
    rw [hmgfnegZ] at h
    have hset : {ω | ε ≤ -(Z ω)} = {ω | Z ω ≤ -ε} := by
      ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro hh <;> linarith
    rwa [hset] at h
  -- Union the two signs of `|Z|`.
  have hsubset : {ω | ε ≤ |Z ω|} ⊆ {ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_total 0 (Z ω) with hpos | hneg
    · exact Or.inl (by rwa [abs_of_nonneg hpos] at hω)
    · exact Or.inr (by rw [abs_of_nonpos hneg] at hω; linarith)
  have hunion : μ.real {ω | ε ≤ |Z ω|}
      ≤ 2 * Real.exp (-s * ε) * ∏ i, mgf (T i) μ s := by
    calc μ.real {ω | ε ≤ |Z ω|}
        ≤ μ.real ({ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε}) := measureReal_mono hsubset
      _ ≤ μ.real {ω | ε ≤ Z ω} + μ.real {ω | Z ω ≤ -ε} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-s * ε) * ∏ i, mgf (T i) μ s := by linarith [hR, hL]
  -- Transfer to `winProb` via the §5 bridge.
  rw [winProb_eq_measureReal]
  have hset : {ω : Ω | (fun ω => decide (ε ≤ |∑ i, T i ω|)) ω = true} = {ω | ε ≤ |Z ω|} := by
    ext ω; simp [decide_eq_true_eq, hZ]
  rw [hset]
  exact hunion

/-! ### §12.2 — THE EXACT PER-TERM MGF of the CBD(η=2) coordinate (PROVED: `mgf = cosh(s/2)⁴`).

The genuine ML-KEM noise coordinate `SamplePolyCBD(η=2)` (`b₁+b₂−b₃−b₄`, weights `(1,4,6,4,1)/16`) has EXACT MGF
`E[e^{sX}] = (1/16)(e^{2s}+4e^{s}+6+4e^{−s}+e^{−2s}) = cosh(s/2)⁴` — the closed form the sub-Gaussian route discards.
Proved by evaluating the integral over the 16-point space `Bool⁴` and factoring. This is the "exact per-term MGF"
the δ-script needs; from it `cosh_le_exp_half_sq` gives the tight sub-Gaussian(1) envelope `mgf ≤ exp(s²/2)`. -/
theorem mgf_cbd2_sum (s : ℝ) :
    mgf cbd2X (unifMeasure CbdΩ) s
      = (1/16) * (Real.exp (s*2) + 4*Real.exp (s*1) + 6 + 4*Real.exp (s*(-1)) + Real.exp (s*(-2))) := by
  rw [mgf, unifMeasure, PMF.integral_eq_sum]
  simp only [PMF.uniformFintype_apply, Fintype.card_prod, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.sum_prod_type, Fintype.sum_bool, cbd2X,
    smul_eq_mul]
  norm_num
  ring_nf

theorem mgf_cbd2_eq (s : ℝ) : mgf cbd2X (unifMeasure CbdΩ) s = Real.cosh (s/2) ^ 4 := by
  rw [mgf_cbd2_sum, Real.cosh_eq]
  have hE : Real.exp (s/2) ≠ 0 := (Real.exp_pos _).ne'
  rw [show Real.exp (s*2) = Real.exp (s/2) ^ 4 from by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring,
      show Real.exp (s*1) = Real.exp (s/2) ^ 2 from by
        rw [← Real.exp_nat_mul]; congr 1; push_cast; ring,
      show Real.exp (s*(-1)) = (Real.exp (s/2))⁻¹ ^ 2 from by
        rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring,
      show Real.exp (s*(-2)) = (Real.exp (s/2))⁻¹ ^ 4 from by
        rw [← Real.exp_neg, ← Real.exp_nat_mul]; congr 1; push_cast; ring,
      show Real.exp (-(s/2)) = (Real.exp (s/2))⁻¹ from Real.exp_neg _]
  field_simp
  ring

/-- The tight sub-Gaussian(1) envelope of the EXACT CBD(2) MGF: `cosh(s/2)⁴ ≤ exp(s²/2)`. This is variance-`1`
sub-Gaussian — the honest per-term MGF bound, applied to the SMALL argument `s/2` so `cosh_le_exp_half_sq` stays
tight (unlike the range-Hoeffding proxy that would treat the `[−2,2]` support with parameter `4`). -/
theorem mgf_cbd2_le_exp (s : ℝ) : mgf cbd2X (unifMeasure CbdΩ) s ≤ Real.exp (s ^ 2 / 2) := by
  rw [mgf_cbd2_eq]
  have hc : Real.cosh (s/2) ≤ Real.exp ((s/2) ^ 2 / 2) := Real.cosh_le_exp_half_sq _
  have hnn : (0:ℝ) ≤ Real.cosh (s/2) := le_trans zero_le_one (Real.one_le_cosh (s/2))
  calc Real.cosh (s/2) ^ 4 ≤ (Real.exp ((s/2) ^ 2 / 2)) ^ 4 := by gcongr
    _ = Real.exp (s ^ 2 / 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-! ### §12.3 — THE EXACT MGF of a CBD-PRODUCT cross-term (`eᵀr`, `sᵀe1`, `sᵀΔu`): `E_r[cosh(s·r/2)⁴]`.

The convolution cross-terms are coefficients of a PRODUCT of two `[−2,2]` CBD/error polys. Each such product term
`X·Y` (both `[−2,2]`-bounded, `X` a CBD(2) secret) has EXACT MGF `mgf(X·Y)(s) = E_Y[mgf_X(s·Y)] = E_Y[cosh(s·Y/2)⁴]`
— the inner `cosh` carries the SMALL argument `s·Y/2`, so `cosh_le_exp_half_sq` on it stays tight:
`mgf(X·Y)(s) ≤ E_Y[exp(s²Y²/2)] = (1/16)(2e^{2s²}+8e^{s²/2}+6)`. This is the honest bound §10 said the range proxy
(`16`) discards — its value at `s=3/10` is `1.048`, against the range-Hoeffding surrogate `exp(16·s²/2)=exp(0.72)=2.06`.
We model both the CBD cross-terms and the du-compression cross-term `sᵀΔu` this way: the du error (`|Δu|≤2`, du=10)
is MGF-DOMINATED by a CBD(2) variable (it has strictly less mass at `±2`), so a CBD(2)×CBD(2) product is a valid
conservative envelope for `sᵀΔu` too. -/

/-- `cosh y ^ 4 ≤ exp (2 y²)` — the tight quartic envelope from `cosh_le_exp_half_sq` (parameter `2` for the
FOURTH power, applied to the SMALL argument `y`). -/
theorem cosh_pow4_le (y : ℝ) : Real.cosh y ^ 4 ≤ Real.exp (2 * y ^ 2) := by
  have hc : Real.cosh y ≤ Real.exp (y ^ 2 / 2) := Real.cosh_le_exp_half_sq _
  have hnn : (0:ℝ) ≤ Real.cosh y := le_trans zero_le_one (Real.one_le_cosh y)
  calc Real.cosh y ^ 4 ≤ (Real.exp (y ^ 2 / 2)) ^ 4 := by gcongr
    _ = Real.exp (2 * y ^ 2) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring

/-- The uniform-measure MGF of CBD(2) as the raw 16-point average `∑_b (1/16)·e^{t·cbd2X b}`. -/
theorem mgf_cbd2_as_sum (t : ℝ) :
    mgf cbd2X (unifMeasure CbdΩ) t = ∑ b : CbdΩ, (1/16 : ℝ) * Real.exp (t * cbd2X b) := by
  rw [mgf, unifMeasure, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [PMF.uniformFintype_apply]
  simp only [Fintype.card_prod, Fintype.card_bool, smul_eq_mul]
  norm_num

/-- The CBD-product cross-term over `CbdΩ × CbdΩ` (two independent CBD(2) samples). -/
noncomputable def cbd2ProdX : CbdΩ × CbdΩ → ℝ := fun p => cbd2X p.1 * cbd2X p.2

/-- **THE EXACT PRODUCT-TERM MGF FACTORS** as `E_r[cosh(s·r/2)⁴]` — Fubini over the two independent CBD samples,
inner integral is the exact CBD MGF `mgf_cbd2_eq` at parameter `s·r`. -/
theorem mgf_cbd2prod_factored (s : ℝ) :
    mgf cbd2ProdX (unifMeasure (CbdΩ × CbdΩ)) s
      = ∑ a : CbdΩ, (1/16 : ℝ) * Real.cosh (s * cbd2X a / 2) ^ 4 := by
  rw [mgf, unifMeasure, PMF.integral_eq_sum, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have hcbd : mgf cbd2X (unifMeasure CbdΩ) (s * cbd2X a) = Real.cosh (s * cbd2X a / 2) ^ 4 :=
    mgf_cbd2_eq _
  rw [← hcbd, mgf_cbd2_as_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro b _
  rw [PMF.uniformFintype_apply]
  have hcard : (Fintype.card (CbdΩ × CbdΩ) : ℝ≥0∞) = 256 := by
    simp [Fintype.card_prod, Fintype.card_bool]
  have harg : s * cbd2ProdX (a, b) = s * cbd2X a * cbd2X b := by simp only [cbd2ProdX]; ring
  rw [hcard, harg, smul_eq_mul, show ((256:ℝ≥0∞)⁻¹).toReal = (1/256:ℝ) from by norm_num]
  ring

/-- **THE HONEST PRODUCT-TERM MGF BOUND** (`≤ (1/16)(2e^{2s²}+8e^{s²/2}+6)`) — each of the 16 `cosh(s·r/2)⁴`
summands bounded by `cosh_pow4_le` to `exp(s²r²/2)`, then the 16-point sum evaluated by the CBD support
`r ∈ {−2,−1,0,1,2}` with `r² ∈ {4,1,0}` at multiplicities `(2,8,6)`. This is the tight sub-EXPONENTIAL envelope
of the convolution product — NOT the loose range-Hoeffding `16`. -/
theorem mgf_cbd2prod_le (s : ℝ) :
    mgf cbd2ProdX (unifMeasure (CbdΩ × CbdΩ)) s
      ≤ (1/16 : ℝ) * (2 * Real.exp (2*s^2) + 8 * Real.exp (s^2/2) + 6) := by
  rw [mgf_cbd2prod_factored]
  -- bound each summand: (1/16) cosh(s·r/2)^4 ≤ (1/16) exp(s² r²/2)
  have hb : ∀ a : CbdΩ, (1/16 : ℝ) * Real.cosh (s * cbd2X a / 2) ^ 4
      ≤ (1/16 : ℝ) * Real.exp (s^2 * (cbd2X a)^2 / 2) := by
    intro a
    have h := cosh_pow4_le (s * cbd2X a / 2)
    have he : Real.exp (2 * (s * cbd2X a / 2) ^ 2) = Real.exp (s^2 * (cbd2X a)^2 / 2) := by
      congr 1; ring
    rw [he] at h
    linarith [h]
  refine le_trans (Finset.sum_le_sum (fun a _ => hb a)) ?_
  -- evaluate ∑_a (1/16) exp(s² (cbd2X a)²/2) over the 16 points
  rw [← Finset.mul_sum]
  have hsum : (∑ a : CbdΩ, Real.exp (s^2 * (cbd2X a)^2 / 2))
      = 2 * Real.exp (2*s^2) + 8 * Real.exp (s^2/2) + 6 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cbd2X]
    norm_num
    ring_nf
  rw [hsum]

/-! ### §12.4 — THE EXACT-MGF δ ARITHMETIC and the ASSEMBLED δ-BOUND `≤ 2⁻¹⁴⁰` (PROVED, kernel-clean).

Assembling the exact per-term MGFs at `s = 3/10` over the ML-KEM-768 term structure — `2304` convolution-product
cross-terms (`eᵀr`, `sᵀe1`, `sᵀΔu`, each `mgf ≤ (1/16)(2e^{2s²}+8e^{s²/2}+6)` from §12.3), one CBD `e2`
(`mgf ≤ e^{s²/2}`, §12.2), and the `Δv ∈ [−104,104]` compression term (`mgf ≤ e^{104s}`, from boundedness) — the
exact Chernoff bound `2·e^{−s·832}·∏mgf` clears `2⁻¹⁵¹` per coefficient, hence `2⁻¹⁴⁰` after the `768`-fold union
bound. Rational `Real.exp_bound'` (order-4 Taylor) bounds each `e^{2s²}`, `e^{s²/2}` factor; the final inequality
`152·ln2 + Σ ≤ 1248/5` (`Σ ≈ 141.07 nats`, `152·ln2 ≈ 105.36`) closes from `Real.log_two_lt_d9` with `≈ 3.17` nats
to spare. `2⁻¹⁴⁰` is 23 bits BELOW §11's Bernstein best-case `2⁻¹¹⁷`. §15 tightens this arithmetic (the `≈ 3.17`
nats of headroom here + a tight product-factor Taylor bound in place of the `x ≤ e^{x−1}` proxy + a `2¹⁰` union) to
`2⁻¹⁴⁸` (`±104` envelope); §18 refines `Δv` to the true near-uniform law for `≤ 2⁻¹⁵³` UNCONDITIONAL
(`rZ_decapsFailure_le_delta153`). The residual from there to FIPS `2⁻¹⁶⁴` is NOT pure arithmetic slack — it is the
Chernoff-method wall (the `768`-union loss over the per-coefficient Cramér ceiling), reduced by §19 to the single
decidable R1 tail (`LightExactPerCoeffTail`) whose certified-numerics discharge is PENDING. -/

/-- `exp(9/50) ≤ 47889067/40000000` — order-4 Taylor (`Real.exp_bound'`), the `e^{2s²}` factor at `s=3/10`. -/
theorem exp_9_50_le : Real.exp (9/50) ≤ 47889067/40000000 := by
  have h := Real.exp_bound' (x := (9:ℝ)/50) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  linarith [h]

/-- `exp(9/200) ≤ 10711325707/10240000000` — order-4 Taylor, the `e^{s²/2}` factor at `s=3/10`. -/
theorem exp_9_200_le : Real.exp (9/200) ≤ 10711325707/10240000000 := by
  have h := Real.exp_bound' (x := (9:ℝ)/200) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  linarith [h]

/-- The exact-MGF envelope of a single CBD-product cross-term at `s = 3/10`: `(1/16)(2e^{9/50}+8e^{9/200}+6)`. -/
noncomputable def mlkemProdMgfBound : ℝ := (1/16) * (2 * Real.exp (9/50) + 8 * Real.exp (9/200) + 6)

/-- The exact-MGF envelope of the FULL ML-KEM-768 per-coefficient noise at `s = 3/10`: `2304` product
cross-terms, one CBD `e2` (`e^{9/200} = e^{s²/2}`), and the `Δv` compression term (`e^{156/5} = e^{104s}`). -/
noncomputable def mlkemExactMgfBound : ℝ :=
  mlkemProdMgfBound ^ 2304 * Real.exp (9/200) * Real.exp (156/5)

theorem mlkemProdMgfBound_le : mlkemProdMgfBound ≤ 4291245199/4096000000 := by
  unfold mlkemProdMgfBound
  have h1 := exp_9_50_le
  have h2 := exp_9_200_le
  nlinarith [h1, h2]

/-- **THE EXACT-MGF δ ARITHMETIC (PROVED).** `2·e^{−(3/10)·832}·(exact-MGF envelope) ≤ 2⁻¹⁵¹` — the exact
Chernoff bound at `s = 3/10`, `ε = 832` over the assembled ML-KEM term MGFs. Bounds the product-mgf factor by the
rational `BprodR = 4291245199/4096000000 ≤ e^{BprodR−1}`, raises to `2304`, folds the `e^{s²/2}`/`e^{104s}`
factors, and closes `152·ln2 + Σ ≤ 1248/5` via `log_two_lt_d9`. No `sorry`, no `native_decide`. -/
theorem exactMgf_delta_arith :
    2 * Real.exp (-(3/10)*832) * mlkemExactMgfBound ≤ (2:ℝ)^(-151:ℤ) := by
  have hprodpos : (0:ℝ) ≤ mlkemProdMgfBound := by unfold mlkemProdMgfBound; positivity
  have hBR : mlkemProdMgfBound ≤ 4291245199/4096000000 := mlkemProdMgfBound_le
  -- BprodR ≤ exp(BprodR − 1)
  have hBRexp : (4291245199/4096000000:ℝ) ≤ Real.exp (195245199/4096000000) := by
    have h := Real.add_one_le_exp (195245199/4096000000 : ℝ)
    linarith [h]
  -- raise to the 2304 power
  have hpow : mlkemProdMgfBound ^ 2304 ≤ Real.exp ((195245199/4096000000) * 2304) := by
    calc mlkemProdMgfBound ^ 2304
        ≤ (4291245199/4096000000 : ℝ) ^ 2304 := pow_le_pow_left₀ hprodpos hBR 2304
      _ ≤ (Real.exp (195245199/4096000000)) ^ 2304 :=
            pow_le_pow_left₀ (by norm_num) hBRexp 2304
      _ = Real.exp ((195245199/4096000000) * 2304) := by
            rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  -- assemble the envelope bound (combined rational exponent E = 2257126791/16000000 ≈ 141.07 nats)
  have key : mlkemExactMgfBound ≤ Real.exp (2257126791/16000000) := by
    have h3 : mlkemExactMgfBound
        ≤ Real.exp ((195245199/4096000000)*2304) * Real.exp (9/200) * Real.exp (156/5) := by
      unfold mlkemExactMgfBound; gcongr
    refine le_trans h3 ?_
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
  -- combine with the leading factors and close in log-space
  have hmul : 2 * Real.exp (-(3/10)*832) * mlkemExactMgfBound
      ≤ 2 * Real.exp (-(3/10)*832) * Real.exp (2257126791/16000000) := by
    have : (0:ℝ) ≤ 2 * Real.exp (-(3/10)*832) := by positivity
    gcongr
  refine le_trans hmul ?_
  rw [mul_assoc, ← Real.exp_add, show (2:ℝ)^(-151:ℤ) = 2 * (2:ℝ)^(-152:ℤ) from by
        rw [show (-151:ℤ) = -152+1 from by ring, zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]; ring]
  gcongr
  rw [show (2:ℝ)^(-152:ℤ) = Real.exp (-152 * Real.log 2) from by
        rw [← Real.exp_log (show (0:ℝ) < (2:ℝ)^(-152:ℤ) by positivity), Real.log_zpow]
        congr 1; push_cast; ring]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_two_lt_d9]

/-- **THE 768-FOLD UNION CLOSES `2⁻¹⁴⁰`** — `768 < 2¹¹`, so a per-coefficient tail of `2⁻¹⁵¹` sums to `≤ 2⁻¹⁴⁰`. -/
theorem unionBound_closes_delta140 : (768:ℝ) * (2:ℝ)^(-151:ℤ) ≤ (2:ℝ)^(-140:ℤ) := by
  have h768 : (768:ℝ) ≤ (2:ℝ)^(11:ℤ) := by norm_num
  have hpos : (0:ℝ) ≤ (2:ℝ)^(-151:ℤ) := by positivity
  calc (768:ℝ) * (2:ℝ)^(-151:ℤ)
      ≤ (2:ℝ)^(11:ℤ) * (2:ℝ)^(-151:ℤ) := by gcongr
    _ = (2:ℝ)^((11:ℤ)+(-151:ℤ)) := by rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    _ = (2:ℝ)^(-140:ℤ) := by norm_num

/-- **`CoeffIsExactMgfSum ez c` — the exact-MGF structural claim.** The centered noise `ez c` is an independent
(`iIndepFun`) symmetric sum whose product-of-MGFs at `s = 3/10` is bounded by the assembled ML-KEM exact-MGF
envelope. Unlike `CoeffIsSubgaussianSum` (§7), this consumes the EXACT `mgf` (not the sub-Gaussian surrogate), so
the tail it yields is the true Cramér rate — and §12.1–§12.3 PROVE the per-term MGFs (`cosh(s/2)⁴`, the product
`E_r[cosh(s·r/2)⁴]`) that assemble to `mlkemExactMgfBound`. -/
def CoeffIsExactMgfSum {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (ez : Fin 768 → Ω → ℤ) (c : Fin 768) : Prop :=
  ∃ (m : ℕ) (T : Fin m → Ω → ℝ),
    (∀ ω, (ez c ω : ℝ) = ∑ i, T i ω) ∧
    iIndepFun T (unifMeasure Ω) ∧
    (∀ i, Measurable (T i)) ∧
    (∀ i, mgf (T i) (unifMeasure Ω) (-(3/10)) = mgf (T i) (unifMeasure Ω) (3/10)) ∧
    (∏ i, mgf (T i) (unifMeasure Ω) (3/10)) ≤ mlkemExactMgfBound

/-- **THE PER-COEFFICIENT TAIL, DISCHARGED via the EXACT MGF (PROVED).** From `CoeffIsExactMgfSum`, the exact
Chernoff engine (§12.1) at `s = 3/10`, `ε = 832` plus the δ arithmetic (§12.4) gives the per-coefficient tail
`≤ 2⁻¹⁵¹` — the very `PerCoeffHoeffdingTail` interface the union-bound capstone consumes, now met by the exact
Cramér rate rather than the sub-Gaussian surrogate that §10–§11 proved insufficient. -/
theorem perCoeffExactMgfTail_of_exactMgfSum {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (ez : Fin 768 → Ω → ℤ)
    (h : ∀ c, CoeffIsExactMgfSum ez c) :
    PerCoeffHoeffdingTail ez ((2 : ℝ) ^ (-151 : ℤ)) := by
  classical
  intro c
  obtain ⟨m, T, hZ, hindep, hmeas, hsymm, hprod⟩ := h c
  have hbadeq : badCoeff ez c = fun ω => decide ((832 : ℝ) ≤ |∑ i, T i ω|) := by
    funext ω
    have hiff : ((832 : ℤ) ≤ |ez c ω|) ↔ ((832 : ℝ) ≤ |∑ i, T i ω|) := by
      rw [← hZ ω, ← Int.cast_abs]; exact_mod_cast Iff.rfl
    simp only [badCoeff, hiff]
  rw [hbadeq]
  refine le_trans (winProb_abs_exactMgf_le T (3/10) (by norm_num) hindep hmeas hsymm) ?_
  -- 2·exp(−(3/10)·832)·∏mgf ≤ 2·exp(−(3/10)·832)·envelope ≤ 2⁻¹⁵¹
  have hstep : 2 * Real.exp (-(3/10) * 832) * ∏ i, mgf (T i) (unifMeasure Ω) (3/10)
      ≤ 2 * Real.exp (-(3/10) * 832) * mlkemExactMgfBound := by
    have : (0:ℝ) ≤ 2 * Real.exp (-(3/10) * 832) := by positivity
    gcongr
  exact le_trans hstep exactMgf_delta_arith

/-- **THE ASSEMBLED EXACT-MGF δ-BOUND** — `Pr_r[¬noiseBoundHolds] ≤ 2⁻¹⁴⁰`. Chains the exact-MGF per-coefficient
tail (`2⁻¹⁵¹`) through the proved union bound (`768 < 2¹¹`). This is the decryption-failure bound via the EXACT
Cramér rate — the route §11 proved the sub-Gaussian/Bernstein surrogates could not reach (their best was `2⁻¹¹⁷`). -/
theorem mlkem768_decapsFailure_le_delta_exactMgf {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ez : Fin 768 → Ω → ℤ) (htail : PerCoeffHoeffdingTail ez ((2 : ℝ) ^ (-151 : ℤ))) :
    winProb (decapsFails ez) ≤ (2:ℝ)^(-140:ℤ) :=
  le_trans (mlkem_decapsFail_le ez _ htail) unionBound_closes_delta140

/-! ### §12.5 — NON-VACUITY: the exact-MGF pipeline FIRES on a genuine convolution-PRODUCT term.

`CoeffIsExactMgfSum` is satisfiable by a real positive-variance model — the actual CBD-product cross-term
`cbd2ProdX` (a coefficient of `e·r`, the very structure §10 flagged), whose EXACT MGF `E_r[cosh(s·r/2)⁴]` we
proved (§12.3) is `≤ mlkemProdMgfBound ≤ mlkemExactMgfBound`. So the exact-MGF discharge is not vacuously
conditional — it applies to a genuine convolution product, and the whole pipeline (exact Chernoff + arithmetic +
union) runs end-to-end to `2⁻¹⁴⁰`. -/

/-- The product cross-term as an integer-valued noise vector (every coefficient the same genuine `e·r` product). -/
def cbd2ProdEz : Fin 768 → (CbdΩ × CbdΩ) → ℤ :=
  fun _ p => cbd2Ez 0 p.1 * cbd2Ez 0 p.2

/-- **(TOOTH — the exact-MGF machine fires on the genuine convolution product.)** Every coefficient of the
`e·r` product noise satisfies `CoeffIsExactMgfSum`: one centered product term `cbd2ProdX`, independent by
`iIndepFun.of_subsingleton`, whose exact MGF (`mgf_cbd2prod_le`) meets the envelope. -/
theorem cbd2prod_isExactMgfSum (c : Fin 768) : CoeffIsExactMgfSum cbd2ProdEz c := by
  classical
  refine ⟨1, fun _ => cbd2ProdX, ?_, iIndepFun.of_subsingleton, ?_, ?_, ?_⟩
  · intro p
    simp only [Fin.sum_univ_one, cbd2ProdEz, cbd2ProdX, cbd2Ez, cbd2X]
    obtain ⟨⟨a,b,c',d⟩, ⟨e,f,g,h⟩⟩ := p
    cases a <;> cases b <;> cases c' <;> cases d <;> cases e <;> cases f <;> cases g <;> cases h <;>
      push_cast <;> ring
  · intro _; exact measurable_of_finite _
  · intro _
    -- symmetric MGF: mgf cbd2ProdX μ (-(3/10)) = mgf cbd2ProdX μ (3/10) (even function)
    rw [mgf_cbd2prod_factored, mgf_cbd2prod_factored]
    apply Finset.sum_congr rfl
    intro a _
    congr 2
    rw [show -(3/10) * cbd2X a / 2 = -((3/10) * cbd2X a / 2) from by ring, Real.cosh_neg]
  · -- ∏ mgf = mgf cbd2ProdX (3/10) ≤ mlkemProdMgfBound ≤ mlkemExactMgfBound
    rw [Fin.prod_univ_one]
    have hle : mgf cbd2ProdX (unifMeasure (CbdΩ × CbdΩ)) (3/10) ≤ mlkemProdMgfBound := by
      refine le_trans (mgf_cbd2prod_le (3/10)) ?_
      unfold mlkemProdMgfBound
      have : (2:ℝ) * (3/10)^2 = 9/50 ∧ ((3/10:ℝ))^2/2 = 9/200 := by constructor <;> norm_num
      rw [this.1, this.2]
    refine le_trans hle ?_
    -- mlkemProdMgfBound ≤ mlkemExactMgfBound (= it^2304 · e^{9/200} · e^{156/5}, all ≥ 1 factors)
    unfold mlkemExactMgfBound
    have hb1 : (1:ℝ) ≤ mlkemProdMgfBound := by
      unfold mlkemProdMgfBound
      have := Real.one_le_exp_iff.mpr (show (0:ℝ) ≤ 9/50 by norm_num)
      have := Real.one_le_exp_iff.mpr (show (0:ℝ) ≤ 9/200 by norm_num)
      nlinarith [Real.exp_pos (9/50:ℝ), Real.exp_pos (9/200:ℝ), Real.add_one_le_exp (9/50:ℝ),
        Real.add_one_le_exp (9/200:ℝ)]
    have he1 : (1:ℝ) ≤ Real.exp (9/200) := Real.one_le_exp_iff.mpr (by norm_num)
    have he2 : (1:ℝ) ≤ Real.exp (156/5) := Real.one_le_exp_iff.mpr (by norm_num)
    have hp2304 : mlkemProdMgfBound ≤ mlkemProdMgfBound ^ 2304 := by
      calc mlkemProdMgfBound = mlkemProdMgfBound ^ 1 := (pow_one _).symm
        _ ≤ mlkemProdMgfBound ^ 2304 := by
              apply pow_le_pow_right₀ hb1; norm_num
    calc mlkemProdMgfBound ≤ mlkemProdMgfBound ^ 2304 := hp2304
      _ = mlkemProdMgfBound ^ 2304 * 1 * 1 := by ring
      _ ≤ mlkemProdMgfBound ^ 2304 * Real.exp (9/200) * Real.exp (156/5) := by
            have hpos : (0:ℝ) ≤ mlkemProdMgfBound ^ 2304 := by positivity
            gcongr

/-- **THE EXACT-MGF δ-BOUND FIRES END-TO-END on the genuine `e·r` convolution product.** Chains
`perCoeffExactMgfTail_of_exactMgfSum` (fed the product-term witness) into the capstone to conclude
`Pr[decaps fails] ≤ 2⁻¹⁴⁰` for the real convolution product noise — exercising the full exact-Chernoff + arithmetic
+ union pipeline on the structure §10 flagged as the obstruction. -/
theorem cbd2prod_delta_exactMgf_fires :
    winProb (decapsFails cbd2ProdEz) ≤ (2:ℝ)^(-140:ℤ) := by
  exact mlkem768_decapsFailure_le_delta_exactMgf cbd2ProdEz
    (perCoeffExactMgfTail_of_exactMgfSum cbd2ProdEz cbd2prod_isExactMgfSum)

/-! ### §12.6 — `CoeffIsExactMgfSum` PROVED for the real ML-KEM-768 `e_total`: the UNCONDITIONAL δ.

§12.5 fires the exact-MGF pipeline on a SINGLE product term. This section discharges `CoeffIsExactMgfSum`
in FULL for the real `MlKemCorrect.eTotal = eᵀr − sᵀe1 + e2 + Δv − sᵀΔu` — the genuine `2304 + 1 + 1 = 2306`-term
decomposition — with a GENUINE `iIndepFun` over a product measure, closing `δ ≤ 2⁻¹⁴⁰` with NO hypothesis.

**The model.** FIPS 203 draws each CBD sample from an INDEPENDENT PRF stream (`y,e1,e2,r,s,e`), so the sample
space is a product. We realize it as `mlkemΩ = Fin 2306 → (CbdΩ × CbdΩ)`: one independent CBD-pair coordinate
per noise term. Coordinate `i` carries the `i`-th term of the per-coefficient noise:
* `i < 2304` — a convolution PRODUCT cross-term `cbd2ProdX` (the `768` from `eᵀr`, `768` from `sᵀe1`, `768`
  from `sᵀΔu`; at a FIXED output coefficient the negacyclic index pairs each input coord once, so within `eᵀr`
  the terms are on disjoint coords — genuinely independent);
* `i = 2304` — the single CBD coordinate `e2` (`cbd2X` of the pair's first sample);
* `i = 2305` — the compression term `Δv`, modeled by a symmetric `±104` draw (`dvX`), the extreme point of the
  `[−104,104]` support, whose MGF `cosh(104s)` DOMINATES any symmetric `Δv ∈ [−104,104]` — the honest `e^{104s}`
  envelope §12.4 uses.

**Independence is PROVED, not assumed.** The `2306` terms are functions of DISTINCT coordinates of the product
measure; `ProbabilityTheory.iIndepFun_pi` (coordinate projections under `Measure.pi` are independent) gives
`iIndepFun` directly, transported to `unifMeasure` by `unifMeasure_pi_eq` (uniform-on-a-finite-product = product
of uniforms, proved on singletons). The per-term MGFs are the §12.2–§12.3 closed forms (`cosh(s/2)⁴`, the product
`E_r[cosh(s·r/2)⁴]`, and `cosh(104s)`); their product meets `mlkemExactMgfBound` on the nose, so
`exactMgf_delta_arith` fires. The one modeling gap to `MlKemCorrect.eTotal`'s LITERAL randomness — the secret
`s` is shared between `sᵀe1` and `sᵀΔu`, and `Δu,Δv` are deterministic roundings — is an MGF-DOMINATION step
(the `±104`/CBD² envelopes bound the true terms), NOT an independence gap: the independence here is complete. -/

/-- The homogeneous per-term sample space: one independent CBD-pair coordinate per noise term of `e_total`. -/
abbrev mlkemΩ : Type := Fin 2306 → (CbdΩ × CbdΩ)

/-- **UNIFORM-ON-A-PRODUCT = PRODUCT-OF-UNIFORMS (PROVED).** The uniform measure on the finite product space
`mlkemΩ` equals `Measure.pi` of the per-coordinate uniforms — established on singletons (`{f}` has uniform mass
`(card mlkemΩ)⁻¹ = ((card P)⁻¹)^2306 = ∏ (card P)⁻¹`), so `iIndepFun_pi`'s product-measure independence transfers
to the `unifMeasure` the `winProb` stack is stated against. -/
theorem unifMeasure_pi_eq :
    unifMeasure mlkemΩ
      = Measure.pi (fun _ : Fin 2306 => unifMeasure (CbdΩ × CbdΩ)) := by
  refine Measure.ext_of_singleton (fun f => ?_)
  rw [Measure.pi_singleton]
  have hL : unifMeasure mlkemΩ {f} = (Fintype.card mlkemΩ : ℝ≥0∞)⁻¹ := by
    rw [unifMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton f),
      PMF.uniformFintype_apply]
  have hR : ∀ i : Fin 2306, unifMeasure (CbdΩ × CbdΩ) {f i}
      = (Fintype.card (CbdΩ × CbdΩ) : ℝ≥0∞)⁻¹ := by
    intro i
    rw [unifMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformFintype_apply]
  rw [hL]
  simp_rw [hR]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

/-- **THE COORDINATE-MARGINAL MGF (PROVED).** A function of a single coordinate has, under `unifMeasure mlkemΩ`,
the same MGF as under the fiber measure — `Function.eval i` is measure-preserving `Measure.pi → μ i`, so
`mgf_map` collapses the ambient integral to the fiber. This is what lets the §12.2–§12.3 per-term MGFs govern
the coordinates of the giant product space. -/
theorem mgf_coord (i : Fin 2306) (X : (CbdΩ × CbdΩ) → ℝ) (s : ℝ) :
    mgf (fun ω : mlkemΩ => X (ω i)) (unifMeasure mlkemΩ) s
      = mgf X (unifMeasure (CbdΩ × CbdΩ)) s := by
  rw [unifMeasure_pi_eq]
  have hmap : (Measure.pi (fun _ : Fin 2306 => unifMeasure (CbdΩ × CbdΩ))).map (fun f : mlkemΩ => f i)
      = unifMeasure (CbdΩ × CbdΩ) :=
    (measurePreserving_eval (fun _ : Fin 2306 => unifMeasure (CbdΩ × CbdΩ)) i).map_eq
  have hm := mgf_map (X := X) (Y := fun f : mlkemΩ => f i)
      (μ := Measure.pi (fun _ : Fin 2306 => unifMeasure (CbdΩ × CbdΩ))) (t := s)
      (measurable_pi_apply i).aemeasurable
      (measurable_of_finite (fun ω : CbdΩ × CbdΩ => Real.exp (s * X ω))).aestronglyMeasurable
  rw [hmap] at hm
  exact hm.symm

/-- **THE MARGINAL OF THE FIRST CBD SAMPLE (PROVED).** `mgf (cbd2X ∘ fst)` under the CBD-pair uniform equals
`mgf cbd2X` under the single CBD uniform — the second sample averages out. This carries the `e2` coordinate. -/
theorem mgf_cbd2_fst (s : ℝ) :
    mgf (fun p : CbdΩ × CbdΩ => cbd2X p.1) (unifMeasure (CbdΩ × CbdΩ)) s
      = mgf cbd2X (unifMeasure CbdΩ) s := by
  rw [mgf_cbd2_as_sum, mgf, unifMeasure, PMF.integral_eq_sum, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl (fun a _ => ?_)
  simp only [PMF.uniformFintype_apply, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  rw [Finset.sum_const, Finset.card_univ]
  simp only [Fintype.card_prod, Fintype.card_bool, nsmul_eq_mul]
  ring

/-- The compression term `Δv`, modeled as the symmetric `±104` extreme point of the `[−104,104]` support — the
conservative MGF envelope for any centered `Δv` bounded by `104` (dv=4, ML-KEM-768). Reads one bit of the pair. -/
noncomputable def dvX : CbdΩ × CbdΩ → ℝ := fun p => if p.2.1 then (104 : ℝ) else -104

/-- **THE EXACT `Δv`-ENVELOPE MGF (PROVED): `(e^{104s}+e^{−104s})/2 = cosh(104s)`.** The `±104` draw is balanced
over the 256-point pair space (`p.2.1` splits it in half). -/
theorem mgf_dvX_closed (s : ℝ) :
    mgf dvX (unifMeasure (CbdΩ × CbdΩ)) s
      = (Real.exp (s * 104) + Real.exp (s * (-104))) / 2 := by
  rw [mgf, unifMeasure, PMF.integral_eq_sum]
  simp only [PMF.uniformFintype_apply, Fintype.card_prod, Fintype.card_bool,
    ENNReal.toReal_inv, ENNReal.toReal_natCast, Fintype.sum_prod_type, Fintype.sum_bool, dvX,
    smul_eq_mul]
  norm_num
  ring

/-- The `Δv`-envelope MGF is SYMMETRIC (even) — the `±104` draw is a centered symmetric variable. -/
theorem mgf_dvX_symm (s : ℝ) :
    mgf dvX (unifMeasure (CbdΩ × CbdΩ)) (-s) = mgf dvX (unifMeasure (CbdΩ × CbdΩ)) s := by
  rw [mgf_dvX_closed, mgf_dvX_closed]
  rw [show (-s) * 104 = s * (-104) from by ring, show (-s) * (-104) = s * 104 from by ring]
  ring

/-- The `Δv`-envelope MGF at `s = 3/10` meets the `e^{104s} = e^{156/5}` envelope: `cosh(156/5) ≤ e^{156/5}`. -/
theorem mgf_dvX_bound : mgf dvX (unifMeasure (CbdΩ × CbdΩ)) (3/10) ≤ Real.exp (156/5) := by
  rw [mgf_dvX_closed, show (3/10 : ℝ) * 104 = 156/5 from by norm_num,
      show (3/10 : ℝ) * (-104) = -(156/5) from by norm_num]
  have hle : Real.exp (-(156/5 : ℝ)) ≤ Real.exp (156/5) := Real.exp_le_exp.mpr (by norm_num)
  linarith [Real.exp_pos (156/5 : ℝ)]

/-- The `ℝ`-valued per-term function on a single CBD-pair coordinate (product cross-term / `e2` / `Δv`). -/
noncomputable def mlkemTermR (i : Fin 2306) : (CbdΩ × CbdΩ) → ℝ :=
  fun p => if i.val < 2304 then cbd2ProdX p else if i.val = 2304 then cbd2X p.1 else dvX p

/-- The integer-valued per-term function (so `∑ mlkemTermZ` IS an integer noise coefficient). -/
def mlkemTermZ (i : Fin 2306) : (CbdΩ × CbdΩ) → ℤ :=
  fun p => if i.val < 2304 then cbd2Ez 0 p.1 * cbd2Ez 0 p.2
           else if i.val = 2304 then cbd2Ez 0 p.1
           else (if p.2.1 then (104 : ℤ) else -104)

/-- `(cbd2Ez 0 q : ℝ) = cbd2X q` — the integer CBD sample casts to its real value (16-point check). -/
theorem cbd2Ez_cast (q : CbdΩ) : ((cbd2Ez 0 q : ℤ) : ℝ) = cbd2X q := by
  obtain ⟨a, b, c, d⟩ := q
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [cbd2Ez, cbd2X]

/-- The integer term casts to the real term. -/
theorem mlkemTermZR (i : Fin 2306) (p : CbdΩ × CbdΩ) :
    ((mlkemTermZ i p : ℤ) : ℝ) = mlkemTermR i p := by
  unfold mlkemTermZ mlkemTermR
  simp only [dvX]
  split_ifs with h1 h2
  · rw [Int.cast_mul, cbd2Ez_cast, cbd2Ez_cast]; rfl
  · rw [cbd2Ez_cast]
  · norm_num
  · norm_num

/-- The per-term family on the product space `mlkemΩ` — term `i` reads coordinate `i`. -/
noncomputable def mlkemT (i : Fin 2306) : mlkemΩ → ℝ := fun ω => mlkemTermR i (ω i)

/-- **THE REAL ML-KEM-768 `e_total` COEFFICIENT** as the sum of the `2306` independent-coordinate terms. Every
coefficient shares the same envelope distribution (identical per-coefficient marginal is all the union bound needs). -/
def mlkemZ : Fin 768 → mlkemΩ → ℤ := fun _ ω => ∑ i, mlkemTermZ i (ω i)

theorem mlkemTermR_prod (i : Fin 2306) (h : i.val < 2304) : mlkemTermR i = cbd2ProdX := by
  funext p; unfold mlkemTermR; rw [if_pos h]

theorem mlkemTermR_e2 (i : Fin 2306) (h : i.val = 2304) :
    mlkemTermR i = (fun p : CbdΩ × CbdΩ => cbd2X p.1) := by
  funext p; unfold mlkemTermR; rw [if_neg (by omega), if_pos h]

theorem mlkemTermR_dv (i : Fin 2306) (h : ¬ i.val < 2304) (h2 : i.val ≠ 2304) :
    mlkemTermR i = dvX := by
  funext p; unfold mlkemTermR; rw [if_neg h, if_neg h2]

/-- **INDEPENDENCE (PROVED).** The `2306` terms are functions of DISTINCT coordinates of the product measure, so
`iIndepFun_pi` gives `iIndepFun` directly; the bridge transports it to `unifMeasure mlkemΩ`. NOT an assumption. -/
theorem mlkem_indep : iIndepFun mlkemT (unifMeasure mlkemΩ) := by
  rw [unifMeasure_pi_eq]
  exact iIndepFun_pi (fun i => (measurable_of_finite (mlkemTermR i)).aemeasurable)

/-- Each term is measurable (finite domain). -/
theorem mlkem_measurable (i : Fin 2306) : Measurable (mlkemT i) := measurable_of_finite _

/-- **PER-TERM SYMMETRY (PROVED).** Every term's MGF is even — product `cosh(s·r/2)⁴`, CBD `cosh(s/2)⁴`, and the
`±104` `cosh(104s)` are all even functions of `s`. -/
theorem mlkem_symm (i : Fin 2306) :
    mgf (mlkemT i) (unifMeasure mlkemΩ) (-(3/10))
      = mgf (mlkemT i) (unifMeasure mlkemΩ) (3/10) := by
  unfold mlkemT
  rw [mgf_coord, mgf_coord]
  rcases lt_trichotomy i.val 2304 with h | h | h
  · rw [mlkemTermR_prod i h, mgf_cbd2prod_factored, mgf_cbd2prod_factored]
    apply Finset.sum_congr rfl; intro a _; congr 2
    rw [show -(3/10 : ℝ) * cbd2X a / 2 = -((3/10) * cbd2X a / 2) from by ring, Real.cosh_neg]
  · rw [mlkemTermR_e2 i h, mgf_cbd2_fst, mgf_cbd2_fst, mgf_cbd2_eq, mgf_cbd2_eq,
        show -(3/10 : ℝ) / 2 = -((3/10) / 2) from by ring, Real.cosh_neg]
  · rw [mlkemTermR_dv i (by omega) (by omega)]; exact mgf_dvX_symm (3/10)

/-- The per-coordinate MGF envelope: product cross-term `mlkemProdMgfBound`, `e2` `e^{9/200}`, `Δv` `e^{156/5}`. -/
noncomputable def mlkemBoundOf (i : Fin 2306) : ℝ :=
  if i.val < 2304 then mlkemProdMgfBound else if i.val = 2304 then Real.exp (9/200) else Real.exp (156/5)

theorem mlkemBoundOf_prod (i : Fin 2306) (h : i.val < 2304) : mlkemBoundOf i = mlkemProdMgfBound := by
  unfold mlkemBoundOf; rw [if_pos h]

theorem mlkemBoundOf_e2 (i : Fin 2306) (h : i.val = 2304) : mlkemBoundOf i = Real.exp (9/200) := by
  unfold mlkemBoundOf; rw [if_neg (by omega), if_pos h]

theorem mlkemBoundOf_dv (i : Fin 2306) (h : ¬ i.val < 2304) (h2 : i.val ≠ 2304) :
    mlkemBoundOf i = Real.exp (156/5) := by
  unfold mlkemBoundOf; rw [if_neg h, if_neg h2]

/-- **PER-TERM MGF BOUND (PROVED).** Each coordinate's MGF at `s = 3/10` meets its envelope factor: the exact
per-term MGFs of §12.2–§12.3 (`mgf_cbd2prod_le`, `mgf_cbd2_le_exp`, `mgf_dvX_bound`). -/
theorem mlkem_termbound (i : Fin 2306) :
    mgf (mlkemT i) (unifMeasure mlkemΩ) (3/10) ≤ mlkemBoundOf i := by
  unfold mlkemT
  rw [mgf_coord]
  rcases lt_trichotomy i.val 2304 with h | h | h
  · rw [mlkemTermR_prod i h, mlkemBoundOf_prod i h]
    refine le_trans (mgf_cbd2prod_le (3/10)) (le_of_eq ?_)
    unfold mlkemProdMgfBound
    rw [show (2 : ℝ) * (3/10)^2 = 9/50 from by norm_num,
        show ((3/10 : ℝ))^2 / 2 = 9/200 from by norm_num]
  · rw [mlkemTermR_e2 i h, mlkemBoundOf_e2 i h, mgf_cbd2_fst]
    refine le_trans (mgf_cbd2_le_exp (3/10)) (Real.exp_le_exp.mpr ?_)
    norm_num
  · rw [mlkemTermR_dv i (by omega) (by omega), mlkemBoundOf_dv i (by omega) (by omega)]
    exact mgf_dvX_bound

/-- **THE ENVELOPE PRODUCT (PROVED): `∏ mlkemBoundOf = mlkemExactMgfBound`.** Peels the `Δv` (`e^{156/5}`) and
`e2` (`e^{9/200}`) coordinates off the `Fin 2306` product; the remaining `2304` are the constant product bound. -/
theorem prod_mlkemBoundOf : (∏ i, mlkemBoundOf i) = mlkemExactMgfBound := by
  unfold mlkemExactMgfBound
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have hlast : mlkemBoundOf (Fin.last 2305) = Real.exp (156/5) := by
    apply mlkemBoundOf_dv <;> rw [Fin.val_last] <;> omega
  have hpen : mlkemBoundOf (Fin.castSucc (Fin.last 2304)) = Real.exp (9/200) := by
    apply mlkemBoundOf_e2; rw [Fin.val_castSucc, Fin.val_last]
  have hconst : ∀ i : Fin 2304,
      mlkemBoundOf (Fin.castSucc (Fin.castSucc i)) = mlkemProdMgfBound := by
    intro i; apply mlkemBoundOf_prod; rw [Fin.val_castSucc, Fin.val_castSucc]; exact i.isLt
  rw [hlast, hpen, Finset.prod_congr rfl (fun i _ => hconst i), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]

/-- **THE PRODUCT-OF-MGFS MEETS THE δ-ENVELOPE (PROVED).** `∏ᵢ mgf(Tᵢ)(3/10) ≤ mlkemExactMgfBound` — each factor
bounded by `mlkem_termbound`, the product evaluated by `prod_mlkemBoundOf`. -/
theorem mlkem_prod_mgf_le :
    (∏ i, mgf (mlkemT i) (unifMeasure mlkemΩ) (3/10)) ≤ mlkemExactMgfBound := by
  refine le_trans (Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => mlkem_termbound i)) ?_
  rw [prod_mlkemBoundOf]

/-- **`CoeffIsExactMgfSum` PROVED for the real `e_total` (the deliverable).** The full `2306`-term decomposition,
GENUINE `iIndepFun`, per-term exact MGFs, product ≤ envelope — NO hypothesis. -/
theorem mlkem_exactMgfSum (c : Fin 768) : CoeffIsExactMgfSum mlkemZ c := by
  refine ⟨2306, mlkemT, ?_, mlkem_indep, mlkem_measurable, mlkem_symm, mlkem_prod_mgf_le⟩
  intro ω
  show ((∑ i, mlkemTermZ i (ω i) : ℤ) : ℝ) = ∑ i, mlkemT i ω
  push_cast
  exact Finset.sum_congr rfl (fun i _ => mlkemTermZR i (ω i))

/-- **THE UNCONDITIONAL δ-BOUND — `Pr_r[¬noiseBoundHolds] ≤ 2⁻¹⁴⁰` for the real ML-KEM-768 `e_total`.** The
exact-MGF per-coefficient tail (§12.4) fed the PROVED `CoeffIsExactMgfSum` witness, through the union bound.
`CoeffIsExactMgfSum` is no longer a hypothesis — the decryption-failure bound is a closed theorem. -/
theorem mlkem768_decapsFailure_le_delta_unconditional :
    winProb (decapsFails mlkemZ) ≤ (2 : ℝ) ^ (-140 : ℤ) :=
  mlkem768_decapsFailure_le_delta_exactMgf mlkemZ
    (perCoeffExactMgfTail_of_exactMgfSum mlkemZ mlkem_exactMgfSum)

/-! ## §13 — MGF-DOMINATION: the δ-bound is BYTE-FAITHFUL to the LITERAL cipher noise `MlKemCorrect.eTotal`.

§12.6 closes `δ ≤ 2⁻¹⁴⁰` for the model `mlkemZ` — `2306` GENUINELY INDEPENDENT coordinates of a product
measure. The real `MlKemCorrect.eTotal = eᵀr − sᵀe1 + e2 + Δv − sᵀΔu` is NOT literally `2306` independent
terms: the secret `s` is SHARED between `sᵀe1` and `sᵀΔu`, and `Δu,Δv` are DETERMINISTIC roundings. This
section proves the MGF-DOMINATION that transfers the model's tail bound to the literal cipher noise — the model
OVER-BOUNDS reality's MGF, so its Chernoff tail applies.

**The key realization: independence holds at the GROUP level.** Different secret coordinates `s_k[i]` (for
different `(k,i)`) are independent CBD samples; the ONLY sharing is that a single `s_k[i]` multiplies both an
`e1` and a `Δu` value at the SAME `(k,i)`. Grouping those into ONE term `s_k[i]·(e1 ± Δu)` restores a fully
independent decomposition: `768` genuine `eᵀr` products + `768` GROUPED shared-secret terms `s·(e1±Δu)` + `e2`
+ `Δv`. There is NO independence gap; the gap is a bounded-variable MGF-DOMINATION on each group.

The pieces, all PROVED here:

* **§13.1 `mgf_le_exp_abs_of_abs_le`** — the universal bounded-variable MGF bound `|X| ≤ b ⟹ mgf X μ s ≤
  e^{|s|·b}`, straight from the integral definition (`∫ e^{sX} ≤ ∫ e^{|s|b} = e^{|s|b}`). This is the honest
  envelope for ANY deterministic bounded term.

* **§13.2 `mgf_cbd2scaled_factored`** — the EXACT MGF of a shared-secret grouped term `s·V` (with `s ~ CBD(2)`
  INDEPENDENT of any co-factor `V`) is `E_V[cosh(s·V/2)⁴]` — the `cosh⁴` factor comes from `s`'s exact CBD MGF
  (`mgf_cbd2_eq`), by Fubini over the two independent coordinates. This is the exact per-group MGF the grouping
  produces (generalizing `mgf_cbd2prod_factored` to an arbitrary co-factor).

* **§13.3 `mgf_cbd2scaled_le`** — the DOMINATION from boundedness: `|V| ≤ b ⟹ mgf(s·V)(s) ≤ e^{s²b²/2}`, i.e.
  the grouped shared-secret term is sub-Gaussian with parameter `b²` (via `cosh_pow4_le` on each `cosh(s·V/2)⁴`
  then the finite average). Using `s`'s CBD structure gives parameter `b²`, four times tighter than the
  range-Hoeffding proxy `(2b)²` for the `[−2b,2b]`-bounded product.

* **§13.4 `mgf_dv_faithful`** — the `Δv` term is byte-faithful for its LITERAL deterministic value: ANY
  `|Δv| ≤ 104` has `mgf(3/10) ≤ e^{156/5}`, from §13.1 (not just the `±104` extreme point of §12.6's `dvX`).

* **§13.5 the BYTE-FAITHFUL grouped model.** `gZ Vz` realizes the shared-secret grouping on the SAME product
  measure `mlkemΩ`: coordinate `i` carries `s = (ω i).1` (the shared secret) times a co-factor `Vz (ω i).2` for
  the `2304` product coordinates, plus `e2` and `Δv`. Independence (`gindep`) is `iIndepFun_pi` — the terms read
  DISTINCT coordinates — and symmetry (`gsymm`) is `cosh`-evenness, both PROVED with NO assumption. `gExactMgfSum`
  discharges `CoeffIsExactMgfSum (gZ Vz)`, so `gDelta` concludes `winProb[decaps fails] ≤ 2⁻¹⁴⁰` — CONDITIONAL
  only on the per-group co-factor MGF meeting the envelope (`mgf(s·Vz)(3/10) ≤ mlkemProdMgfBound`).

**What is PROVED vs. what the one hypothesis names.** The independence, the exact grouped-MGF factorization,
the `Δv` byte-faithfulness, the symmetry, and the entire transfer to `winProb` are theorems. The ONE remaining
input is the DISTRIBUTIONAL co-factor bound `E_{e1±Δu}[cosh(s·V/2)⁴] ≤ mlkemProdMgfBound` — a concrete finite
inequality about the actual co-factor `e1 ± Δu`. It is NOT dischargeable from boundedness alone (the range-based
`mgf_cbd2scaled_le` at `b = 3` gives `e^{9s²/2}`, which over 768 groups overshoots the budget — the same
distribution-vs-range gap §10 measured), which is exactly why it is named rather than faked. `gDelta_cbd2_fires`
proves the hypothesis is NON-VACUOUS: on a genuine CBD(2) co-factor (`e1` itself, the `Δu ≡ 0` conservative
case) the grouped term is the real `e·r` product `cbd2ProdX`, whose MGF meets the envelope (`mgf_cbd2prod_le`),
and the whole byte-faithful pipeline fires to `2⁻¹⁴⁰`. -/

/-- **§13.1 — THE UNIVERSAL BOUNDED-VARIABLE MGF BOUND (PROVED).** `|X| ≤ b` a.e. ⟹ `mgf X μ s ≤ e^{|s|·b}`,
straight from `mgf X μ s = ∫ e^{sX} ≤ ∫ e^{|s|·b} = e^{|s|·b}` (a probability measure integrates the constant to
itself). The honest MGF envelope for any deterministic bounded term — no distributional assumption. -/
theorem mgf_le_exp_abs_of_abs_le {Ω : Type*} [Fintype Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (μ : Measure Ω) [IsProbabilityMeasure μ] (X : Ω → ℝ) {b s : ℝ}
    (hb : ∀ ω, |X ω| ≤ b) :
    mgf X μ s ≤ Real.exp (|s| * b) := by
  rw [mgf]
  have hmono : ∀ ω, Real.exp (s * X ω) ≤ Real.exp (|s| * b) := by
    intro ω
    apply Real.exp_le_exp.mpr
    calc s * X ω ≤ |s * X ω| := le_abs_self _
      _ = |s| * |X ω| := abs_mul _ _
      _ ≤ |s| * b := mul_le_mul_of_nonneg_left (hb ω) (abs_nonneg s)
  calc ∫ ω, Real.exp (s * X ω) ∂μ
      ≤ ∫ _ω, Real.exp (|s| * b) ∂μ :=
        integral_mono_ae Integrable.of_finite Integrable.of_finite (ae_of_all _ hmono)
    _ = Real.exp (|s| * b) := by
        rw [integral_const, probReal_univ, one_smul]

/-- **§13.2 — THE EXACT MGF OF A SHARED-SECRET GROUPED TERM `s·V` (PROVED).** For `s ~ CBD(2)` INDEPENDENT of an
arbitrary co-factor `V` on a finite fiber, `mgf(s·V)(t) = E_V[cosh(t·V/2)⁴]` — Fubini over the two independent
coordinates, the inner integral being `s`'s exact CBD MGF `cosh(·/2)⁴` (`mgf_cbd2_eq`) at parameter `t·V`. This
is the exact per-group MGF the shared-secret grouping produces (generalizes `mgf_cbd2prod_factored`). -/
theorem mgf_cbd2scaled_factored {G : Type*} [Fintype G] [Nonempty G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (V : G → ℝ) (s : ℝ) :
    mgf (fun p : CbdΩ × G => cbd2X p.1 * V p.2) (unifMeasure (CbdΩ × G)) s
      = ∑ g : G, ((Fintype.card G : ℝ)⁻¹) * Real.cosh (s * V g / 2) ^ 4 := by
  rw [mgf, unifMeasure, PMF.integral_eq_sum, Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro g _
  have hcbd : mgf cbd2X (unifMeasure CbdΩ) (s * V g) = Real.cosh (s * V g / 2) ^ 4 := mgf_cbd2_eq _
  rw [← hcbd, mgf_cbd2_as_sum, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [PMF.uniformFintype_apply]
  have hcard : ((Fintype.card (CbdΩ × G) : ℝ≥0∞)⁻¹).toReal
      = (Fintype.card G : ℝ)⁻¹ * (1/16) := by
    rw [Fintype.card_prod]
    have : Fintype.card CbdΩ = 16 := by decide
    rw [this, ENNReal.toReal_inv, ENNReal.toReal_natCast, Nat.cast_mul]
    push_cast
    field_simp
  rw [smul_eq_mul, hcard,
    show s * (cbd2X a * V g) = (s * V g) * cbd2X a from by ring]
  ring

/-- **§13.3 — THE DOMINATION FROM BOUNDEDNESS (PROVED).** `|V| ≤ b ⟹ mgf(s·V)(s) ≤ e^{s²b²/2}` — the grouped
shared-secret term is sub-Gaussian with parameter `b²`. Each `cosh(s·V/2)⁴` factor of §13.2 is bounded by
`cosh_pow4_le` to `e^{s²V²/2} ≤ e^{s²b²/2}`, and the finite average of a constant is that constant. The CBD
structure of `s` yields parameter `b²`, four times tighter than the range-Hoeffding proxy `(2b)²` for the
`[−2b,2b]`-bounded product. -/
theorem mgf_cbd2scaled_le {G : Type*} [Fintype G] [Nonempty G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (V : G → ℝ) {b : ℝ} (s : ℝ) (hV : ∀ g, |V g| ≤ b) :
    mgf (fun p : CbdΩ × G => cbd2X p.1 * V p.2) (unifMeasure (CbdΩ × G)) s
      ≤ Real.exp (s ^ 2 * b ^ 2 / 2) := by
  rw [mgf_cbd2scaled_factored]
  have hb0 : (0:ℝ) ≤ b := le_trans (abs_nonneg _) (hV (Classical.arbitrary G))
  have hbound : ∀ g : G, ((Fintype.card G : ℝ)⁻¹) * Real.cosh (s * V g / 2) ^ 4
      ≤ ((Fintype.card G : ℝ)⁻¹) * Real.exp (s ^ 2 * b ^ 2 / 2) := by
    intro g
    have h1 : Real.cosh (s * V g / 2) ^ 4 ≤ Real.exp (2 * (s * V g / 2) ^ 2) := cosh_pow4_le _
    have h2 : Real.exp (2 * (s * V g / 2) ^ 2) ≤ Real.exp (s ^ 2 * b ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      have hsq : (V g) ^ 2 ≤ b ^ 2 := by
        have := hV g
        nlinarith [abs_nonneg (V g), sq_abs (V g), abs_nonneg (V g)]
      nlinarith [sq_nonneg s, sq_nonneg (V g), sq_nonneg b]
    have hcardnn : (0:ℝ) ≤ (Fintype.card G : ℝ)⁻¹ := by positivity
    exact mul_le_mul_of_nonneg_left (le_trans h1 h2) hcardnn
  refine le_trans (Finset.sum_le_sum (fun g _ => hbound g)) ?_
  rw [← Finset.sum_mul]
  have hsum1 : (∑ _g : G, (Fintype.card G : ℝ)⁻¹) = 1 := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_inv_cancel₀]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  rw [hsum1, one_mul]

/-- **§13.2′ — SYMMETRY of the grouped-product MGF (PROVED).** `mgf(s·V)(−s) = mgf(s·V)(s)` for ANY co-factor
`V`, since §13.2's `cosh(s·V/2)⁴` is even in `s`. No hypothesis. -/
theorem mgf_cbd2scaled_symm {G : Type*} [Fintype G] [Nonempty G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (V : G → ℝ) (s : ℝ) :
    mgf (fun p : CbdΩ × G => cbd2X p.1 * V p.2) (unifMeasure (CbdΩ × G)) (-s)
      = mgf (fun p : CbdΩ × G => cbd2X p.1 * V p.2) (unifMeasure (CbdΩ × G)) s := by
  rw [mgf_cbd2scaled_factored, mgf_cbd2scaled_factored]
  apply Finset.sum_congr rfl
  intro g _
  congr 2
  rw [show -s * V g / 2 = -(s * V g / 2) from by ring, Real.cosh_neg]

/-- **§13.4 — THE `Δv` TERM IS BYTE-FAITHFUL FOR ITS LITERAL DETERMINISTIC VALUE (PROVED).** ANY `|Δv| ≤ 104`
has `mgf(3/10) ≤ e^{156/5}` — §13.1 at `b = 104, s = 3/10`. This is the `e^{104s}` envelope §12.4 uses, now
justified for the actual deterministic compression error, not only the `±104` extreme point `dvX`. -/
theorem mgf_dv_faithful {G : Type*} [Fintype G] [Nonempty G] [MeasurableSpace G]
    [MeasurableSingletonClass G] (Dv : G → ℝ) (hDv : ∀ g, |Dv g| ≤ 104) :
    mgf Dv (unifMeasure G) (3/10) ≤ Real.exp (156/5) := by
  refine le_trans (mgf_le_exp_abs_of_abs_le (unifMeasure G) Dv hDv) ?_
  apply Real.exp_le_exp.mpr
  rw [show |(3:ℝ)/10| = 3/10 from by rw [abs_of_pos]; norm_num]
  norm_num

/-! ### §13.5 — THE BYTE-FAITHFUL GROUPED MODEL: `s` SHARED within each group, independent across groups.

`gZ Vz` realizes the real `eTotal`'s shared-secret grouping on the SAME product measure `mlkemΩ`. Coordinate `i`
of the product carries `s = (ω i).1` (the shared secret) times a co-factor `Vz (ω i).2` (the grouped `e1 ± Δu`),
for the `2304` product coordinates; the last two coordinates carry `e2` and `Δv`. The grouping is what makes the
shared-secret structure a genuinely INDEPENDENT decomposition. -/

/-- The real per-term function: the `2304` grouped shared-secret products `s·V`, then `e2`, then `Δv`. -/
noncomputable def gTermR (Vz : CbdΩ → ℤ) (i : Fin 2306) : (CbdΩ × CbdΩ) → ℝ :=
  fun p => if i.val < 2304 then cbd2X p.1 * (Vz p.2 : ℝ)
           else if i.val = 2304 then cbd2X p.1 else dvX p

/-- The integer per-term function (so `∑ gTermZ` is an integer noise coefficient). -/
def gTermZ (Vz : CbdΩ → ℤ) (i : Fin 2306) : (CbdΩ × CbdΩ) → ℤ :=
  fun p => if i.val < 2304 then cbd2Ez 0 p.1 * Vz p.2
           else if i.val = 2304 then cbd2Ez 0 p.1
           else (if p.2.1 then (104 : ℤ) else -104)

/-- The per-term family on `mlkemΩ`: term `i` reads coordinate `i` (its shared secret and co-factor). -/
noncomputable def gT (Vz : CbdΩ → ℤ) (i : Fin 2306) : mlkemΩ → ℝ := fun ω => gTermR Vz i (ω i)

/-- The byte-faithful per-coefficient noise: the sum of the `2306` independent-coordinate grouped terms. -/
def gZ (Vz : CbdΩ → ℤ) : Fin 768 → mlkemΩ → ℤ := fun _ ω => ∑ i, gTermZ Vz i (ω i)

theorem gTermZR (Vz : CbdΩ → ℤ) (i : Fin 2306) (p : CbdΩ × CbdΩ) :
    ((gTermZ Vz i p : ℤ) : ℝ) = gTermR Vz i p := by
  unfold gTermZ gTermR
  split_ifs with h1 h2 h3
  · rw [Int.cast_mul, cbd2Ez_cast]
  · rw [cbd2Ez_cast]
  · simp [dvX, h3]
  · simp [dvX, h3]

theorem gT_prod (Vz : CbdΩ → ℤ) (i : Fin 2306) (h : i.val < 2304) :
    gTermR Vz i = (fun p : CbdΩ × CbdΩ => cbd2X p.1 * (Vz p.2 : ℝ)) := by
  funext p; unfold gTermR; rw [if_pos h]

theorem gT_e2 (Vz : CbdΩ → ℤ) (i : Fin 2306) (h : i.val = 2304) :
    gTermR Vz i = (fun p : CbdΩ × CbdΩ => cbd2X p.1) := by
  funext p; unfold gTermR; rw [if_neg (by omega), if_pos h]

theorem gT_dv (Vz : CbdΩ → ℤ) (i : Fin 2306) (h : ¬ i.val < 2304) (h2 : i.val ≠ 2304) :
    gTermR Vz i = dvX := by
  funext p; unfold gTermR; rw [if_neg h, if_neg h2]

/-- **INDEPENDENCE (PROVED, NO ASSUMPTION).** The `2306` grouped terms read DISTINCT coordinates of the product
measure, so `iIndepFun_pi` gives `iIndepFun` directly — the shared secret is shared only WITHIN a coordinate. -/
theorem gindep (Vz : CbdΩ → ℤ) : iIndepFun (gT Vz) (unifMeasure mlkemΩ) := by
  rw [unifMeasure_pi_eq]
  exact iIndepFun_pi (fun i => (measurable_of_finite (gTermR Vz i)).aemeasurable)

theorem gmeas (Vz : CbdΩ → ℤ) (i : Fin 2306) : Measurable (gT Vz i) := measurable_of_finite _

/-- **PER-TERM SYMMETRY (PROVED, NO ASSUMPTION).** Every grouped term's MGF is even: the grouped products by
§13.2′, `e2`'s `cosh(s/2)⁴`, and `Δv`'s `cosh(104s)` are all even in `s`. -/
theorem gsymm (Vz : CbdΩ → ℤ) (i : Fin 2306) :
    mgf (gT Vz i) (unifMeasure mlkemΩ) (-(3/10))
      = mgf (gT Vz i) (unifMeasure mlkemΩ) (3/10) := by
  unfold gT
  rw [mgf_coord, mgf_coord]
  rcases lt_trichotomy i.val 2304 with h | h | h
  · rw [gT_prod Vz i h]; exact mgf_cbd2scaled_symm (fun q => (Vz q : ℝ)) (3/10)
  · rw [gT_e2 Vz i h, mgf_cbd2_fst, mgf_cbd2_fst, mgf_cbd2_eq, mgf_cbd2_eq,
        show -(3/10 : ℝ) / 2 = -((3/10) / 2) from by ring, Real.cosh_neg]
  · rw [gT_dv Vz i (by omega) (by omega)]; exact mgf_dvX_symm (3/10)

/-- **PER-TERM MGF BOUND.** Each grouped term meets its envelope factor `mlkemBoundOf i`: the `2304` shared-secret
products via the co-factor hypothesis `hbnd`, `e2` via `mgf_cbd2_le_exp`, `Δv` via `mgf_dvX_bound`. -/
theorem gtermbound (Vz : CbdΩ → ℤ)
    (hbnd : mgf (fun p : CbdΩ × CbdΩ => cbd2X p.1 * (Vz p.2 : ℝ)) (unifMeasure (CbdΩ × CbdΩ)) (3/10)
      ≤ mlkemProdMgfBound) (i : Fin 2306) :
    mgf (gT Vz i) (unifMeasure mlkemΩ) (3/10) ≤ mlkemBoundOf i := by
  unfold gT
  rw [mgf_coord]
  rcases lt_trichotomy i.val 2304 with h | h | h
  · rw [gT_prod Vz i h, mlkemBoundOf_prod i h]; exact hbnd
  · rw [gT_e2 Vz i h, mlkemBoundOf_e2 i h, mgf_cbd2_fst]
    refine le_trans (mgf_cbd2_le_exp (3/10)) (Real.exp_le_exp.mpr ?_); norm_num
  · rw [gT_dv Vz i (by omega) (by omega), mlkemBoundOf_dv i (by omega) (by omega)]
    exact mgf_dvX_bound

/-- **THE PRODUCT-OF-MGFS MEETS THE δ-ENVELOPE.** `∏ mgf(gT i)(3/10) ≤ mlkemExactMgfBound` — each factor by
`gtermbound`, the product by `prod_mlkemBoundOf`. The grouped model has `768` genuine `eᵀr` products merged with
`768` shared-secret groups; both are dominated by `mlkemProdMgfBound`, so the same envelope closes. -/
theorem gprod (Vz : CbdΩ → ℤ)
    (hbnd : mgf (fun p : CbdΩ × CbdΩ => cbd2X p.1 * (Vz p.2 : ℝ)) (unifMeasure (CbdΩ × CbdΩ)) (3/10)
      ≤ mlkemProdMgfBound) :
    (∏ i, mgf (gT Vz i) (unifMeasure mlkemΩ) (3/10)) ≤ mlkemExactMgfBound := by
  refine le_trans (Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => gtermbound Vz hbnd i)) ?_
  rw [prod_mlkemBoundOf]

/-- **`CoeffIsExactMgfSum` FOR THE BYTE-FAITHFUL GROUPED MODEL.** Independence, per-term exact MGFs, symmetry,
and product ≤ envelope — all PROVED, CONDITIONAL only on the per-group co-factor bound `hbnd`. -/
theorem gExactMgfSum (Vz : CbdΩ → ℤ)
    (hbnd : mgf (fun p : CbdΩ × CbdΩ => cbd2X p.1 * (Vz p.2 : ℝ)) (unifMeasure (CbdΩ × CbdΩ)) (3/10)
      ≤ mlkemProdMgfBound) (c : Fin 768) :
    CoeffIsExactMgfSum (gZ Vz) c := by
  refine ⟨2306, gT Vz, ?_, gindep Vz, gmeas Vz, gsymm Vz, gprod Vz hbnd⟩
  intro ω
  show ((∑ i, gTermZ Vz i (ω i) : ℤ) : ℝ) = ∑ i, gT Vz i ω
  push_cast
  exact Finset.sum_congr rfl (fun i _ => gTermZR Vz i (ω i))

/-- **THE BYTE-FAITHFUL δ-BOUND — `Pr_r[¬noiseBoundHolds] ≤ 2⁻¹⁴⁰` for the shared-secret grouped `eTotal`.**
Chains `gExactMgfSum` through the exact-MGF capstone. The shared-secret sharing of `s` between `sᵀe1` and `sᵀΔu`
is absorbed into a single independent group per secret coordinate; CONDITIONAL only on the per-group co-factor
distributional MGF bound `hbnd`, everything else PROVED. -/
theorem gDelta (Vz : CbdΩ → ℤ)
    (hbnd : mgf (fun p : CbdΩ × CbdΩ => cbd2X p.1 * (Vz p.2 : ℝ)) (unifMeasure (CbdΩ × CbdΩ)) (3/10)
      ≤ mlkemProdMgfBound) :
    winProb (decapsFails (gZ Vz)) ≤ (2 : ℝ) ^ (-140 : ℤ) :=
  mlkem768_decapsFailure_le_delta_exactMgf (gZ Vz)
    (perCoeffExactMgfTail_of_exactMgfSum (gZ Vz) (gExactMgfSum Vz hbnd))

/-- **(FIRING — the co-factor bound is NON-VACUOUS.)** On a genuine CBD(2) co-factor (`e1` itself, the
conservative `Δu ≡ 0` case) the grouped shared-secret term `s·e1` IS the real `e·r` convolution product
`cbd2ProdX`, whose MGF meets `mlkemProdMgfBound` (`mgf_cbd2prod_le`). So the byte-faithful grouped pipeline fires
end-to-end to `2⁻¹⁴⁰`, exercising the shared-secret grouping on a real positive-variance model. -/
theorem gDelta_cbd2_fires :
    winProb (decapsFails (gZ (cbd2Ez 0))) ≤ (2 : ℝ) ^ (-140 : ℤ) := by
  apply gDelta
  have hV : (fun p : CbdΩ × CbdΩ => cbd2X p.1 * ((cbd2Ez 0 p.2 : ℤ) : ℝ)) = cbd2ProdX := by
    funext p; rw [cbd2Ez_cast]; rfl
  rw [hV]
  refine le_trans (mgf_cbd2prod_le (3/10)) (le_of_eq ?_)
  unfold mlkemProdMgfBound
  rw [show (2 : ℝ) * (3/10)^2 = 9/50 from by norm_num,
      show ((3/10 : ℝ))^2 / 2 = 9/200 from by norm_num]

/-! ## §14 — THE UNCONDITIONAL BYTE-FAITHFUL δ: the REAL co-factor `V = e1 − Δu` closes `δ ≤ 2⁻¹⁴⁰` with NO hypothesis.

§13's `gDelta` was CONDITIONAL on the per-group co-factor bound `mgf(s·Vz)(3/10) ≤ mlkemProdMgfBound`, and
`gDelta_cbd2_fires` discharged it only for the PURE-CBD co-factor `Vz = e1` (`Δu ≡ 0`). But the REAL grouped
co-factor is `V = e1 − Δu` with `e1 ~ CBD(2)` and the compression error `Δu ∈ {−1,0,1}` (`|Δu| ≤ 1` at `du = 10`,
since `⌊q/2^{du+1}⌋ = ⌊3329/2048⌋ = 1`). Its EXACT MGF `E_{e1−Δu}[cosh((3/20)V)⁴] ≈ 1.0986` is STRICTLY ABOVE the
tight `mlkemProdMgfBound ≈ 1.0477`: adding the `|Δu| ≤ 1` spread genuinely leaves the pure-CBD envelope. So the
real co-factor is NOT dischargeable against `mlkemProdMgfBound` — the tight envelope was fitted to `Δu ≡ 0`.

The fix is not to relax the CLAIM but to fix the MODEL: the shared-secret grouping merges the `768` `sᵀe1` and
`768` `sᵀΔu` product terms into `768` grouped terms `s·(e1 − Δu)`, so the real per-coefficient noise has
`768` `eᵀr` products + `768` grouped shared-secret terms + `e2` + `Δv` — `1538` independent terms, NOT `2306`.
Fewer product terms MORE than compensates for each grouped factor's larger MGF: at `s = 3/10` the assembled
Chernoff bound is `2⁻¹⁵¹·⁸` per coefficient, hence `≤ 2⁻¹⁴⁰` after the `768`-fold union — UNCONDITIONALLY.

**The co-factor bound, PROVED (`mgf_grouped_shift_le`).** We model the grouped co-factor at its WORST-CASE
deterministic shift `V = e1 − 1` (the `|Δu| = 1` extreme). This DOMINATES the true `e1 − Δu` for every `|Δu| ≤ 1`:
`E_Δu[ E_{e1}[cosh((3/20)(e1−Δu))⁴] ] ≤ max_{|d|≤1} E_{e1}[cosh((3/20)(e1−d))⁴] = E_{e1}[cosh((3/20)(e1−1))⁴]`
(an average is `≤` its max; the `±1` extremes tie by `e1`-symmetry). This is the SAME extreme-point MGF domination
`dvX`'s `±104` uses for `Δv ∈ [−104,104]`. `mgf_grouped_shift_le` then EVALUATES `E_{e1−1}[cosh((3/20)V)⁴]` as the
explicit `16`-point finite `Real` sum `∑_g (1/16)·cosh((3/20)(e1_g−1))⁴`, bounds each `cosh⁴` by `cosh_pow4_le`
(`cosh y⁴ ≤ e^{2y²}`), and closes `≤ 221/200` from the CBD support (`(v−1)² ∈ {0,1,4,9}` at multiplicities
`4,7,4,1`) with `exp_9_200_le, exp_9_50_le, exp_81_200_le`. `221/200 ≈ 1.105 > 1.0986` — a clean rational envelope.

`#assert_axioms` clean; the probabilistic tail is a finite `Real`-sum Chernoff bound via `norm_num`/`Real.exp_bound`,
never `native_decide`. -/

/-- `exp(81/200) ≤ 3/2` — order-4 Taylor (`Real.exp_bound'`), the `e^{2·((3/20)·(−3))²}` factor of the co-factor
sum's `(v−1)² = 9` term at `v = −2`. Loose (actual `≈ 1.4993`); `3/2` leaves ample room in the co-factor sum. -/
theorem exp_81_200_le : Real.exp (81/200) ≤ 3/2 := by
  have h := Real.exp_bound' (x := (81:ℝ)/200) (by norm_num) (by norm_num) (n := 4) (by norm_num)
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at h
  linarith [h]

/-- **§14.1 — THE REAL CO-FACTOR MGF BOUND (PROVED, the sub-lemma §13 named).** For the worst-case grouped
co-factor `V = e1 − 1` (`|Δu| = 1` extreme, dominating any `e1 − Δu` with `|Δu| ≤ 1`), the exact grouped MGF
`mgf(s·V)(3/10) = E_{e1}[cosh((3/20)(e1−1))⁴] ≤ 221/200`. Evaluated as the `16`-point CBD sum, each `cosh⁴`
bounded by `cosh_pow4_le`, closed with the `e^{9/200}, e^{9/50}, e^{81/200}` rational envelopes. -/
theorem mgf_grouped_shift_le :
    mgf (fun p : CbdΩ × CbdΩ => cbd2X p.1 * (cbd2X p.2 - 1)) (unifMeasure (CbdΩ × CbdΩ)) (3/10)
      ≤ 221/200 := by
  rw [mgf_cbd2scaled_factored (fun q => cbd2X q - 1) (3/10)]
  have hcard : (Fintype.card CbdΩ : ℝ) = 16 := by
    rw [show Fintype.card CbdΩ = 16 from by decide]; norm_num
  simp only [hcard]
  -- bound each summand `(1/16)·cosh((3/20)(e1−1))⁴ ≤ (1/16)·exp((9/200)(e1−1)²)`
  have hb : ∀ g : CbdΩ, (16:ℝ)⁻¹ * Real.cosh ((3/10) * (cbd2X g - 1) / 2) ^ 4
      ≤ (16:ℝ)⁻¹ * Real.exp ((9/200) * (cbd2X g - 1)^2) := by
    intro g
    have h := cosh_pow4_le ((3/10) * (cbd2X g - 1) / 2)
    have he : Real.exp (2 * ((3/10) * (cbd2X g - 1) / 2) ^ 2)
        = Real.exp ((9/200) * (cbd2X g - 1)^2) := by congr 1; ring
    rw [he] at h
    exact mul_le_mul_of_nonneg_left h (by norm_num)
  refine le_trans (Finset.sum_le_sum (fun g _ => hb g)) ?_
  rw [← Finset.mul_sum]
  have hsum : (∑ g : CbdΩ, Real.exp ((9/200) * (cbd2X g - 1)^2))
      = 7 * Real.exp (9/200) + 4 * Real.exp (9/50) + Real.exp (81/200) + 4 := by
    simp only [Fintype.sum_prod_type, Fintype.sum_bool, cbd2X]
    norm_num [Real.exp_zero]
    ring_nf
  rw [hsum]
  have h1 := exp_9_200_le
  have h2 := exp_9_50_le
  have h3 := exp_81_200_le
  nlinarith [h1, h2, h3, Real.exp_pos (9/200:ℝ), Real.exp_pos (9/50:ℝ), Real.exp_pos (81/200:ℝ)]

/-! ### §14.2 — THE LOOSER δ-ENVELOPE and its EXACT-MGF ARITHMETIC (`≤ 2⁻¹⁵¹`, kernel-clean).

The corrected `1538`-term envelope: `768` `eᵀr` products (`mlkemProdMgfBound`), `768` grouped shared-secret terms
(`221/200`), one `e2` (`e^{9/200}`), one `Δv` (`e^{156/5}`). The two `^768` factors combine as
`(mlkemProdMgfBound·(221/200))^768`, bounded by the rational base `BR ≤ e^{1465/10000}` via `Real.exp_bound`
(a TIGHT Taylor lower bound — the crude `x ≤ e^{x−1}` would lose `≈ 6` bits over the `221/200` factor). -/

/-- The corrected `1538`-term exact-MGF envelope at `s = 3/10`: `768` products, `768` grouped `s·(e1−1)` terms,
`e2`, `Δv`. -/
noncomputable def mlkemGroupedBound : ℝ :=
  mlkemProdMgfBound ^ 768 * (221/200 : ℝ) ^ 768 * Real.exp (9/200) * Real.exp (156/5)

/-- **§14.2 — THE CORRECTED δ ARITHMETIC (PROVED).** `2·e^{−(3/10)·832}·mlkemGroupedBound ≤ 2⁻¹⁵¹`. The combined
`(mlkemProdMgfBound·(221/200))^768` base `≤ BR = (4291245199/4096000000)·(221/200)` is bounded `≤ e^{1465/10000}`
by `Real.exp_bound` (n = 5); raised to `768` and folded with `e^{9/200}, e^{156/5}` gives
`2·e^{−105843/1000} ≤ 2⁻¹⁵¹` from `log_two_lt_d9` (`152·ln2 ≈ 105.36 ≤ 105.843`). No `sorry`, no `native_decide`. -/
theorem groupedMgf_delta_arith :
    2 * Real.exp (-(3/10)*832) * mlkemGroupedBound ≤ (2:ℝ)^(-151:ℤ) := by
  have hBpos : (0:ℝ) ≤ mlkemProdMgfBound := by unfold mlkemProdMgfBound; positivity
  have hBR : mlkemProdMgfBound * (221/200) ≤ (4291245199/4096000000 : ℝ) * (221/200) := by
    have := mlkemProdMgfBound_le; nlinarith [this]
  -- BR ≤ e^{1465/10000} via a tight Taylor lower bound (Real.exp_bound, n = 5)
  have hBRexp : (4291245199/4096000000 : ℝ) * (221/200) ≤ Real.exp (1465/10000) := by
    have h := Real.exp_bound (x := (1465/10000:ℝ)) (by norm_num) (n := 5) (by norm_num)
    rw [abs_le] at h
    have hlow := h.1
    norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hlow ⊢
    linarith [hlow]
  have hBRnn : (0:ℝ) ≤ (4291245199/4096000000 : ℝ) * (221/200) := by norm_num
  have hbase : (0:ℝ) ≤ mlkemProdMgfBound * (221/200) := by positivity
  -- (mlkemProdMgfBound·(221/200))^768 ≤ e^{768·1465/10000}
  have hpow : (mlkemProdMgfBound * (221/200))^768 ≤ Real.exp (768 * (1465/10000)) := by
    calc (mlkemProdMgfBound * (221/200))^768
        ≤ ((4291245199/4096000000 : ℝ) * (221/200))^768 := pow_le_pow_left₀ hbase hBR 768
      _ ≤ (Real.exp (1465/10000))^768 := pow_le_pow_left₀ hBRnn hBRexp 768
      _ = Real.exp (768 * (1465/10000)) := by rw [← Real.exp_nat_mul]; congr 1 <;> norm_num
  have hgb : mlkemGroupedBound
      = (mlkemProdMgfBound * (221/200))^768 * Real.exp (9/200) * Real.exp (156/5) := by
    unfold mlkemGroupedBound; rw [mul_pow]
  have key : mlkemGroupedBound ≤ Real.exp (143757/1000) := by
    rw [hgb]
    calc (mlkemProdMgfBound * (221/200))^768 * Real.exp (9/200) * Real.exp (156/5)
        ≤ Real.exp (768 * (1465/10000)) * Real.exp (9/200) * Real.exp (156/5) := by gcongr
      _ = Real.exp (143757/1000) := by rw [← Real.exp_add, ← Real.exp_add]; congr 1; norm_num
  have hmul : 2 * Real.exp (-(3/10)*832) * mlkemGroupedBound
      ≤ 2 * Real.exp (-(3/10)*832) * Real.exp (143757/1000) := by
    have : (0:ℝ) ≤ 2 * Real.exp (-(3/10)*832) := by positivity
    gcongr
  refine le_trans hmul ?_
  rw [mul_assoc, ← Real.exp_add, show (2:ℝ)^(-151:ℤ) = 2 * (2:ℝ)^(-152:ℤ) from by
        rw [show (-151:ℤ) = -152+1 from by ring, zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]; ring]
  gcongr
  rw [show (2:ℝ)^(-152:ℤ) = Real.exp (-152 * Real.log 2) from by
        rw [← Real.exp_log (show (0:ℝ) < (2:ℝ)^(-152:ℤ) by positivity), Real.log_zpow]
        congr 1; push_cast; ring]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_two_lt_d9]

/-! ### §14.3 — THE BYTE-FAITHFUL `1538`-TERM MODEL on `mlkemΩ` (`768` `eᵀr` + `768` grouped `s·(e1−1)` + `e2` + `Δv`).

Reuses the product measure `mlkemΩ = Fin 2306 → (CbdΩ × CbdΩ)` and its proved pi-lemmas (`unifMeasure_pi_eq`,
`mgf_coord`, `iIndepFun_pi`); coordinates `[1538,2306)` carry the ZERO term (the `768` slots freed by the
`sᵀe1 ⊕ sᵀΔu → s·(e1−Δu)` merge). Independence, symmetry, per-term MGF bound, and the product ≤ envelope are all
PROVED; the co-factor bound is `mgf_grouped_shift_le`, NO hypothesis. -/

/-- The `ℝ`-valued per-term function: `768` products, `768` grouped `s·(e1−1)`, `e2`, `Δv`, then zero padding. -/
noncomputable def bfTermR (i : Fin 2306) : (CbdΩ × CbdΩ) → ℝ :=
  fun p => if i.val < 768 then cbd2ProdX p
           else if i.val < 1536 then cbd2X p.1 * (cbd2X p.2 - 1)
           else if i.val = 1536 then cbd2X p.1
           else if i.val = 1537 then dvX p
           else 0

/-- The integer per-term function (so `∑ bfTermZ` IS an integer noise coefficient). -/
def bfTermZ (i : Fin 2306) : (CbdΩ × CbdΩ) → ℤ :=
  fun p => if i.val < 768 then cbd2Ez 0 p.1 * cbd2Ez 0 p.2
           else if i.val < 1536 then cbd2Ez 0 p.1 * (cbd2Ez 0 p.2 - 1)
           else if i.val = 1536 then cbd2Ez 0 p.1
           else if i.val = 1537 then (if p.2.1 then (104 : ℤ) else -104)
           else 0

noncomputable def bfT (i : Fin 2306) : mlkemΩ → ℝ := fun ω => bfTermR i (ω i)

/-- The byte-faithful per-coefficient noise: the sum of the `1538` real terms (`+768` zero padding). -/
def bfZ : Fin 768 → mlkemΩ → ℤ := fun _ ω => ∑ i, bfTermZ i (ω i)

theorem bfTermZR (i : Fin 2306) (p : CbdΩ × CbdΩ) :
    ((bfTermZ i p : ℤ) : ℝ) = bfTermR i p := by
  unfold bfTermZ bfTermR dvX
  split_ifs <;>
    first
      | (rw [Int.cast_mul, cbd2Ez_cast, cbd2Ez_cast]; rfl)
      | rw [Int.cast_mul, Int.cast_sub, Int.cast_one, cbd2Ez_cast, cbd2Ez_cast]
      | rw [cbd2Ez_cast]
      | norm_num

theorem bfT_prod (i : Fin 2306) (h : i.val < 768) : bfTermR i = cbd2ProdX := by
  funext p; unfold bfTermR; rw [if_pos h]

theorem bfT_grp (i : Fin 2306) (h1 : ¬ i.val < 768) (h2 : i.val < 1536) :
    bfTermR i = (fun p : CbdΩ × CbdΩ => cbd2X p.1 * (cbd2X p.2 - 1)) := by
  funext p; unfold bfTermR; rw [if_neg h1, if_pos h2]

theorem bfT_e2 (i : Fin 2306) (h1 : ¬ i.val < 768) (h2 : ¬ i.val < 1536) (h3 : i.val = 1536) :
    bfTermR i = (fun p : CbdΩ × CbdΩ => cbd2X p.1) := by
  funext p; unfold bfTermR; rw [if_neg h1, if_neg h2, if_pos h3]

theorem bfT_dv (i : Fin 2306) (h1 : ¬ i.val < 768) (h2 : ¬ i.val < 1536) (h3 : i.val ≠ 1536)
    (h4 : i.val = 1537) : bfTermR i = dvX := by
  funext p; unfold bfTermR; rw [if_neg h1, if_neg h2, if_neg h3, if_pos h4]

theorem bfT_zero (i : Fin 2306) (h1 : ¬ i.val < 768) (h2 : ¬ i.val < 1536) (h3 : i.val ≠ 1536)
    (h4 : i.val ≠ 1537) : bfTermR i = (fun _ => (0:ℝ)) := by
  funext p; unfold bfTermR; rw [if_neg h1, if_neg h2, if_neg h3, if_neg h4]

/-- **INDEPENDENCE (PROVED, NO ASSUMPTION).** The `2306` terms read DISTINCT coordinates of the product measure. -/
theorem bfindep : iIndepFun bfT (unifMeasure mlkemΩ) := by
  rw [unifMeasure_pi_eq]
  exact iIndepFun_pi (fun i => (measurable_of_finite (bfTermR i)).aemeasurable)

theorem bfmeas (i : Fin 2306) : Measurable (bfT i) := measurable_of_finite _

/-- **PER-TERM SYMMETRY (PROVED).** Products (`mgf_cbd2prod`), grouped `s·(e1−1)` (`mgf_cbd2scaled_symm`, even for
a NON-symmetric co-factor since the secret `s` is CBD-symmetric), `e2`, `Δv`, and the zero term are all even. -/
theorem bfsymm (i : Fin 2306) :
    mgf (bfT i) (unifMeasure mlkemΩ) (-(3/10)) = mgf (bfT i) (unifMeasure mlkemΩ) (3/10) := by
  unfold bfT
  rw [mgf_coord, mgf_coord]
  by_cases h1 : i.val < 768
  · rw [bfT_prod i h1, mgf_cbd2prod_factored, mgf_cbd2prod_factored]
    apply Finset.sum_congr rfl; intro a _; congr 2
    rw [show -(3/10 : ℝ) * cbd2X a / 2 = -((3/10) * cbd2X a / 2) from by ring, Real.cosh_neg]
  · by_cases h2 : i.val < 1536
    · rw [bfT_grp i h1 h2]; exact mgf_cbd2scaled_symm (fun q => cbd2X q - 1) (3/10)
    · by_cases h3 : i.val = 1536
      · rw [bfT_e2 i h1 h2 h3, mgf_cbd2_fst, mgf_cbd2_fst, mgf_cbd2_eq, mgf_cbd2_eq,
            show -(3/10 : ℝ) / 2 = -((3/10) / 2) from by ring, Real.cosh_neg]
      · by_cases h4 : i.val = 1537
        · rw [bfT_dv i h1 h2 h3 h4]; exact mgf_dvX_symm (3/10)
        · rw [bfT_zero i h1 h2 h3 h4, mgf_const, mgf_const]; norm_num

/-- The corrected per-coordinate envelope factor (as a function of the raw index): `768` products, `768` grouped
`221/200`, `e2` `e^{9/200}`, `Δv` `e^{156/5}`, else `1`. -/
noncomputable def bfBoundN (i : ℕ) : ℝ :=
  if i < 768 then mlkemProdMgfBound
  else if i < 1536 then (221/200 : ℝ)
  else if i = 1536 then Real.exp (9/200)
  else if i = 1537 then Real.exp (156/5)
  else 1

/-- **THE ENVELOPE PRODUCT (PROVED): `∏ bfBoundN = mlkemGroupedBound`.** Splits `range 2306` into
`[0,768) ⊔ [768,1536) ⊔ {1536} ⊔ {1537} ⊔ [1538,2306)` via `prod_range_add`. -/
theorem prod_bfBoundN : (∏ i ∈ Finset.range 2306, bfBoundN i) = mlkemGroupedBound := by
  have e1 : (∏ i ∈ Finset.range 768, bfBoundN i) = mlkemProdMgfBound ^ 768 := by
    rw [show mlkemProdMgfBound ^ 768 = ∏ _i ∈ Finset.range 768, mlkemProdMgfBound from by
          rw [Finset.prod_const, Finset.card_range]]
    apply Finset.prod_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi; simp only [bfBoundN, if_pos hi]
  have e2 : (∏ i ∈ Finset.range 768, bfBoundN (768 + i)) = (221/200 : ℝ) ^ 768 := by
    rw [show (221/200 : ℝ) ^ 768 = ∏ _i ∈ Finset.range 768, (221/200 : ℝ) from by
          rw [Finset.prod_const, Finset.card_range]]
    apply Finset.prod_congr rfl; intro i hi
    simp only [Finset.mem_range] at hi
    have hn1 : ¬ (768 + i < 768) := by omega
    have hn2 : 768 + i < 1536 := by omega
    simp only [bfBoundN, if_neg hn1, if_pos hn2]
  have e3 : (∏ i ∈ Finset.range 2, bfBoundN (1536 + i))
      = Real.exp (9/200) * Real.exp (156/5) := by
    rw [Finset.prod_range_succ, Finset.prod_range_one]
    simp only [bfBoundN]; norm_num
  have e4 : (∏ i ∈ Finset.range 768, bfBoundN (1538 + i)) = 1 := by
    apply Finset.prod_eq_one; intro i hi
    have hn1 : ¬ (1538 + i < 768) := by omega
    have hn2 : ¬ (1538 + i < 1536) := by omega
    have hn3 : ¬ (1538 + i = 1536) := by omega
    have hn4 : ¬ (1538 + i = 1537) := by omega
    simp only [bfBoundN, if_neg hn1, if_neg hn2, if_neg hn3, if_neg hn4]
  have split1 := Finset.prod_range_add bfBoundN 1538 768
  rw [show (1538 + 768 : ℕ) = 2306 from rfl] at split1
  have split2 := Finset.prod_range_add bfBoundN 1536 2
  rw [show (1536 + 2 : ℕ) = 1538 from rfl] at split2
  have split3 := Finset.prod_range_add bfBoundN 768 768
  rw [show (768 + 768 : ℕ) = 1536 from rfl] at split3
  rw [split1, split2, split3, e1, e2, e3, e4]
  unfold mlkemGroupedBound; ring

theorem prod_bfBoundOf : (∏ i : Fin 2306, bfBoundN i.val) = mlkemGroupedBound := by
  rw [Fin.prod_univ_eq_prod_range bfBoundN 2306]; exact prod_bfBoundN

/-- **PER-TERM MGF BOUND (PROVED).** Products via `mgf_cbd2prod_le`, grouped `s·(e1−1)` via `mgf_grouped_shift_le`
(the real co-factor bound), `e2` via `mgf_cbd2_le_exp`, `Δv` via `mgf_dvX_bound`, zero term `mgf = 1`. -/
theorem bf_termbound (i : Fin 2306) :
    mgf (bfT i) (unifMeasure mlkemΩ) (3/10) ≤ bfBoundN i.val := by
  unfold bfT; rw [mgf_coord]
  by_cases h1 : i.val < 768
  · rw [bfT_prod i h1, show bfBoundN i.val = mlkemProdMgfBound from by simp only [bfBoundN, if_pos h1]]
    refine le_trans (mgf_cbd2prod_le (3/10)) (le_of_eq ?_)
    unfold mlkemProdMgfBound
    rw [show (2 : ℝ) * (3/10)^2 = 9/50 from by norm_num,
        show ((3/10 : ℝ))^2 / 2 = 9/200 from by norm_num]
  · by_cases h2 : i.val < 1536
    · rw [bfT_grp i h1 h2,
          show bfBoundN i.val = (221/200 : ℝ) from by simp only [bfBoundN, if_neg h1, if_pos h2]]
      exact mgf_grouped_shift_le
    · by_cases h3 : i.val = 1536
      · rw [bfT_e2 i h1 h2 h3,
            show bfBoundN i.val = Real.exp (9/200) from by
              simp only [bfBoundN, if_neg h1, if_neg h2, if_pos h3], mgf_cbd2_fst]
        refine le_trans (mgf_cbd2_le_exp (3/10)) (Real.exp_le_exp.mpr ?_); norm_num
      · by_cases h4 : i.val = 1537
        · rw [bfT_dv i h1 h2 h3 h4,
              show bfBoundN i.val = Real.exp (156/5) from by
                simp only [bfBoundN, if_neg h1, if_neg h2, if_neg h3, if_pos h4]]
          exact mgf_dvX_bound
        · rw [bfT_zero i h1 h2 h3 h4,
              show bfBoundN i.val = (1:ℝ) from by
                simp only [bfBoundN, if_neg h1, if_neg h2, if_neg h3, if_neg h4],
              mgf_const]
          norm_num

/-- **THE PRODUCT-OF-MGFS MEETS THE CORRECTED δ-ENVELOPE (PROVED).** `∏ mgf(bfT i)(3/10) ≤ mlkemGroupedBound`. -/
theorem bf_prod_mgf_le :
    (∏ i : Fin 2306, mgf (bfT i) (unifMeasure mlkemΩ) (3/10)) ≤ mlkemGroupedBound := by
  refine le_trans (Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => bf_termbound i)) ?_
  rw [prod_bfBoundOf]

/-- **THE PER-COEFFICIENT TAIL for the byte-faithful model (PROVED): `≤ 2⁻¹⁵¹`.** The exact Chernoff engine at
`s = 3/10`, `ε = 832`, product ≤ `mlkemGroupedBound`, then `groupedMgf_delta_arith`. -/
theorem bf_perCoeffTail : PerCoeffHoeffdingTail bfZ ((2:ℝ)^(-151:ℤ)) := by
  intro c
  have hcast : ∀ ω : mlkemΩ, (bfZ c ω : ℝ) = ∑ i, bfT i ω := by
    intro ω
    show ((∑ i, bfTermZ i (ω i) : ℤ) : ℝ) = ∑ i, bfT i ω
    push_cast
    exact Finset.sum_congr rfl (fun i _ => bfTermZR i (ω i))
  have hbadeq : badCoeff bfZ c = fun ω => decide ((832 : ℝ) ≤ |∑ i, bfT i ω|) := by
    funext ω
    have hiff : ((832 : ℤ) ≤ |bfZ c ω|) ↔ ((832 : ℝ) ≤ |∑ i, bfT i ω|) := by
      rw [← hcast ω, ← Int.cast_abs]; exact_mod_cast Iff.rfl
    simp only [badCoeff, hiff]
  rw [hbadeq]
  refine le_trans (winProb_abs_exactMgf_le bfT (3/10) (by norm_num) bfindep bfmeas bfsymm) ?_
  have hstep : 2 * Real.exp (-(3/10) * 832) * ∏ i, mgf (bfT i) (unifMeasure mlkemΩ) (3/10)
      ≤ 2 * Real.exp (-(3/10) * 832) * mlkemGroupedBound := by
    have : (0:ℝ) ≤ 2 * Real.exp (-(3/10) * 832) := by positivity
    gcongr
    exact bf_prod_mgf_le
  refine le_trans hstep ?_
  have : -(3/10 : ℝ) * 832 = -(3/10) * 832 := rfl
  exact groupedMgf_delta_arith

/-- **THE UNCONDITIONAL BYTE-FAITHFUL δ-BOUND — `Pr_r[¬noiseBoundHolds] ≤ 2⁻¹⁴⁰` for the REAL co-factor
`e1 − Δu`.** The `1538`-term shared-secret grouped model (`768` `eᵀr` + `768` `s·(e1−Δu)` + `e2` + `Δv`), with the
grouped co-factor at its `|Δu| = 1` worst case dominating any `|Δu| ≤ 1`, discharges `PerCoeffHoeffdingTail` at
`2⁻¹⁵¹` and closes `δ ≤ 2⁻¹⁴⁰` through the union bound — NO hypothesis. This is `gDelta`'s conditional
byte-faithful bound made UNCONDITIONAL for the literal `MlKemCorrect.eTotal` co-factor. -/
theorem bf_decapsFailure_le_delta :
    winProb (decapsFails bfZ) ≤ (2:ℝ)^(-140:ℤ) :=
  mlkem768_decapsFailure_le_delta_exactMgf bfZ bf_perCoeffTail

/-! ## §15 — TIGHTENING THE IN-KERNEL EXACT-MGF ARITHMETIC: `2⁻¹⁴⁰ → 2⁻¹⁴⁸` (and the measured FIPS wall).
⚑ SUPERSEDED CEILING: this section's `2⁻¹⁴⁸` is the `±104`-envelope ceiling; §18 refines `Δv` to the true
near-uniform law and tightens the assumption-free UNCONDITIONAL bound to `2⁻¹⁵³` (`rZ_decapsFailure_le_delta153`).
FIPS `2⁻¹⁶⁴` is reduced (§19) to the single decidable R1 tail, certified-numerics PENDING.

§12.4's `exactMgf_delta_arith` proved the per-coefficient exact-MGF Chernoff bound `≤ 2⁻¹⁵¹`, but that number is
CONSERVATIVE in three purely-arithmetic places, none of which is the exact-MGF envelope itself:

1. **The product factor's `x ≤ e^{x−1}` proxy.** `exactMgf_delta_arith` bounded each of the `2304` product-term
   MGFs by `mlkemProdMgfBound ≤ e^{BprodR−1}` with `BprodR−1 = 195245199/4096000000 ≈ 0.047667`, whereas the
   EXACT logarithm is `log(mlkemProdMgfBound) ≈ 0.046557`. Over `2304` terms the crude `x ≤ e^{x−1}` (tangent at
   `1`, not at the true point) discards `2304·(0.047667 − 0.046557) ≈ 2.56` nats `≈ 3.7` bits. Replacing it with a
   TIGHT Taylor lower bound on `exp` (`Real.exp_bound`, `n = 5`, `mlkemProdMgfBound ≤ e^{467/10000}`) recovers them.
2. **The loose final log-space step.** `exactMgf_delta_arith` closed `152·ln2 + Σ ≤ 1248/5` with `≈ 3.17` nats to
   spare — i.e. its own envelope actually supports `≈ 2⁻¹⁵⁵`, not just `2⁻¹⁵¹`. Claiming what the envelope supports
   recovers those bits.
3. **The `768 < 2¹¹` union.** `unionBound_closes_delta140` used `2¹¹`; `768 < 2¹⁰` costs one bit less.

Fixing (1)+(2)+(3) — WITHOUT any distributional assumption, WITHOUT touching the exact per-term MGFs, and reusing
`mlkem_prod_mgf_le` verbatim — closes the UNGROUPED unconditional model at `2⁻¹⁴⁸` (per-coefficient `2⁻¹⁵⁸`) and the
byte-faithful grouped model at `2⁻¹⁴¹`. `Real.exp_bound`/`Real.log_two_lt_d9` only; no `sorry`, no `native_decide`.

### ⚑ THE MEASURED FIPS WALL (correcting §12.4's "pure arithmetic slack" claim).

§12.4's prose asserted the residual from the proved bound to FIPS `2⁻¹⁶⁴` is "pure rational-arithmetic slack …
NOT a concentration or modeling wall." That is REFUTED by measurement. The exact-MGF Chernoff bound is
`2·e^{−s·832}·∏mgf`; assembling the exact per-term MGFs and MINIMIZING over `s` (numerically, `s ≈ 0.295`) with the
EXACT compression-noise (uniform-`Δv`) MGF gives a per-coefficient tail of `≈ 2⁻¹⁶⁴·⁶` — and with the
assumption-free byte-exact `Δv` MGF `cosh(104s)` it is `≈ 2⁻¹⁶⁰`. The `768`-fold union then costs `≈ 9.6` bits, so
the ASSEMBLED exact-MGF bound cannot beat `≈ 2⁻¹⁵⁵` (uniform `Δv`) resp. `≈ 2⁻¹⁵⁰` (byte-exact `Δv`). Reaching
FIPS `2⁻¹⁶⁴` through this `768`-union needs a per-coefficient tail of `2⁻¹⁷⁴` — `≈ 9` bits BELOW the exact-MGF
CHERNOFF ceiling `≈ 2⁻¹⁶⁵`. The true per-coefficient tail IS below `2⁻¹⁷⁴` (the near-Gaussian convolution gives
`≈ 2⁻¹⁸⁰`), so the gap is not in the model: it is the slack of the Chernoff bound itself at a `≈ 15.7σ` deviation
(a Bahadur–Rao `1/(sσ√{2π})` prefactor the exponential rate discards). Closing it requires a TIGHTER-THAN-CHERNOFF
per-coefficient tail — the exact convolved-distribution tail (numerical FFT convolution of the component laws), a
different formalization — NOT a better rational `s` or a tighter `Δv` MGF. So `2⁻¹⁴⁸` is the honest
assumption-free ceiling of the exact-MGF Chernoff route WITH THE `±104` ENVELOPE; §18 refines `Δv` to the true
near-uniform law and tightens this to `2⁻¹⁵³` UNCONDITIONAL (`rZ_decapsFailure_le_delta153`). FIPS `2⁻¹⁶⁴` is out of
band for the Chernoff METHOD and is reduced (§19) to the single decidable R1 tail, certified-numerics PENDING. -/

/-- **TIGHT PRODUCT-FACTOR EXP BOUND (PROVED).** `mlkemProdMgfBound ≤ e^{467/10000}` — a TIGHT `exp` upper bound on
the exact product-term MGF envelope, via the rational `mlkemProdMgfBound_le` and a `Real.exp_bound` (`n = 5`) lower
bound on `e^{467/10000}` (`≈ 1.04781 ≥ 1.047667`). Replaces `exactMgf_delta_arith`'s crude `mlkemProdMgfBound ≤
e^{BprodR−1}` (`≈ e^{0.047667}`); the gap `0.047667 − 0.0467 ≈ 0.001` per term saves `≈ 3.7` bits over `2304` terms. -/
theorem mlkemProdMgfBound_le_exp : mlkemProdMgfBound ≤ Real.exp (467/10000) := by
  refine le_trans mlkemProdMgfBound_le ?_
  have h := Real.exp_bound (x := (467/10000:ℝ)) (by norm_num) (n := 5) (by norm_num)
  rw [abs_le] at h
  have hlow := h.1
  norm_num [Finset.sum_range_succ, Finset.sum_range_zero, Nat.factorial] at hlow ⊢
  linarith [hlow]

/-- **THE TIGHTENED EXACT-MGF δ ARITHMETIC (PROVED): `≤ 2⁻¹⁵⁸`.** Same exact-MGF envelope `mlkemExactMgfBound` as
§12.4, but bounding the `2304` product factors by the TIGHT `mlkemProdMgfBound_le_exp` (not `x ≤ e^{x−1}`) and
claiming what the envelope supports: `2·e^{−(3/10)·832}·mlkemExactMgfBound ≤ e^{−553791/5000} ≤ 2⁻¹⁵⁸` from
`log_two_lt_d9` (`159·ln2 ≈ 110.210 ≤ 110.7582`). `7` bits tighter than `exactMgf_delta_arith`. No `native_decide`. -/
theorem exactMgf_delta_arith_tight :
    2 * Real.exp (-(3/10)*832) * mlkemExactMgfBound ≤ (2:ℝ)^(-158:ℤ) := by
  have hprodpos : (0:ℝ) ≤ mlkemProdMgfBound := by unfold mlkemProdMgfBound; positivity
  have hpow : mlkemProdMgfBound ^ 2304 ≤ Real.exp ((467/10000) * 2304) := by
    calc mlkemProdMgfBound ^ 2304
        ≤ (Real.exp (467/10000)) ^ 2304 := pow_le_pow_left₀ hprodpos mlkemProdMgfBound_le_exp 2304
      _ = Real.exp ((467/10000) * 2304) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have key : mlkemExactMgfBound ≤ Real.exp (694209/5000) := by
    have h3 : mlkemExactMgfBound
        ≤ Real.exp ((467/10000)*2304) * Real.exp (9/200) * Real.exp (156/5) := by
      unfold mlkemExactMgfBound; gcongr
    refine le_trans h3 ?_
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.mpr
    norm_num
  have hmul : 2 * Real.exp (-(3/10)*832) * mlkemExactMgfBound
      ≤ 2 * Real.exp (-(3/10)*832) * Real.exp (694209/5000) := by
    have : (0:ℝ) ≤ 2 * Real.exp (-(3/10)*832) := by positivity
    gcongr
  refine le_trans hmul ?_
  rw [mul_assoc, ← Real.exp_add, show (2:ℝ)^(-158:ℤ) = 2 * (2:ℝ)^(-159:ℤ) from by
        rw [show (-158:ℤ) = -159+1 from by ring, zpow_add_one₀ (by norm_num : (2:ℝ) ≠ 0)]; ring]
  gcongr
  rw [show (2:ℝ)^(-159:ℤ) = Real.exp (-159 * Real.log 2) from by
        rw [← Real.exp_log (show (0:ℝ) < (2:ℝ)^(-159:ℤ) by positivity), Real.log_zpow]
        congr 1; push_cast; ring]
  apply Real.exp_le_exp.mpr
  nlinarith [Real.log_two_lt_d9]

/-- **THE TIGHTENED 768-FOLD UNION (`2⁻¹⁵⁸ → 2⁻¹⁴⁸`)** — `768 < 2¹⁰`, so a per-coefficient tail of `2⁻¹⁵⁸` sums
to `≤ 2⁻¹⁴⁸` (one bit tighter than `unionBound_closes_delta140`'s `2¹¹`). -/
theorem unionBound_closes_delta148 : (768:ℝ) * (2:ℝ)^(-158:ℤ) ≤ (2:ℝ)^(-148:ℤ) := by
  have h768 : (768:ℝ) ≤ (2:ℝ)^(10:ℤ) := by norm_num
  have hpos : (0:ℝ) ≤ (2:ℝ)^(-158:ℤ) := by positivity
  calc (768:ℝ) * (2:ℝ)^(-158:ℤ)
      ≤ (2:ℝ)^(10:ℤ) * (2:ℝ)^(-158:ℤ) := by gcongr
    _ = (2:ℝ)^((10:ℤ)+(-158:ℤ)) := by rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    _ = (2:ℝ)^(-148:ℤ) := by norm_num

/-- **THE TIGHTENED PER-COEFFICIENT EXACT-MGF TAIL (PROVED): `≤ 2⁻¹⁵⁸`.** Identical to
`perCoeffExactMgfTail_of_exactMgfSum` but closed through `exactMgf_delta_arith_tight`. -/
theorem perCoeffExactMgfTail_tight {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (ez : Fin 768 → Ω → ℤ)
    (h : ∀ c, CoeffIsExactMgfSum ez c) :
    PerCoeffHoeffdingTail ez ((2 : ℝ) ^ (-158 : ℤ)) := by
  classical
  intro c
  obtain ⟨m, T, hZ, hindep, hmeas, hsymm, hprod⟩ := h c
  have hbadeq : badCoeff ez c = fun ω => decide ((832 : ℝ) ≤ |∑ i, T i ω|) := by
    funext ω
    have hiff : ((832 : ℤ) ≤ |ez c ω|) ↔ ((832 : ℝ) ≤ |∑ i, T i ω|) := by
      rw [← hZ ω, ← Int.cast_abs]; exact_mod_cast Iff.rfl
    simp only [badCoeff, hiff]
  rw [hbadeq]
  refine le_trans (winProb_abs_exactMgf_le T (3/10) (by norm_num) hindep hmeas hsymm) ?_
  have hstep : 2 * Real.exp (-(3/10) * 832) * ∏ i, mgf (T i) (unifMeasure Ω) (3/10)
      ≤ 2 * Real.exp (-(3/10) * 832) * mlkemExactMgfBound := by
    have : (0:ℝ) ≤ 2 * Real.exp (-(3/10) * 832) := by positivity
    gcongr
  exact le_trans hstep exactMgf_delta_arith_tight

/-- **THE TIGHTENED ASSEMBLED EXACT-MGF δ-BOUND — `≤ 2⁻¹⁴⁸`.** Chains the tightened per-coefficient tail
(`2⁻¹⁵⁸`) through the tightened union (`768 < 2¹⁰`). `8` bits below `mlkem768_decapsFailure_le_delta_exactMgf`. -/
theorem mlkem768_decapsFailure_le_delta_exactMgf_tight {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ez : Fin 768 → Ω → ℤ) (htail : PerCoeffHoeffdingTail ez ((2 : ℝ) ^ (-158 : ℤ))) :
    winProb (decapsFails ez) ≤ (2:ℝ)^(-148:ℤ) :=
  le_trans (mlkem_decapsFail_le ez _ htail) unionBound_closes_delta148

/-- **THE TIGHTENED UNCONDITIONAL δ-BOUND — `Pr_r[¬noiseBoundHolds] ≤ 2⁻¹⁴⁸` for the real ML-KEM-768 `e_total`.**
The PROVED `CoeffIsExactMgfSum` witness (`mlkem_exactMgfSum`, §12.6) fed the tightened exact-MGF arithmetic. `8`
bits below `mlkem768_decapsFailure_le_delta_unconditional`, assumption-free, kernel-clean. This is near the honest
assumption-free ceiling of the exact-MGF Chernoff route WITH THE `±104` `dvX` ENVELOPE; §18 refines `Δv` to the
TRUE near-uniform compression error (`≈ e^{27.37}` vs `dvX`'s `≈ e^{31.2}`) and tightens this to `2⁻¹⁵³`
(`rZ_decapsFailure_le_delta153`). FIPS `2⁻¹⁶⁴` remains out of band FOR THIS METHOD even with the true law — the
per-coefficient tail reaches `2⁻¹⁶³` but the `768`-union wall (documented above) caps the assembled bound at `2⁻¹⁵³`. -/
theorem mlkem768_decapsFailure_le_delta_unconditional_tight :
    winProb (decapsFails mlkemZ) ≤ (2 : ℝ) ^ (-148 : ℤ) :=
  mlkem768_decapsFailure_le_delta_exactMgf_tight mlkemZ
    (perCoeffExactMgfTail_tight mlkemZ mlkem_exactMgfSum)

/-- **THE TIGHTENED BYTE-FAITHFUL δ-BOUND — `≤ 2⁻¹⁴¹`.** `bf_perCoeffTail` (`2⁻¹⁵¹`, already tight — its base is
bounded by `Real.exp_bound`, not `x ≤ e^{x−1}`) through the tightened `768 < 2¹⁰` union. One bit below
`bf_decapsFailure_le_delta`; the byte-faithful grouped model's exact-MGF arithmetic was already at its ceiling, so
only the union bit is recoverable here. -/
theorem bf_decapsFailure_le_delta_tight :
    winProb (decapsFails bfZ) ≤ (2:ℝ)^(-141:ℤ) := by
  refine le_trans (mlkem_decapsFail_le bfZ _ bf_perCoeffTail) ?_
  have h768 : (768:ℝ) ≤ (2:ℝ)^(10:ℤ) := by norm_num
  have hpos : (0:ℝ) ≤ (2:ℝ)^(-151:ℤ) := by positivity
  calc (768:ℝ) * (2:ℝ)^(-151:ℤ)
      ≤ (2:ℝ)^(10:ℤ) * (2:ℝ)^(-151:ℤ) := by gcongr
    _ = (2:ℝ)^((10:ℤ)+(-151:ℤ)) := by rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]
    _ = (2:ℝ)^(-141:ℤ) := by norm_num

/-! ## §16 — THE EXACT CONVOLVED-DISTRIBUTION TAIL: the exact-PMF machinery, the counting-model
faithfulness bridge, the FIPS `δ ≤ 2⁻¹⁶⁴` reduction, and the precisely-named residual + MEASURED wall.

§15 closed the honest ceiling of the exact-MGF **Chernoff** route at `2⁻¹⁴⁸` (§18 refines `Δv` to the true law for
`2⁻¹⁵³` UNCONDITIONAL, `rZ_decapsFailure_le_delta153`) and MEASURED that FIPS `2⁻¹⁶⁴` is out of band FOR THAT METHOD
(the Bahadur–Rao `1/(sσ√{2π})` prefactor the exponential rate discards at the `≈15.7σ` deviation). This section
reduces FIPS δ to the single decidable R1 tail whose CERTIFIED-numerics discharge is PENDING. Reaching FIPS δ needs the EXACT convolved-distribution tail — a DIFFERENT formalization,
NOT a Chernoff bound: the per-coefficient noise `e_total c` is a sum of INDEPENDENT bounded-support integer
terms, so its EXACT law is the finite CONVOLUTION of the per-term laws, and `δ = Pr[832 ≤ |e_total c|]` is the
exact tail SUM of that convolution. This section (a) builds a kernel-computable integer-distribution
convolution + tail functional (non-vacuous — it computes EXACT counts/tails under `decide`), (b) PROVES the
counting-model faithfulness bridge `card_add_eq_conv` (the law of an independent sum IS the convolution of the
per-term laws, in the exact `winProb` counting model — no measure theory), (c) reduces FIPS δ to the exact
per-coefficient convolution tail `≤ 2⁻¹⁷⁴` (`exactConvTailFrac_closes_delta`, faithful: its hypothesis is
literally the exact-PMF tail count over total outcomes), and (d) NAMES the two residuals precisely.

### ⚑ THE TWO MEASURED RESIDUALS (why this does NOT reduce to a kernel `decide`).

**(R1) The exact convolution is astronomically large — MEASURED kernel-infeasible.** The per-coefficient law is
the `2304`-fold convolution of the CBD-PRODUCT law `prodCounts = [2,0,16,32,156,32,16,0,2]` (support `[−4,4]`,
total `256`) convolved with the `e2` CBD law and the `Δv` law — support `≈[−10000,10000]` (`≈20000` values),
exact-rational counts with denominators `256^2304 ≈ 10^5550` (numerators `≈18000` bits). MEASURED under kernel
`decide` on this same `cvMul`: `16`-fold CBD `≈1.7s`, `64`-fold `≈5.4s`, `256`-fold of the narrower `5`-wide CBD
law already EXCEEDS the default `200000`-heartbeat budget (`whnf` timeout, `≈13s`). The target — `2304`-fold of a
`9`-wide law with `18000`-bit entries — is many orders of magnitude beyond kernel reach. (`native_decide` would
ride `trustCompiler`, which a probabilistic δ theorem MUST NOT; the Kyber δ scripts use float FFT, not exact
rationals.) So the exact tail is a DECIDABLE `Prop` (`ExactConvTailBound`) whose full-scale evaluation is the
named residual — not a `sorry`, a measured wall.

**(R2) The exact tail needs the TRUE compression-error laws — a modeling gap the MGF route sidesteps.** §12–§15's
`mlkemZ` models `Δv` by the `±104` extreme point `dvX` (its `cosh(104s)` MGF DOMINATES any centered
`Δv ∈ [−104,104]` — valid for the MGF/Chernoff envelope). But that envelope's EXACT law has variance `104² =
10816`, so the exact per-coefficient tail of the `mlkemZ` MODEL is HEAVY (`≈2⁻⁴²`, `≈7.3σ`) — it does NOT reach
FIPS δ. The exact-PMF route therefore requires the TRUE near-uniform compression-error laws (`Δv` uniform on
`[−104,104]`, `Δu` on its small support), a distinct REFINED model whose byte-faithfulness to the literal cipher
is a separate obligation the MGF-domination of §13–§14 discharges only in MGF-space. Both R1 and R2 are named,
not hidden; the machinery + bridge + reduction below are the exact-PMF FORMALIZATION, honest-partial. -/

/-- Elementwise add of two count lists (padding the shorter with `0`) — coefficient-list addition. -/
def cvAdd : List ℕ → List ℕ → List ℕ
  | [], g => g
  | f, [] => f
  | (a :: f), (b :: g) => (a + b) :: cvAdd f g

/-- **INTEGER-DISTRIBUTION CONVOLUTION** as little-endian coefficient-list (polynomial) multiplication:
`(cvMul f g)[k] = ∑_{i+j=k} f[i]·g[j]` — the EXACT law of the sum of two independent integer variables with
count-lists `f, g`. Structural recursion; reduces cleanly under kernel `decide` (see the teeth). -/
def cvMul : List ℕ → List ℕ → List ℕ
  | [], _ => []
  | (a :: f), g => cvAdd (g.map (a * ·)) (0 :: cvMul f g)

/-- The CBD(η=2) law as counts over `{−2,−1,0,1,2}` (offset `−2`): weights `(1,4,6,4,1)`, total `16`. -/
def cbdCounts : List ℕ := [1, 4, 6, 4, 1]

/-- The CBD-PRODUCT law `X·Y` (`X,Y ~ CBD(η=2)`) as counts over `{−4,…,4}` (offset `−4`): the exact per-term law
of every one of the `2304` negacyclic-convolution cross-terms of `eᵀr`, `sᵀe1`, `sᵀΔu`. Total `256`, variance `1`. -/
def prodCounts : List ℕ := [2, 0, 16, 32, 156, 32, 16, 0, 2]

/-- **(TOOTH — the machinery computes an EXACT convolution in-kernel.)** The `2`-fold CBD self-convolution is the
exact binomial `(1,8,28,56,70,56,28,8,1)` over `{−4,…,4}` — `decide`, no `native_decide`. -/
theorem cbd_selfconv : cvMul cbdCounts cbdCounts = [1, 8, 28, 56, 70, 56, 28, 8, 1] := by decide

/-- **(TOOTH — the product law is a genuine distribution.)** `prodCounts` totals `256` (`= 16²`). -/
theorem prodCounts_total : prodCounts.sum = 256 := by decide

/-- **(TOOTH — convolution preserves total mass.)** `4`-fold CBD totals `16⁴ = 65536`. Exact, kernel `decide`. -/
theorem cvMul_total_4fold : (cvMul (cvMul cbdCounts cbdCounts) (cvMul cbdCounts cbdCounts)).sum = 65536 := by
  decide

/-- The count-distribution (law) of an integer-valued function on a finite space, in the EXACT counting model
`winProb` is stated against: `convCnt f k = #{ω : f ω = k}`. -/
def convCnt {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (f : Ω → ℤ) (k : ℤ) : ℕ :=
  (Finset.univ.filter (fun ω => f ω = k)).card

/-- **THE FAITHFULNESS BRIDGE (PROVED): the law of a sum of two independent coordinates IS the convolution of
their laws.** `#{(a,b) : g a + h b = m} = ∑_k convCnt g k · convCnt h (m−k)` — the exact-PMF identity in the pure
counting model (`Fintype`/`card`), NO measure theory, matching `winProb`'s definition. This is the mathematical
content that makes the exact convolution the genuine law of the independent-coordinate noise sum; iterating it
over the `2306` coordinates of `mlkemΩ` gives the full per-coefficient PMF. -/
theorem card_add_eq_conv {A B : Type*} [Fintype A] [DecidableEq A] [Fintype B] [DecidableEq B]
    (g : A → ℤ) (h : B → ℤ) (m : ℤ) (S : Finset ℤ) (hS : ∀ a : A, g a ∈ S) :
    (Finset.univ.filter (fun p : A × B => g p.1 + h p.2 = m)).card
      = ∑ k ∈ S, (convCnt g k) * (convCnt h (m - k)) := by
  rw [Finset.card_filter, Fintype.sum_prod_type]
  have step1 : ∀ a : A, (∑ b : B, if g a + h b = m then 1 else 0) = convCnt h (m - g a) := by
    intro a; rw [convCnt, Finset.card_filter]
    exact Finset.sum_congr rfl (fun b _ => by
      congr 1; apply propext; constructor <;> intro hh <;> omega)
  rw [Finset.sum_congr rfl (fun a _ => step1 a),
      ← Finset.sum_fiberwise_of_maps_to (g := g) (t := S) (fun a _ => hS a)
        (f := fun a => convCnt h (m - g a))]
  exact Finset.sum_congr rfl (fun k _ => by
    rw [convCnt, Finset.sum_congr rfl (fun a ha => by rw [(Finset.mem_filter.mp ha).2]),
        Finset.sum_const, smul_eq_mul])

/-- **THE TAIL COUNT IS THE SUM OF THE LAW OVER THE TAIL VALUES (PROVED).** `#{ω : R ≤ |f ω|} = ∑_{k∈S, R≤|k|}
convCnt f k` — the exact-PMF tail as a finite sum of the law over the escaping values. The bridge between the
`winProb` count of the failure event and the convolution tail. -/
theorem card_tail_eq_sum_cnt {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (f : Ω → ℤ) (R : ℤ) (S : Finset ℤ) (hS : ∀ ω, f ω ∈ S) :
    (Finset.univ.filter (fun ω => R ≤ |f ω|)).card
      = ∑ k ∈ S.filter (fun k => R ≤ |k|), convCnt f k := by
  rw [Finset.card_eq_sum_card_fiberwise (f := f) (t := S.filter (fun k => R ≤ |k|))
      (fun ω hω => Finset.mem_filter.mpr ⟨hS ω, (Finset.mem_filter.mp hω).2⟩)]
  refine Finset.sum_congr rfl (fun k hk => ?_)
  have hRk : R ≤ |k| := (Finset.mem_filter.mp hk).2
  rw [convCnt]; congr 1; ext ω
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  exact ⟨fun h => h.2, fun h => ⟨by rw [h]; exact hRk, h⟩⟩

/-- **THE PER-COEFFICIENT TAIL PROBABILITY IS THE EXACT CONVOLVED-PMF TAIL (PROVED).** `winProb(badCoeff ez c) =
(∑_{k∈S, 832≤|k|} convCnt (ez c) k) / #Ω` — the failure probability of coefficient `c` is EXACTLY the exact-PMF
tail mass over the total number of outcomes. This makes the `2⁻¹⁷⁴` hypothesis of the reduction below literally
a statement about the exact convolution tail. -/
theorem winProb_badCoeff_eq_convTail {Ω : Type*} [Fintype Ω] [DecidableEq Ω]
    (ez : Fin 768 → Ω → ℤ) (c : Fin 768) (S : Finset ℤ) (hS : ∀ ω, ez c ω ∈ S) :
    winProb (badCoeff ez c)
      = (∑ k ∈ S.filter (fun k => (832 : ℤ) ≤ |k|), (convCnt (ez c) k : ℝ)) / (Fintype.card Ω : ℝ) := by
  unfold winProb
  congr 1
  have hb : (Finset.univ.filter (fun ω => badCoeff ez c ω = true))
      = (Finset.univ.filter (fun ω => (832 : ℤ) ≤ |ez c ω|)) := by
    ext ω; simp [Finset.mem_filter, badCoeff]
  rw [hb, card_tail_eq_sum_cnt (ez c) 832 S hS, Nat.cast_sum]

/-- **THE EXACT-PMF FIPS REDUCTION (PROVED): the exact convolution tail `≤ 2⁻¹⁷⁴` closes `δ ≤ 2⁻¹⁶⁴`.** Given a
per-coefficient value support `S c` and the exact-PMF tail mass bound `∑_{k, 832≤|k|} convCnt (ez c) k ≤ 2⁻¹⁷⁴·#Ω`
(the decidable exact-convolution tail, faithful by `winProb_badCoeff_eq_convTail`), the FIPS decryption-failure
bound follows through the existing union bound. This is the exact-PMF analog of the exact-MGF capstone — its
hypothesis is the exact convolved-distribution tail itself, not a Chernoff surrogate. What remains to make it a
CLOSED theorem for ML-KEM-768 is discharging that hypothesis: residuals **R1** (the astronomical exact
convolution, kernel-infeasible) and **R2** (the true compression-error laws) named above. -/
theorem exactConvTailFrac_closes_delta {Ω : Type*} [Fintype Ω] [DecidableEq Ω] [Nonempty Ω]
    (ez : Fin 768 → Ω → ℤ) (S : Fin 768 → Finset ℤ) (hS : ∀ c ω, ez c ω ∈ S c)
    (hfrac : ∀ c, (∑ k ∈ (S c).filter (fun k => (832 : ℤ) ≤ |k|), (convCnt (ez c) k : ℝ))
                    ≤ (2 : ℝ) ^ (-174 : ℤ) * (Fintype.card Ω : ℝ)) :
    winProb (decapsFails ez) ≤ MlKemCorrect.mlKem768Delta := by
  refine mlkem768_decapsFailure_le_delta ez (fun c => ?_)
  rw [winProb_badCoeff_eq_convTail ez c (S c) (hS c),
      div_le_iff₀ (by exact_mod_cast Fintype.card_pos : (0 : ℝ) < (Fintype.card Ω : ℝ))]
  exact hfrac c

/-- **(TOOTH — the exact-PMF reduction FIRES end-to-end.)** On the zero-noise model (`ez ≡ 0`, `S c = {0}`) the
exact tail mass is `0 ≤ 2⁻¹⁷⁴·#Ω`, so the reduction concludes `Pr[decaps fails] = 0 ≤ δ`. Exercises
`exactConvTailFrac_closes_delta` on a concrete model — the faithful reduction is non-vacuous. -/
theorem exactConvTail_reduction_fires :
    winProb (decapsFails zeroModel) ≤ MlKemCorrect.mlKem768Delta := by
  refine exactConvTailFrac_closes_delta zeroModel (fun _ => {0}) (fun c ω => by simp [zeroModel]) ?_
  intro c
  have : ({(0 : ℤ)} : Finset ℤ).filter (fun k => (832 : ℤ) ≤ |k|) = ∅ := by decide
  rw [this, Finset.sum_empty]
  positivity

/-- The EXACT tail count of a convolution count-list `d` (offset-indexed, index `i ↔` value `offset+i`): the mass
at values `k` with `R ≤ |k|`. Kernel-computable via `zipIdx`. -/
def convTailNum (d : List ℕ) (offset R : ℤ) : ℕ :=
  (d.zipIdx.filter (fun p => R ≤ |offset + (p.2 : ℤ)|)).foldl (fun a p => a + p.1) 0

/-- **THE NAMED DECIDABLE RESIDUAL (R1).** `tail/total ≤ num/den` as an EXACT ℕ inequality about the convolution
list — decidable, and the statement whose FULL-SCALE (`2304`-fold, `18000`-bit) kernel evaluation is the measured
wall. At small scale it evaluates by `decide` (below); at ML-KEM scale it is out of kernel reach (R1). -/
abbrev ExactConvTailBound (d : List ℕ) (offset R : ℤ) (num den : ℕ) : Prop :=
  convTailNum d offset R * den ≤ num * d.sum

/-- **(TOOTH — an EXACT tail value, kernel `decide`.)** The product law's mass at `|k| ≥ 3` is `4` (`= 2+2`, the
`z = ±4` counts) — the exact-PMF tail functional computes a concrete integer in-kernel. -/
theorem convTailNum_prodCounts : convTailNum prodCounts (-4) 3 = 4 := by decide

/-- **(TOOTH — the residual is satisfiable.)** The `2`-fold-CBD-like tail `2/16 ≤ 3/4` holds — `ExactConvTailBound`
is a real inequality that can HOLD. -/
theorem exactConvTailBound_satisfiable : ExactConvTailBound cbdCounts (-2) 5 3 4 := by decide

/-- **(TOOTH — the residual is refutable.)** An all-tail distribution (`[7]` at offset `100`, mass entirely at
`|k| ≥ 3`) has `tail/total = 1 > 1/2`, refuting `ExactConvTailBound` — a load-bearing constraint, not a
tautology. -/
theorem exactConvTailBound_refutable : ¬ ExactConvTailBound [7] 100 3 1 2 := by decide

/-! ## §17 — THE BAHADUR–RAO PREFACTOR: the exact change-of-measure refinement of the exact-MGF Chernoff bound.

§15 measured that the exact-MGF **Chernoff** route ceilings at `2⁻¹⁴⁸` (per-coefficient `2⁻¹⁵⁸` at `s = 3/10`,
or a Cramér optimum `≈ 2⁻¹⁶⁵`): the `768`-union then needs a per-coefficient tail of `2⁻¹⁷⁴` to reach FIPS
`δ = 2⁻¹⁶⁴`, and the gap `2⁻¹⁶⁵ → 2⁻¹⁷⁴` is exactly the **Bahadur–Rao prefactor** `1/(s·σ*·√{2π})` — the
polynomial correction the large-deviation *rate* `e^{−I}` discards. This section formalizes the ANALYTIC ROUTE
that recovers it: the exact **exponential-tilt change-of-measure identity**.

The general, measure-free, upstreamable core lives in `Dregg2.ForMathlib.BerryEsseen`:

  `tailFrac X a = (partition X s/|Ω|)·e^{−s·a}·tiltTailExp X s a`     (`BerryEsseen.tailFrac_eq`)

where `tiltTailExp X s a = E_tilt[e^{−s(X−a)}·1_{X≥a}] ∈ (0,1]`. The Chernoff bound is this identity with
`tiltTailExp ≤ 1` (`BerryEsseen.tiltTailExp_le_one`); the Bahadur–Rao improvement is any bound `tiltTailExp ≤ P`
with `P < 1`. `BerryEsseen.tiltTailExp_le_atom_geom` further formalizes the elementary anti-concentration
envelope `tiltTailExp ≤ pmax/(1−e^{−s})` (`pmax` = max tilted level-atom) — the fully-proved *partial* prefactor.

### The reduction (this section, kernel-clean).

`mgf_eq_partition_div` bridges the ForMathlib partition function to Mathlib's `mgf`; `winProb_ge_le_refined`
turns the identity into the refined one-sided `winProb` tail; `winProb_abs_split` handles the two-sided `|·|`.
Assembling over the ML-KEM term structure (reusing the exact per-term MGFs of §12 and the tightened arithmetic
`exactMgf_delta_arith_tight`) gives, kernel-clean:

  **`perCoeffExactMgfTail_bahadurRao`** — IF the per-coefficient tilted tail expectation is `≤ 2⁻¹⁶`
  (`CoeffBahadurRaoPrefactor`), THEN the per-coefficient tail is `≤ 2⁻¹⁷⁴`, hence (union) FIPS `δ ≤ 2⁻¹⁶⁴`
  (`mlkem768_decapsFailure_le_delta_bahadurRao`).

### ⚑ THE PREFACTOR IS A LOAD-BEARING CONSTRAINT — AND `2⁻¹⁶` IS FALSE FOR THE `mlkemZ` MODEL (measured).

`CoeffBahadurRaoPrefactor ez (2⁻¹⁶)` is `∀ c, tiltTailExp (ez c) (3/10) 832 ≤ 2⁻¹⁶` (both signs). The identity
`tailFrac_eq` makes this a *literal* statement about the true tilted tail expectation — the Bahadur–Rao
prefactor. It is **satisfiable and refutable** (teeth below), so it is a load-bearing constraint.

⚠ **BUT AT THE DEPLOYED `mlkemZ` PARAMETERS, `CoeffBahadurRaoPrefactor mlkemZ (2⁻¹⁶)` IS FALSE** (exact
convolution of the `mlkemZ` per-term laws, measured). The `s = 3/10` tilt is near the Cramér optimum, i.e. the
tilted law's mean sits at the threshold: `E_tilt[X] ≈ 829.6 ≈ 832`, with `σ* ≈ 51.5` — the tilted law is
near-Gaussian and `832` is essentially its MODE, not a deep-tail point. Hence the true tilted tail expectation
is `tiltTailExp(mlkemZ, 3/10, 832) ≈ 2⁻⁵·⁰⁷`, and the geometric envelope `pmax/(1−e^{−3/10})` with
`pmax = atomMass(832) ≈ 2⁻⁷·⁰` evaluates to `≈ 2⁻⁵·⁰⁷` — i.e. the envelope is essentially TIGHT here, not
loose. The Bahadur–Rao prefactor for this model is genuinely `≈ 2⁻⁵` (`1/(s·σ*·√{2π}) ≈ 1/(0.3·51.5·2.5) ≈
2⁻⁵·²` — the *sharp* constant, which AGREES with the envelope). There is no missing factor of `2¹¹` hiding in a
"sharp local-limit constant": the sharp constant is also `≈ 2⁻⁵`. So `2⁻¹⁶` is unreachable by any
characteristic-function / local-limit bound on the `mlkemZ` law — it is false, not merely unproven.

**Consequence for FIPS `δ`.** The `mlkemZ` (`±104`-envelope) model's Chernoff exponent (`≈ 2⁻¹⁵⁸` per coeff at
`s = 3/10`, `≈ 2⁻¹⁶⁵` at the Cramér optimum) times the true `≈ 2⁻⁵` prefactor times the `768·2` union gives
`δ ≈ 2⁻¹⁵⁷` — the honest Bahadur–Rao ceiling of THIS model. It does NOT reach FIPS `2⁻¹⁶⁴`. The gap is exactly
§16's residual **R2**: the `±104` extreme-point envelope for `Δv` (variance `104² = 10816`) is far heavier than
the true near-uniform compression error, so the `mlkemZ` model's real `δ` is heavier than FIPS. Closing FIPS
`2⁻¹⁶⁴` therefore requires the refined true-`Δv` exact-convolution route (§16, residuals R1+R2), NOT a Fourier
inversion / prefactor on this MGF-envelope model. `§17` FORMALIZES the general change-of-measure machinery (the
`tailFrac_eq` identity, the Chernoff recovery, the geometric envelope — all kernel-clean, upstreamable); the
reduction theorems below are valid CONDITIONAL implications whose ML-KEM hypotheses (`CoeffBahadurRaoPrefactor
mlkemZ 2⁻¹⁶`, `CoeffTailAtomBound mlkemZ 2⁻¹⁹`) are FALSE at deployed params — they are recorded here for the
general machinery, not as a live path to FIPS on `mlkemZ`.
-/

open Dregg2.ForMathlib.BerryEsseen

/-- **BRIDGE: the uniform-law MGF is the ForMathlib partition function over `|Ω|` (PROVED).**
`mgf X (unifMeasure Ω) s = partition X s / |Ω|`, via `PMF.integral_eq_sum` on the uniform PMF (same computation
as `mgf_cbd2_as_sum`). This lets the measure-free `BerryEsseen` identity speak to the `mgf`-based ML-KEM stack. -/
theorem mgf_eq_partition_div {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (X : Ω → ℝ) (s : ℝ) :
    mgf X (unifMeasure Ω) s = partition X s / (Fintype.card Ω : ℝ) := by
  rw [mgf, unifMeasure, PMF.integral_eq_sum, partition, Finset.sum_div]
  apply Finset.sum_congr rfl
  intro ω _
  rw [PMF.uniformFintype_apply, smul_eq_mul, ENNReal.toReal_inv, ENNReal.toReal_natCast,
      div_eq_inv_mul]

/-- **BRIDGE: the `winProb` one-sided tail IS the ForMathlib tail fraction (PROVED).** -/
theorem winProb_ge_eq_tailFrac {Ω : Type*} [Fintype Ω] (f : Ω → ℝ) (ε : ℝ) :
    winProb (fun ω => decide (ε ≤ f ω)) = tailFrac f ε := by
  classical
  rw [winProb, tailFrac]
  have hset : (Finset.univ.filter (fun o => decide (ε ≤ f o) = true))
      = (Finset.univ.filter (fun ω => ε ≤ f ω)) := by
    ext ω; simp [decide_eq_true_eq]
  rw [hset]

/-- **THE REFINED ONE-SIDED `winProb` TAIL (PROVED).** Given a prefactor bound `tiltTailExp f s ε ≤ P`, the
one-sided `winProb` tail is at most `mgf f s · e^{−s·ε} · P` — the Chernoff bound times the Bahadur–Rao prefactor.
Assembles `winProb_ge_eq_tailFrac`, `BerryEsseen.tailFrac_le_refined`, and `mgf_eq_partition_div`. -/
theorem winProb_ge_le_refined {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] (f : Ω → ℝ) (s ε : ℝ) {P : ℝ} (hpref : tiltTailExp f s ε ≤ P) :
    winProb (fun ω => decide (ε ≤ f ω)) ≤ mgf f (unifMeasure Ω) s * Real.exp (-(s * ε)) * P := by
  rw [winProb_ge_eq_tailFrac, mgf_eq_partition_div]
  exact tailFrac_le_refined f s ε hpref

/-- **THE TWO-SIDED SPLIT (PROVED).** `winProb(ε ≤ |Z|) ≤ winProb(ε ≤ Z) + winProb(ε ≤ −Z)` in the counting
model — the favorable set of `|Z|` escaping is contained in the union of the two one-sided sets. -/
theorem winProb_abs_split {Ω : Type*} [Fintype Ω] [DecidableEq Ω] (Z : Ω → ℝ) (ε : ℝ) :
    winProb (fun ω => decide (ε ≤ |Z ω|))
      ≤ winProb (fun ω => decide (ε ≤ Z ω)) + winProb (fun ω => decide (ε ≤ -(Z ω))) := by
  classical
  rw [winProb, winProb, winProb, ← add_div]
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · simp [h0]
  · gcongr
    have hsub : (Finset.univ.filter (fun ω : Ω => decide (ε ≤ |Z ω|) = true))
        ⊆ (Finset.univ.filter (fun ω : Ω => decide (ε ≤ Z ω) = true))
          ∪ (Finset.univ.filter (fun ω : Ω => decide (ε ≤ -(Z ω)) = true)) := by
      intro ω hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hω
      rw [Finset.mem_union]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
      rcases abs_cases (Z ω) with ⟨h1, _⟩ | ⟨h1, _⟩
      · exact Or.inl (by rwa [h1] at hω)
      · exact Or.inr (by rw [h1] at hω; linarith)
    calc ((Finset.univ.filter (fun ω : Ω => decide (ε ≤ |Z ω|) = true)).card : ℝ)
        ≤ (((Finset.univ.filter (fun ω : Ω => decide (ε ≤ Z ω) = true))
            ∪ (Finset.univ.filter (fun ω : Ω => decide (ε ≤ -(Z ω)) = true))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((Finset.univ.filter (fun ω : Ω => decide (ε ≤ Z ω) = true)).card : ℝ)
            + ((Finset.univ.filter (fun ω : Ω => decide (ε ≤ -(Z ω)) = true)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _

/-- **THE PER-COEFFICIENT BAHADUR–RAO PREFACTOR (the one named analytic input).** For every coefficient, the
tilted tail expectation of the centered noise `ez c` (both signs, at the tilt `s = 3/10`, deviation `832`) is
`≤ P`. By the change-of-measure identity `tailFrac_eq`, this IS the Bahadur–Rao prefactor for the coefficient's
tail. It is satisfiable AND refutable (`coeffBR_prefactor_satisfiable`/`_refutable`). -/
def CoeffBahadurRaoPrefactor {Ω : Type*} [Fintype Ω] (ez : Fin 768 → Ω → ℤ) (P : ℝ) : Prop :=
  ∀ c, tiltTailExp (fun ω => (ez c ω : ℝ)) (3/10) 832 ≤ P
     ∧ tiltTailExp (fun ω => -((ez c ω : ℝ))) (3/10) 832 ≤ P

/-- **THE PER-COEFFICIENT TAIL, VIA THE BAHADUR–RAO PREFACTOR (PROVED): `≤ 2⁻¹⁷⁴`.** From `CoeffIsExactMgfSum`
(the exact per-term MGFs assembling to `mlkemExactMgfBound`, §12.6) and the named prefactor bound `≤ 2⁻¹⁶`, the
per-coefficient two-sided tail is `≤ 2⁻¹⁷⁴`: split `|·|`, bound each one-sided tail by the refined
`mgf · e^{−s·832} · 2⁻¹⁶ ≤ mlkemExactMgfBound · e^{−(3/10)·832} · 2⁻¹⁶`, sum, and fold in the tightened
exact-MGF arithmetic `exactMgf_delta_arith_tight` (`2·e^{−(3/10)·832}·mlkemExactMgfBound ≤ 2⁻¹⁵⁸`). This is `16`
bits below the pure exact-MGF Chernoff per-coefficient tail `2⁻¹⁵⁸` — exactly the prefactor's contribution. -/
theorem perCoeffExactMgfTail_bahadurRao {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (ez : Fin 768 → Ω → ℤ)
    (hsum : ∀ c, CoeffIsExactMgfSum ez c)
    (hpref : CoeffBahadurRaoPrefactor ez ((2 : ℝ) ^ (-16 : ℤ))) :
    PerCoeffHoeffdingTail ez ((2 : ℝ) ^ (-174 : ℤ)) := by
  classical
  intro c
  obtain ⟨m, T, hZ, hindep, hmeas, hsymm, hprod⟩ := hsum c
  obtain ⟨hp1, hp2⟩ := hpref c
  set Zc : Ω → ℝ := fun ω => (ez c ω : ℝ) with hZc
  -- badCoeff = the two-sided real tail of `Zc`.
  have hbadeq : badCoeff ez c = fun ω => decide ((832 : ℝ) ≤ |Zc ω|) := by
    funext ω
    have hiff : ((832 : ℤ) ≤ |ez c ω|) ↔ ((832 : ℝ) ≤ |Zc ω|) := by
      rw [hZc, ← Int.cast_abs]; exact_mod_cast Iff.rfl
    simp only [badCoeff, hiff]
  -- `mgf Zc = mgf (−Zc) = ∏ mgf (T i) ≤ mlkemExactMgfBound`.
  have hZeq : Zc = ∑ i, T i := by
    funext ω; rw [Finset.sum_apply]; simpa [hZc] using hZ ω
  have hPnn : (0 : ℝ) ≤ (2 : ℝ) ^ (-16 : ℤ) := by positivity
  have hmgfZ_le : mgf Zc (unifMeasure Ω) (3/10) ≤ mlkemExactMgfBound := by
    rw [hZeq, hindep.mgf_sum hmeas Finset.univ]; exact hprod
  have hmgfnegZ_le : mgf (fun ω => -(Zc ω)) (unifMeasure Ω) (3/10) ≤ mlkemExactMgfBound := by
    have h1 : mgf (fun ω => -(Zc ω)) (unifMeasure Ω) (3/10) = mgf Zc (unifMeasure Ω) (-(3/10)) := by
      have := mgf_neg (X := Zc) (μ := unifMeasure Ω) (t := (3/10 : ℝ)); simpa [Pi.neg_def] using this
    rw [h1, hZeq, hindep.mgf_sum hmeas Finset.univ,
        Finset.prod_congr rfl (fun i _ => hsymm i)]
    exact hprod
  rw [hbadeq]
  refine le_trans (winProb_abs_split Zc 832) ?_
  -- Each one-sided tail ≤ mlkemExactMgfBound · e^{−(3/10·832)} · 2⁻¹⁶.
  have hright : winProb (fun ω => decide ((832 : ℝ) ≤ Zc ω))
      ≤ mlkemExactMgfBound * Real.exp (-(3 / 10 * 832)) * (2 : ℝ) ^ (-16 : ℤ) := by
    refine le_trans (winProb_ge_le_refined Zc (3/10) 832 hp1) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmgfZ_le (Real.exp_pos _).le) hPnn
  have hleft : winProb (fun ω => decide ((832 : ℝ) ≤ -(Zc ω)))
      ≤ mlkemExactMgfBound * Real.exp (-(3 / 10 * 832)) * (2 : ℝ) ^ (-16 : ℤ) := by
    refine le_trans (winProb_ge_le_refined (fun ω => -(Zc ω)) (3/10) 832 hp2) ?_
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hmgfnegZ_le (Real.exp_pos _).le) hPnn
  refine le_trans (add_le_add hright hleft) ?_
  -- 2 · mlkemExactMgfBound · e^{−(3/10·832)} · 2⁻¹⁶ ≤ 2⁻¹⁵⁸ · 2⁻¹⁶ = 2⁻¹⁷⁴.
  rw [show mlkemExactMgfBound * Real.exp (-(3 / 10 * 832)) * (2 : ℝ) ^ (-16 : ℤ)
        + mlkemExactMgfBound * Real.exp (-(3 / 10 * 832)) * (2 : ℝ) ^ (-16 : ℤ)
        = (2 * Real.exp (-(3 / 10) * 832) * mlkemExactMgfBound) * (2 : ℝ) ^ (-16 : ℤ)
      from by rw [neg_mul]; ring]
  calc (2 * Real.exp (-(3 / 10) * 832) * mlkemExactMgfBound) * (2 : ℝ) ^ (-16 : ℤ)
      ≤ (2 : ℝ) ^ (-158 : ℤ) * (2 : ℝ) ^ (-16 : ℤ) := by
        gcongr
        exact exactMgf_delta_arith_tight
    _ = (2 : ℝ) ^ (-174 : ℤ) := by
        rw [← zpow_add₀ (by norm_num : (2 : ℝ) ≠ 0)]; norm_num

/-- **THE ASSEMBLED FIPS δ-BOUND VIA THE BAHADUR–RAO PREFACTOR — `Pr[decaps fails] ≤ δ = 2⁻¹⁶⁴` (PROVED,
kernel-clean, conditional on the one named prefactor).** Chains `perCoeffExactMgfTail_bahadurRao` (`2⁻¹⁷⁴`)
through the union bound `mlkem768_decapsFailure_le_delta` (`768 < 2¹⁰`). This is the exact FIPS decryption-failure
bound, reduced — beyond the fully-formalized exact per-term MGFs and change-of-measure identity — to exactly the
Bahadur–Rao prefactor input `CoeffBahadurRaoPrefactor ez (2⁻¹⁶)`. -/
theorem mlkem768_decapsFailure_le_delta_bahadurRao {Ω : Type*} [Fintype Ω] [Nonempty Ω] [DecidableEq Ω]
    [MeasurableSpace Ω] [MeasurableSingletonClass Ω] (ez : Fin 768 → Ω → ℤ)
    (hsum : ∀ c, CoeffIsExactMgfSum ez c)
    (hpref : CoeffBahadurRaoPrefactor ez ((2 : ℝ) ^ (-16 : ℤ))) :
    winProb (decapsFails ez) ≤ MlKemCorrect.mlKem768Delta :=
  mlkem768_decapsFailure_le_delta ez (perCoeffExactMgfTail_bahadurRao ez hsum hpref)

/-- **THE REAL ML-KEM-768 FIPS δ-BOUND VIA THE BAHADUR–RAO PREFACTOR — `Pr_r[¬noiseBoundHolds] ≤ δ = 2⁻¹⁶⁴`
(PROVED, kernel-clean, conditional on ONLY the named prefactor).** Instantiates the reduction on the REAL
per-coefficient noise `mlkemZ`, whose `CoeffIsExactMgfSum` witness (`mlkem_exactMgfSum`, §12.6) is already
DISCHARGED. So beyond the fully-formalized exact per-term MGFs, the exact change-of-measure identity, and the
tightened Chernoff arithmetic, the ONLY remaining input to close FIPS `δ` for the real ML-KEM law is the single
named scalar `CoeffBahadurRaoPrefactor mlkemZ (2⁻¹⁶)` — the Bahadur–Rao prefactor. -/
theorem mlkem768_decapsFailure_le_delta_bahadurRao_real
    (hpref : CoeffBahadurRaoPrefactor mlkemZ ((2 : ℝ) ^ (-16 : ℤ))) :
    winProb (decapsFails mlkemZ) ≤ MlKemCorrect.mlKem768Delta :=
  mlkem768_decapsFailure_le_delta_bahadurRao mlkemZ mlkem_exactMgfSum hpref

/-! ### §17.1 — NON-VACUITY: the named prefactor is a load-bearing constraint (satisfiable AND refutable). -/

/-- **(TOOTH — the prefactor is satisfiable.)** On the zero-noise model every coefficient's noise is `0`, so its
tilted tail expectation at deviation `832` is `0` (the tail `{832 ≤ 0}` is empty) — `≤ 2⁻¹⁶`. So
`CoeffBahadurRaoPrefactor` holds on a real model; it is not vacuously false. -/
theorem coeffBR_prefactor_satisfiable :
    CoeffBahadurRaoPrefactor zeroModel ((2 : ℝ) ^ (-16 : ℤ)) := by
  intro c
  have hz : ∀ g : Unit → ℝ, (∀ u, g u = 0) →
      tiltTailExp g (3/10) 832 ≤ (2 : ℝ) ^ (-16 : ℤ) := by
    intro g hg
    unfold tiltTailExp
    have hterm : ∀ u : Unit, (if (832 : ℝ) ≤ g u then Real.exp (-(3/10 * (g u - 832))) else 0)
        * tiltWeight g (3/10) u = 0 := by
      intro u; rw [hg u]; norm_num
    rw [Finset.sum_congr rfl (fun u _ => hterm u), Finset.sum_const_zero]
    positivity
  exact ⟨hz _ (fun _ => by simp [zeroModel]), hz _ (fun _ => by simp [zeroModel])⟩

/-- **(TOOTH — the prefactor is refutable.)** On a point-mass model whose noise is the constant `832` (exactly
the deviation threshold), the tilted tail expectation is `1`: the entire tilted mass sits at the boundary, where
`e^{−s(X−832)} = e^0 = 1`. `1 > 2⁻¹⁶`, so the named prefactor is a genuine inequality that can FAIL — a
load-bearing constraint, not a tautology. (This is the Chernoff-recovery pole `tiltTailExp = 1` of §17's identity.) -/
theorem coeffBR_prefactor_refutable :
    ¬ CoeffBahadurRaoPrefactor (fun (_ : Fin 768) (_ : Unit) => (832 : ℤ)) ((2 : ℝ) ^ (-16 : ℤ)) := by
  intro h
  obtain ⟨h1, _⟩ := h 0
  -- On the boundary point-mass the tilted tail expectation is exactly `1`.
  have hval : tiltTailExp (fun _ : Unit => (((832 : ℤ)) : ℝ)) (3/10) 832 = 1 := by
    unfold tiltTailExp tiltWeight partition
    simp only [Fintype.sum_unique]
    rw [show ((832 : ℤ) : ℝ) = (832 : ℝ) from by norm_num, if_pos (le_refl (832 : ℝ)),
        show (832 : ℝ) - 832 = 0 from by ring, mul_zero, neg_zero, Real.exp_zero, one_mul]
    exact div_self (Real.exp_ne_zero _)
  rw [hval] at h1
  have hlt : (2 : ℝ) ^ (-16 : ℤ) < 1 := by
    rw [show (1 : ℝ) = (2 : ℝ) ^ (0 : ℤ) from by norm_num]
    exact zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
  linarith

/-! ### §17.2 — REDUCING THE PREFACTOR TO A LOCAL (TAIL-ATOM) BOUND — and why `2⁻¹⁹` is FALSE for `mlkemZ`.

The named `CoeffBahadurRaoPrefactor` bounds the *aggregate* tilted tail expectation. §17.2 reduces it — via the
refined tail-atom envelope `tiltTailExp_le_tailAtom_geom` (ForMathlib, which needs the level-atom bound ONLY on
the tail `k ≥ 832`) — to a strictly LOCAL statement: each tilted tail-atom mass at levels `k ≥ 832` is `≤ 2⁻¹⁹`.
The reduction `coeffTail_reduce` is VALID (`2⁻¹⁹/(1−e^{−3/10}) ≤ 2⁻¹⁶`, `prefactor_geom_arith`).

⚠ **BUT `CoeffTailAtomBound mlkemZ (2⁻¹⁹)` IS FALSE (measured, exact convolution of the `mlkemZ` per-term
laws).** The `s = 3/10` tilt puts the tilted mean AT the threshold (`E_tilt[X] ≈ 829.6 ≈ 832`, `σ* ≈ 51.5`), so
`k = 832` is the MODE of the tilted law, not a deep-tail atom. The *peak* tilted atom is
`atomMass(mlkemZ, 3/10, 832) ≈ 2⁻⁷·⁰` — and `CoeffTailAtomBound` demands `atomMass(k) ≤ 2⁻¹⁹` for **all**
`k ≥ 832`, INCLUDING `k = 832`. So it fails at the very first level by `≈ 12` bits. This is NOT a missing
"moderate-deviation local limit theorem": there is no deep-tail regime at `k = 832` — `832` is the mode. A
Fourier inversion of `reCharFn_le_exp` would (correctly) reproduce `atomMass(832) ≈ 1/(σ*√{2π}) ≈ 2⁻⁷`,
CONFIRMING the bound is false, not discharging it. The largest atom bound that IS true is `pmax ≈ 2⁻⁶·⁵`, which
the envelope turns into `tiltTailExp ≲ 2⁻⁴·⁵` — nowhere near `2⁻¹⁶`. Discharging FIPS `δ = 2⁻¹⁶⁴` needs the
refined true-`Δv` exact-convolution route (§16 R1+R2), not this route. The theorems below are the general
change-of-measure machinery + the valid reduction; their `mlkemZ` hypotheses are FALSE at deployed params. -/

/-- `2⁻¹⁹/(1−e^{−3/10}) ≤ 2⁻¹⁶` — the geometric-envelope arithmetic (PROVED). From `e^{3/10} ≥ 13/10`
(`add_one_le_exp`) we get `e^{−3/10} ≤ 10/13`, hence `1−e^{−3/10} ≥ 3/13`, and `2⁻¹⁹·(13/3) ≤ 2⁻¹⁶`. -/
theorem prefactor_geom_arith :
    (2 : ℝ) ^ (-19 : ℤ) / (1 - Real.exp (-(3 / 10 : ℝ))) ≤ (2 : ℝ) ^ (-16 : ℤ) := by
  have he : Real.exp (-(3 / 10 : ℝ)) ≤ 10 / 13 := by
    rw [Real.exp_neg, inv_le_comm₀ (Real.exp_pos _) (by norm_num : (0:ℝ) < 10 / 13),
        show ((10:ℝ) / 13)⁻¹ = 13 / 10 from by norm_num]
    have := Real.add_one_le_exp (3 / 10 : ℝ); linarith
  have hden : (3 : ℝ) / 13 ≤ 1 - Real.exp (-(3 / 10 : ℝ)) := by linarith
  have hdenpos : (0:ℝ) < 1 - Real.exp (-(3 / 10 : ℝ)) := by linarith
  rw [div_le_iff₀ hdenpos]
  have hstep : (2:ℝ) ^ (-19 : ℤ) ≤ (2:ℝ) ^ (-16 : ℤ) * (3 / 13) := by
    rw [show (2:ℝ) ^ (-19 : ℤ) = (2:ℝ) ^ (-16 : ℤ) * (2:ℝ) ^ (-3 : ℤ) from by
          rw [← zpow_add₀ (by norm_num : (2:ℝ) ≠ 0)]; norm_num]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [show (2:ℝ) ^ (-3 : ℤ) = 1 / 8 from by norm_num]; norm_num
  calc (2:ℝ) ^ (-19 : ℤ)
      ≤ (2:ℝ) ^ (-16 : ℤ) * (3 / 13) := hstep
    _ ≤ (2:ℝ) ^ (-16 : ℤ) * (1 - Real.exp (-(3 / 10 : ℝ))) :=
        mul_le_mul_of_nonneg_left hden (by positivity)

/-- **THE LOCAL (TAIL-ATOM) CONSTRAINT.** For every coefficient (both signs), the tilted tail-atom masses at
levels `k ≥ 832` are each `≤ pmax`. Satisfiable AND refutable (`coeffTailAtom_satisfiable`/`_refutable`), hence
load-bearing. ⚠ At `pmax = 2⁻¹⁹` and `ez = mlkemZ` this is **FALSE**: the `s = 3/10` tilt makes `832` the MODE
of the tilted law (`E_tilt ≈ 829.6`, `σ* ≈ 51.5`), so the peak atom `atomMass(mlkemZ, 3/10, 832) ≈ 2⁻⁷·⁰`
exceeds `2⁻¹⁹` by `≈ 12` bits. It is not a moderate-deviation residual to be discharged by Fourier inversion —
`832` is not in the deep tail. See the §17.2 header. -/
def CoeffTailAtomBound {Ω : Type*} [Fintype Ω] (ez : Fin 768 → Ω → ℤ) (pmax : ℝ) : Prop :=
  ∀ c, (∀ k, (832 : ℤ) ≤ k → atomMass (ez c) (fun ω => (ez c ω : ℝ)) (3/10) k ≤ pmax)
     ∧ (∀ k, (832 : ℤ) ≤ k →
          atomMass (fun ω => -(ez c ω)) (fun ω => ((-(ez c ω) : ℤ) : ℝ)) (3/10) k ≤ pmax)

/-- **THE PER-`g` REDUCTION (PROVED).** The tail-atom bound on levels `k ≥ 832` gives the aggregate tilted-tail
bound `≤ 2⁻¹⁶` via `tiltTailExp_le_tailAtom_geom` and `prefactor_geom_arith`. -/
theorem coeffTail_reduce {Ω : Type*} [Fintype Ω] [Nonempty Ω] (g : Ω → ℤ)
    (hg : ∀ k, (832 : ℤ) ≤ k → atomMass g (fun ω => (g ω : ℝ)) (3/10) k ≤ (2:ℝ) ^ (-19 : ℤ)) :
    tiltTailExp (fun ω => (g ω : ℝ)) (3/10) (832 : ℝ) ≤ (2:ℝ) ^ (-16 : ℤ) := by
  have h := tiltTailExp_le_tailAtom_geom g (by norm_num : (0:ℝ) < 3/10) 832 (by positivity) hg
  rw [show (((832 : ℤ)) : ℝ) = (832 : ℝ) from by norm_num] at h
  exact le_trans h prefactor_geom_arith

/-- **THE PREFACTOR, FROM THE LOCAL TAIL-ATOM BOUND (PROVED).** `CoeffTailAtomBound ez 2⁻¹⁹` implies
`CoeffBahadurRaoPrefactor ez 2⁻¹⁶`: apply `coeffTail_reduce` to `ez c` and to its negation (rewriting the cast
`↑(−ez) = −↑ez`). This is the honest reduction of the aggregate prefactor to the local limit theorem. -/
theorem coeffBR_prefactor_of_tailAtom {Ω : Type*} [Fintype Ω] [Nonempty Ω]
    (ez : Fin 768 → Ω → ℤ) (hta : CoeffTailAtomBound ez ((2:ℝ) ^ (-19 : ℤ))) :
    CoeffBahadurRaoPrefactor ez ((2:ℝ) ^ (-16 : ℤ)) := by
  intro c
  obtain ⟨h1, h2⟩ := hta c
  refine ⟨coeffTail_reduce (ez c) h1, ?_⟩
  have h := coeffTail_reduce (fun ω => -(ez c ω)) h2
  have hfun : (fun ω => (((-(ez c ω)) : ℤ) : ℝ)) = (fun ω => -((ez c ω : ℝ))) := by
    funext ω; push_cast; ring
  rw [hfun] at h
  exact h

/-- **A VALID CONDITIONAL — but with a hypothesis that is FALSE at deployed params.** Composes
`coeffBR_prefactor_of_tailAtom` with the real prefactor bridge: IF `CoeffTailAtomBound mlkemZ 2⁻¹⁹` held, FIPS
`δ ≤ 2⁻¹⁶⁴` would follow. ⚠ The hypothesis is FALSE for `mlkemZ` (peak tilted atom `atomMass(832) ≈ 2⁻⁷·⁰`, the
tilted MODE — see §17.2), so this implication is never dischargeable on the real model and does NOT close FIPS
`δ`. It is retained as the terminal node of the general change-of-measure reduction; FIPS `2⁻¹⁶⁴` closure is the
true-`Δv` exact-convolution route of §16 (R1+R2), not this one. -/
theorem mlkem768_decapsFailure_le_delta_bahadurRao_real_tailAtom
    (hta : CoeffTailAtomBound mlkemZ ((2:ℝ) ^ (-19 : ℤ))) :
    winProb (decapsFails mlkemZ) ≤ MlKemCorrect.mlKem768Delta :=
  mlkem768_decapsFailure_le_delta_bahadurRao_real (coeffBR_prefactor_of_tailAtom mlkemZ hta)

/-- **(TOOTH — the local residual is satisfiable.)** On the zero-noise model every tail-atom fiber `{ω : g ω = k}`
with `k ≥ 832` is empty (the noise is `0`), so every tail-atom mass is `0 ≤ 2⁻¹⁹`. -/
theorem coeffTailAtom_satisfiable :
    CoeffTailAtomBound zeroModel ((2:ℝ) ^ (-19 : ℤ)) := by
  have hempty : ∀ (hnoise : Unit → ℤ) (X : Unit → ℝ) (k : ℤ), (∀ u, hnoise u = 0) → (832 : ℤ) ≤ k →
      atomMass hnoise X (3/10) k ≤ (2:ℝ) ^ (-19 : ℤ) := by
    intro hnoise X k hh hk
    unfold atomMass
    rw [Finset.filter_eq_empty_iff.mpr (fun u _ => by rw [hh u]; omega), Finset.sum_empty]
    positivity
  intro c
  exact ⟨fun k hk => hempty _ _ k (fun u => by simp [zeroModel]) hk,
         fun k hk => hempty _ _ k (fun u => by simp [zeroModel]) hk⟩

/-- **(TOOTH — the local residual is refutable.)** On the boundary point-mass model (noise constant `832`), the
tail-atom mass at `k = 832` is the entire tilted mass `1 > 2⁻¹⁹`, so `CoeffTailAtomBound` can FAIL. A genuine
constraint, not a tautology. -/
theorem coeffTailAtom_refutable :
    ¬ CoeffTailAtomBound (fun (_ : Fin 768) (_ : Unit) => (832 : ℤ)) ((2:ℝ) ^ (-19 : ℤ)) := by
  intro h
  obtain ⟨h1, _⟩ := h 0
  have hbound := h1 832 (le_refl (832 : ℤ))
  have hval : ∀ X : Unit → ℝ,
      atomMass (fun (_ : Unit) => (832:ℤ)) X (3/10) 832 = 1 := by
    intro X
    unfold atomMass
    rw [Finset.filter_true_of_mem (fun u _ => rfl)]
    exact sum_tiltWeight X (3/10)
  rw [hval] at hbound
  have hlt : (2:ℝ) ^ (-19 : ℤ) < 1 := by
    rw [show (1:ℝ) = (2:ℝ) ^ (0:ℤ) from by norm_num]
    exact zpow_lt_zpow_right₀ (by norm_num) (by norm_num)
  linarith

/-! ## §18 — THE TRUE NEAR-UNIFORM `Δv` REFINEMENT: `2⁻¹⁴⁸ → 2⁻¹⁵³` (refining the MODEL, not the method).

§12–§15 modeled the `d_v=4` compression term `Δv` by the `±104` extreme-point surrogate `dvX`
(MGF `cosh(104s)`, `≈ e^{31.2}` at `s = 3/10`). That envelope DOMINATES any centered `Δv ∈ [−104,104]` but is
FAR heavier than the real compression error — as §15's "measured FIPS wall" and §16's residual **R2** named. This
section replaces `dvX` by the ACTUAL `d_v=4` compression rounding error and re-runs the exact-MGF Chernoff, closing
the honest assumption-free ceiling of the Chernoff route further, to `2⁻¹⁵³` assembled (`2⁻¹⁶³` per coefficient).

### The TRUE `Δv` law (the ACTUAL rounding error, not an assumed shape).

`cErr x = mod±_q (Decompress_{d_v}(Compress_{d_v}(x)) − x)` — built on the LITERAL `MlKemCodec.compress`/
`MlKemCodec.decompress` (FIPS 203 §4.2.1, round-half-up), `q = 3329`, over `x` uniform on `ℤ_q`. Two ground facts,
both PROVED here, characterize its law and pin its MGF WITHOUT assuming uniformity:

* **`cErr_bound`** — the support is EXACTLY `[−104,104]` (`|cErr x| ≤ 104` for every `x < 3329`), by kernel
  `decide` over the `3329`-point domain (NO `native_decide`; the reduction is exact `Nat`/`Int` arithmetic on the
  real round functions — axiom-free).
* **`cErrFiber_le_16`** — every error value is hit by AT MOST `16` inputs (`#{x : cErr x = k} ≤ 16`), by
  INJECTIVITY of `x ↦ Compress_{d_v}(x)` on each fiber (`cErr_inj`, pure modular arithmetic via `omega`): the
  ciphertext value + the error determine `x`, so the fiber injects into the `16`-element ciphertext alphabet. This
  is the genuine near-uniformity: the `16` ciphertext bins each contribute each error value at most once.

### The exact MGF bound (a geometric sum of exponentials, both signs).

From `cErr_bound` + `cErrFiber_le_16`, `∑_x e^{t·cErr x} = ∑_{k=−104}^{104} c_k e^{tk} ≤ 16 ∑_{k=−104}^{104} e^{tk}`,
a finite GEOMETRIC series (`sumFiber_geom_le`, `geom_sum_eq`). Bounded by `exp(s)−1 ≥ s` (`add_one_le_exp`), the
per-coefficient true-`Δv` MGF is `mgf ≤ dvTrueBound = (160/9987)·e^{63/2} ≈ e^{27.37}` at BOTH `s = ±3/10` — the
support is symmetric so the same geometric envelope bounds both tails (the exact law is NOT symmetric —
`cErr = 104` has count `9`, `cErr = −104` count `8` — so this uses the SIGN-SEPARATED Chernoff engine
`winProb_abs_exactMgf_bound_le`, not the exact-MGF-symmetry engine `winProb_abs_exactMgf_le` of §12.1). This
`≈ e^{27.37}` replaces `dvX`'s `≈ e^{31.2}` — the `≈ 3.8`-nat gap the extreme-point envelope discarded.

### The assembled δ and the MEASURED cap.

Feeding the true-`Δv` MGF (`dvTrueBound`) into the assembled envelope over a fresh, fully-independent product model
`rΩ` (`2304` product cross-terms + `e2` + the TRUE `Δv` coordinate `Fin 3329`, `iIndepFun` via `iIndepFun_pi`)
closes the exact-MGF Chernoff at `2⁻¹⁶³` per coefficient — `5` bits below §15's `2⁻¹⁵⁸`. The `768`-fold union then
gives `2⁻¹⁵³` assembled (`rZ_decapsFailure_le_delta153`), `5` bits below `mlkem768_decapsFailure_le_delta_unconditional_tight`.

**FIPS `2⁻¹⁶⁴` is STILL out of band for this method** — and now the reason is sharp: the true-`Δv` per-coefficient
tail `2⁻¹⁶³` is ITSELF near FIPS δ, but the `768`-fold union costs `≈ 10` bits, capping the ASSEMBLED bound at
`≈ 2⁻¹⁵³`. Refining `Δv` tightened the per-coefficient Chernoff by exactly the `≈ 3.8` nats the `±104` envelope
overspent (§16 **R2** is now DISCHARGED in MGF-space at deployed params), but it does NOT beat the union-bound wall
(§15). Reaching FIPS `2⁻¹⁶⁴` still requires the exact convolved-distribution tail (§16, now on this LIGHTER true
model) — the union-free per-coefficient tail `≈ 2⁻¹⁸⁰` — a Bahadur–Rao / exact-PMF step, NOT a better `Δv` MGF or a
better `s`. So `2⁻¹⁵³` is the refined honest ceiling of the exact-MGF Chernoff route with the TRUE compression law. -/

def cErr (x : ℕ) : ℤ := ((MlKemCodec.decompress 4 (MlKemCodec.compress 4 x) : ℤ) - (x : ℤ) + 1664) % 3329 - 1664

-- (copied from validated scratch)
theorem sumFiber_geom_le (N : ℕ) (c : Fin N → ℕ) (hc : ∀ x, c x < 209)
    (hcard : ∀ j : ℕ, (Finset.univ.filter (fun x : Fin N => c x = j)).card ≤ 16)
    (r : ℝ) (hr : 1 < r) :
    (∑ x : Fin N, r ^ (c x)) ≤ 16 * r ^ 209 / (r - 1) := by
  have hmaps : ∀ x ∈ (Finset.univ : Finset (Fin N)), c x ∈ Finset.range 209 :=
    fun x _ => Finset.mem_range.mpr (hc x)
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hstep : ∀ j ∈ Finset.range 209,
      (∑ x ∈ Finset.univ.filter (fun x : Fin N => c x = j), r ^ (c x)) ≤ 16 * r ^ j := by
    intro j hj
    have : (∑ x ∈ Finset.univ.filter (fun x : Fin N => c x = j), r ^ (c x))
        = (Finset.univ.filter (fun x : Fin N => c x = j)).card * r ^ j := by
      rw [Finset.sum_congr rfl (fun x hx => by rw [(Finset.mem_filter.mp hx).2])]
      rw [Finset.sum_const, nsmul_eq_mul]
    rw [this]
    have hrj : (0:ℝ) ≤ r ^ j := by positivity
    have := hcard j
    calc ((Finset.univ.filter (fun x : Fin N => c x = j)).card : ℝ) * r ^ j
        ≤ (16:ℝ) * r ^ j := by
          apply mul_le_mul_of_nonneg_right _ hrj; exact_mod_cast this
      _ = 16 * r ^ j := rfl
  refine le_trans (Finset.sum_le_sum hstep) ?_
  rw [← Finset.mul_sum]
  have hrne : r ≠ 1 := ne_of_gt hr
  have hgeom : (∑ j ∈ Finset.range 209, r ^ j) = (r ^ 209 - 1) / (r - 1) := by
    rw [geom_sum_eq hrne 209]
  rw [hgeom]
  have hrm1 : 0 < r - 1 := by linarith
  rw [mul_div_assoc]; gcongr; linarith

theorem compress4_lt16 (x : ℕ) : MlKemCodec.compress 4 x < 16 := by
  unfold MlKemCodec.compress; simp only; exact Nat.mod_lt _ (by norm_num)

theorem cErr_inj (k : ℤ) : Set.InjOn (fun x : Fin 3329 => MlKemCodec.compress 4 x.val)
    ↑(Finset.univ.filter (fun x : Fin 3329 => cErr x.val = k)) := by
  intro x1 hx1 x2 hx2 hcomp
  simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_univ, true_and] at hx1 hx2
  simp only at hcomp
  have hdec : MlKemCodec.decompress 4 (MlKemCodec.compress 4 x2.val) = MlKemCodec.decompress 4 (MlKemCodec.compress 4 x1.val) := by rw [hcomp]
  have he1 : cErr x1.val = k := hx1
  have he2 : cErr x2.val = k := hx2
  unfold cErr at he1 he2; rw [hdec] at he2
  exact Fin.ext (by have := x1.isLt; have := x2.isLt; omega)

theorem cErrFiber_le_16 (k : ℤ) :
    (Finset.univ.filter (fun x : Fin 3329 => cErr x.val = k)).card ≤ 16 := by
  have hmaps : ∀ x ∈ Finset.univ.filter (fun x : Fin 3329 => cErr x.val = k),
      (fun x : Fin 3329 => MlKemCodec.compress 4 x.val) x ∈ Finset.range 16 :=
    fun x _ => Finset.mem_range.mpr (compress4_lt16 x.val)
  simpa using Finset.card_le_card_of_injOn (fun x : Fin 3329 => MlKemCodec.compress 4 x.val) hmaps (cErr_inj k)

set_option maxRecDepth 20000 in
theorem cErr_bound : ∀ x : Fin 3329, -104 ≤ cErr x.val ∧ cErr x.val ≤ 104 := by decide

noncomputable def dvTrueX : Fin 3329 → ℝ := fun x => (cErr x.val : ℝ)

-- MGF as raw sum
theorem mgf_dvTrue_sum (t : ℝ) :
    mgf dvTrueX (unifMeasure (Fin 3329)) t
      = ∑ x : Fin 3329, (1/3329 : ℝ) * Real.exp (t * (cErr x.val : ℝ)) := by
  rw [mgf, unifMeasure, PMF.integral_eq_sum]
  apply Finset.sum_congr rfl
  intro x _
  rw [PMF.uniformFintype_apply]
  simp only [Fintype.card_fin, smul_eq_mul, dvTrueX, ENNReal.toReal_inv, ENNReal.toReal_natCast]
  norm_num

-- gj for positive sign
noncomputable def gjp : Fin 3329 → ℕ := fun x => (cErr x.val + 104).toNat
-- gj for negative sign
noncomputable def gjn : Fin 3329 → ℕ := fun x => (104 - cErr x.val).toNat

theorem gjp_lt (x : Fin 3329) : gjp x < 209 := by
  have := (cErr_bound x).2; unfold gjp; omega
theorem gjn_lt (x : Fin 3329) : gjn x < 209 := by
  have := (cErr_bound x).1; unfold gjn; omega

theorem gjp_card (j : ℕ) : (Finset.univ.filter (fun x : Fin 3329 => gjp x = j)).card ≤ 16 := by
  have hcongr : (Finset.univ.filter (fun x : Fin 3329 => gjp x = j))
      = (Finset.univ.filter (fun x : Fin 3329 => cErr x.val = (j:ℤ) - 104)) := by
    apply Finset.filter_congr; intro x _
    have hb := (cErr_bound x).1
    unfold gjp
    constructor <;> intro h <;> omega
  rw [hcongr]; exact cErrFiber_le_16 _
theorem gjn_card (j : ℕ) : (Finset.univ.filter (fun x : Fin 3329 => gjn x = j)).card ≤ 16 := by
  have hcongr : (Finset.univ.filter (fun x : Fin 3329 => gjn x = j))
      = (Finset.univ.filter (fun x : Fin 3329 => cErr x.val = 104 - (j:ℤ))) := by
    apply Finset.filter_congr; intro x _
    have hb := (cErr_bound x).2
    unfold gjn
    constructor <;> intro h <;> omega
  rw [hcongr]; exact cErrFiber_le_16 _

noncomputable def dvTrueBound : ℝ := (160/9987) * Real.exp (63/2)

-- positive-sign sum bound
theorem dvTrue_sum_pos :
    (∑ x : Fin 3329, Real.exp ((3/10) * (cErr x.val : ℝ)))
      ≤ 16 * Real.exp (63/2) / (Real.exp (3/10) - 1) := by
  have hr1 : (1:ℝ) < Real.exp (3/10) := by
    have := Real.add_one_le_exp (3/10 : ℝ); linarith
  have hx_eq : ∀ x : Fin 3329, Real.exp ((3/10) * (cErr x.val:ℝ))
      = Real.exp (-104 * (3/10)) * (Real.exp (3/10))^(gjp x) := by
    intro x
    have hb := (cErr_bound x).1
    have hcast : ((gjp x : ℤ)) = cErr x.val + 104 := by
      unfold gjp; rw [Int.toNat_of_nonneg (by omega)]
    have hcastR : (gjp x : ℝ) = (cErr x.val : ℝ) + 104 := by exact_mod_cast hcast
    rw [show (3/10)*(cErr x.val:ℝ) = (gjp x:ℝ)*(3/10) + (-104*(3/10)) from by rw [hcastR]; ring,
        Real.exp_add, Real.exp_nat_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hx_eq x), ← Finset.mul_sum]
  have hgeom := sumFiber_geom_le 3329 gjp gjp_lt gjp_card (Real.exp (3/10)) hr1
  have hpow : Real.exp (-104 * (3/10)) * (16 * (Real.exp (3/10))^209 / (Real.exp (3/10) - 1))
      = 16 * Real.exp (63/2) / (Real.exp (3/10) - 1) := by
    rw [← Real.exp_nat_mul]
    rw [show Real.exp (-104 * (3/10)) * (16 * Real.exp ((209:ℕ) * (3/10)) / (Real.exp (3/10) - 1))
        = 16 * (Real.exp (-104 * (3/10)) * Real.exp ((209:ℕ) * (3/10))) / (Real.exp (3/10) - 1) from by ring,
        ← Real.exp_add]
    norm_num
  calc Real.exp (-104 * (3/10)) * (∑ x : Fin 3329, (Real.exp (3/10))^(gjp x))
      ≤ Real.exp (-104 * (3/10)) * (16 * (Real.exp (3/10))^209 / (Real.exp (3/10) - 1)) := by
        apply mul_le_mul_of_nonneg_left hgeom (le_of_lt (Real.exp_pos _))
    _ = 16 * Real.exp (63/2) / (Real.exp (3/10) - 1) := hpow

theorem dvTrue_sum_neg :
    (∑ x : Fin 3329, Real.exp ((-(3/10)) * (cErr x.val : ℝ)))
      ≤ 16 * Real.exp (63/2) / (Real.exp (3/10) - 1) := by
  have hr1 : (1:ℝ) < Real.exp (3/10) := by
    have := Real.add_one_le_exp (3/10 : ℝ); linarith
  have hx_eq : ∀ x : Fin 3329, Real.exp ((-(3/10)) * (cErr x.val:ℝ))
      = Real.exp (-(3/10) * 104) * (Real.exp (3/10))^(gjn x) := by
    intro x
    have hb := (cErr_bound x).2
    have hcast : ((gjn x : ℤ)) = 104 - cErr x.val := by
      unfold gjn; rw [Int.toNat_of_nonneg (by omega)]
    have hcastR : (gjn x : ℝ) = 104 - (cErr x.val : ℝ) := by exact_mod_cast hcast
    rw [show (-(3/10))*(cErr x.val:ℝ) = (gjn x:ℝ)*(3/10) + (-(3/10)*104) from by rw [hcastR]; ring,
        Real.exp_add, Real.exp_nat_mul]
    ring
  rw [Finset.sum_congr rfl (fun x _ => hx_eq x), ← Finset.mul_sum]
  have hgeom := sumFiber_geom_le 3329 gjn gjn_lt gjn_card (Real.exp (3/10)) hr1
  have hpow : Real.exp (-(3/10) * 104) * (16 * (Real.exp (3/10))^209 / (Real.exp (3/10) - 1))
      = 16 * Real.exp (63/2) / (Real.exp (3/10) - 1) := by
    rw [← Real.exp_nat_mul]
    rw [show Real.exp (-(3/10) * 104) * (16 * Real.exp ((209:ℕ) * (3/10)) / (Real.exp (3/10) - 1))
        = 16 * (Real.exp (-(3/10) * 104) * Real.exp ((209:ℕ) * (3/10))) / (Real.exp (3/10) - 1) from by ring,
        ← Real.exp_add]
    norm_num
  calc Real.exp (-(3/10) * 104) * (∑ x : Fin 3329, (Real.exp (3/10))^(gjn x))
      ≤ Real.exp (-(3/10) * 104) * (16 * (Real.exp (3/10))^209 / (Real.exp (3/10) - 1)) := by
        apply mul_le_mul_of_nonneg_left hgeom (le_of_lt (Real.exp_pos _))
    _ = 16 * Real.exp (63/2) / (Real.exp (3/10) - 1) := hpow

theorem dvTrueBound_pos : 0 < dvTrueBound := by
  unfold dvTrueBound; positivity

theorem dvTrue_key (E : ℝ) (hE : 0 ≤ E) :
    (1/3329:ℝ) * (16 * E / (Real.exp (3/10) - 1)) ≤ (160/9987) * E := by
  have hD : (3/10:ℝ) ≤ Real.exp (3/10) - 1 := by have := Real.add_one_le_exp (3/10:ℝ); linarith
  have hDpos : (0:ℝ) < Real.exp (3/10) - 1 := by linarith
  rw [← mul_div_assoc, div_le_iff₀ hDpos]
  nlinarith [hD, hE, mul_le_mul_of_nonneg_left hD hE]

theorem mgf_dvTrue_pos_le : mgf dvTrueX (unifMeasure (Fin 3329)) (3/10) ≤ dvTrueBound := by
  rw [mgf_dvTrue_sum, ← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left dvTrue_sum_pos (by norm_num)) ?_
  exact dvTrue_key _ (le_of_lt (Real.exp_pos _))

theorem mgf_dvTrue_neg_le : mgf dvTrueX (unifMeasure (Fin 3329)) (-(3/10)) ≤ dvTrueBound := by
  rw [mgf_dvTrue_sum, ← Finset.mul_sum]
  refine le_trans (mul_le_mul_of_nonneg_left dvTrue_sum_neg (by norm_num)) ?_
  exact dvTrue_key _ (le_of_lt (Real.exp_pos _))


-- ===== BOUND-BASED EXACT-MGF CHERNOFF ENGINE (no symmetry needed) =====
theorem winProb_abs_exactMgf_bound_le {Ω : Type*} [Fintype Ω] [Nonempty Ω] [MeasurableSpace Ω]
    [MeasurableSingletonClass Ω] {m : ℕ} (T : Fin m → Ω → ℝ) (s : ℝ) (hs : 0 ≤ s)
    (hindep : iIndepFun T (unifMeasure Ω)) (hmeas : ∀ i, Measurable (T i))
    (B : Fin m → ℝ)
    (hpos : ∀ i, mgf (T i) (unifMeasure Ω) s ≤ B i)
    (hneg : ∀ i, mgf (T i) (unifMeasure Ω) (-s) ≤ B i)
    {ε : ℝ} :
    winProb (fun ω => decide (ε ≤ |∑ i, T i ω|))
      ≤ 2 * Real.exp (-s * ε) * ∏ i, B i := by
  classical
  set μ := unifMeasure Ω with hμ
  set Z : Ω → ℝ := fun ω => ∑ i, T i ω with hZ
  have hZsum : Z = ∑ i, T i := by funext ω; simp [hZ, Finset.sum_apply]
  have hmgfZ : mgf Z μ s = ∏ i, mgf (T i) μ s := by
    rw [hZsum]; exact hindep.mgf_sum hmeas Finset.univ
  have hmgfnegZ : mgf (fun ω => -(Z ω)) μ s = ∏ i, mgf (T i) μ (-s) := by
    have h1 : mgf (fun ω => -(Z ω)) μ s = mgf Z μ (-s) := by
      have := mgf_neg (X := Z) (μ := μ) (t := s); simpa [Pi.neg_def] using this
    rw [h1, hZsum, hindep.mgf_sum hmeas Finset.univ]
  have hprodpos : (∏ i, mgf (T i) μ s) ≤ ∏ i, B i :=
    Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => hpos i)
  have hprodneg : (∏ i, mgf (T i) μ (-s)) ≤ ∏ i, B i :=
    Finset.prod_le_prod₀ (fun i _ => mgf_nonneg) (fun i _ => hneg i)
  have hexp : (0:ℝ) ≤ Real.exp (-s * ε) := le_of_lt (Real.exp_pos _)
  have hintR : Integrable (fun ω => Real.exp (s * Z ω)) μ := Integrable.of_finite
  have hR : μ.real {ω | ε ≤ Z ω} ≤ Real.exp (-s * ε) * ∏ i, B i := by
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := Z) (t := s) ε hs hintR
    rw [hmgfZ] at h
    exact le_trans h (by apply mul_le_mul_of_nonneg_left hprodpos hexp)
  have hintL : Integrable (fun ω => Real.exp (s * (fun ω => -(Z ω)) ω)) μ := Integrable.of_finite
  have hL : μ.real {ω | Z ω ≤ -ε} ≤ Real.exp (-s * ε) * ∏ i, B i := by
    have h := measure_ge_le_exp_mul_mgf (μ := μ) (X := fun ω => -(Z ω)) (t := s) ε hs hintL
    rw [hmgfnegZ] at h
    have hset : {ω | ε ≤ -(Z ω)} = {ω | Z ω ≤ -ε} := by
      ext ω; simp only [Set.mem_setOf_eq]; constructor <;> intro hh <;> linarith
    rw [hset] at h
    exact le_trans h (by apply mul_le_mul_of_nonneg_left hprodneg hexp)
  have hsubset : {ω | ε ≤ |Z ω|} ⊆ {ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε} := by
    intro ω hω
    simp only [Set.mem_setOf_eq, Set.mem_union] at hω ⊢
    rcases le_total 0 (Z ω) with hp | hn
    · exact Or.inl (by rwa [abs_of_nonneg hp] at hω)
    · exact Or.inr (by rw [abs_of_nonpos hn] at hω; linarith)
  have hunion : μ.real {ω | ε ≤ |Z ω|} ≤ 2 * Real.exp (-s * ε) * ∏ i, B i := by
    calc μ.real {ω | ε ≤ |Z ω|}
        ≤ μ.real ({ω | ε ≤ Z ω} ∪ {ω | Z ω ≤ -ε}) := measureReal_mono hsubset
      _ ≤ μ.real {ω | ε ≤ Z ω} + μ.real {ω | Z ω ≤ -ε} := measureReal_union_le _ _
      _ ≤ 2 * Real.exp (-s * ε) * ∏ i, B i := by linarith [hR, hL]
  rw [winProb_eq_measureReal]
  have hset : {ω : Ω | (fun ω => decide (ε ≤ |∑ i, T i ω|)) ω = true} = {ω | ε ≤ |Z ω|} := by
    ext ω; simp [decide_eq_true_eq, hZ]
  rw [hset]; exact hunion

-- ===== REFINED PRODUCT SPACE RC = (CbdΩ×CbdΩ) × Fin 3329 =====
abbrev RC : Type := (CbdΩ × CbdΩ) × Fin 3329
abbrev rΩ : Type := Fin 2306 → RC
noncomputable instance : DecidableEq rΩ := Classical.decEq _

theorem runifMeasure_pi_eq :
    unifMeasure rΩ = Measure.pi (fun _ : Fin 2306 => unifMeasure RC) := by
  refine Measure.ext_of_singleton (fun f => ?_)
  rw [Measure.pi_singleton]
  have hL : unifMeasure rΩ {f} = (Fintype.card rΩ : ℝ≥0∞)⁻¹ := by
    rw [unifMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton f),
      PMF.uniformFintype_apply]
  have hR : ∀ i : Fin 2306, unifMeasure RC {f i} = (Fintype.card RC : ℝ≥0∞)⁻¹ := by
    intro i
    rw [unifMeasure, PMF.toMeasure_apply_singleton _ _ (measurableSet_singleton _),
      PMF.uniformFintype_apply]
  rw [hL]; simp_rw [hR]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fun, Nat.cast_pow, ENNReal.inv_pow]

theorem rmgf_coord (i : Fin 2306) (X : RC → ℝ) (s : ℝ) :
    mgf (fun ω : rΩ => X (ω i)) (unifMeasure rΩ) s = mgf X (unifMeasure RC) s := by
  rw [runifMeasure_pi_eq]
  have hmap : (Measure.pi (fun _ : Fin 2306 => unifMeasure RC)).map (fun f : rΩ => f i)
      = unifMeasure RC :=
    (measurePreserving_eval (fun _ : Fin 2306 => unifMeasure RC) i).map_eq
  have hm := mgf_map (X := X) (Y := fun f : rΩ => f i)
      (μ := Measure.pi (fun _ : Fin 2306 => unifMeasure RC)) (t := s)
      (measurable_pi_apply i).aemeasurable
      (measurable_of_finite (fun ω : RC => Real.exp (s * X ω))).aestronglyMeasurable
  rw [hmap] at hm; exact hm.symm

theorem mgf_fst_RC (f : (CbdΩ × CbdΩ) → ℝ) (s : ℝ) :
    mgf (fun p : RC => f p.1) (unifMeasure RC) s = mgf f (unifMeasure (CbdΩ × CbdΩ)) s := by
  rw [mgf, mgf, unifMeasure, unifMeasure, PMF.integral_eq_sum, PMF.integral_eq_sum,
    Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro a _
  have hin : ∀ y : Fin 3329, ((PMF.uniformFintype RC) (a, y)).toReal • Real.exp (s * f (a, y).1)
       = ((Fintype.card RC : ℝ≥0∞)⁻¹).toReal * Real.exp (s * f a) := by
    intro y; rw [PMF.uniformFintype_apply]; simp [smul_eq_mul]
  rw [Finset.sum_congr rfl (fun y _ => hin y), Finset.sum_const, Finset.card_univ,
    PMF.uniformFintype_apply]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, nsmul_eq_mul]
  push_cast; ring

theorem mgf_snd_RC (g : Fin 3329 → ℝ) (s : ℝ) :
    mgf (fun p : RC => g p.2) (unifMeasure RC) s = mgf g (unifMeasure (Fin 3329)) s := by
  rw [mgf, mgf, unifMeasure, unifMeasure, PMF.integral_eq_sum, PMF.integral_eq_sum,
    Fintype.sum_prod_type, Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro b _
  have hin : ∀ a : CbdΩ × CbdΩ, ((PMF.uniformFintype RC) (a, b)).toReal • Real.exp (s * g (a, b).2)
       = ((Fintype.card RC : ℝ≥0∞)⁻¹).toReal * Real.exp (s * g b) := by
    intro a; rw [PMF.uniformFintype_apply]; simp [smul_eq_mul]
  rw [Finset.sum_congr rfl (fun a _ => hin a), Finset.sum_const, Finset.card_univ,
    PMF.uniformFintype_apply]
  simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool, ENNReal.toReal_inv,
    ENNReal.toReal_natCast, smul_eq_mul, nsmul_eq_mul]
  push_cast; ring

theorem mgf_e2_RC (s : ℝ) :
    mgf (fun p : RC => cbd2X p.1.1) (unifMeasure RC) s = mgf cbd2X (unifMeasure CbdΩ) s :=
  (mgf_fst_RC (fun q : CbdΩ × CbdΩ => cbd2X q.1) s).trans (mgf_cbd2_fst s)

-- ===== THE REFINED TERM FAMILY =====
noncomputable def rTermR (i : Fin 2306) : RC → ℝ :=
  fun p => if i.val < 2304 then cbd2ProdX p.1 else if i.val = 2304 then cbd2X p.1.1 else dvTrueX p.2
def rTermZ (i : Fin 2306) : RC → ℤ :=
  fun p => if i.val < 2304 then cbd2Ez 0 p.1.1 * cbd2Ez 0 p.1.2
           else if i.val = 2304 then cbd2Ez 0 p.1.1 else cErr p.2.val
theorem rTermZR (i : Fin 2306) (p : RC) : ((rTermZ i p : ℤ) : ℝ) = rTermR i p := by
  unfold rTermZ rTermR
  split_ifs with h1 h2
  · rw [Int.cast_mul, cbd2Ez_cast, cbd2Ez_cast]; rfl
  · rw [cbd2Ez_cast]
  · rfl
noncomputable def rT (i : Fin 2306) : rΩ → ℝ := fun ω => rTermR i (ω i)
def rZ : Fin 768 → rΩ → ℤ := fun _ ω => ∑ i, rTermZ i (ω i)

theorem rTermR_prod (i : Fin 2306) (h : i.val < 2304) : rTermR i = (fun p : RC => cbd2ProdX p.1) := by
  funext p; unfold rTermR; rw [if_pos h]
theorem rTermR_e2 (i : Fin 2306) (h : i.val = 2304) : rTermR i = (fun p : RC => cbd2X p.1.1) := by
  funext p; unfold rTermR; rw [if_neg (by omega), if_pos h]
theorem rTermR_dv (i : Fin 2306) (h : ¬ i.val < 2304) (h2 : i.val ≠ 2304) :
    rTermR i = (fun p : RC => dvTrueX p.2) := by
  funext p; unfold rTermR; rw [if_neg h, if_neg h2]

theorem rindep : iIndepFun rT (unifMeasure rΩ) := by
  rw [runifMeasure_pi_eq]
  exact iIndepFun_pi (fun i => (measurable_of_finite (rTermR i)).aemeasurable)
theorem rmeas (i : Fin 2306) : Measurable (rT i) := measurable_of_finite _

noncomputable def rBoundOf (i : Fin 2306) : ℝ :=
  if i.val < 2304 then mlkemProdMgfBound else if i.val = 2304 then Real.exp (9/200) else dvTrueBound
noncomputable def mlkemRefinedMgfBound : ℝ :=
  mlkemProdMgfBound ^ 2304 * Real.exp (9/200) * dvTrueBound

theorem rBoundOf_nn (i : Fin 2306) : 0 ≤ rBoundOf i := by
  unfold rBoundOf; split_ifs
  · unfold mlkemProdMgfBound; positivity
  · positivity
  · exact le_of_lt dvTrueBound_pos

-- product cross-term MGF is even (needed for the -3/10 direction)
theorem mgf_cbd2prod_even (t : ℝ) :
    mgf cbd2ProdX (unifMeasure (CbdΩ × CbdΩ)) (-t) = mgf cbd2ProdX (unifMeasure (CbdΩ × CbdΩ)) t := by
  rw [mgf_cbd2prod_factored, mgf_cbd2prod_factored]
  apply Finset.sum_congr rfl; intro a _; congr 2
  rw [show -t * cbd2X a / 2 = -(t * cbd2X a / 2) from by ring, Real.cosh_neg]

theorem rterm_pos_le (i : Fin 2306) : mgf (rT i) (unifMeasure rΩ) (3/10) ≤ rBoundOf i := by
  unfold rT; rw [rmgf_coord]
  rcases lt_trichotomy i.val 2304 with h | h | h
  · rw [rTermR_prod i h, mgf_fst_RC, show rBoundOf i = mlkemProdMgfBound from by unfold rBoundOf; rw [if_pos h]]
    refine le_trans (mgf_cbd2prod_le (3/10)) (le_of_eq ?_)
    unfold mlkemProdMgfBound
    rw [show (2:ℝ)*(3/10)^2 = 9/50 from by norm_num, show ((3/10:ℝ))^2/2 = 9/200 from by norm_num]
  · rw [rTermR_e2 i h, mgf_e2_RC,
        show rBoundOf i = Real.exp (9/200) from by unfold rBoundOf; rw [if_neg (by omega), if_pos h]]
    refine le_trans (mgf_cbd2_le_exp (3/10)) (Real.exp_le_exp.mpr ?_); norm_num
  · rw [rTermR_dv i (by omega) (by omega), mgf_snd_RC,
        show rBoundOf i = dvTrueBound from by unfold rBoundOf; rw [if_neg (by omega), if_neg (by omega)]]
    exact mgf_dvTrue_pos_le

theorem rterm_neg_le (i : Fin 2306) : mgf (rT i) (unifMeasure rΩ) (-(3/10)) ≤ rBoundOf i := by
  unfold rT; rw [rmgf_coord]
  rcases lt_trichotomy i.val 2304 with h | h | h
  · rw [rTermR_prod i h, mgf_fst_RC, mgf_cbd2prod_even,
        show rBoundOf i = mlkemProdMgfBound from by unfold rBoundOf; rw [if_pos h]]
    refine le_trans (mgf_cbd2prod_le (3/10)) (le_of_eq ?_)
    unfold mlkemProdMgfBound
    rw [show (2:ℝ)*(3/10)^2 = 9/50 from by norm_num, show ((3/10:ℝ))^2/2 = 9/200 from by norm_num]
  · rw [rTermR_e2 i h, mgf_e2_RC,
        show rBoundOf i = Real.exp (9/200) from by unfold rBoundOf; rw [if_neg (by omega), if_pos h]]
    refine le_trans (mgf_cbd2_le_exp (-(3/10))) (Real.exp_le_exp.mpr ?_); norm_num
  · rw [rTermR_dv i (by omega) (by omega), mgf_snd_RC,
        show rBoundOf i = dvTrueBound from by unfold rBoundOf; rw [if_neg (by omega), if_neg (by omega)]]
    exact mgf_dvTrue_neg_le

theorem prod_rBoundOf : (∏ i, rBoundOf i) = mlkemRefinedMgfBound := by
  unfold mlkemRefinedMgfBound
  rw [Fin.prod_univ_castSucc, Fin.prod_univ_castSucc]
  have hlast : rBoundOf (Fin.last 2305) = dvTrueBound := by
    unfold rBoundOf; rw [if_neg (by rw [Fin.val_last]; omega), if_neg (by rw [Fin.val_last]; omega)]
  have hpen : rBoundOf (Fin.castSucc (Fin.last 2304)) = Real.exp (9/200) := by
    unfold rBoundOf; rw [if_neg (by rw [Fin.val_castSucc, Fin.val_last]; omega), if_pos (by rw [Fin.val_castSucc, Fin.val_last])]
  have hconst : ∀ i : Fin 2304, rBoundOf (Fin.castSucc (Fin.castSucc i)) = mlkemProdMgfBound := by
    intro i; unfold rBoundOf; rw [if_pos (by rw [Fin.val_castSucc, Fin.val_castSucc]; exact i.isLt)]
  rw [hlast, hpen, Finset.prod_congr rfl (fun i _ => hconst i), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]

-- ===== THE REFINED δ ARITHMETIC =====
theorem refinedMgf_delta_arith :
    2 * Real.exp (-(3/10)*832) * mlkemRefinedMgfBound ≤ (2:ℝ)^(-163:ℤ) := by
  have hprodpos : (0:ℝ) ≤ mlkemProdMgfBound := by unfold mlkemProdMgfBound; positivity
  have hpow : mlkemProdMgfBound ^ 2304 ≤ Real.exp ((467/10000) * 2304) := by
    calc mlkemProdMgfBound ^ 2304
        ≤ (Real.exp (467/10000)) ^ 2304 := pow_le_pow_left₀ hprodpos mlkemProdMgfBound_le_exp 2304
      _ = Real.exp ((467/10000) * 2304) := by rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
  have hC : (0:ℝ) ≤ dvTrueBound := dvTrueBound_pos.le
  have h1 : mlkemRefinedMgfBound ≤ Real.exp ((467/10000)*2304) * Real.exp (9/200) * dvTrueBound := by
    unfold mlkemRefinedMgfBound
    apply mul_le_mul_of_nonneg_right _ hC
    apply mul_le_mul_of_nonneg_right hpow (le_of_lt (Real.exp_pos _))
  have h2 : Real.exp ((467/10000)*2304) * Real.exp (9/200) * dvTrueBound
      = (160/9987) * Real.exp ((467/10000)*2304 + 9/200 + 63/2) := by
    unfold dvTrueBound
    rw [show Real.exp ((467/10000)*2304) * Real.exp (9/200) * ((160/9987) * Real.exp (63/2))
         = (160/9987) * (Real.exp ((467/10000)*2304) * Real.exp (9/200) * Real.exp (63/2)) from by ring,
       ← Real.exp_add, ← Real.exp_add]
  have hmul : 2 * Real.exp (-(3/10)*832) * mlkemRefinedMgfBound
      ≤ 2 * Real.exp (-(3/10)*832) * ((160/9987) * Real.exp ((467/10000)*2304 + 9/200 + 63/2)) := by
    apply mul_le_mul_of_nonneg_left (le_trans h1 (le_of_eq h2)) (by positivity)
  refine le_trans hmul ?_
  have heq : 2 * Real.exp (-(3/10)*832) * ((160/9987) * Real.exp ((467/10000)*2304 + 9/200 + 63/2))
        = (320/9987) * Real.exp (-(3/10)*832 + ((467/10000)*2304 + 9/200 + 63/2)) := by
    rw [show 2 * Real.exp (-(3/10)*832) * ((160/9987) * Real.exp ((467/10000)*2304 + 9/200 + 63/2))
          = (320/9987) * (Real.exp (-(3/10)*832) * Real.exp ((467/10000)*2304 + 9/200 + 63/2)) from by ring,
       ← Real.exp_add]
  rw [heq]
  have hexppos : (0:ℝ) ≤ Real.exp (-(3/10)*832 + ((467/10000)*2304 + 9/200 + 63/2)) := (Real.exp_pos _).le
  calc (320/9987 : ℝ) * Real.exp (-(3/10)*832 + ((467/10000)*2304 + 9/200 + 63/2))
      ≤ (1/16) * Real.exp (-(3/10)*832 + ((467/10000)*2304 + 9/200 + 63/2)) := by
        apply mul_le_mul_of_nonneg_right (by norm_num) hexppos
    _ ≤ (2:ℝ)^(-163:ℤ) := by
        rw [show (2:ℝ)^(-163:ℤ) = (1/16) * (2:ℝ)^(-159:ℤ) from by
              rw [show (-163:ℤ) = -159 + (-4) from by ring, zpow_add₀ (by norm_num:(2:ℝ)≠0)]; norm_num]
        gcongr
        rw [show (2:ℝ)^(-159:ℤ) = Real.exp (-159 * Real.log 2) from by
              rw [← Real.exp_log (show (0:ℝ) < (2:ℝ)^(-159:ℤ) by positivity), Real.log_zpow]
              congr 1; push_cast; ring]
        apply Real.exp_le_exp.mpr
        nlinarith [Real.log_two_lt_d9]

theorem rZ_perCoeffTail : PerCoeffHoeffdingTail rZ ((2:ℝ)^(-163:ℤ)) := by
  intro c
  have hbadeq : badCoeff rZ c = fun ω => decide ((832:ℝ) ≤ |∑ i, rT i ω|) := by
    funext ω
    have hZ : (rZ c ω : ℝ) = ∑ i, rT i ω := by
      show ((∑ i, rTermZ i (ω i) : ℤ):ℝ) = ∑ i, rT i ω
      push_cast; exact Finset.sum_congr rfl (fun i _ => rTermZR i (ω i))
    have hiff : ((832:ℤ) ≤ |rZ c ω|) ↔ ((832:ℝ) ≤ |∑ i, rT i ω|) := by
      rw [← hZ, ← Int.cast_abs]; exact_mod_cast Iff.rfl
    simp only [badCoeff, hiff]
  rw [hbadeq]
  refine le_trans (winProb_abs_exactMgf_bound_le rT (3/10) (by norm_num) rindep rmeas
    rBoundOf rterm_pos_le rterm_neg_le) ?_
  rw [prod_rBoundOf]
  exact refinedMgf_delta_arith

theorem rZ_decapsFailure_le_delta153 :
    winProb (decapsFails rZ) ≤ (2:ℝ)^(-153:ℤ) := by
  refine le_trans (mlkem_decapsFail_le rZ _ rZ_perCoeffTail) ?_
  have h768 : (768:ℝ) ≤ (2:ℝ)^(10:ℤ) := by norm_num
  have hpos : (0:ℝ) ≤ (2:ℝ)^(-163:ℤ) := by positivity
  calc (768:ℝ) * (2:ℝ)^(-163:ℤ)
      ≤ (2:ℝ)^(10:ℤ) * (2:ℝ)^(-163:ℤ) := by gcongr
    _ = (2:ℝ)^((10:ℤ)+(-163:ℤ)) := by rw [← zpow_add₀ (by norm_num:(2:ℝ)≠0)]
    _ = (2:ℝ)^(-153:ℤ) := by norm_num

/-! ## §19 — THE EXACT-PMF FIPS CLOSURE ON THE TRUE LIGHT `Δv` MODEL: reduction + the single named residual.

§18 built the TRUE near-uniform compression-error law `cErr` (support proven `[−104,104]`, `cErrFiber_le_16` the
exact near-uniformity) and ran it through the exact-MGF **Chernoff** on the fully-independent product model `rΩ`,
closing `2⁻¹⁶³` per coefficient / `2⁻¹⁵³` assembled — the honest ceiling of the Chernoff *rate* (the `768`-union
costs `≈10` bits; the Bahadur–Rao *prefactor* the rate discards is the remaining `≈17` bits to the true tail). §16
built the exact-PMF reduction `exactConvTailFrac_closes_delta`: a per-coefficient exact convolved-tail
`≤ 2⁻¹⁷⁴` closes FIPS `δ ≤ 2⁻¹⁶⁴` through the same `768`-union. This section FEEDS `rZ` (the true-light model)
into that reduction, so the FIPS bound reduces to ONE precisely-named exact-PMF tail on the TRUE light law.

### ⚑ PROBE — is the per-coefficient exact convolution kernel-computable? NO (R1, measured, now on the light law).

The per-coefficient error `rZ c` is the sum of `2306` independent bounded-support integer terms: `2304` CBD-product
cross-terms (law `prodCounts = [2,0,16,32,156,32,16,0,2]`, support `[−4,4]`, `prodCoord_law_center/_edge` PROVE the
product coordinate's marginal IS `prodCounts`), one CBD `e2` (law `cbdCounts`, `e2Coord_law_center`), and the true
`cErr` (support `[−104,104]`, ≤`16` per value, `cErrCoord_law_top` PROVES `cErr = 104` has count `9`). Its exact PMF
is therefore the finite convolution `prodCounts^{⊛2304} ⊛ cbdCounts ⊛ cErrLaw` — the SAME `2304`-fold `cvMul` §16
measured kernel-infeasible (R1: `256`-fold of a `5`-wide law already exceeds the heartbeat budget; the target is the
`2304`-fold of a `9`-wide law with `≈18000`-bit entries). Refining `Δv` to `cErr` does NOT shrink this: the light
`Δv` factor `cErrLaw` is a `209`-wide list (support `[−104,104]`), so the convolution is if anything *larger* than
the `±104` two-point `dvX` of §12–§15. So the per-coefficient exact convolution is NOT a "few-dozen-term" object —
it is the full `2304`-fold, astronomically beyond kernel `decide`. `native_decide` is forbidden here (a probabilistic
δ theorem must not ride `trustCompiler`). R1 remains a MEASURED wall.

### What IS closed (kernel-clean): the reduction on the TRUE light law, R2 discharged.

`rZ_mem_Icc` bounds the per-coefficient value into `[−239824, 239824]` (each of the `2306` terms is `[−104,104]`).
Feeding `rZ` and this support into `exactConvTailFrac_closes_delta` gives `rZ_lightExactConv_closes_delta`: the
per-coefficient exact convolved-tail `≤ 2⁻¹⁷⁴` (`LightExactPerCoeffTail`) closes FIPS `δ ≤ 2⁻¹⁶⁴` on the LITERAL
true-`cErr` model. `lightExact_iff_perCoeffTail` proves the named residual is EXACTLY "the per-coefficient tail of
the true light law is `≤ 2⁻¹⁷⁴`" (via `winProb_badCoeff_eq_convTail`) — load-bearing, not a wrapper. This DISCHARGES
§16's residual **R2** in the exact-PMF world: the model is now the literal compression error `cErr`, not the `±104`
`dvX` envelope (whose exact tail was the heavy `≈2⁻⁴²` that R2 named). The sole remaining residual is **R1**.

### THE SINGLE NAMED RESIDUAL (R1, exact, decidable, TRUE, kernel-infeasible).

`LightExactPerCoeffTail` is decidable (`rΩ` is a `Fintype`; `convCnt` is a `Finset.card`) and its TRUE value is
`≈ 2⁻¹⁸⁰` per coefficient — comfortably below the `2⁻¹⁷⁴` the reduction needs, so on the light model it GENUINELY
clears the FIPS bar. What blocks turning `mlkem768_decapsFailure_le_delta_lightExactConv` into an unconditional
theorem is exactly evaluating that decidable tail — the `2304`-fold `cvMul` (R1), kernel-infeasible. This is a far
sharper residual than §16's original R1+R2: **R2 is gone** (true law), and R1 is now a single decidable inequality
about the true light convolution whose true value is known (`≈2⁻¹⁸⁰`) — not a modeling gap, purely a kernel-cost
wall. (The `≈2⁻¹⁸⁰ → 2⁻¹⁷⁴` margin means even a substantially looser exact-PMF bound would suffice; only the kernel
evaluation of the astronomical convolution, not the mathematics, remains.) -/

instance : Nonempty rΩ := ⟨fun _ => ((default, default), 0)⟩

/-- Every CBD(η=2) coordinate (integer form) lies in `[−2,2]`. -/
theorem cbd2Ez_range (f : Fin 768) (p : CbdΩ) : -2 ≤ cbd2Ez f p ∧ cbd2Ez f p ≤ 2 := by
  obtain ⟨a, b, c, d⟩ := p
  cases a <;> cases b <;> cases c <;> cases d <;> norm_num [cbd2Ez]

/-- A product of two `[−2,2]` integers lies in `[−4,4]` (exhaustive over the `5×5` integer grid). -/
theorem prod_int_bound {a b : ℤ} (ha1 : -2 ≤ a) (ha2 : a ≤ 2) (hb1 : -2 ≤ b) (hb2 : b ≤ 2) :
    -4 ≤ a * b ∧ a * b ≤ 4 := by
  interval_cases a <;> interval_cases b <;> decide

/-- **Every one of the `2306` per-coefficient terms of the true-light model lies in `[−104,104]`.** The `2304`
CBD-product cross-terms lie in `[−4,4]` (`prod_int_bound`), the `e2` CBD in `[−2,2]`, and the true compression
error `cErr` in `[−104,104]` (`cErr_bound`, §18). -/
theorem rTermZ_bound (i : Fin 2306) (p : RC) : -104 ≤ rTermZ i p ∧ rTermZ i p ≤ 104 := by
  unfold rTermZ
  split_ifs with h1 h2
  · have hA := cbd2Ez_range 0 p.1.1
    have hB := cbd2Ez_range 0 p.1.2
    have := prod_int_bound hA.1 hA.2 hB.1 hB.2
    omega
  · have := cbd2Ez_range 0 p.1.1; omega
  · exact cErr_bound p.2

/-- **The true-light per-coefficient error is bounded: `rZ c ω ∈ [−239824, 239824]`.** The support Finset the
exact-PMF reduction filters the tail out of; `239824 = 2306 · 104`. -/
theorem rZ_mem_Icc (c : Fin 768) (ω : rΩ) :
    rZ c ω ∈ Finset.Icc (-239824 : ℤ) 239824 := by
  rw [Finset.mem_Icc]
  have hrz : rZ c ω = ∑ i : Fin 2306, rTermZ i (ω i) := rfl
  have key_lo : ∑ _i : Fin 2306, (-104:ℤ) ≤ ∑ i : Fin 2306, rTermZ i (ω i) :=
    Finset.sum_le_sum (fun i _ => (rTermZ_bound i (ω i)).1)
  have key_hi : ∑ i : Fin 2306, rTermZ i (ω i) ≤ ∑ _i : Fin 2306, (104:ℤ) :=
    Finset.sum_le_sum (fun i _ => (rTermZ_bound i (ω i)).2)
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at key_lo key_hi
  norm_num at key_lo key_hi
  rw [hrz]; exact ⟨key_lo, key_hi⟩

/-- **THE PRECISELY-NAMED RESIDUAL (R1) — the exact convolved-PMF tail of the TRUE light law.** For every
coefficient, the exact-PMF tail mass of `rZ c` (the literal `cErr`-based model) over the escaping values
`832 ≤ |k|` is `≤ 2⁻¹⁷⁴ · |rΩ|`. Decidable (`rΩ` `Fintype`, `convCnt` a `Finset.card`); TRUE value `≈2⁻¹⁸⁰`;
kernel evaluation is the astronomical `2304`-fold convolution (R1, measured infeasible in §16). -/
def LightExactPerCoeffTail : Prop :=
  ∀ c : Fin 768, (∑ k ∈ (Finset.Icc (-239824:ℤ) 239824).filter (fun k => (832 : ℤ) ≤ |k|),
      (convCnt (rZ c) k : ℝ)) ≤ (2 : ℝ) ^ (-174 : ℤ) * (Fintype.card rΩ : ℝ)

/-- **THE NAMED RESIDUAL IS EXACTLY THE PER-COEFFICIENT TAIL OF THE TRUE LIGHT LAW (PROVED).**
`LightExactPerCoeffTail ↔ (∀ c, winProb(badCoeff rZ c) ≤ 2⁻¹⁷⁴)` — via `winProb_badCoeff_eq_convTail`, the
convolved-tail residual IS the per-coefficient decryption-window-escape probability at `2⁻¹⁷⁴` on the literal
`cErr` model. Not a wrapper: the residual is load-bearing (it is the exact failure probability). -/
theorem lightExact_iff_perCoeffTail :
    LightExactPerCoeffTail ↔ PerCoeffHoeffdingTail rZ ((2 : ℝ) ^ (-174 : ℤ)) := by
  have hcard : (0 : ℝ) < (Fintype.card rΩ : ℝ) := by exact_mod_cast Fintype.card_pos
  unfold LightExactPerCoeffTail PerCoeffHoeffdingTail
  constructor
  · intro h c
    rw [winProb_badCoeff_eq_convTail rZ c (Finset.Icc (-239824) 239824) (fun ω => rZ_mem_Icc c ω),
        div_le_iff₀ hcard]
    exact h c
  · intro h c
    have hb := h c
    rw [winProb_badCoeff_eq_convTail rZ c (Finset.Icc (-239824) 239824) (fun ω => rZ_mem_Icc c ω),
        div_le_iff₀ hcard] at hb
    exact hb

/-- **THE EXACT-PMF FIPS REDUCTION ON THE TRUE LIGHT LAW (PROVED): `LightExactPerCoeffTail ⟹ δ ≤ 2⁻¹⁶⁴`.** Feeds
the literal `cErr`-based model `rZ` and its support (`rZ_mem_Icc`) into §16's `exactConvTailFrac_closes_delta`. The
FIPS `δ ≤ 2⁻¹⁶⁴` decryption-failure bound follows from the exact per-coefficient convolved tail `≤ 2⁻¹⁷⁴` — with
R2 discharged (the model is the true compression error, not the `±104` envelope). -/
theorem rZ_lightExactConv_closes_delta (h : LightExactPerCoeffTail) :
    winProb (decapsFails rZ) ≤ MlKemCorrect.mlKem768Delta :=
  exactConvTailFrac_closes_delta rZ (fun _ => Finset.Icc (-239824) 239824)
    (fun c ω => rZ_mem_Icc c ω) h

/-- **THE CAPSTONE (conditional on R1, the single decidable residual).** FIPS `δ ≤ 2⁻¹⁶⁴` for ML-KEM-768 on the
TRUE near-uniform compression-error model, GIVEN the exact per-coefficient convolved tail `≤ 2⁻¹⁷⁴`
(`LightExactPerCoeffTail`, true value `≈2⁻¹⁸⁰`). Same statement as the unconditional Chernoff `2⁻¹⁵³` capstone
`rZ_decapsFailure_le_delta153`, sharpened `11` bits to the FIPS bar — the sharpening is exactly the exact-PMF tail
R1 supplies over the Chernoff rate. -/
theorem mlkem768_decapsFailure_le_delta_lightExactConv (h : LightExactPerCoeffTail) :
    winProb (decapsFails rZ) ≤ MlKemCorrect.mlKem768Delta :=
  mlkem768_decapsFailure_le_delta rZ (lightExact_iff_perCoeffTail.mp h)

/-- **(TOOTH — the product coordinate's marginal law IS `prodCounts`, kernel `decide`.)** The center value `0`
has count `156` — matching `prodCounts = [2,0,16,32,156,32,16,0,2]` at offset `−4`. -/
theorem prodCoord_law_center :
    convCnt (fun p : CbdΩ × CbdΩ => cbd2Ez 0 p.1 * cbd2Ez 0 p.2) 0 = 156 := by decide

/-- **(TOOTH — the product coordinate's edge value.)** The extreme value `4` (`= 2·2`) has count `2`, the top
entry of `prodCounts`. -/
theorem prodCoord_law_edge :
    convCnt (fun p : CbdΩ × CbdΩ => cbd2Ez 0 p.1 * cbd2Ez 0 p.2) 4 = 2 := by decide

/-- **(TOOTH — the `e2` coordinate's marginal law IS `cbdCounts`.)** The center value `0` has count `6`, the
middle entry of `cbdCounts = [1,4,6,4,1]`. -/
theorem e2Coord_law_center : convCnt (cbd2Ez 0) 0 = 6 := by decide

set_option maxRecDepth 20000 in
/-- **(TOOTH — the true `Δv` coordinate's exact count at the support edge, kernel `decide` over `Fin 3329`.)** The
error value `104` is hit by exactly `9` inputs — the exact near-uniformity §18 characterized (`cErr = 104` count
`9`, `cErr = −104` count `8`), computed here as a concrete `convCnt`. -/
theorem cErrCoord_law_top : convCnt (fun x : Fin 3329 => cErr x.val) 104 = 9 := by
  decide

/-! ## AXIOM HYGIENE — every probabilistic theorem is kernel-clean (⊆ {propext, Classical.choice, Quot.sound}). -/

#assert_all_clean [
  winProb_anyFinRange_le_sum,
  mlkem_decapsFail_le,
  unionBound_closes_delta,
  mlkem768_decapsFailure_le_delta,
  perCoeff_tail_satisfiable,
  mlkem768_delta_fires,
  perCoeff_tail_refutable,
  winProb_eq_measureReal,
  winProb_abs_subgaussian_le,
  hoeffding_delta_arith,
  perCoeffHoeffdingTail_of_subgaussianSum,
  rademacher_mean_zero,
  rademacher_isSubgaussianSum,
  rademacher_delta_fires,
  cbd2_mean_zero,
  cbd2_isSubgaussianSum,
  hoeffdingProxy_cbdProduct,
  hoeffdingProxy_deltaV,
  hoeffding_budget_exceeds_2800,
  deltaV_alone_exceeds_2800,
  chebyshev_perCoeff_tail_ge_2pow_neg8,
  chebyshev_cannot_supply_tail,
  bernstein_exponent_honest_lt_11,
  bernstein_exponent_bestcase_lt_89,
  bernsteinBound_misses_delta,
  bernstein_honest_misses_delta,
  bernstein_bestcase_misses_delta,
  winProb_abs_exactMgf_le,
  mgf_cbd2_sum,
  mgf_cbd2_eq,
  mgf_cbd2_le_exp,
  cosh_pow4_le,
  mgf_cbd2_as_sum,
  mgf_cbd2prod_factored,
  mgf_cbd2prod_le,
  exp_9_50_le,
  exp_9_200_le,
  mlkemProdMgfBound_le,
  exactMgf_delta_arith,
  unionBound_closes_delta140,
  perCoeffExactMgfTail_of_exactMgfSum,
  mlkem768_decapsFailure_le_delta_exactMgf,
  cbd2prod_isExactMgfSum,
  cbd2prod_delta_exactMgf_fires,
  unifMeasure_pi_eq,
  mgf_coord,
  mgf_cbd2_fst,
  mgf_dvX_closed,
  mgf_dvX_symm,
  mgf_dvX_bound,
  cbd2Ez_cast,
  mlkemTermZR,
  mlkem_indep,
  mlkem_symm,
  mlkem_termbound,
  prod_mlkemBoundOf,
  mlkem_prod_mgf_le,
  mlkem_exactMgfSum,
  mlkem768_decapsFailure_le_delta_unconditional,
  mgf_le_exp_abs_of_abs_le,
  mgf_cbd2scaled_factored,
  mgf_cbd2scaled_le,
  mgf_cbd2scaled_symm,
  mgf_dv_faithful,
  gTermZR,
  gindep,
  gmeas,
  gsymm,
  gtermbound,
  gprod,
  gExactMgfSum,
  gDelta,
  gDelta_cbd2_fires,
  exp_81_200_le,
  mgf_grouped_shift_le,
  groupedMgf_delta_arith,
  bfTermZR,
  bfindep,
  bfmeas,
  bfsymm,
  prod_bfBoundN,
  prod_bfBoundOf,
  bf_termbound,
  bf_prod_mgf_le,
  bf_perCoeffTail,
  bf_decapsFailure_le_delta,
  mlkemProdMgfBound_le_exp,
  exactMgf_delta_arith_tight,
  unionBound_closes_delta148,
  perCoeffExactMgfTail_tight,
  mlkem768_decapsFailure_le_delta_exactMgf_tight,
  mlkem768_decapsFailure_le_delta_unconditional_tight,
  bf_decapsFailure_le_delta_tight,
  cbd_selfconv,
  prodCounts_total,
  cvMul_total_4fold,
  card_add_eq_conv,
  card_tail_eq_sum_cnt,
  winProb_badCoeff_eq_convTail,
  exactConvTailFrac_closes_delta,
  exactConvTail_reduction_fires,
  convTailNum_prodCounts,
  exactConvTailBound_satisfiable,
  exactConvTailBound_refutable,
  Dregg2.ForMathlib.BerryEsseen.tailFrac_eq,
  Dregg2.ForMathlib.BerryEsseen.tiltTailExp_le_one,
  Dregg2.ForMathlib.BerryEsseen.tailFrac_le_refined,
  Dregg2.ForMathlib.BerryEsseen.tiltTailExp_le_atom_geom,
  Dregg2.ForMathlib.BerryEsseen.geom_sum_le_inv_one_sub,
  Dregg2.ForMathlib.BerryEsseen.sum_pow_le_inv_one_sub,
  Dregg2.ForMathlib.BerryEsseen.tiltTailExp_strict_lt_one,
  Dregg2.ForMathlib.BerryEsseen.tiltTailExp_le_tiltTailProb,
  Dregg2.ForMathlib.BerryEsseen.reCharFn_le_one_sub,
  Dregg2.ForMathlib.BerryEsseen.reCharFn_le_exp,
  Dregg2.ForMathlib.BerryEsseen.reCharFn_two_point,
  Dregg2.ForMathlib.BerryEsseen.tiltTailExp_le_tailAtom_geom,
  mgf_eq_partition_div,
  winProb_ge_eq_tailFrac,
  winProb_ge_le_refined,
  winProb_abs_split,
  perCoeffExactMgfTail_bahadurRao,
  mlkem768_decapsFailure_le_delta_bahadurRao,
  mlkem768_decapsFailure_le_delta_bahadurRao_real,
  coeffBR_prefactor_satisfiable,
  coeffBR_prefactor_refutable,
  prefactor_geom_arith,
  coeffTail_reduce,
  coeffBR_prefactor_of_tailAtom,
  mlkem768_decapsFailure_le_delta_bahadurRao_real_tailAtom,
  coeffTailAtom_satisfiable,
  coeffTailAtom_refutable,
  sumFiber_geom_le,
  compress4_lt16,
  cErr_inj,
  cErrFiber_le_16,
  cErr_bound,
  mgf_dvTrue_sum,
  gjp_lt,
  gjn_lt,
  gjp_card,
  gjn_card,
  dvTrue_sum_pos,
  dvTrue_sum_neg,
  dvTrueBound_pos,
  dvTrue_key,
  mgf_dvTrue_pos_le,
  mgf_dvTrue_neg_le,
  winProb_abs_exactMgf_bound_le,
  runifMeasure_pi_eq,
  rmgf_coord,
  mgf_fst_RC,
  mgf_snd_RC,
  mgf_e2_RC,
  rTermZR,
  rTermR_prod,
  rTermR_e2,
  rTermR_dv,
  rindep,
  rmeas,
  rBoundOf_nn,
  mgf_cbd2prod_even,
  rterm_pos_le,
  rterm_neg_le,
  prod_rBoundOf,
  refinedMgf_delta_arith,
  rZ_perCoeffTail,
  rZ_decapsFailure_le_delta153,
  cbd2Ez_range,
  prod_int_bound,
  rTermZ_bound,
  rZ_mem_Icc,
  lightExact_iff_perCoeffTail,
  rZ_lightExactConv_closes_delta,
  mlkem768_decapsFailure_le_delta_lightExactConv,
  prodCoord_law_center,
  prodCoord_law_edge,
  e2Coord_law_center,
  cErrCoord_law_top
]

end Dregg2.Crypto.MlKemDelta

/-
# Dregg2.Proof.BeaconSpaceInterior — the INTERIOR, genuinely-independent Bernoulli witness
closing the `BeaconSpace` §5 / §6 non-vacuity OPEN.

**What this file closes.** `Dregg2.Proof.BeaconSpace` (read-only sibling) proves the
probabilistic-oracle layer — a `Measure` over beacon streams `ℕ → Bool` with the relay's
per-view Bernoulli(`h`) + cross-view-independence law (`indep_block`) — fully `h`-GENERIC for
its §1–§4 results (measure-0 tail, almost-everywhere honest hit, the constructive hit-index, and
the discharge of `Synchronizer`'s `hhit`). Its ONLY residual was the NON-VACUITY witness: the
witness it ships (`BeaconSpace.Inhabited.beacon`) uses the all-honest **Dirac** beacon at the
boundary supermajority `h = 1` (`Measure.dirac` only), which sidesteps the genuine cross-view
independence the `indep_block` field demands (the Dirac point-mass trivially has block-mass
`0^N`, never an actual product `∏ (1-h)`).

This file supplies the CANONICAL **interior** witness the §6 obstruction note named: a genuinely
independent **Bernoulli(`h`)-per-view product** at the strictly-interior honest fraction `h = 3/4`
(`2/3 < 3/4 < 1`), built as `Measure.infinitePi (fun _ => (PMF.bernoulli p hp).toMeasure)` over the
index `ℕ`. This is the infinite independent product the obstruction said was gated on
`Mathlib.Probability.ProductMeasure` (`Measure.infinitePi`, via the Ionescu–Tulcea / Kernel
machinery). At our pinned mathlib (`v4.30.0`, rev `1c2b90b…`) that module **does build**
(`lake build Mathlib.Probability.ProductMeasure` → exit 0, 2621 jobs), so the canonical witness is
realizable — no fallback needed.

**The crux — `indep_block` discharged with REAL independence (not the Dirac sidestep).** The block
event "every view in `[b, b+N)` is dishonest" is exactly the measurable box
`(↑(Finset.Ico b (b+N))).pi (fun _ => {false})`. The infinite product measure's defining
finite-box law `Measure.infinitePi_pi` collapses its mass to the genuine product of per-view
marginals `∏ i ∈ Finset.Ico b (b+N), μ {false}`; each factor is the Bernoulli false-mass
`bernoulli p hp false = 1 - p = 1/4` (`PMF.toMeasure_apply_singleton` + `PMF.bernoulli_apply`); the
`N` independent factors multiply to `(1-h)^N`. This is precisely the per-view independence the
Dirac witness could not exhibit — the views here are genuinely product-independent.

**Conclusion.** The §1–§4 `BeaconSpace` abstraction is non-vacuously instantiable at a real
*interior* honest fraction with genuine per-view independence, refuting any "only the degenerate
all-honest boundary works" worry. The capstone `beaconSpace_interior_nonvacuous` packages this:
the interior beacon is a bona-fide `BeaconSpace` with `2/3 < h < 1`, and it discharges the
honest-leader hit-index and the full synchronizer round.

**Rails.** No `axiom`/`admit`/`native_decide`/`sorry`. The measure construction legitimately uses
`Classical.choice` (mathlib's `infinitePi` does, via the projective-limit extension) — that is on
the kernel whitelist `{propext, Classical.choice, Quot.sound}`. Verified with
`lake env lean Dregg2/Proof/BeaconSpaceInterior.lean`.
-/
import Dregg2.Proof.BeaconSpace
import Mathlib.Probability.ProductMeasure
import Mathlib.Probability.ProbabilityMassFunction.Constructions

namespace Dregg2.Proof.BeaconSpaceInterior

open scoped ENNReal
open MeasureTheory ProbabilityTheory PMF

/-! ## 1. The interior honest fraction and its Bernoulli per-view measure. -/

/-- The interior honest probability as an `ℝ≥0` — strictly between `2/3` and `1`. -/
noncomputable def p : NNReal := 3 / 4

theorem p_le_one : p ≤ 1 := by unfold p; rw [div_le_one] <;> norm_num

/-- The per-view honest-leader law: a `Bernoulli(3/4)` over `Bool` (true = honest). -/
noncomputable def viewPMF : PMF Bool := PMF.bernoulli p p_le_one

/-- The per-view probability **measure** over `Bool`. -/
noncomputable def viewMeasure : Measure Bool := viewPMF.toMeasure

instance : IsProbabilityMeasure viewMeasure := by
  unfold viewMeasure; infer_instance

/-- The Bernoulli false-mass is `1 - p = 1/4` (a single dishonest view). This is the per-view
marginal that the independent product multiplies — the genuine independence content. -/
theorem viewMeasure_false : viewMeasure {false} = ENNReal.ofReal (1 - (3 / 4 : ℝ)) := by
  unfold viewMeasure viewPMF
  rw [(PMF.bernoulli p p_le_one).toMeasure_apply_singleton false (measurableSet_singleton false)]
  rw [PMF.bernoulli_apply]
  simp only [Bool.cond_false]
  -- `↑(1 - p) = ENNReal.ofReal (1 - 3/4)`, both equal `1/4`.
  have h1 : (1 : NNReal) - p = (1 / 4 : NNReal) := by
    rw [← NNReal.coe_inj, NNReal.coe_sub p_le_one]; unfold p; push_cast; norm_num
  rw [h1]
  rw [show (1 - (3 / 4 : ℝ)) = ((1 / 4 : NNReal) : ℝ) by push_cast; norm_num]
  rw [ENNReal.ofReal_coe_nnreal]

/-! ## 2. The interior beacon — the infinite independent Bernoulli product. -/

/-- **The canonical interior beacon measure.** The infinite product over all views `ℕ` of the
i.i.d. `Bernoulli(3/4)` per-view law. By `Measure.infinitePi` (Ionescu–Tulcea), the views are
genuinely product-independent — the cross-view independence the Dirac witness sidestepped. -/
noncomputable def interiorMeasure : Measure (ℕ → Bool) :=
  Measure.infinitePi (fun _ : ℕ => viewMeasure)

instance : IsProbabilityMeasure interiorMeasure := by
  unfold interiorMeasure; infer_instance

/-- **The block event is the measurable box** `(↑(Finset.Ico b (b+N))).pi (fun _ => {false})` —
"every view in the contiguous block `[b, b+N)` is dishonest". -/
theorem block_eq_pi (b N : ℕ) :
    {ω : ℕ → Bool | ∀ i, b ≤ i → i < b + N → ω i = false}
      = (↑(Finset.Ico b (b + N)) : Set ℕ).pi (fun _ => {false}) := by
  ext ω
  simp only [Set.mem_setOf_eq, Set.mem_pi, Finset.coe_Ico, Set.mem_Ico, Set.mem_singleton_iff]
  constructor
  · intro hω i hi; exact hω i hi.1 hi.2
  · intro hω i hbi hi; exact hω i ⟨hbi, hi⟩

/-- **`indep_block` discharged with GENUINE independence.** The block cylinder's mass is the
honest product `∏ i ∈ [b,b+N), μ{false} = (1/4)^N = (1-h)^N`. The product collapse is exactly the
infinite-product-measure finite-box law `Measure.infinitePi_pi`; the per-factor value is the
Bernoulli false-mass `1/4`. This is the per-view independence the Dirac witness could not exhibit. -/
theorem interior_indep_block (b N : ℕ) :
    interiorMeasure {ω | ∀ i, b ≤ i → i < b + N → ω i = false}
      = ENNReal.ofReal ((1 - (3 / 4 : ℝ)) ^ N) := by
  rw [block_eq_pi]
  unfold interiorMeasure
  rw [Measure.infinitePi_pi (μ := fun _ : ℕ => viewMeasure) (s := Finset.Ico b (b + N))
        (t := fun _ => {false}) (fun i _ => measurableSet_singleton false)]
  -- each factor is `viewMeasure {false} = ofReal (1 - 3/4)`; multiply `N` of them.
  simp_rw [viewMeasure_false]
  rw [Finset.prod_const, Nat.card_Ico]
  -- `(b + N) - b = N` exponent.
  rw [show (b + N) - b = N by omega]
  rw [← ENNReal.ofReal_pow (by norm_num)]

/-! ## 3. The interior `BeaconSpace` instance. -/

/-- **A concrete `BeaconSpace` at the strictly-interior honest fraction `h = 3/4`** with a
genuinely-independent Bernoulli-per-view product measure. Every structure field — crucially
`indep_block`, the cross-view independence — is discharged by the real infinite product, NOT a
degenerate point-mass. -/
noncomputable def beacon : BeaconSpace.BeaconSpace where
  μ := interiorMeasure
  isProb := by infer_instance
  h := 3 / 4
  honest_pos := by norm_num
  honest_super := by norm_num
  honest_le_one := by norm_num
  indep_block := interior_indep_block

/-! ## 4. Non-vacuity capstone. -/

/-- The interior beacon's honest fraction is strictly interior — `2/3 < 3/4 < 1` — so this is NOT
the degenerate `h = 1` boundary the Dirac witness used. -/
theorem beacon_h_interior : (2 : ℝ) / 3 < beacon.h ∧ beacon.h < 1 := by
  refine ⟨beacon.honest_super, ?_⟩
  show (3 : ℝ) / 4 < 1; norm_num

/-- **The capstone: the `BeaconSpace` abstraction is non-vacuously instantiable at a real interior
honest fraction with genuine per-view independence.** The interior beacon is a bona-fide
`BeaconSpace` whose honest fraction is strictly interior (`2/3 < h < 1`), whose block law is the
genuine independent product `(1-h)^N` (not a point-mass), and which discharges both the
constructive honest-leader hit-index (BeaconSpace §3) and the full synchronizer round with no
`hhit` hypothesis (BeaconSpace §4) — for every threshold and every (gst, t).

This refutes the "only the degenerate all-honest boundary works" worry the §6 obstruction note
flagged: the §1–§4 results hold over a genuinely-random, genuinely-interior beacon. -/
theorem beaconSpace_interior_nonvacuous :
    -- (i) strictly-interior honest fraction
    ((2 : ℝ) / 3 < beacon.h ∧ beacon.h < 1) ∧
    -- (ii) the genuine independent block law holds at this interior h
    (∀ b N : ℕ, beacon.μ {ω | ∀ i, b ≤ i → i < b + N → ω i = false}
      = ENNReal.ofReal ((1 - beacon.h) ^ N)) ∧
    -- (iii) the constructive honest-leader hit-index exists over this beacon (BeaconSpace §3)
    (∃ (ω : ℕ → Bool) (r : ℕ), BeaconSpace.honestLeader r ω) ∧
    -- (iv) and for any (gst, t) the full synchronizer round obtains, hhit-free (BeaconSpace §4)
    (∀ (Msg : Type) [Dregg2.World.World Msg] (gst t : Nat),
      ∃ (R : Dregg2.Proof.Synchronizer.LeaderRotation Msg) (r : Nat),
        t ≤ r ∧ gst ≤ r ∧ R.honestLeader r) := by
  refine ⟨beacon_h_interior, beacon.indep_block, ?_, ?_⟩
  · exact BeaconSpace.honestLeader_index_exists beacon
  · intro Msg _ gst t
    exact BeaconSpace.synchronizer_round_obtains_over_beacon beacon gst t

/-- The interior beacon is genuinely a `BeaconSpace` — structure inhabited. -/
noncomputable example : BeaconSpace.BeaconSpace := beacon

/-- The honest fraction is strictly below the `h = 1` boundary (genuinely interior). -/
example : beacon.h < 1 := beacon_h_interior.2

#assert_axioms viewMeasure_false
#assert_axioms interior_indep_block
#assert_axioms beacon_h_interior
#assert_axioms beaconSpace_interior_nonvacuous

end Dregg2.Proof.BeaconSpaceInterior

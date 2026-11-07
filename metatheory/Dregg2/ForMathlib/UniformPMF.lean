import Mathlib.Probability.ProbabilityMassFunction.Constructions

/-!
# The uniform `PMF` on a finset / fintype

Mathlib (2026-10-04) replaced `PMF.uniformOfFinset` / `PMF.uniformOfFintype` by the `Measure`
`MeasureTheory.Measure.uniformOfFinset`, leaving deprecated aliases that now name the measure.
The game-based proofs here sample from a `PMF` (pointwise masses, `toMeasure`), so this file keeps
the `PMF` constructions as they were, under the names `PMF.uniformFinset` / `PMF.uniformFintype`.
-/

open scoped Finset ENNReal

namespace PMF

variable {α : Type*}

section UniformFinset

/-- Uniform distribution taking the same non-zero probability on the nonempty finset `s`. -/
noncomputable def uniformFinset (s : Finset α) (hs : s.Nonempty) : PMF α := by
  classical
  refine ofFinset (fun a => if a ∈ s then s.card⁻¹ else 0) s ?_ ?_
  · simp only [Finset.sum_ite_mem, Finset.inter_self, Finset.sum_const, nsmul_eq_mul]
    have : (s.card : ℝ≥0∞) ≠ 0 := by
      simpa only [Ne, Nat.cast_eq_zero, Finset.card_eq_zero] using
        Finset.nonempty_iff_ne_empty.1 hs
    exact ENNReal.mul_inv_cancel this <| ENNReal.natCast_ne_top s.card
  · exact fun x hx => by simp only [hx, if_false]

variable {s : Finset α} (hs : s.Nonempty)

open scoped Classical in
@[simp]
theorem uniformFinset_apply (a : α) :
    uniformFinset s hs a = if a ∈ s then (s.card : ℝ≥0∞)⁻¹ else 0 :=
  rfl

variable (t : Set α)

open scoped Classical in
@[simp]
theorem toOuterMeasure_uniformFinset_apply :
    (uniformFinset s hs).toOuterMeasure t = #{x ∈ s | x ∈ t} / #s :=
  calc
    (uniformFinset s hs).toOuterMeasure t = ∑' x, if x ∈ t then uniformFinset s hs x else 0 :=
      toOuterMeasure_apply (uniformFinset s hs) t
    _ = ∑' x, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_congr fun x => by simp_rw [uniformFinset_apply, ← ite_and, and_comm]
    _ = ∑ x ∈ s with x ∈ t, if x ∈ s ∧ x ∈ t then (#s : ℝ≥0∞)⁻¹ else 0 :=
      tsum_eq_sum fun _ hx => if_neg fun h => hx (Finset.mem_filter.2 h)
    _ = ∑ x ∈ s with x ∈ t, (#s : ℝ≥0∞)⁻¹ :=
      Finset.sum_congr rfl fun x hx => by
        have this : x ∈ s ∧ x ∈ t := by simpa using hx
        simp only [this, and_self_iff, if_true]
    _ = #{x ∈ s | x ∈ t} / #s := by
        simp only [div_eq_mul_inv, Finset.sum_const, nsmul_eq_mul]

open scoped Classical in
@[simp]
theorem toMeasure_uniformFinset_apply [MeasurableSpace α] (ht : MeasurableSet t) :
    (uniformFinset s hs).toMeasure t = #{x ∈ s | x ∈ t} / #s :=
  (toMeasure_apply_eq_toOuterMeasure_apply _ ht).trans (toOuterMeasure_uniformFinset_apply hs t)

end UniformFinset

section UniformFintype

/-- The uniform pmf taking the same uniform value on all of the fintype `α`. -/
noncomputable def uniformFintype (α : Type*) [Fintype α] [Nonempty α] : PMF α :=
  uniformFinset Finset.univ Finset.univ_nonempty

variable [Fintype α] [Nonempty α]

@[simp]
theorem uniformFintype_apply (a : α) : uniformFintype α a = (Fintype.card α : ℝ≥0∞)⁻¹ := by
  simp [uniformFintype, Finset.mem_univ, uniformFinset_apply]

@[simp]
theorem support_uniformFintype (α : Type*) [Fintype α] [Nonempty α] :
    (uniformFintype α).support = ⊤ :=
  Set.ext fun x => by simp [mem_support_iff]

theorem mem_support_uniformFintype (a : α) : a ∈ (uniformFintype α).support := by simp

variable (s : Set α)

theorem toOuterMeasure_uniformFintype_apply [Fintype s] :
    (uniformFintype α).toOuterMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [uniformFintype, toOuterMeasure_uniformFinset_apply, Fintype.card_subtype,
    Finset.card_univ]

theorem toMeasure_uniformFintype_apply [MeasurableSpace α] (hs : MeasurableSet s) [Fintype s] :
    (uniformFintype α).toMeasure s = Fintype.card s / Fintype.card α := by
  classical
  rw [toMeasure_apply_eq_toOuterMeasure_apply _ hs, toOuterMeasure_uniformFintype_apply]

end UniformFintype

end PMF

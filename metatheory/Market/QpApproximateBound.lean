/-
# Market.QpApproximateBound — an honest quantitative meaning for inexact stationarity.

The deployed OSQP-shaped checker accepts three residuals at a positive tolerance.  That fact alone
does not imply exact global optimality: approximate primal feasibility and approximate projection
membership need their own error analysis.  There is nevertheless a useful proof-carrying rung that
does not overclaim.

If the candidate is exactly feasible, its dual is exactly in the constraint-box normal cone, and
only stationarity is inexact with coordinatewise error at most `epsilon`, convexity proves

    f(x) <= f(x') + epsilon * ||x' - x||_1

for every feasible competitor `x'`.  A relying product with an independently certified feasible-set
diameter `R` immediately gets an `epsilon * R` additive optimality guarantee.  This is the precise
distance term that disappears when stationarity is exact.

Wire parsing, fixed-point scaling, an `R` certificate, and reduction of the deployed positive primal
and normal residuals remain outside this theorem.
-/

import Market.CertQpRustDenotation
import Dregg2.Tactics

namespace Market.QpApproximateBound

set_option autoImplicit false

open Matrix

/-- Coordinatewise exact-rational stationarity error bound. -/
def StationarityResidualAtMost {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (x : Fin n -> ℚ) (y : Fin mc -> ℚ)
    (epsilon : ℚ) : Prop :=
  ∀ j, |Market.rustPTimes prob x j + prob.q j + Market.rustATTimes prob y j| ≤ epsilon

/-- The exact feasible/normal-cone envelope with bounded, possibly nonzero stationarity. -/
structure DistanceBoundedKkt {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (x : Fin n -> ℚ) (y : Fin mc -> ℚ)
    (epsilon : ℚ) : Prop where
  epsilon_nonneg : 0 ≤ epsilon
  feasible : Market.RustQpFeasible prob x
  stationarity : StationarityResidualAtMost prob x y epsilon
  normalCone : Market.RustQpNormalCone prob x y

/-- L1 displacement from the certified point to a competitor. -/
def l1Distance {n : Nat} (x x' : Fin n -> ℚ) : ℚ :=
  ∑ j, |x' j - x j|

theorem residual_dot_lower_bound {n : Nat} {r delta : Fin n -> ℚ} {epsilon : ℚ}
    (hres : ∀ j, |r j| ≤ epsilon) :
    -(epsilon * ∑ j, |delta j|) ≤ r ⬝ᵥ delta := by
  have hterm : ∀ j, -(epsilon * |delta j|) ≤ r j * delta j := by
    intro j
    have hlo : -epsilon ≤ r j := by
      have habs := neg_abs_le (r j)
      linarith [hres j]
    have hhi : r j ≤ epsilon := le_trans (le_abs_self (r j)) (hres j)
    by_cases hdelta : 0 ≤ delta j
    · have hmul := mul_le_mul_of_nonneg_right hlo hdelta
      simpa [abs_of_nonneg hdelta] using hmul
    · have hdelta' : delta j ≤ 0 := le_of_not_ge hdelta
      have hmul := mul_le_mul_of_nonpos_right hhi hdelta'
      rw [abs_of_nonpos hdelta']
      linarith
  rw [dotProduct]
  calc
    -(epsilon * ∑ j, |delta j|) = ∑ j, -(epsilon * |delta j|) := by
      rw [Finset.mul_sum, Finset.sum_neg_distrib]
    _ ≤ ∑ j, r j * delta j := Finset.sum_le_sum fun j _ => hterm j

/-- **Approximate KKT distance law.** Exact feasibility and exact normal-cone membership turn a
coordinatewise stationarity tolerance into a quantitative objective bound, rather than a false exact
optimality claim. -/
theorem approximate_kkt_distance_bound {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (hP : Market.PsdSymm prob.p)
    {x : Fin n -> ℚ} {y : Fin mc -> ℚ} {epsilon : ℚ}
    (cert : DistanceBoundedKkt prob x y epsilon)
    {x' : Fin n -> ℚ} (hfeas' : Market.RustQpFeasible prob x') :
    Market.rustQpObjective prob x ≤
      Market.rustQpObjective prob x' + epsilon * l1Distance x x' := by
  let residual : Fin n -> ℚ := fun j =>
    Market.rustPTimes prob x j + prob.q j + Market.rustATTimes prob y j
  have hnormalPoint : ∀ i,
      y i * (Market.rustATimes prob x' i - Market.rustATimes prob x i) ≤ 0 := by
    intro i
    exact Market.rustClamp_fixed_normal (cert.feasible i).1 (cert.feasible i).2
      (hfeas' i).1 (hfeas' i).2 (cert.normalCone i)
  have hnormalSum :
      y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x)) ≤ 0 := by
    rw [dotProduct]
    apply Finset.sum_nonpos
    intro i _hi
    simpa [Market.rustATimes_eq_mulVec] using hnormalPoint i
  have hdecomp : prob.p *ᵥ x + prob.q = residual - (y ᵥ* prob.a) := by
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, residual]
    rw [← Market.rustPTimes_eq_mulVec, ← Market.rustATTimes_eq_vecMul]
    ring
  have hgrad :
      (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) =
        residual ⬝ᵥ (x' - x) -
          y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x)) := by
    rw [hdecomp, sub_dotProduct]
    exact congrArg (residual ⬝ᵥ (x' - x) - ·)
      ((dotProduct_mulVec y prob.a (x' - x)).symm.trans
        (congrArg (y ⬝ᵥ ·) (mulVec_sub prob.a x' x)))
  have hres : ∀ j, |residual j| ≤ epsilon := by
    intro j
    exact cert.stationarity j
  have hresLower :
      -(epsilon * l1Distance x x') ≤ residual ⬝ᵥ (x' - x) := by
    simpa [l1Distance] using
      (residual_dot_lower_bound (r := residual) (delta := x' - x)
        hres)
  let core : Market.QP (Fin n) (Fin 0) :=
    { P := prob.p
      q := prob.q
      A := fun i => i.elim0
      b := fun i => i.elim0
      l := fun _ => 0
      u := fun _ => 0
      ε := 0 }
  have hconv := Market.quad_convex_ge (qp := core) hP x x'
  change (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) ≤
    Market.rustQpObjective prob x' - Market.rustQpObjective prob x at hconv
  rw [hgrad] at hconv
  linarith

/-- A separately certified feasible-set radius removes the competitor-dependent term. -/
theorem approximate_kkt_radius_bound {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (hP : Market.PsdSymm prob.p)
    {x : Fin n -> ℚ} {y : Fin mc -> ℚ} {epsilon radius : ℚ}
    (cert : DistanceBoundedKkt prob x y epsilon)
    (hradius : ∀ x', Market.RustQpFeasible prob x' -> l1Distance x x' ≤ radius)
    {x' : Fin n -> ℚ} (hfeas' : Market.RustQpFeasible prob x') :
    Market.rustQpObjective prob x ≤ Market.rustQpObjective prob x' + epsilon * radius := by
  have hbase := approximate_kkt_distance_bound prob hP cert hfeas'
  have hscale := mul_le_mul_of_nonneg_left (hradius x' hfeas') cert.epsilon_nonneg
  linarith

/-! ## The deployed projection residual, quantitatively rather than exactly. -/

/-- A clamped value is inside its public interval. -/
theorem rustClamp_mem {value lower upper : ℚ} (hlu : lower ≤ upper) :
    lower ≤ Market.rustClamp value lower upper ∧
      Market.rustClamp value lower upper ≤ upper := by
  constructor
  · exact le_min (le_max_right _ _) hlu
  · exact min_le_right _ _

/-- Approximate projection membership gives an explicit normal-cone loss.  The loss depends only
on the projection error, interval width, and the public dual magnitude; it is zero at an exact
projection fixed point. -/
theorem approximate_clamp_normal {lower z upper y z' delta : ℚ}
    (hlu : lower ≤ upper) (hz'lower : lower ≤ z') (hz'upper : z' ≤ upper)
    (hdelta : 0 ≤ delta)
    (hprojection : |z - Market.rustClamp (z + y) lower upper| ≤ delta) :
    y * (z' - z) ≤ delta * ((upper - lower) + |y|) := by
  let w := Market.rustClamp (z + y) lower upper
  let normal := z + y - w
  have hw := rustClamp_mem (value := z + y) hlu
  have hnormal : normal * (z' - w) ≤ 0 := by
    apply Market.rustClamp_fixed_normal hw.1 hw.2 hz'lower hz'upper
    change w = Market.rustClamp (w + normal) lower upper
    have : w + normal = z + y := by simp [normal]
    rw [this]
  have hwidth : 0 ≤ upper - lower := sub_nonneg.mpr hlu
  have hspan : |z' - w| ≤ upper - lower := by
    rw [abs_le]
    constructor <;> linarith [hw.1, hw.2]
  have herror : |w - z| ≤ delta := by
    simpa [w, abs_sub_comm] using hprojection
  have hcross : (w - z) * (z' - w) ≤ delta * (upper - lower) := by
    calc
      (w - z) * (z' - w) ≤ |(w - z) * (z' - w)| := le_abs_self _
      _ = |w - z| * |z' - w| := abs_mul _ _
      _ ≤ delta * (upper - lower) :=
        mul_le_mul herror hspan (abs_nonneg _) hdelta
  have hdualError : y * (w - z) ≤ |y| * delta := by
    calc
      y * (w - z) ≤ |y * (w - z)| := le_abs_self _
      _ = |y| * |w - z| := abs_mul _ _
      _ ≤ |y| * delta := mul_le_mul_of_nonneg_left herror (abs_nonneg y)
  have hsplit :
      y * (z' - z) = normal * (z' - w) + (w - z) * (z' - w) + y * (w - z) := by
    simp only [normal]
    ring
  rw [hsplit]
  nlinarith

/-- Pointwise projection/normal residual bound used by the deployed checker. -/
def NormalResidualAtMost {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (x : Fin n -> ℚ) (y : Fin mc -> ℚ)
    (epsilon : ℚ) : Prop :=
  ∀ i, Market.rustNormalViolation prob x y i ≤ epsilon

/-- The two residuals that affect the convex objective inequality. Candidate feasibility is a
separate admissibility obligation: the objective law itself remains true for an infeasible `x`, but
a product must not call that point an executable allocation without also checking primal residual. -/
structure ResidualObjectiveCertificate {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (x : Fin n -> ℚ) (y : Fin mc -> ℚ)
    (dualTolerance normalTolerance : ℚ) : Prop where
  dual_nonneg : 0 ≤ dualTolerance
  normal_nonneg : 0 ≤ normalTolerance
  ordered_bounds : ∀ i, prob.l i ≤ prob.u i
  stationarity : StationarityResidualAtMost prob x y dualTolerance
  normal : NormalResidualAtMost prob x y normalTolerance

/-- Public coefficient multiplying the normal/projection tolerance. -/
def normalLossWeight {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (y : Fin mc -> ℚ) : ℚ :=
  ∑ i : Fin mc, ((prob.u i - prob.l i) + abs (y i))

/-- **Full residual objective law.** Positive stationarity and normal/projection tolerances produce
two explicit additive loss terms. This is the theorem shape needed by the deployed checker; its
separate primal residual still governs whether `x` is an admissible executable allocation. -/
theorem residual_objective_bound {n mc : Nat}
    (prob : Market.RustQpProblem n mc) (hP : Market.PsdSymm prob.p)
    {x : Fin n -> ℚ} {y : Fin mc -> ℚ} {dualTolerance normalTolerance : ℚ}
    (cert : ResidualObjectiveCertificate prob x y dualTolerance normalTolerance)
    {x' : Fin n -> ℚ} (hfeas' : Market.RustQpFeasible prob x') :
    Market.rustQpObjective prob x ≤ Market.rustQpObjective prob x' +
      dualTolerance * l1Distance x x' +
      normalTolerance * normalLossWeight prob y := by
  let residual : Fin n -> ℚ := fun j =>
    Market.rustPTimes prob x j + prob.q j + Market.rustATTimes prob y j
  have hnormalPoint : ∀ i,
      y i * (Market.rustATimes prob x' i - Market.rustATimes prob x i) ≤
        normalTolerance * ((prob.u i - prob.l i) + |y i|) := by
    intro i
    apply approximate_clamp_normal (cert.ordered_bounds i) (hfeas' i).1 (hfeas' i).2
      cert.normal_nonneg
    exact cert.normal i
  have hnormalSum :
      y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x)) ≤
        normalTolerance * normalLossWeight prob y := by
    rw [dotProduct, normalLossWeight, Finset.mul_sum]
    apply Finset.sum_le_sum
    intro i _hi
    simpa [Market.rustATimes_eq_mulVec] using hnormalPoint i
  have hdecomp : prob.p *ᵥ x + prob.q = residual - (y ᵥ* prob.a) := by
    funext j
    simp only [Pi.add_apply, Pi.sub_apply, residual]
    rw [← Market.rustPTimes_eq_mulVec, ← Market.rustATTimes_eq_vecMul]
    ring
  have hgrad :
      (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) =
        residual ⬝ᵥ (x' - x) -
          y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x)) := by
    rw [hdecomp, sub_dotProduct]
    exact congrArg (residual ⬝ᵥ (x' - x) - ·)
      ((dotProduct_mulVec y prob.a (x' - x)).symm.trans
        (congrArg (y ⬝ᵥ ·) (mulVec_sub prob.a x' x)))
  have hres : ∀ j, |residual j| ≤ dualTolerance := by
    intro j
    exact cert.stationarity j
  have hresLower :
      -(dualTolerance * l1Distance x x') ≤ residual ⬝ᵥ (x' - x) := by
    simpa [l1Distance] using
      (residual_dot_lower_bound (r := residual) (delta := x' - x) hres)
  let core : Market.QP (Fin n) (Fin 0) :=
    { P := prob.p
      q := prob.q
      A := fun i => i.elim0
      b := fun i => i.elim0
      l := fun _ => 0
      u := fun _ => 0
      ε := 0 }
  have hconv := Market.quad_convex_ge (qp := core) hP x x'
  change (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) ≤
    Market.rustQpObjective prob x' - Market.rustQpObjective prob x at hconv
  rw [hgrad] at hconv
  linarith

/-! ## Composition with the deployed exact-rational checker denotation. -/

theorem foldl_max_acc_le (values : List ℚ) (acc : ℚ) :
    acc ≤ values.foldl max acc := by
  induction values generalizing acc with
  | nil => rfl
  | cons value values ih =>
      simp only [List.foldl_cons]
      exact (le_max_left acc value).trans (ih (max acc value))

theorem mem_le_foldl_max (values : List ℚ) {value : ℚ} (hmem : value ∈ values)
    (acc : ℚ) : value ≤ values.foldl max acc := by
  induction values generalizing acc with
  | nil => simp at hmem
  | cons head tail ih =>
      simp only [List.foldl_cons]
      rcases List.mem_cons.mp hmem with rfl | htail
      · exact (le_max_right acc value).trans (foldl_max_acc_le tail (max acc value))
      · exact ih htail (max acc head)

theorem coordinate_le_rustMaxResidual {n : Nat} (values : Fin n -> ℚ) (i : Fin n) :
    values i ≤ Market.rustMaxResidual (List.ofFn values) := by
  apply mem_le_foldl_max (List.ofFn values) (List.mem_ofFn.mpr ⟨i, rfl⟩) 0

theorem checked_dual_coordinate {n mc : Nat} (cert : Market.RustCertQp n mc)
    (hcheck : Market.rustCertQpCheck cert = true) (j : Fin n) :
    Market.rustDualViolation cert.prob cert.x cert.y j ≤ cert.epsilon := by
  have hbound := (Market.rustCertQpCheck_iff cert).mp hcheck |>.2.1
  exact (coordinate_le_rustMaxResidual
    (fun k => Market.rustDualViolation cert.prob cert.x cert.y k) j).trans hbound

theorem checked_normal_coordinate {n mc : Nat} (cert : Market.RustCertQp n mc)
    (hcheck : Market.rustCertQpCheck cert = true) (i : Fin mc) :
    Market.rustNormalViolation cert.prob cert.x cert.y i ≤ cert.epsilon := by
  have hbound := (Market.rustCertQpCheck_iff cert).mp hcheck |>.2.2
  exact (coordinate_le_rustMaxResidual
    (fun k => Market.rustNormalViolation cert.prob cert.x cert.y k) i).trans hbound

theorem checked_primal_coordinate {n mc : Nat} (cert : Market.RustCertQp n mc)
    (hcheck : Market.rustCertQpCheck cert = true) (i : Fin mc) :
    Market.rustPrimalViolation cert.prob cert.x i ≤ cert.epsilon := by
  have hbound := (Market.rustCertQpCheck_iff cert).mp hcheck |>.1
  exact (coordinate_le_rustMaxResidual
    (fun k => Market.rustPrimalViolation cert.prob cert.x k) i).trans hbound

/-- The checker's primal residual means the returned point lies in the public constraint box
expanded by exactly `epsilon` on each side. -/
theorem checked_point_is_epsilon_feasible {n mc : Nat} (cert : Market.RustCertQp n mc)
    (hcheck : Market.rustCertQpCheck cert = true) (i : Fin mc) :
    cert.prob.l i - cert.epsilon ≤ Market.rustATimes cert.prob cert.x i ∧
      Market.rustATimes cert.prob cert.x i ≤ cert.prob.u i + cert.epsilon := by
  have hres := checked_primal_coordinate cert hcheck i
  change max (Market.rustATimes cert.prob cert.x i - cert.prob.u i) 0 +
    max (cert.prob.l i - Market.rustATimes cert.prob cert.x i) 0 ≤ cert.epsilon at hres
  have hupperPart :
      max (Market.rustATimes cert.prob cert.x i - cert.prob.u i) 0 ≤ cert.epsilon := by
    have hnonneg : 0 ≤ max (cert.prob.l i - Market.rustATimes cert.prob cert.x i) 0 :=
      le_max_right _ _
    linarith
  have hlowerPart :
      max (cert.prob.l i - Market.rustATimes cert.prob cert.x i) 0 ≤ cert.epsilon := by
    have hnonneg : 0 ≤ max (Market.rustATimes cert.prob cert.x i - cert.prob.u i) 0 :=
      le_max_right _ _
    linarith
  constructor
  · have := le_max_left (cert.prob.l i - Market.rustATimes cert.prob cert.x i) 0
    linarith
  · have := le_max_left (Market.rustATimes cert.prob cert.x i - cert.prob.u i) 0
    linarith

/-- **Deployed-checker quantitative meaning.** At its exact-rational denotation, positive-tolerance
acceptance gives both coordinatewise epsilon-feasibility and an explicit convex-objective loss bound.
It still does not give exact feasibility or exact global optimality. -/
theorem rustCertQpCheck_quantitative {n mc : Nat} (cert : Market.RustCertQp n mc)
    (hP : Market.PsdSymm cert.prob.p)
    (hordered : ∀ i, cert.prob.l i ≤ cert.prob.u i)
    (hepsilon : 0 ≤ cert.epsilon)
    (hcheck : Market.rustCertQpCheck cert = true)
    {x' : Fin n -> ℚ} (hfeas' : Market.RustQpFeasible cert.prob x') :
    (∀ i, cert.prob.l i - cert.epsilon ≤ Market.rustATimes cert.prob cert.x i ∧
      Market.rustATimes cert.prob cert.x i ≤ cert.prob.u i + cert.epsilon) ∧
    Market.rustQpObjective cert.prob cert.x ≤ Market.rustQpObjective cert.prob x' +
      cert.epsilon * l1Distance cert.x x' +
      cert.epsilon * normalLossWeight cert.prob cert.y := by
  constructor
  · intro i
    exact checked_point_is_epsilon_feasible cert hcheck i
  · apply residual_objective_bound cert.prob hP
      { dual_nonneg := hepsilon
        normal_nonneg := hepsilon
        ordered_bounds := hordered
        stationarity := by
          intro j
          exact checked_dual_coordinate cert hcheck j
        normal := by
          intro i
          exact checked_normal_coordinate cert hcheck i }
      hfeas'

/-! ## Executable/non-vacuous one-dimensional tooth. -/

def approximateFixture : DistanceBoundedKkt Market.rustQpOne
    Market.rustApproxWitness.x Market.rustApproxWitness.y 1 where
  epsilon_nonneg := by norm_num
  feasible := by
    intro i
    fin_cases i
    norm_num [Market.rustQpOne, Market.rustApproxWitness, Market.rustATimes]
  stationarity := by
    intro j
    fin_cases j
    norm_num [StationarityResidualAtMost, Market.rustQpOne, Market.rustApproxWitness,
      Market.rustPTimes, Market.rustATTimes]
  normalCone := by
    intro i
    fin_cases i
    norm_num [Market.rustQpOne, Market.rustApproxWitness, Market.rustATimes, Market.rustClamp]

/-- The accepted positive stationarity tolerance does not claim that `x=0` beats the true feasible
optimum `x'=1`; it proves only the honest additive-distance bound. -/
theorem approximateFixture_bound :
    Market.rustQpObjective Market.rustQpOne Market.rustApproxWitness.x ≤
      Market.rustQpObjective Market.rustQpOne (fun _ => 1) +
        1 * l1Distance Market.rustApproxWitness.x (fun _ => 1) := by
  apply approximate_kkt_distance_bound Market.rustQpOne Market.qp1_psd approximateFixture
  intro i
  fin_cases i
  norm_num [Market.rustQpOne, Market.rustATimes]

#guard Market.rustQpObjective Market.rustQpOne (fun _ => 1) <
  Market.rustQpObjective Market.rustQpOne Market.rustApproxWitness.x

#assert_axioms residual_dot_lower_bound
#assert_axioms approximate_kkt_distance_bound
#assert_axioms approximate_kkt_radius_bound
#assert_axioms rustClamp_mem
#assert_axioms approximate_clamp_normal
#assert_axioms residual_objective_bound
#assert_axioms coordinate_le_rustMaxResidual
#assert_axioms checked_dual_coordinate
#assert_axioms checked_normal_coordinate
#assert_axioms checked_primal_coordinate
#assert_axioms checked_point_is_epsilon_feasible
#assert_axioms rustCertQpCheck_quantitative
#assert_axioms approximateFixture_bound

-- POSITIVE CONTROL for the rejector below: the distance bound is proved through
-- `residual_dot_lower_bound`, which its statement never mentions.
#assert_depends_on Market.QpApproximateBound.approximate_kkt_distance_bound
  [Market.QpApproximateBound.residual_dot_lower_bound]

#assert_not_depends_on Market.QpApproximateBound.StationarityResidualAtMost [
  Market.PsdSymm,
  Market.RustQpFeasible,
  Market.RustQpNormalCone]

#assert_all_clean [
  Market.QpApproximateBound.residual_dot_lower_bound,
  Market.QpApproximateBound.approximate_kkt_distance_bound,
  Market.QpApproximateBound.approximate_kkt_radius_bound,
  Market.QpApproximateBound.rustClamp_mem,
  Market.QpApproximateBound.approximate_clamp_normal,
  Market.QpApproximateBound.residual_objective_bound,
  Market.QpApproximateBound.coordinate_le_rustMaxResidual,
  Market.QpApproximateBound.checked_dual_coordinate,
  Market.QpApproximateBound.checked_normal_coordinate,
  Market.QpApproximateBound.checked_primal_coordinate,
  Market.QpApproximateBound.checked_point_is_epsilon_feasible,
  Market.QpApproximateBound.rustCertQpCheck_quantitative,
  Market.QpApproximateBound.approximateFixture_bound]

end Market.QpApproximateBound

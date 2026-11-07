/-
# Market.CertQpRustDenotation — the deployed `CertQp::check` arithmetic, without conflating certificates.

`fhegg-solver/src/qp.rs` checks an OSQP-form problem

    minimize 1/2 xᵀPx + qᵀx     subject to l ≤ Ax ≤ u

by recomputing three infinity residuals from `(x,y)`:

* `maxᵢ ((Ax-u)ᵢ₊ + (l-Ax)ᵢ₊)`;
* `maxⱼ |(Px+q+Aᵀy)ⱼ|`.
* `maxᵢ |(Ax)ᵢ - clamp((Ax)ᵢ+yᵢ,lᵢ,uᵢ)|`, the normal-cone/sign/complementarity check.

It accepts when all three are at most `epsilon`; the stored `objective`, `prim_res`, and `dual_res` fields
are deliberately ignored.  This file mirrors those source expressions over exact rationals for
well-shaped arrays.  It does NOT identify that approximate residual check with `CertifiedQP`, whose
certificate is different: exact stationarity plus explicit lower/upper multipliers and a bounded
complementarity gap.  `rustApprox_accepts_nonexact_stationarity` is the load-bearing counterexample.

The remaining `CertQpRustF64RefinementResidual` is narrow and honest: prove that the deployed `f64`
loops (including IEEE finite/NaN behaviour and array-shape preconditions) refine these exact source
expressions with a stated rounding envelope.  No floating-point theorem is fabricated here.
-/
import Market.CertQp
import Dregg2.Tactics

namespace Market

set_option autoImplicit false

open Matrix

/-! ## 1. Exact-rational denotation of the deployed OSQP checker. -/

/-- A well-shaped OSQP problem, matching `QpProblem` after its flat vectors have passed their length
preconditions. -/
structure RustQpProblem (n mc : Nat) where
  p : Fin n → Fin n → ℚ
  q : Fin n → ℚ
  a : Fin mc → Fin n → ℚ
  l : Fin mc → ℚ
  u : Fin mc → ℚ

/-- Exact `A x`, mirroring `QpProblem::a_times`. -/
def rustATimes {n mc : Nat} (prob : RustQpProblem n mc) (x : Fin n → ℚ) (i : Fin mc) : ℚ :=
  ∑ j, prob.a i j * x j

/-- Exact `P x`, mirroring `QpProblem::p_times`. -/
def rustPTimes {n mc : Nat} (prob : RustQpProblem n mc) (x : Fin n → ℚ) (i : Fin n) : ℚ :=
  ∑ j, prob.p i j * x j

/-- Exact `Aᵀ y`, mirroring `QpProblem::at_times`. -/
def rustATTimes {n mc : Nat} (prob : RustQpProblem n mc) (y : Fin mc → ℚ) (j : Fin n) : ℚ :=
  ∑ i, prob.a i j * y i

theorem rustATimes_eq_mulVec {n mc : Nat} (prob : RustQpProblem n mc) (x : Fin n → ℚ) :
    rustATimes prob x = prob.a *ᵥ x := rfl

theorem rustPTimes_eq_mulVec {n mc : Nat} (prob : RustQpProblem n mc) (x : Fin n → ℚ) :
    rustPTimes prob x = prob.p *ᵥ x := rfl

theorem rustATTimes_eq_vecMul {n mc : Nat} (prob : RustQpProblem n mc) (y : Fin mc → ℚ) :
    rustATTimes prob y = y ᵥ* prob.a := by
  funext j
  simp [rustATTimes, Matrix.vecMul, dotProduct, mul_comm]

/-- Exact rational clamp used by the repaired normal-cone check. -/
def rustClamp (x l u : ℚ) : ℚ := min (max x l) u

/-- Exact convex objective computed by the source problem. -/
def rustQpObjective {n mc : Nat} (prob : RustQpProblem n mc) (x : Fin n → ℚ) : ℚ :=
  (1 / 2) * quadForm prob.p x + prob.q ⬝ᵥ x

/-- Pointwise exact OSQP feasibility. -/
def RustQpFeasible {n mc : Nat} (prob : RustQpProblem n mc) (x : Fin n → ℚ) : Prop :=
  ∀ i, prob.l i ≤ rustATimes prob x i ∧ rustATimes prob x i ≤ prob.u i

/-- Exact source stationarity. -/
def RustQpStationary {n mc : Nat} (prob : RustQpProblem n mc)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) : Prop :=
  ∀ j, rustPTimes prob x j + prob.q j + rustATTimes prob y j = 0

/-- Exact dual normal-cone membership in projection form. -/
def RustQpNormalCone {n mc : Nat} (prob : RustQpProblem n mc)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) : Prop :=
  ∀ i, rustATimes prob x i =
    rustClamp (rustATimes prob x i + y i) (prob.l i) (prob.u i)

/-- Rust's left fold `fold(0.0, f64::max)`, over exact rationals. -/
def rustMaxResidual (xs : List ℚ) : ℚ := xs.foldl max 0

/-- Per-constraint OSQP primal violation `(Ax-u)₊ + (l-Ax)₊`. -/
def rustPrimalViolation {n mc : Nat} (prob : RustQpProblem n mc)
    (x : Fin n → ℚ) (i : Fin mc) : ℚ :=
  max (rustATimes prob x i - prob.u i) 0 + max (prob.l i - rustATimes prob x i) 0

/-- The source-level primal infinity residual. -/
def rustPrimalResidual {n mc : Nat} (prob : RustQpProblem n mc) (x : Fin n → ℚ) : ℚ :=
  rustMaxResidual (List.ofFn fun i => rustPrimalViolation prob x i)

/-- One source-level dual/stationarity residual coordinate. -/
def rustDualViolation {n mc : Nat} (prob : RustQpProblem n mc)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) (j : Fin n) : ℚ :=
  |rustPTimes prob x j + prob.q j + rustATTimes prob y j|

/-- The source-level dual infinity residual. -/
def rustDualResidual {n mc : Nat} (prob : RustQpProblem n mc)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) : ℚ :=
  rustMaxResidual (List.ofFn fun j => rustDualViolation prob x y j)

/-- The scalar normal-cone inequality behind the repaired check.  If `z` is feasible and fixed by
projection of `z+y`, then the dual has the correct sign/complementarity against every other feasible
`z'`. -/
theorem rustClamp_fixed_normal {l z u y z' : ℚ}
    (hlz : l ≤ z) (hzu : z ≤ u) (hlz' : l ≤ z') (hz'u : z' ≤ u)
    (hfix : z = rustClamp (z + y) l u) : y * (z' - z) ≤ 0 := by
  by_cases hlow : z + y ≤ l
  · have hmax : max (z + y) l = l := max_eq_right hlow
    have hmin : min l u = l := min_eq_left (hlz.trans hzu)
    have hz : z = l := by simpa [rustClamp, hmax, hmin] using hfix
    rw [hz] at hlow ⊢
    nlinarith
  · have hlower : l ≤ z + y := le_of_lt (lt_of_not_ge hlow)
    by_cases hupp : u ≤ z + y
    · have hmax : max (z + y) l = z + y := max_eq_left hlower
      have hmin : min (z + y) u = u := min_eq_right hupp
      have hz : z = u := by simpa [rustClamp, hmax, hmin] using hfix
      rw [hz] at hupp ⊢
      nlinarith
    · have hupper : z + y ≤ u := le_of_lt (lt_of_not_ge hupp)
      have hmax : max (z + y) l = z + y := max_eq_left hlower
      have hmin : min (z + y) u = z + y := min_eq_left hupper
      have hy : y = 0 := by
        have := hfix
        simp [rustClamp, hmax, hmin] at this
        linarith
      simp [hy]

/-- **Exact repaired CertQp soundness.**  For a symmetric PSD objective, exact primal feasibility,
stationarity, and the repaired normal-cone condition imply global optimality over the OSQP feasible
set.  This is the theorem the old two-residual checker could not support.  Positive-tolerance and
floating-point error remain the explicitly named residual below. -/
theorem rustExactKkt_optimal {n mc : Nat} (prob : RustQpProblem n mc)
    (hP : PsdSymm prob.p) {x : Fin n → ℚ} {y : Fin mc → ℚ}
    (hfeas : RustQpFeasible prob x)
    (hstat : RustQpStationary prob x y)
    (hnormal : RustQpNormalCone prob x y)
    {x' : Fin n → ℚ} (hfeas' : RustQpFeasible prob x') :
    rustQpObjective prob x ≤ rustQpObjective prob x' := by
  have hnormalPoint : ∀ i, y i * (rustATimes prob x' i - rustATimes prob x i) ≤ 0 := by
    intro i
    exact rustClamp_fixed_normal (hfeas i).1 (hfeas i).2 (hfeas' i).1 (hfeas' i).2
      (hnormal i)
  have hnormalSum :
      y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x)) ≤ 0 := by
    rw [dotProduct]
    apply Finset.sum_nonpos
    intro i _hi
    simpa [rustATimes_eq_mulVec] using hnormalPoint i
  have hstatFun : prob.p *ᵥ x + prob.q = -(y ᵥ* prob.a) := by
    funext j
    have hj := hstat j
    rw [← rustPTimes_eq_mulVec, ← rustATTimes_eq_vecMul]
    simp only [Pi.add_apply, Pi.neg_apply]
    linarith
  have hgrad :
      (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) =
        -(y ⬝ᵥ ((prob.a *ᵥ x') - (prob.a *ᵥ x))) := by
    rw [hstatFun, neg_dotProduct, neg_inj]
    exact (dotProduct_mulVec y prob.a (x' - x)).symm.trans
      (congrArg (y ⬝ᵥ ·) (mulVec_sub prob.a x' x))
  let core : QP (Fin n) (Fin 0) :=
    { P := prob.p
      q := prob.q
      A := fun i => i.elim0
      b := fun i => i.elim0
      l := fun _ => 0
      u := fun _ => 0
      ε := 0 }
  have hconv := quad_convex_ge (qp := core) hP x x'
  change (prob.p *ᵥ x + prob.q) ⬝ᵥ (x' - x) ≤
    rustQpObjective prob x' - rustQpObjective prob x at hconv
  rw [hgrad] at hconv
  linarith

/-- `y ∈ N_[l,u](z)` iff `z = projection_[l,u](z+y)`.  This one residual enforces the
lower-bound sign, upper-bound sign, and interior complementarity conditions while leaving equality-row
duals free. -/
def rustNormalViolation {n mc : Nat} (prob : RustQpProblem n mc)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) (i : Fin mc) : ℚ :=
  |rustATimes prob x i - rustClamp (rustATimes prob x i + y i) (prob.l i) (prob.u i)|

/-- The repaired source-level normal-cone infinity residual. -/
def rustNormalResidual {n mc : Nat} (prob : RustQpProblem n mc)
    (x : Fin n → ℚ) (y : Fin mc → ℚ) : ℚ :=
  rustMaxResidual (List.ofFn fun i => rustNormalViolation prob x y i)

/-- The fields consumed by `CertQp::check`.  The three stored report fields are included so their
non-use can be stated as a theorem rather than prose. -/
structure RustCertQp (n mc : Nat) where
  prob : RustQpProblem n mc
  x : Fin n → ℚ
  y : Fin mc → ℚ
  epsilon : ℚ
  storedObjective : ℚ
  storedPrimRes : ℚ
  storedDualRes : ℚ

/-- Exact-arithmetic denotation of `CertQp::check().valid`. -/
def rustCertQpCheck {n mc : Nat} (c : RustCertQp n mc) : Bool :=
  decide (rustPrimalResidual c.prob c.x ≤ c.epsilon) &&
    decide (rustDualResidual c.prob c.x c.y ≤ c.epsilon) &&
    decide (rustNormalResidual c.prob c.x c.y ≤ c.epsilon)

/-- The checker accepts exactly when all three recomputed residuals meet `epsilon`. -/
theorem rustCertQpCheck_iff {n mc : Nat} (c : RustCertQp n mc) :
    rustCertQpCheck c = true ↔
      rustPrimalResidual c.prob c.x ≤ c.epsilon ∧
      rustDualResidual c.prob c.x c.y ≤ c.epsilon ∧
      rustNormalResidual c.prob c.x c.y ≤ c.epsilon := by
  simp [rustCertQpCheck, and_assoc]

/-- Stored objective/residual claims are not trusted by the checker; only `(problem,x,y,epsilon)` is
recomputed. -/
theorem rustCertQpCheck_ignores_stored_reports {n mc : Nat} (c : RustCertQp n mc)
    (objective prim dual : ℚ) :
    rustCertQpCheck
      { c with storedObjective := objective, storedPrimRes := prim, storedDualRes := dual } =
    rustCertQpCheck c := rfl

/-! ## 2. Non-vacuity and the certificate-mismatch tooth. -/

/-- One-dimensional source problem `min 1/2 x²-x`, with the box represented in OSQP form as
`0 ≤ x ≤ 2`. -/
def rustQpOne : RustQpProblem 1 1 where
  p := fun _ _ => 1
  q := fun _ => -1
  a := fun _ _ => 1
  l := fun _ => 0
  u := fun _ => 2

/-- At `x=0,y=0,epsilon=1`, primal residual is zero and stationarity residual is one. -/
def rustApproxWitness : RustCertQp 1 1 where
  prob := rustQpOne
  x := fun _ => 0
  y := fun _ => 0
  epsilon := 1
  storedObjective := 999
  storedPrimRes := 999
  storedDualRes := 999

theorem rustApprox_primal_zero : rustPrimalResidual rustQpOne rustApproxWitness.x = 0 := by
  norm_num [rustPrimalResidual, rustPrimalViolation, rustATimes, rustMaxResidual,
    rustQpOne, rustApproxWitness]

theorem rustApprox_dual_one : rustDualResidual rustQpOne rustApproxWitness.x rustApproxWitness.y = 1 := by
  norm_num [rustDualResidual, rustDualViolation, rustPTimes, rustATTimes, rustMaxResidual,
    rustQpOne, rustApproxWitness]

theorem rustApprox_normal_zero :
    rustNormalResidual rustQpOne rustApproxWitness.x rustApproxWitness.y = 0 := by
  norm_num [rustNormalResidual, rustNormalViolation, rustATimes, rustClamp, rustMaxResidual,
    rustQpOne, rustApproxWitness]

/-- **Mismatch tooth.** The deployed residual rule accepts a genuinely nonzero stationarity residual
at positive tolerance.  Therefore its valid bit is not the exact `CertifiedQP` premise. -/
theorem rustApprox_accepts_nonexact_stationarity :
    rustCertQpCheck rustApproxWitness = true ∧
    rustPTimes rustQpOne rustApproxWitness.x 0 + rustQpOne.q 0 +
      rustATTimes rustQpOne rustApproxWitness.y 0 ≠ 0 := by
  constructor
  · apply (rustCertQpCheck_iff rustApproxWitness).2
    constructor
    · change rustPrimalResidual rustQpOne rustApproxWitness.x ≤ 1
      rw [rustApprox_primal_zero]
      norm_num
    · constructor
      · change rustDualResidual rustQpOne rustApproxWitness.x rustApproxWitness.y ≤ 1
        rw [rustApprox_dual_one]
      · change rustNormalResidual rustQpOne rustApproxWitness.x rustApproxWitness.y ≤ 1
        rw [rustApprox_normal_zero]
        norm_num
  · norm_num [rustPTimes, rustATTimes, rustQpOne, rustApproxWitness]

/-- The exact forgery accepted by the old deployed checker: at the suboptimal lower bound `x=0`, the
wrong-sign dual `y=+1` cancels the gradient, so primal and stationarity residuals are both zero. -/
def rustForgedDualWitness : RustCertQp 1 1 :=
  { rustApproxWitness with y := fun _ => 1, epsilon := 0 }

/-- A zero-tolerance, exact-KKT optimum; the repaired checker remains non-vacuously accepting. -/
def rustExactWitness : RustCertQp 1 1 :=
  { rustApproxWitness with x := fun _ => 1, epsilon := 0 }

theorem rustForgedDual_primal_zero :
    rustPrimalResidual rustQpOne rustForgedDualWitness.x = 0 := by
  norm_num [rustPrimalResidual, rustPrimalViolation, rustATimes, rustMaxResidual,
    rustQpOne, rustForgedDualWitness, rustApproxWitness]

theorem rustForgedDual_stationarity_zero :
    rustDualResidual rustQpOne rustForgedDualWitness.x rustForgedDualWitness.y = 0 := by
  norm_num [rustDualResidual, rustDualViolation, rustPTimes, rustATTimes, rustMaxResidual,
    rustQpOne, rustForgedDualWitness, rustApproxWitness]

theorem rustForgedDual_normal_one :
    rustNormalResidual rustQpOne rustForgedDualWitness.x rustForgedDualWitness.y = 1 := by
  norm_num [rustNormalResidual, rustNormalViolation, rustATimes, rustClamp, rustMaxResidual,
    rustQpOne, rustForgedDualWitness, rustApproxWitness]

/-- **Deployed repair tooth.** The added normal-cone check rejects the exact-residual, wrong-sign dual
forgery that the old two-residual checker accepted. -/
theorem rustForgedDual_rejected : rustCertQpCheck rustForgedDualWitness = false := by
  apply Bool.eq_false_iff.mpr
  intro hacc
  have hnormal := (rustCertQpCheck_iff rustForgedDualWitness).mp hacc |>.2.2
  change rustNormalResidual rustQpOne rustForgedDualWitness.x rustForgedDualWitness.y ≤ 0 at hnormal
  rw [rustForgedDual_normal_one] at hnormal
  norm_num at hnormal

#guard rustCertQpCheck rustApproxWitness
#guard rustPrimalResidual rustQpOne rustApproxWitness.x == 0
#guard rustDualResidual rustQpOne rustApproxWitness.x rustApproxWitness.y == 1
#guard rustNormalResidual rustQpOne rustForgedDualWitness.x rustForgedDualWitness.y == 1
#guard !rustCertQpCheck rustForgedDualWitness
#guard rustCertQpCheck rustExactWitness

/-! ## 3. Exact remaining deployed obligation. -/

/-- The shape of the remaining bit-level theorem.  `Raw` must be instantiated by a real IEEE-754
certificate carrier, `decodeFinite` by a shape-checking finite-value decoder with its stated rounding
envelope, and `runF64Check` by the deployed checker semantics.  Only then does the equality say that
Rust acceptance agrees with the exact residual model; no placeholder execution is installed here. -/
def CertQpRustF64Refines {n mc : Nat} {Raw : Type}
    (decodeFinite : Raw → Option (RustCertQp n mc))
    (runF64Check : Raw → Bool) : Prop :=
  ∀ raw c, decodeFinite raw = some c → runF64Check raw = rustCertQpCheck c

/-- Named residual: instantiate the raw IEEE carrier/decoder/execution relation above for deployed
`fhegg_solver::qp::CertQp`. -/
abbrev CertQpRustF64RefinementResidual := @CertQpRustF64Refines

#assert_axioms rustCertQpCheck_iff
#assert_axioms rustCertQpCheck_ignores_stored_reports
#assert_axioms rustATimes_eq_mulVec
#assert_axioms rustPTimes_eq_mulVec
#assert_axioms rustATTimes_eq_vecMul
#assert_axioms rustClamp_fixed_normal
#assert_axioms rustExactKkt_optimal
#assert_axioms rustApprox_primal_zero
#assert_axioms rustApprox_dual_one
#assert_axioms rustApprox_normal_zero
#assert_axioms rustApprox_accepts_nonexact_stationarity
#assert_axioms rustForgedDual_primal_zero
#assert_axioms rustForgedDual_stationarity_zero
#assert_axioms rustForgedDual_normal_one
#assert_axioms rustForgedDual_rejected

end Market

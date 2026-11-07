/-
# Certified finite-field projection of Gabbay matrix residuals

`GabbayMatrixSemantics` deliberately evaluates the original construction in
`ℚ`, where squared atomic residuals are nonnegative and addition therefore has
its intended conjunction/universal meaning.  This file supplies the safe field
boundary:

1. evaluate the bounded matrix formula exactly in `ℚ`;
2. expose its reduced integer numerator and positive denominator;
3. require a prime larger than both the numerator magnitude and denominator;
4. only then project into `ZMod p`.

The resulting field zero test is equivalent to ordinary formula satisfaction.
The numerator bound is load-bearing: without it, a nonzero rational residual
whose numerator is divisible by `p` becomes zero in the field.  The final
section gives an executable five-adic counterexample and proves that the
certificate rejects it.

This module does not claim that the bound is inexpensive.  `ProjectionCost`
exports the exact formula degree, normalized denominator, numerator magnitude,
and least strict modulus floor so a compiler and benchmark must account for
them rather than hide them in prose.
-/
import Dregg2.Metatheory.GabbayMatrixSemantics
import Mathlib.Algebra.Field.ZMod
import Mathlib.Data.ZMod.Basic
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.NormNum.Prime

namespace Dregg2.Metatheory.GabbayFiniteFieldProjection

open scoped BigOperators
open GabbayMatrixSemantics

noncomputable section

/-! ## 1. Exact denominator clearing -/

/-- Reduced integer numerator of an exactly evaluated matrix formula. -/
def clearedNumerator {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (formula : Formula S) : Int :=
  (residual rho x formula).num

/-- Positive normalized denominator of the same exact residual. -/
def clearedDenominator {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (formula : Formula S) : Nat :=
  (residual rho x formula).den

/-- Clearing is exact: the exported numerator divided by the exported positive
denominator reconstructs the rational residual. -/
theorem cleared_value_exact {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (formula : Formula S) :
    (clearedNumerator rho x formula : Rat) /
        (clearedDenominator rho x formula : Rat) = residual rho x formula := by
  exact Rat.num_div_den _

/-- The emitted denominator can never be zero. -/
theorem clearedDenominator_pos {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (formula : Formula S) :
    0 < clearedDenominator rho x formula :=
  (residual rho x formula).den_pos

/-- The cleared integer numerator is zero exactly when the source formula
holds.  This already separates logical correctness from any field choice. -/
theorem clearedNumerator_eq_zero_iff_holds {S : MatrixSignature}
    (rho : Valuation S) (x : Rat) (formula : Formula S) :
    clearedNumerator rho x formula = 0 <-> Holds rho x formula := by
  rw [clearedNumerator, Rat.num_eq_zero]
  exact residual_eq_zero_iff_holds rho formula x

/-! ## 2. Prime/no-wrap certificates and field projection -/

/-- A checkable projection certificate.  Both bounds are strict, so neither a
nonzero numerator nor the positive denominator can wrap to zero modulo `p`.
`prime` additionally makes `ZMod p` a field for the rational projection. -/
structure ProjectionCertificate (q : Rat) (p : Nat) : Prop where
  prime : Nat.Prime p
  numeratorNoWrap : q.num.natAbs < p
  denominatorNoWrap : q.den < p

/-- The least convenient modulus floor emitted by this compiler: a modulus at
least this value is strictly larger than both normalized components. -/
def modulusFloor (q : Rat) : Nat := max q.num.natAbs q.den + 1

theorem numerator_lt_modulusFloor (q : Rat) : q.num.natAbs < modulusFloor q := by
  simp [modulusFloor]

theorem denominator_lt_modulusFloor (q : Rat) : q.den < modulusFloor q := by
  simp [modulusFloor]

/-- Any prime at or above the emitted floor yields a projection certificate. -/
theorem certificate_of_prime_ge (q : Rat) {p : Nat} (hp : Nat.Prime p)
    (hfloor : modulusFloor q <= p) : ProjectionCertificate q p := by
  refine ⟨hp, ?_, ?_⟩
  · exact (numerator_lt_modulusFloor q).trans_le hfloor
  · exact (denominator_lt_modulusFloor q).trans_le hfloor

/-- Projection after clearing denominators: only the exact integer numerator
is sent to the field. -/
def projectCleared (q : Rat) (p : Nat) : ZMod p := q.num

/-- A bounded integer cannot become zero modulo a larger modulus unless it was
already zero. -/
theorem projectCleared_eq_zero_iff (q : Rat) {p : Nat}
    (cert : ProjectionCertificate q p) :
    projectCleared q p = 0 <-> q = 0 := by
  constructor
  · intro hzero
    have hdiv : (p : Int) ∣ q.num :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd q.num p).1 hzero
    have habs : q.num.natAbs < (p : Int).natAbs := by
      simpa using cert.numeratorNoWrap
    have hnum : q.num = 0 :=
      Int.eq_zero_of_dvd_of_natAbs_lt_natAbs hdiv habs
    exact Rat.num_eq_zero.mp hnum
  · intro hq
    simp [projectCleared, hq]

/-- Direct rational projection, now legitimate because the certificate gives a
prime field and proves that the denominator does not vanish in it. -/
def projectRational (q : Rat) {p : Nat} (cert : ProjectionCertificate q p) : ZMod p := by
  letI : Fact (Nat.Prime p) := ⟨cert.prime⟩
  letI : Field (ZMod p) := inferInstance
  exact (q.num : ZMod p) / (q.den : ZMod p)

/-- The certificate's denominator bound implies a nonzero field denominator. -/
theorem denominator_cast_ne_zero (q : Rat) {p : Nat}
    (cert : ProjectionCertificate q p) :
    (q.den : ZMod p) ≠ 0 := by
  intro hzero
  have hdiv : p ∣ q.den := (ZMod.natCast_eq_zero_iff q.den p).1 hzero
  exact Nat.not_dvd_of_pos_of_lt q.den_pos cert.denominatorNoWrap hdiv

/-- The direct numerator/denominator field value is zero exactly when the
source rational is zero. -/
theorem projectRational_eq_zero_iff (q : Rat) {p : Nat}
    (cert : ProjectionCertificate q p) :
    projectRational q cert = 0 <-> q = 0 := by
  letI : Fact (Nat.Prime p) := ⟨cert.prime⟩
  letI : Field (ZMod p) := inferInstance
  have hden : (q.den : ZMod p) ≠ 0 := denominator_cast_ne_zero q cert
  rw [projectRational, div_eq_zero_iff, or_iff_left hden]
  exact projectCleared_eq_zero_iff q cert

/-! ## 3. Formula-level compiler theorem -/

/-- The certificate required for one evaluated matrix formula. -/
abbrev FormulaProjectionCertificate {S : MatrixSignature} (rho : Valuation S)
    (x : Rat) (formula : Formula S) (p : Nat) : Prop :=
  ProjectionCertificate (residual rho x formula) p

/-- **Certified finite-field compiler theorem (cleared representation).** -/
theorem projected_formula_zero_iff_holds {S : MatrixSignature}
    (rho : Valuation S) (x : Rat) (formula : Formula S) {p : Nat}
    (cert : FormulaProjectionCertificate rho x formula p) :
    projectCleared (residual rho x formula) p = 0 <-> Holds rho x formula := by
  rw [projectCleared_eq_zero_iff _ cert]
  exact residual_eq_zero_iff_holds rho formula x

/-- The same compiler theorem for direct numerator/denominator projection. -/
theorem projected_rational_formula_zero_iff_holds {S : MatrixSignature}
    (rho : Valuation S) (x : Rat) (formula : Formula S) {p : Nat}
    (cert : FormulaProjectionCertificate rho x formula p) :
    projectRational (residual rho x formula) cert = 0 <-> Holds rho x formula := by
  rw [projectRational_eq_zero_iff _ cert]
  exact residual_eq_zero_iff_holds rho formula x

/-! ## 4. Exact compiler cost record -/

/-- Exact certificate-generation statistics.  These are deliberately a vector,
not a context-free scalar "speedup": polynomial degree, numerator magnitude,
and denominator growth stress different proof backends. -/
structure ProjectionCost where
  formulaDegree : WithBot Nat
  numeratorMagnitude : Nat
  normalizedDenominator : Nat
  requiredModulusFloor : Nat
  deriving DecidableEq, Repr

def projectionCost {S : MatrixSignature} (rho : Valuation S) (x : Rat)
    (formula : Formula S) : ProjectionCost where
  formulaDegree := (denoteFormula rho formula).degree
  numeratorMagnitude := (residual rho x formula).num.natAbs
  normalizedDenominator := (residual rho x formula).den
  requiredModulusFloor := modulusFloor (residual rho x formula)

@[simp] theorem projectionCost_degree {S : MatrixSignature} (rho : Valuation S)
    (x : Rat) (formula : Formula S) :
    (projectionCost rho x formula).formulaDegree =
      (denoteFormula rho formula).degree := rfl

@[simp] theorem projectionCost_numerator {S : MatrixSignature} (rho : Valuation S)
    (x : Rat) (formula : Formula S) :
    (projectionCost rho x formula).numeratorMagnitude =
      (residual rho x formula).num.natAbs := rfl

@[simp] theorem projectionCost_denominator {S : MatrixSignature} (rho : Valuation S)
    (x : Rat) (formula : Formula S) :
    (projectionCost rho x formula).normalizedDenominator =
      (residual rho x formula).den := rfl

@[simp] theorem projectionCost_modulusFloor {S : MatrixSignature} (rho : Valuation S)
    (x : Rat) (formula : Formula S) :
    (projectionCost rho x formula).requiredModulusFloor =
      max (projectionCost rho x formula).numeratorMagnitude
        (projectionCost rho x formula).normalizedDenominator + 1 := rfl

/-- A prime meeting the emitted cost floor certifies the formula projection. -/
theorem formulaCertificate_of_cost_floor {S : MatrixSignature}
    (rho : Valuation S) (x : Rat) (formula : Formula S) {p : Nat}
    (hp : Nat.Prime p)
    (hfloor : (projectionCost rho x formula).requiredModulusFloor <= p) :
    FormulaProjectionCertificate rho x formula p := by
  exact certificate_of_prime_ge _ hp hfloor

/-- Bounded quantifiers retain the exact constant-polynomial degree fact from
the rational construction; field projection does not make it disappear. -/
theorem boundedForall_projection_degree_le_zero {S : MatrixSignature}
    (rho : Valuation S) (C : S.Symbol) (body : Formula S) (x : Rat) :
    (projectionCost rho x (.forallIn C body)).formulaDegree <= 0 := by
  exact forall_degree_le_zero rho C body

/-! ## 5. Concrete good and bad primes -/

/-- The closed successor-table formula from the matrix module, evaluated once
before projection. -/
def successorResidual : Rat :=
  residual successorValuation 0 successorSkolemFormula

@[simp] theorem successorResidual_eq_zero : successorResidual = 0 := by
  exact successorTable_compiles_to_zero 0

set_option maxRecDepth 8192 in
/-- BabyBear, the STARK field used elsewhere in dregg, is prime. -/
theorem babyBear_prime : Nat.Prime 2013265921 := by
  norm_num

/-- The exact zero successor residual has a valid BabyBear projection
certificate. -/
def successorBabyBearCertificate :
    ProjectionCertificate successorResidual 2013265921 := by
  rw [successorResidual_eq_zero]
  exact certificate_of_prime_ge 0 babyBear_prime (by norm_num [modulusFloor])

/-- The concrete Skolem/function-table witness accepts in BabyBear for the
right reason: the certified rational residual was already zero. -/
theorem successor_projects_to_BabyBear_zero :
    projectRational successorResidual successorBabyBearCertificate = 0 := by
  exact (projectRational_eq_zero_iff successorResidual
    successorBabyBearCertificate).2 successorResidual_eq_zero

/-- A false equality whose exact rational residual is `25`. -/
def badPrimeFormula : Formula skolemSignature :=
  .eq (.rational 0) (.rational 5)

theorem badPrimeFormula_not_holds :
    ¬ Holds successorValuation 0 badPrimeFormula := by
  norm_num [badPrimeFormula, Holds, evalTerm, denoteTerm]

theorem badPrimeResidual_eq :
    residual successorValuation 0 badPrimeFormula = 25 := by
  norm_num [badPrimeFormula, residual, denoteFormula, denoteTerm]

/-- **Unchecked bad-prime counterexample.**  The nonzero residual `25` becomes
zero modulo the prime `5`, so an unbounded projection accepts a false formula. -/
theorem badPrime_unchecked_accepts :
    projectCleared (residual successorValuation 0 badPrimeFormula) 5 = 0 := by
  rw [badPrimeResidual_eq]
  decide

/-- The compiler refuses that projection: the required strict numerator bound
`25 < 5` is impossible. -/
theorem badPrime_certificate_rejected :
    ¬ FormulaProjectionCertificate successorValuation 0 badPrimeFormula 5 := by
  intro cert
  change ProjectionCertificate
    (residual successorValuation 0 badPrimeFormula) 5 at cert
  rw [badPrimeResidual_eq] at cert
  have h := cert.numeratorNoWrap
  norm_num at h

#assert_all_clean [cleared_value_exact, clearedDenominator_pos,
  clearedNumerator_eq_zero_iff_holds, numerator_lt_modulusFloor,
  denominator_lt_modulusFloor, certificate_of_prime_ge,
  projectCleared_eq_zero_iff, denominator_cast_ne_zero,
  projectRational_eq_zero_iff, projected_formula_zero_iff_holds,
  projected_rational_formula_zero_iff_holds, projectionCost_degree,
  projectionCost_numerator, projectionCost_denominator,
  projectionCost_modulusFloor, formulaCertificate_of_cost_floor,
  boundedForall_projection_degree_le_zero, successorResidual_eq_zero,
  babyBear_prime, successor_projects_to_BabyBear_zero,
  badPrimeFormula_not_holds, badPrimeResidual_eq,
  badPrime_unchecked_accepts, badPrime_certificate_rejected]

end

end Dregg2.Metatheory.GabbayFiniteFieldProjection

/-
# Dregg2.Logic.CertifiedHybridProofFheZeroObservation

The corrected residual presentation has one boundary operation that ordinary
BFV arithmetic does not make free: converting an encrypted field element `r`
whose truth convention is `r = 0` into a canonical encrypted Boolean bit.

This module closes that accounting gap in two complementary ways.

* It proves that an exact zero indicator on the *whole* plaintext field,
  implemented only by additions, subtractions, constants, and ciphertext
  multiplications, has multiplicative depth at least 20.  The familiar Fermat
  indicator `1 - r^(p-1)` is exact but has degree `p-1 = 1,032,192`.
* It then uses the no-wrap certificate rather than ignoring it: on the finite
  interval `0..B`, the normalized product `product_(i=1..B) (i-r) / B!` is an
  exact encrypted zero bit with only `B-1` ciphertext multiplications in a
  balanced tree.  Its unnormalized form is the scaled bit `B!`/`0`; the Rust
  carrier executes that form because multiplying by the large field inverse
  of `B!` exhausted the deployed noise envelope in oracle tests.  For the
  five-equality demo, the missing conversion costs
  three multiplications, changing the advertised `6 < 9` inner ledger into
  `9 = 9` before any output opening.
* It gives an explicit n-of-n threshold-opening receipt model.  This boundary
  executes one decryption share per party and one combine per residual
  ciphertext.  It reveals the complete residual in every live SIMD slot, not
  merely the zero bit.  If the result is used by a parent encrypted Boolean
  region, one ciphertext re-encryption is also required and the internal
  subformula truth has become public to the opening coordinator.

The receipt is attached to the existing hybrid certificate, so its source,
raw opening, conversion witness, plan, and exact symbolic computation cost are
the same objects already covered by `bound_proof_iff_fhe_plan`.  A comparison
is called end-to-end only when setup, input encryption, same-opening checking,
encrypted evaluation, every required zero observation, and output observation
are all recorded as executed.  Consequently the symbolic demo's `6 < 9`
multiplication fact is deliberately *not* an end-to-end performance result.

Pure.  No axioms.
-/

import Dregg2.Logic.CertifiedHybridProofFheBoundOpening
import Dregg2.Tactics
import Mathlib.Algebra.Polynomial.Roots
import Mathlib.Algebra.BigOperators.GroupWithZero.Finset
import Mathlib.Data.Nat.Factorial.BigOperators
import Mathlib.Data.Nat.Prime.Factorial
import Mathlib.FieldTheory.Finite.Basic

namespace Dregg2.Logic.CertifiedHybridProofFheZeroObservation

set_option autoImplicit false

open Polynomial
open Dregg2.Logic.FheLogicBfvModel
open Dregg2.Logic.CertifiedHybridProofFhe

/-! ## 1. Exact polynomial zero tests are necessarily deep -/

/-- The exact zero-indicator polynomial over the deployed BFV plaintext
field.  This is implementable by repeated ciphertext multiplication, but the
degree lower bound below shows why that is not a cheap boundary operation. -/
def fermatZero (x : ZMod bfvPlaintextModulus) : ZMod bfvPlaintextModulus :=
  1 - x ^ (bfvPlaintextModulus - 1)

theorem fermatZero_eq_one_iff (x : ZMod bfvPlaintextModulus) :
    fermatZero x = 1 <-> x = 0 := by
  constructor
  · intro h
    by_contra hx
    have hpow := ZMod.pow_card_sub_one_eq_one hx
    simp [fermatZero, hpow] at h
  · rintro rfl
    norm_num [fermatZero, bfvPlaintextModulus]

/-- A polynomial that is one at zero and zero at every nonzero field element
has at least `|F|-1` degree.  This is the carrier-level obstruction: no
  low-degree exact zero observation exists without using a smaller certified
  input domain.  The next section does use that smaller domain. -/
theorem zeroIndicator_natDegree_lower_bound
    {F : Type*} [Field F] [Fintype F] [DecidableEq F]
    (poly : F[X])
    (atZero : poly.eval 0 = 1)
    (awayFromZero : forall x : F, x ≠ 0 -> poly.eval x = 0) :
    Fintype.card F - 1 ≤ poly.natDegree := by
  have hpoly : poly ≠ 0 := by
    intro hzero
    rw [hzero, eval_zero] at atZero
    exact zero_ne_one atZero
  let nonzero : Finset F := Finset.univ.erase 0
  have hsubset : nonzero.val ⊆ poly.roots := by
    intro x hx
    have hxmem : x ∈ nonzero := hx
    have hxne : x ≠ 0 := (Finset.mem_erase.mp hxmem).1
    exact (mem_roots hpoly).2 (awayFromZero x hxne)
  have hcard := Polynomial.card_le_degree_of_subset_roots hsubset
  change nonzero.card ≤ poly.natDegree at hcard
  simpa [nonzero] using hcard

/-- The polynomial computed by the arithmetic available in the current BFV
carrier.  Rotations and SIMD packing do not change the per-slot polynomial
degree, so they are intentionally absent from this scalar obstruction. -/
inductive CarrierExpr where
  | constant (value : ZMod bfvPlaintextModulus)
  | input
  | add (left right : CarrierExpr)
  | sub (left right : CarrierExpr)
  | mul (left right : CarrierExpr)
  deriving DecidableEq

noncomputable def CarrierExpr.poly : CarrierExpr -> (ZMod bfvPlaintextModulus)[X]
  | .constant value => C value
  | .input => X
  | .add left right => left.poly + right.poly
  | .sub left right => left.poly - right.poly
  | .mul left right => left.poly * right.poly

def CarrierExpr.eval : CarrierExpr -> ZMod bfvPlaintextModulus ->
    ZMod bfvPlaintextModulus
  | .constant value, _ => value
  | .input, x => x
  | .add left right, x => left.eval x + right.eval x
  | .sub left right, x => left.eval x - right.eval x
  | .mul left right, x => left.eval x * right.eval x

def CarrierExpr.mulDepth : CarrierExpr -> Nat
  | .constant _ => 0
  | .input => 0
  | .add left right => max left.mulDepth right.mulDepth
  | .sub left right => max left.mulDepth right.mulDepth
  | .mul left right => max left.mulDepth right.mulDepth + 1

theorem CarrierExpr.eval_poly (expr : CarrierExpr)
    (x : ZMod bfvPlaintextModulus) : expr.poly.eval x = expr.eval x := by
  induction expr <;> simp [CarrierExpr.poly, CarrierExpr.eval, *]

theorem CarrierExpr.natDegree_le_pow_depth (expr : CarrierExpr) :
    expr.poly.natDegree ≤ 2 ^ expr.mulDepth := by
  induction expr with
  | constant value => simp [CarrierExpr.poly, CarrierExpr.mulDepth]
  | input => simp [CarrierExpr.poly, CarrierExpr.mulDepth]
  | add left right ihLeft ihRight =>
      simp only [CarrierExpr.poly, CarrierExpr.mulDepth]
      calc
        (left.poly + right.poly).natDegree
            ≤ max left.poly.natDegree right.poly.natDegree := natDegree_add_le _ _
        _ ≤ max (2 ^ left.mulDepth) (2 ^ right.mulDepth) :=
          max_le_max ihLeft ihRight
        _ ≤ 2 ^ max left.mulDepth right.mulDepth := by
          exact max_le
            (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
            (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  | sub left right ihLeft ihRight =>
      simp only [CarrierExpr.poly, CarrierExpr.mulDepth]
      calc
        (left.poly - right.poly).natDegree
            ≤ max left.poly.natDegree right.poly.natDegree := natDegree_sub_le _ _
        _ ≤ max (2 ^ left.mulDepth) (2 ^ right.mulDepth) :=
          max_le_max ihLeft ihRight
        _ ≤ 2 ^ max left.mulDepth right.mulDepth := by
          exact max_le
            (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
            (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
  | mul left right ihLeft ihRight =>
      simp only [CarrierExpr.poly, CarrierExpr.mulDepth]
      calc
        (left.poly * right.poly).natDegree
            ≤ left.poly.natDegree + right.poly.natDegree := natDegree_mul_le
        _ ≤ 2 ^ left.mulDepth + 2 ^ right.mulDepth := Nat.add_le_add ihLeft ihRight
        _ ≤ 2 ^ max left.mulDepth right.mulDepth +
              2 ^ max left.mulDepth right.mulDepth := by
          exact Nat.add_le_add
            (Nat.pow_le_pow_right (by decide) (Nat.le_max_left _ _))
            (Nat.pow_le_pow_right (by decide) (Nat.le_max_right _ _))
        _ = 2 ^ (max left.mulDepth right.mulDepth + 1) := by
          rw [pow_succ]
          omega

/-- Any exact zero test in the deployed arithmetic carrier needs at least 20
sequential ciphertext-multiplication layers.  This is a lower bound, not a BFV
noise theorem; the current depth-one/depth-four measurements cannot be
extrapolated across this boundary. -/
theorem deployed_exact_zero_test_depth_at_least_twenty
    (expr : CarrierExpr)
    (atZero : expr.eval 0 = 1)
    (awayFromZero : forall x : ZMod bfvPlaintextModulus,
      x ≠ 0 -> expr.eval x = 0) :
    20 ≤ expr.mulDepth := by
  have hdegree : bfvPlaintextModulus - 1 ≤ expr.poly.natDegree := by
    have := zeroIndicator_natDegree_lower_bound expr.poly
      (by simpa [CarrierExpr.eval_poly] using atZero)
      (by
        intro x hx
        simpa [CarrierExpr.eval_poly] using awayFromZero x hx)
    rwa [ZMod.card] at this
  have hupper := expr.natDegree_le_pow_depth
  by_contra hnot
  have hdepth : expr.mulDepth ≤ 19 := by omega
  have hpow : 2 ^ expr.mulDepth ≤ 2 ^ 19 :=
    Nat.pow_le_pow_right (by decide) hdepth
  norm_num [bfvPlaintextModulus] at hdegree
  norm_num at hpow
  omega

/-! ## 2. The no-wrap range enables an exact bounded encrypted zero test -/

/-- Exact zero indicator on the certified integer interval `0..bound`.
The normalization is valid whenever `bound < p`, because then `p` does not
divide `bound!`. -/
noncomputable def boundedZeroValue (bound : Nat)
    (x : ZMod bfvPlaintextModulus) : ZMod bfvPlaintextModulus :=
  (∏ i ∈ Finset.range bound,
      (((i + 1 : Nat) : ZMod bfvPlaintextModulus) - x)) *
    ((bound.factorial : ZMod bfvPlaintextModulus)⁻¹)

/-- The executable carrier form before normalization: `bound!` means true
and zero means false on the certified interval. -/
noncomputable def boundedZeroScaled (bound : Nat)
    (x : ZMod bfvPlaintextModulus) : ZMod bfvPlaintextModulus :=
  ∏ i ∈ Finset.range bound,
    (((i + 1 : Nat) : ZMod bfvPlaintextModulus) - x)

theorem boundedZeroValue_zero (bound : Nat)
    (hbound : bound < bfvPlaintextModulus) :
    boundedZeroValue bound 0 = 1 := by
  have hproduct :
      (∏ i ∈ Finset.range bound,
          ((i + 1 : Nat) : ZMod bfvPlaintextModulus)) =
        (bound.factorial : ZMod bfvPlaintextModulus) := by
    calc
      (∏ i ∈ Finset.range bound,
          ((i + 1 : Nat) : ZMod bfvPlaintextModulus)) =
          (((∏ i ∈ Finset.range bound, (i + 1)) : Nat) :
            ZMod bfvPlaintextModulus) := by
              exact (Nat.cast_prod (R := ZMod bfvPlaintextModulus)
                (fun i => i + 1) (Finset.range bound)).symm
      _ = (bound.factorial : ZMod bfvPlaintextModulus) := by
        exact congrArg (fun value : Nat =>
          (value : ZMod bfvPlaintextModulus))
          (Finset.prod_range_add_one_eq_factorial bound)
  have hfactorial :
      (bound.factorial : ZMod bfvPlaintextModulus) ≠ 0 := by
    rw [ne_eq, ZMod.natCast_eq_zero_iff]
    intro hdvd
    have hprime : Nat.Prime bfvPlaintextModulus := Fact.out
    have := (hprime.dvd_factorial).mp hdvd
    omega
  rw [boundedZeroValue]
  simp only [sub_zero, hproduct]
  exact mul_inv_cancel₀ hfactorial

theorem boundedZeroValue_positive (bound value : Nat)
    (hpositive : 0 < value) (hle : value ≤ bound) :
    boundedZeroValue bound (value : ZMod bfvPlaintextModulus) = 0 := by
  rw [boundedZeroValue]
  apply mul_eq_zero_of_left
  apply Finset.prod_eq_zero (i := value - 1)
  · simp only [Finset.mem_range]
    omega
  · have hone : value - 1 + 1 = value := by omega
    simp [hone]

theorem boundedZeroScaled_zero (bound : Nat) :
    boundedZeroScaled bound 0 =
      (bound.factorial : ZMod bfvPlaintextModulus) := by
  rw [boundedZeroScaled]
  simp only [sub_zero]
  calc
    (∏ i ∈ Finset.range bound,
        ((i + 1 : Nat) : ZMod bfvPlaintextModulus)) =
        (((∏ i ∈ Finset.range bound, (i + 1)) : Nat) :
          ZMod bfvPlaintextModulus) := by
            exact (Nat.cast_prod (R := ZMod bfvPlaintextModulus)
              (fun i => i + 1) (Finset.range bound)).symm
    _ = (bound.factorial : ZMod bfvPlaintextModulus) := by
      exact congrArg (fun value : Nat =>
        (value : ZMod bfvPlaintextModulus))
        (Finset.prod_range_add_one_eq_factorial bound)

theorem boundedZeroScaled_positive (bound value : Nat)
    (hpositive : 0 < value) (hle : value ≤ bound) :
    boundedZeroScaled bound (value : ZMod bfvPlaintextModulus) = 0 := by
  rw [boundedZeroScaled]
  apply Finset.prod_eq_zero (i := value - 1)
  · simp only [Finset.mem_range]
    omega
  · have hone : value - 1 + 1 = value := by omega
    simp [hone]

theorem boundedZeroValue_natCast_eq_one_iff (bound value : Nat)
    (hle : value ≤ bound) (hbound : bound < bfvPlaintextModulus) :
    boundedZeroValue bound (value : ZMod bfvPlaintextModulus) = 1 <->
      value = 0 := by
  constructor
  · intro hvalue
    by_contra hne
    have hpositive : 0 < value := Nat.pos_of_ne_zero hne
    rw [boundedZeroValue_positive bound value hpositive hle] at hvalue
    exact zero_ne_one hvalue
  · rintro rfl
    simpa using boundedZeroValue_zero bound hbound

/-- A balanced product of `B` encrypted factors uses `B-1`
ciphertext-by-ciphertext multiplications. -/
def boundedZeroMultiplications (bound : Nat) : Nat := bound - 1

/-- The demo's omitted four-point zero conversion costs three ciphertext
multiplications.  Once included, the hybrid and all-Boolean plans both use
nine, so the earlier `6 < 9` theorem is not an end-to-end advantage. -/
theorem demo_bounded_zero_closes_multiplication_ledger :
    demoPlan.cost.ciphertextMultiplications +
        boundedZeroMultiplications (maxResidual demoLeft) =
      (rawBooleanProgram demoSchema demoFormula).cost.ciphertextMultiplications := by
  decide

/-- The balanced four-factor conversion adds two layers after the residual's
depth-one squarings; the parent conjunction adds one more.  This is the same
depth-four envelope as the all-Boolean plan. -/
theorem demo_bounded_zero_output_depth_matches_boolean :
    4 = (rawBooleanProgram demoSchema demoFormula).cost.maximumMultiplicativeDepth := by
  decide

/-! ## 3. A priced threshold-opening boundary -/

/-- What becomes public when one residual ciphertext is threshold-opened. -/
inductive Leakage where
  | encryptedBitOnly
  | finalResiduals (liveSlots : Nat)
  | internalResidualsAndTruth (liveSlots : Nat)
  deriving DecidableEq, Repr

/-- Exact primitive counts at the n-of-n opening seam.  Ciphertext-byte and
wire-byte counts are runtime values and therefore live in the Rust receipt,
not this symbolic manifest. -/
structure BoundaryCost where
  decryptionShares : Nat
  thresholdCombines : Nat
  clearZeroComparisons : Nat
  ciphertextReencryptions : Nat
  deriving DecidableEq, Repr

/-- One explicit way of discharging every residual-to-bit boundary. -/
structure ThresholdObservation where
  partyCount : Nat
  liveSlots : Nat
  residualCiphertexts : Nat
  internalResidualCiphertexts : Nat
  nonzeroParties : 0 < partyCount
  internalLeTotal : internalResidualCiphertexts ≤ residualCiphertexts

def ThresholdObservation.cost (observation : ThresholdObservation) : BoundaryCost :=
  { decryptionShares := observation.partyCount * observation.residualCiphertexts
  , thresholdCombines := observation.residualCiphertexts
  , clearZeroComparisons := observation.liveSlots * observation.residualCiphertexts
  , ciphertextReencryptions := observation.internalResidualCiphertexts }

def ThresholdObservation.leakage (observation : ThresholdObservation) : Leakage :=
  if observation.internalResidualCiphertexts = 0 then
    .finalResiduals observation.liveSlots
  else
    .internalResidualsAndTruth observation.liveSlots

/-- The phases whose costs and leakage must be present before a performance
comparison may be called end-to-end. -/
structure PhaseCoverage where
  keySetup : Bool
  inputEncryption : Bool
  sameOpeningVerification : Bool
  encryptedEvaluation : Bool
  everyZeroObservation : Bool
  outputObservation : Bool
  deriving DecidableEq, Repr

def PhaseCoverage.complete (coverage : PhaseCoverage) : Bool :=
  coverage.keySetup && coverage.inputEncryption &&
    coverage.sameOpeningVerification && coverage.encryptedEvaluation &&
    coverage.everyZeroObservation && coverage.outputObservation

/-- An observation manifest cannot float free of the semantic object: it
contains the exact hybrid certificate whose raw and proof openings are tied by
`ConversionWitness`, and repeats only recomputable accounting fields. -/
structure Manifest (variableCount atomCount : Nat) where
  certificate : CertifiedHybridProofFhe.Certificate variableCount atomCount
  computationCost : Cost
  requiredZeroObservations : Nat
  observation : ThresholdObservation
  coverage : PhaseCoverage

def Manifest.check {variableCount atomCount : Nat}
    (manifest : Manifest variableCount atomCount) : Bool :=
  decide (manifest.computationCost = manifest.certificate.plan.cost) &&
    decide (manifest.requiredZeroObservations =
      manifest.certificate.plan.cost.boundaryZeroDecisions) &&
    decide (manifest.observation.residualCiphertexts =
      manifest.requiredZeroObservations)

theorem Manifest.check_spec {variableCount atomCount : Nat}
    {manifest : Manifest variableCount atomCount} :
    manifest.check = true <->
      manifest.computationCost = manifest.certificate.plan.cost /\
      manifest.requiredZeroObservations =
        manifest.certificate.plan.cost.boundaryZeroDecisions /\
      manifest.observation.residualCiphertexts =
        manifest.requiredZeroObservations := by
  simp [Manifest.check, and_assoc]

/-- An accepted manifest preserves the already-proved same-opening theorem;
pricing the observation seam does not weaken the source/proof/FHE agreement. -/
theorem Manifest.bound_same_opening
    {variableCount atomCount : Nat}
    (manifest : Manifest variableCount atomCount) :
    Dregg2.Logic.FiniteLogicDescriptorIR2.CanonicalLogicSatisfied2
        (fun _ => 0) atomCount manifest.certificate.dual.source
        (fun _ => 0) (fun _ => ((0 : Int), 0)) []
        manifest.certificate.dual.opening.proofTrace <->
      manifest.certificate.plan.evalRing manifest.certificate.rawOpening = 1 := by
  exact manifest.certificate.bound_proof_iff_fhe_plan

def Manifest.endToEndComparable {variableCount atomCount : Nat}
    (manifest : Manifest variableCount atomCount) : Bool :=
  manifest.check && manifest.coverage.complete

/-- A structurally cheaper encrypted computation is not automatically a
cheaper end-to-end system. -/
theorem not_endToEndComparable_of_missing_phase
    {variableCount atomCount : Nat}
    (manifest : Manifest variableCount atomCount)
    (hmissing : manifest.coverage.complete = false) :
    manifest.endToEndComparable = false := by
  simp [Manifest.endToEndComparable, hmissing]

def demoObservation : ThresholdObservation where
  partyCount := 3
  liveSlots := 1
  residualCiphertexts := 1
  internalResidualCiphertexts := 1
  nonzeroParties := by decide
  internalLeTotal := by decide

def symbolicOnlyCoverage : PhaseCoverage :=
  { keySetup := false
  , inputEncryption := false
  , sameOpeningVerification := true
  , encryptedEvaluation := false
  , everyZeroObservation := false
  , outputObservation := false }

def demoSymbolicManifest : Manifest 10 5 where
  certificate := demoCertificate
  computationCost := demoPlan.cost
  requiredZeroObservations := 1
  observation := demoObservation
  coverage := symbolicOnlyCoverage

theorem demoSymbolicManifest_checks : demoSymbolicManifest.check = true := by decide

theorem demoBoundary_cost : demoObservation.cost =
    { decryptionShares := 3
    , thresholdCombines := 1
    , clearZeroComparisons := 1
    , ciphertextReencryptions := 1 } := by decide

theorem demoBoundary_leaks_internal_residual :
    demoObservation.leakage = .internalResidualsAndTruth 1 := by decide

/-- The formal `6 < 9` result remains valid as an encrypted-computation
ledger, while this theorem prevents relabelling it as end-to-end evidence. -/
theorem demo_six_vs_nine_is_not_end_to_end :
    demoSymbolicManifest.endToEndComparable = false := by decide

#assert_all_clean [
  fermatZero_eq_one_iff,
  zeroIndicator_natDegree_lower_bound,
  CarrierExpr.eval_poly,
  CarrierExpr.natDegree_le_pow_depth,
  deployed_exact_zero_test_depth_at_least_twenty,
  boundedZeroValue_zero,
  boundedZeroValue_positive,
  boundedZeroScaled_zero,
  boundedZeroScaled_positive,
  boundedZeroValue_natCast_eq_one_iff,
  demo_bounded_zero_closes_multiplication_ledger,
  demo_bounded_zero_output_depth_matches_boolean,
  Manifest.bound_same_opening,
  Manifest.check_spec,
  not_endToEndComparable_of_missing_phase,
  demoSymbolicManifest_checks,
  demoBoundary_cost,
  demoBoundary_leaks_internal_residual,
  demo_six_vs_nine_is_not_end_to_end
]

end Dregg2.Logic.CertifiedHybridProofFheZeroObservation

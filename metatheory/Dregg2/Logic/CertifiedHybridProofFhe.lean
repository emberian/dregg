/-
# Dregg2.Logic.CertifiedHybridProofFhe -- certified local presentation changes

This module connects `CertifiedPresentationChange` to the versioned dual
proof/FHE certificate.  The source is a positive formula of equality atoms over
one raw opening.  An explicit conversion witness derives the canonical
equality-bit opening consumed by DescriptorIR2.  The FHE side continues to
consume the raw opening and may choose, independently at each region, between:

* a locally bounded zero-means-true residual, followed by an explicit
  zero-to-one observation boundary; and
* the canonical one-means-true Boolean BFV program.

Split nodes convert their children back to one-means-true bits before applying
Boolean conjunction or disjunction.  The conversion is therefore represented
in the plan and in its cost rather than hidden in prose.  Every plan maps to an
actual `CertifiedPresentationChange.DirectLogic.HybridEvidence`, and both its
ring denotation and the live DescriptorIR2 proof relation equal the same source
predicate for every canonical raw opening.

The exact symbolic ledger counts the primitive calls in these definitions.  It
is not a latency, noise, key-management, ciphertext-serialization, or FHE
security theorem.

Pure.  No axioms.
-/

import Dregg2.Logic.ProofFheDualCertificate
import Dregg2.Metatheory.CertifiedPresentationChange
import Dregg2.Tactics

namespace Dregg2.Logic.CertifiedHybridProofFhe

set_option autoImplicit false

open Dregg2.Circuit.DescriptorIR2
open Dregg2.Logic.FiniteLogicDescriptorIR2
open Dregg2.Logic.FheLogicBfvModel
open Dregg2.Logic.ProofFheSharedOpening
open Dregg2.Metatheory.FOLArithmetizationCorrected
open Dregg2.Metatheory.CertifiedPresentationChange

namespace Dual

abbrev Certificate (n : Nat) :=
  Dregg2.Logic.ProofFheDualCertificate.Certificate n

def check {n : Nat} (certificate : Certificate n) : Bool :=
  Dregg2.Logic.ProofFheDualCertificate.check certificate

theorem check_spec {n : Nat} {certificate : Certificate n} :
    check certificate = true <->
      Dregg2.Logic.ProofFheDualCertificate.check certificate = true := Iff.rfl

def certify {n : Nat} (source : TypedSource n) (opening : Opening n) :
    Certificate n :=
  Dregg2.Logic.ProofFheDualCertificate.certify source opening

end Dual

/-! ## 1. Equality schemas and explicit representation conversion -/

/-- Every logical atom names one equality between two slots of the raw opening. -/
structure EqualitySchema (variableCount atomCount : Nat) where
  lhs : Fin atomCount -> Fin variableCount
  rhs : Fin atomCount -> Fin variableCount

def atomTruth {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (atom : Fin atomCount) : Prop :=
  opening.boolEnv (schema.lhs atom).val = opening.boolEnv (schema.rhs atom).val

instance {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (atom : Fin atomCount) :
    Decidable (atomTruth schema opening atom) := by
  unfold atomTruth
  infer_instance

/-- Natural zero-means-true equality residual for canonical bits. -/
def atomResidual {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (atom : Fin atomCount) : Nat :=
  if atomTruth schema opening atom then 0 else 1

/-- DescriptorIR2 consumes canonical equality bits derived from the raw
opening, never an independently supplied Boolean environment. -/
def convertedOpening {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) : Opening atomCount :=
  { word := fun atom => bitInt (decide (atomTruth schema opening atom)) }

/-- Proof-relevant conversion witness carried by a same-opening certificate. -/
structure ConversionWitness {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (raw : Opening variableCount) (proof : Opening atomCount) : Prop where
  exact : forall atom, proof.word atom =
    bitInt (decide (atomTruth schema raw atom))

theorem convertedOpening_witness {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) :
    ConversionWitness schema opening (convertedOpening schema opening) := by
  constructor
  intro atom
  rfl

theorem ConversionWitness.proof_canonical {variableCount atomCount : Nat}
    {schema : EqualitySchema variableCount atomCount}
    {raw : Opening variableCount} {proof : Opening atomCount}
    (witness : ConversionWitness schema raw proof) : proof.Canonical := by
  intro atom
  rw [witness.exact atom]
  cases decide (atomTruth schema raw atom) <;> simp [bitInt]

theorem convertedOpening_canonical {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) :
    (convertedOpening schema opening).Canonical :=
  (convertedOpening_witness schema opening).proof_canonical

theorem convertedOpening_boolEnv {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (name : Nat) (hname : name < atomCount) :
    (convertedOpening schema opening).boolEnv name =
      decide (atomTruth schema opening (Fin.mk name hname)) := by
  simp [Opening.boolEnv, convertedOpening, hname, bitInt]

/-! ## 2. One positive source, in proof and raw-FHE representations -/

def positiveEval {Atom : Type*} (truth : Atom -> Bool) :
    PositiveFormula Atom -> Bool
  | .top => true
  | .bottom => false
  | .atom atom => truth atom
  | .and left right => positiveEval truth left && positiveEval truth right
  | .or left right => positiveEval truth left || positiveEval truth right

theorem positiveEval_eq_true_iff {Atom : Type*} (truth : Atom -> Bool)
    (formula : PositiveFormula Atom) :
    positiveEval truth formula = true <->
      PositiveFormula.Holds (fun atom => truth atom = true) formula := by
  induction formula <;> simp [positiveEval, PositiveFormula.Holds, *]

def proofSource {atomCount : Nat} : PositiveFormula (Fin atomCount) -> Proof.Source
  | .top => .top
  | .bottom => .bot
  | .atom atom => .atom atom.val
  | .and left right => .and (proofSource left) (proofSource right)
  | .or left right => .or (proofSource left) (proofSource right)

theorem proofSource_bounded {atomCount : Nat}
    (formula : PositiveFormula (Fin atomCount)) :
    atomsBelow atomCount (proofSource formula) = true := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | atom atom => simp [proofSource, atomsBelow, atom.isLt]
  | and left right ihLeft ihRight => simp [proofSource, atomsBelow, ihLeft, ihRight]
  | or left right ihLeft ihRight => simp [proofSource, atomsBelow, ihLeft, ihRight]

def typedProofSource {atomCount : Nat} (formula : PositiveFormula (Fin atomCount)) :
    TypedSource atomCount :=
  { formula := proofSource formula, bounded := proofSource_bounded formula }

def equalityBits {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (atom : Fin atomCount) : Bool :=
  decide (atomTruth schema opening atom)

theorem proofSource_eval {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount)
    (formula : PositiveFormula (Fin atomCount)) :
    Proof.eval (convertedOpening schema opening).boolEnv (proofSource formula) =
      positiveEval (equalityBits schema opening) formula := by
  induction formula with
  | top => rfl
  | bottom => rfl
  | atom atom =>
      simpa [proofSource,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval,
        positiveEval, equalityBits] using
        convertedOpening_boolEnv schema opening atom.val atom.isLt
  | and left right ihLeft ihRight =>
      simp [proofSource, Proof.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval,
        positiveEval, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [proofSource, Proof.eval,
        Dregg2.Logic.CompilationCertificateBundle.Source.eval,
        positiveEval, ihLeft, ihRight]

/-- Raw-opening Boolean BFV program.  Each logical atom remains an equality
operation; it is not replaced by an unbound precomputed input bit. -/
def rawBooleanProgram {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount) :
    PositiveFormula (Fin atomCount) -> BooleanProgram
  | .top => .constant true
  | .bottom => .constant false
  | .atom atom => .eq (.input (schema.lhs atom).val) (.input (schema.rhs atom).val)
  | .and left right => .and (rawBooleanProgram schema left) (rawBooleanProgram schema right)
  | .or left right => .or (rawBooleanProgram schema left) (rawBooleanProgram schema right)

theorem rawBooleanProgram_eval {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount)
    (formula : PositiveFormula (Fin atomCount)) :
    (rawBooleanProgram schema formula).evalBool opening.boolEnv =
      positiveEval (equalityBits schema opening) formula := by
  induction formula <;>
    simp [rawBooleanProgram, BooleanProgram.evalBool, positiveEval,
      equalityBits, atomTruth, *] <;>
    congr

theorem positiveEval_source_iff {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount)
    (formula : PositiveFormula (Fin atomCount)) :
    positiveEval (equalityBits schema opening) formula = true <->
      PositiveFormula.Holds (atomTruth schema opening) formula := by
  induction formula <;>
    simp [positiveEval, equalityBits, atomTruth, PositiveFormula.Holds, *]

/-! ## 3. Locally bounded residual regions -/

/-- Opening-independent upper bound when every equality residual is a bit. -/
def maxResidual {Atom : Type*} : PositiveFormula Atom -> Nat
  | .top => 0
  | .bottom => 1
  | .atom _ => 1
  | .and left right => maxResidual left + maxResidual right
  | .or left right => maxResidual left * maxResidual right

theorem atomResidual_le_one {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (atom : Fin atomCount) :
    atomResidual schema opening atom ≤ 1 := by
  by_cases htruth : atomTruth schema opening atom <;>
    simp [atomResidual, htruth]

theorem residual_le_max {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount)
    (formula : PositiveFormula (Fin atomCount)) :
    PositiveFormula.residual (atomResidual schema opening) formula ≤
      maxResidual formula := by
  induction formula with
  | top => simp [PositiveFormula.residual, maxResidual]
  | bottom => simp [PositiveFormula.residual, maxResidual]
  | atom atom => simpa [PositiveFormula.residual, maxResidual] using
      atomResidual_le_one schema opening atom
  | and left right ihLeft ihRight =>
      simpa [PositiveFormula.residual, maxResidual] using Nat.add_le_add ihLeft ihRight
  | or left right ihLeft ihRight =>
      simpa [PositiveFormula.residual, maxResidual] using Nat.mul_le_mul ihLeft ihRight

def bfvPlaintextModulus : Nat := 1032193

def bfvCenteredWindow : Nat := (bfvPlaintextModulus - 1) / 2

theorem bfvCenteredWindow_lt_modulus : bfvCenteredWindow < bfvPlaintextModulus := by
  decide

instance : Fact bfvPlaintextModulus.Prime := ⟨by
  norm_num [bfvPlaintextModulus]⟩

/-- Homomorphic residual polynomial over the BFV plaintext ring. -/
def residualRing {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) :
    PositiveFormula (Fin atomCount) -> ZMod bfvPlaintextModulus
  | .top => 0
  | .bottom => 1
  | .atom atom =>
      (encodeBool (R := ZMod bfvPlaintextModulus)
          (opening.boolEnv (schema.lhs atom).val) -
        encodeBool (R := ZMod bfvPlaintextModulus)
          (opening.boolEnv (schema.rhs atom).val)) ^ 2
  | .and left right => residualRing schema opening left + residualRing schema opening right
  | .or left right => residualRing schema opening left * residualRing schema opening right

theorem atomResidualRing_eq_cast {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (atom : Fin atomCount) :
    (encodeBool (R := ZMod bfvPlaintextModulus)
          (opening.boolEnv (schema.lhs atom).val) -
        encodeBool (R := ZMod bfvPlaintextModulus)
          (opening.boolEnv (schema.rhs atom).val)) ^ 2 =
      (atomResidual schema opening atom : ZMod bfvPlaintextModulus) := by
  cases hleft : opening.boolEnv (schema.lhs atom).val <;>
    cases hright : opening.boolEnv (schema.rhs atom).val <;>
      simp [encodeBool, atomResidual, atomTruth, hleft, hright]

theorem residualRing_eq_cast {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount)
    (formula : PositiveFormula (Fin atomCount)) :
    residualRing schema opening formula =
      ((PositiveFormula.residual (atomResidual schema opening) formula : Nat) :
        ZMod bfvPlaintextModulus) := by
  induction formula with
  | top => simp [residualRing, PositiveFormula.residual]
  | bottom => simp [residualRing, PositiveFormula.residual]
  | atom atom => exact atomResidualRing_eq_cast schema opening atom
  | and left right ihLeft ihRight =>
      simp [residualRing, PositiveFormula.residual, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp [residualRing, PositiveFormula.residual, ihLeft, ihRight]

theorem atomResidual_correct {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount) (atom : Fin atomCount) :
    atomResidual schema opening atom = 0 <-> atomTruth schema opening atom := by
  simp [atomResidual]

/-! ## 4. Hybrid FHE plans and exact costs -/

/-- `noWrap` is a local presentation choice.  Split nodes consume the explicit
one-means-true output of each child conversion. -/
inductive HybridPlan {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount) (window : Nat) :
    PositiveFormula (Fin atomCount) -> Type
  | noWrap (formula : PositiveFormula (Fin atomCount))
      (bound : maxResidual formula < window) : HybridPlan schema window formula
  | boolean (formula : PositiveFormula (Fin atomCount)) : HybridPlan schema window formula
  | and {left right : PositiveFormula (Fin atomCount)} :
      HybridPlan schema window left -> HybridPlan schema window right ->
      HybridPlan schema window (.and left right)
  | or {left right : PositiveFormula (Fin atomCount)} :
      HybridPlan schema window left -> HybridPlan schema window right ->
      HybridPlan schema window (.or left right)

/-- Explicit zero-means residual to one-means Boolean conversion. -/
structure ResidualConversion (residual : ZMod bfvPlaintextModulus) where
  output : ZMod bfvPlaintextModulus
  exact : output = encodeBool (decide (residual = 0))

def convertResidual (residual : ZMod bfvPlaintextModulus) :
    ResidualConversion residual :=
  { output := encodeBool (decide (residual = 0)), exact := rfl }

def HybridPlan.evalRing {variableCount atomCount window : Nat}
    {schema : EqualitySchema variableCount atomCount}
    {formula : PositiveFormula (Fin atomCount)}
    (opening : Opening variableCount) : HybridPlan schema window formula ->
      ZMod bfvPlaintextModulus
  | .noWrap formula _ => (convertResidual (residualRing schema opening formula)).output
  | .boolean formula => (rawBooleanProgram schema formula).evalRing opening.boolEnv
  | .and left right => left.evalRing opening * right.evalRing opening
  | .or left right =>
      left.evalRing opening + right.evalRing opening -
        left.evalRing opening * right.evalRing opening

@[simp] theorem encodeBool_and (left right : Bool) :
    encodeBool (R := ZMod bfvPlaintextModulus) (left && right) =
      encodeBool left * encodeBool right := by
  cases left <;> cases right <;> simp [encodeBool]

@[simp] theorem encodeBool_or (left right : Bool) :
    encodeBool (R := ZMod bfvPlaintextModulus) (left || right) =
      encodeBool left + encodeBool right - encodeBool left * encodeBool right := by
  cases left <;> cases right <;> simp [encodeBool]

def residualFormulaCost {Atom : Type*} : PositiveFormula Atom -> Cost
  | .top => { encryptedConstantReads := 1 }
  | .bottom => { encryptedConstantReads := 1 }
  | .atom _ =>
      { logicalInputReads := 2
        ciphertextSubtractions := 1
        ciphertextMultiplications := 1
        relinearizations := 1
        maximumMultiplicativeDepth := 1 }
  | .and left right =>
      let cost := Cost.merge (residualFormulaCost left) (residualFormulaCost right)
      { cost with ciphertextAdditions := cost.ciphertextAdditions + 1 }
  | .or left right =>
      (Cost.merge (residualFormulaCost left) (residualFormulaCost right)).withMulGate

def withBoundaryDecision (cost : Cost) : Cost :=
  { cost with boundaryZeroDecisions := cost.boundaryZeroDecisions + 1 }

def HybridPlan.cost {variableCount atomCount window : Nat}
    {schema : EqualitySchema variableCount atomCount}
    {formula : PositiveFormula (Fin atomCount)} :
    HybridPlan schema window formula -> Cost
  | .noWrap formula _ => withBoundaryDecision (residualFormulaCost formula)
  | .boolean formula => (rawBooleanProgram schema formula).cost
  | .and left right => (Cost.merge left.cost right.cost).withMulGate
  | .or left right =>
      let cost := (Cost.merge left.cost right.cost).withMulGate
      { cost with
        ciphertextAdditions := cost.ciphertextAdditions + 1
        ciphertextSubtractions := cost.ciphertextSubtractions + 1 }

theorem HybridPlan.evalRing_correct {variableCount atomCount window : Nat}
    {schema : EqualitySchema variableCount atomCount}
    {formula : PositiveFormula (Fin atomCount)}
    (hwindow : window ≤ bfvCenteredWindow)
    (opening : Opening variableCount) (plan : HybridPlan schema window formula) :
    plan.evalRing opening =
      encodeBool (R := ZMod bfvPlaintextModulus)
        (positiveEval (equalityBits schema opening) formula) := by
  induction plan with
  | noWrap formula bound =>
      simp only [HybridPlan.evalRing, convertResidual]
      have hresidual :
          PositiveFormula.residual (atomResidual schema opening) formula <
            bfvPlaintextModulus := by
        have hle := residual_le_max schema opening formula
        have hcenter := bfvCenteredWindow_lt_modulus
        omega
      have hzero : residualRing schema opening formula = 0 <->
          PositiveFormula.Holds (atomTruth schema opening) formula := by
        rw [residualRing_eq_cast]
        rw [Dregg2.Metatheory.FOLArithmetizationCorrected.zmod_natCast_eq_zero_iff_of_lt
          hresidual]
        exact PositiveFormula.residual_eq_zero_iff naturalLaws
          (atomTruth schema opening) (atomResidual schema opening)
          (fun _ => trivial) (atomResidual_correct schema opening) formula
      have heval : positiveEval (equalityBits schema opening) formula = true <->
          PositiveFormula.Holds (atomTruth schema opening) formula := by
        simpa [equalityBits] using
          positiveEval_eq_true_iff (equalityBits schema opening) formula
      cases h : positiveEval (equalityBits schema opening) formula
      · have hnzero : residualRing schema opening formula ≠ 0 := by
          intro hz
          have hholds := hzero.mp hz
          have : positiveEval (equalityBits schema opening) formula = true := heval.mpr hholds
          simp [h] at this
        simp [hnzero, encodeBool]
      · have hreszero : residualRing schema opening formula = 0 := by
          apply hzero.mpr
          exact heval.mp h
        simp [hreszero, encodeBool]
  | boolean formula =>
      rw [HybridPlan.evalRing, BooleanProgram.evalRing_correct,
        rawBooleanProgram_eval]
  | and left right ihLeft ihRight =>
      simp only [HybridPlan.evalRing, positiveEval]
      rw [ihLeft, ihRight]
      simp
  | or left right ihLeft ihRight =>
      simp only [HybridPlan.evalRing, positiveEval]
      rw [ihLeft, ihRight]
      simp

/-! ## 5. The actual certified-presentation witness -/

def directProblem {variableCount atomCount : Nat}
    (schema : EqualitySchema variableCount atomCount)
    (opening : Opening variableCount)
    (formula : PositiveFormula (Fin atomCount)) :
    DirectLogic.Problem (Fin atomCount) bfvPlaintextModulus where
  truth := atomTruth schema opening
  atomResidual := atomResidual schema opening
  atomCorrect := atomResidual_correct schema opening
  atomBound := by
    intro atom
    have hle := atomResidual_le_one schema opening atom
    simp [bfvPlaintextModulus]
    omega
  formula := formula

noncomputable def HybridPlan.toPresentationEvidence
    {variableCount atomCount window : Nat}
    {schema : EqualitySchema variableCount atomCount}
    (hwindow : window ≤ bfvCenteredWindow)
    (opening : Opening variableCount)
    (root : PositiveFormula (Fin atomCount)) :
    {formula : PositiveFormula (Fin atomCount)} ->
    HybridPlan schema window formula ->
      DirectLogic.HybridEvidence (directProblem schema opening root) formula
  | _, .noWrap region bound => by
      apply DirectLogic.HybridEvidence.noWrap region
      change PositiveFormula.residual (atomResidual schema opening) region <
        bfvPlaintextModulus
      have hle := residual_le_max schema opening region
      have hcenter := bfvCenteredWindow_lt_modulus
      omega
  | _, .boolean region => by
      let evidence := DirectLogic.canonicalBooleanEvidence
        (directProblem schema opening root) region
      exact .boolean region evidence.out evidence.graph
  | _, .and left right =>
      .and (left.toPresentationEvidence hwindow opening root)
        (right.toPresentationEvidence hwindow opening root)
  | _, .or left right =>
      .or (left.toPresentationEvidence hwindow opening root)
        (right.toPresentationEvidence hwindow opening root)

theorem HybridPlan.presentation_accepts_iff
    {variableCount atomCount window : Nat}
    {schema : EqualitySchema variableCount atomCount}
    {formula : PositiveFormula (Fin atomCount)}
    (hwindow : window ≤ bfvCenteredWindow)
    (opening : Opening variableCount) (plan : HybridPlan schema window formula) :
    (plan.toPresentationEvidence hwindow opening formula).accepts <->
      PositiveFormula.Holds (atomTruth schema opening) formula :=
  DirectLogic.HybridEvidence.accepts_iff _

/-! ## 6. Hybrid same-opening certificate and cross-backend theorem -/

structure Certificate (variableCount atomCount : Nat) where
  schema : EqualitySchema variableCount atomCount
  formula : PositiveFormula (Fin atomCount)
  window : Nat
  windowSound : window ≤ bfvCenteredWindow
  dual : Dual.Certificate atomCount
  dualAccepted : Dual.check dual = true
  sourceExact : dual.source = proofSource formula
  rawOpening : Opening variableCount
  rawCanonical : rawOpening.Canonical
  conversion : ConversionWitness schema rawOpening dual.opening
  plan : HybridPlan schema window formula

theorem Certificate.descriptor_bound {variableCount atomCount : Nat}
    (certificate : Certificate variableCount atomCount) :
    certificate.dual.descriptorBytes =
      emitVmJson2 (compileDescriptor atomCount (proofSource certificate.formula)) := by
  have hspec := Dregg2.Logic.ProofFheDualCertificate.check_spec.mp
    certificate.dualAccepted
  simpa [certificate.sourceExact] using hspec.2.2.2.1

theorem Certificate.proof_accepts_iff_source
    {variableCount atomCount : Nat}
    (certificate : Certificate variableCount atomCount) :
    forall opening : Opening variableCount, opening.Canonical ->
      (CanonicalLogicSatisfied2 (fun _ => 0) atomCount certificate.dual.source
          (fun _ => 0) (fun _ => ((0 : Int), 0)) []
          (convertedOpening certificate.schema opening).proofTrace <->
        PositiveFormula.Holds (atomTruth certificate.schema opening)
          certificate.formula) := by
  have hspec := Dregg2.Logic.ProofFheDualCertificate.check_spec.mp
    certificate.dualAccepted
  intro opening hcanonical
  have htrace := canonical_trace_iff (fun _ => 0) atomCount certificate.dual.source
    (convertedOpening certificate.schema opening).boolEnv hspec.2.1
  have hcanonicalConverted := convertedOpening_canonical certificate.schema opening
  have hrawTrace := Opening.proofTrace_eq_traceOf
    (convertedOpening certificate.schema opening) hcanonicalConverted
  rw [hrawTrace, htrace, certificate.sourceExact]
  change Proof.eval (convertedOpening certificate.schema opening).boolEnv
      (proofSource certificate.formula) = true <-> _
  rw [proofSource_eval]
  exact positiveEval_source_iff certificate.schema opening certificate.formula

theorem Certificate.fhe_plan_one_iff_source
    {variableCount atomCount : Nat}
    (certificate : Certificate variableCount atomCount) :
    forall opening : Opening variableCount, opening.Canonical ->
      (certificate.plan.evalRing opening = 1 <->
        PositiveFormula.Holds (atomTruth certificate.schema opening)
          certificate.formula) := by
  intro opening _
  rw [certificate.plan.evalRing_correct certificate.windowSound opening]
  have hzeroOne : (0 : ZMod bfvPlaintextModulus) ≠ 1 := by decide
  have hsource := positiveEval_source_iff certificate.schema opening certificate.formula
  cases heval : positiveEval (equalityBits certificate.schema opening)
      certificate.formula
  · constructor
    · simp [encodeBool, hzeroOne]
    · intro hholds
      have := hsource.mpr hholds
      simp [heval] at this
  · simp [encodeBool]
    exact hsource.mp heval

theorem Certificate.proof_iff_fhe_plan
    {variableCount atomCount : Nat}
    (certificate : Certificate variableCount atomCount) :
    forall opening : Opening variableCount, opening.Canonical ->
      (CanonicalLogicSatisfied2 (fun _ => 0) atomCount certificate.dual.source
          (fun _ => 0) (fun _ => ((0 : Int), 0)) []
          (convertedOpening certificate.schema opening).proofTrace <->
        certificate.plan.evalRing opening = 1) := by
  intro opening hcanonical
  exact (certificate.proof_accepts_iff_source opening hcanonical).trans
    (certificate.fhe_plan_one_iff_source opening hcanonical).symm

/-! ## 7. A genuinely mixed plan with a strict formal saving -/

def demoSchema : EqualitySchema 10 5 where
  lhs atom := ⟨2 * atom.val, by have := atom.isLt; omega⟩
  rhs atom := ⟨2 * atom.val + 1, by have := atom.isLt; omega⟩

def demoLeft : PositiveFormula (Fin 5) :=
  .and (.and (.atom 0) (.atom 1)) (.and (.atom 2) (.atom 3))

def demoFormula : PositiveFormula (Fin 5) := .and demoLeft (.atom 4)

/-- The root residual bound is exactly the policy window, so it is not locally
admissible; the four-equality left region remains strictly inside it. -/
theorem demo_root_not_locally_bounded : Not (maxResidual demoFormula < 5) := by decide

def demoPlan : HybridPlan demoSchema 5 demoFormula :=
  .and (.noWrap demoLeft (by decide)) (.boolean (.atom 4))

theorem demoPlan_cost : demoPlan.cost =
    { logicalInputReads := 10
      encryptedConstantReads := 1
      ciphertextAdditions := 5
      ciphertextSubtractions := 6
      ciphertextMultiplications := 6
      relinearizations := 6
      maximumMultiplicativeDepth := 2
      boundaryZeroDecisions := 1 : Cost } := by decide

theorem demoAllBoolean_cost : (rawBooleanProgram demoSchema demoFormula).cost =
    { logicalInputReads := 10
      encryptedConstantReads := 5
      ciphertextAdditions := 10
      ciphertextSubtractions := 10
      ciphertextMultiplications := 9
      relinearizations := 9
      maximumMultiplicativeDepth := 4 : Cost } := by decide

theorem demoPlan_strictly_fewer_multiplications :
    demoPlan.cost.ciphertextMultiplications <
      (rawBooleanProgram demoSchema demoFormula).cost.ciphertextMultiplications := by decide

def demoRawOpening : Opening 10 := { word := fun _ => 0 }

theorem demoRawOpening_canonical : demoRawOpening.Canonical := by
  intro slot
  exact Or.inl rfl

def demoConverted : Opening 5 := convertedOpening demoSchema demoRawOpening

def demoDual : Dual.Certificate 5 :=
  Dual.certify (typedProofSource demoFormula) demoConverted

theorem demoDual_accepted : Dual.check demoDual = true := by
  exact Dregg2.Logic.ProofFheDualCertificate.check_certify
    (typedProofSource demoFormula) demoConverted
    (convertedOpening_canonical demoSchema demoRawOpening)

def demoCertificate : Certificate 10 5 where
  schema := demoSchema
  formula := demoFormula
  window := 5
  windowSound := by decide
  dual := demoDual
  dualAccepted := demoDual_accepted
  sourceExact := rfl
  rawOpening := demoRawOpening
  rawCanonical := demoRawOpening_canonical
  conversion := convertedOpening_witness demoSchema demoRawOpening
  plan := demoPlan

theorem demoCertificate_bound_conversion :
    ConversionWitness demoCertificate.schema demoCertificate.rawOpening
      demoCertificate.dual.opening :=
  demoCertificate.conversion

#assert_all_clean [
  convertedOpening_witness,
  ConversionWitness.proof_canonical,
  convertedOpening_canonical,
  convertedOpening_boolEnv,
  positiveEval_eq_true_iff,
  proofSource_bounded,
  proofSource_eval,
  rawBooleanProgram_eval,
  atomResidual_le_one,
  residual_le_max,
  bfvCenteredWindow_lt_modulus,
  atomResidualRing_eq_cast,
  residualRing_eq_cast,
  atomResidual_correct,
  HybridPlan.evalRing_correct,
  HybridPlan.presentation_accepts_iff,
  Certificate.descriptor_bound,
  Certificate.proof_accepts_iff_source,
  Certificate.fhe_plan_one_iff_source,
  Certificate.proof_iff_fhe_plan,
  demo_root_not_locally_bounded,
  demoPlan_cost,
  demoAllBoolean_cost,
  demoPlan_strictly_fewer_multiplications,
  demoDual_accepted,
  demoRawOpening_canonical,
  demoCertificate_bound_conversion
]

end Dregg2.Logic.CertifiedHybridProofFhe

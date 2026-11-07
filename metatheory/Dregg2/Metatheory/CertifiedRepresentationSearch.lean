/-
# Certified search over direct-logic representations

`CertifiedPresentationChange` proves that exact representation changes compose.
This module adds the search layer:

* a finite graph whose nodes are presentations and whose edges are exact
  changes carrying explicit symbolic resource bounds;
* typed paths, their composite certified change, and the corresponding
  composite cost bound;
* an executable arg-min selector with proofs of membership and minimality over
  the enumerated candidates; and
* a concrete local compiler which refuses an unavailable no-wrap plan and
  chooses a genuinely mixed plan over an all-Boolean graph when the mixed plan
  has lower symbolic cost.

The proof/FHE same-opening bridge is included as a second two-node graph by
reusing `proofAccepts_iff_fheOutput_one`; its coherence theorem is not
duplicated.

Search is deliberately finite and auditable.  Minimality is relative to the
explicit candidate list, never to an unstated universe of compilers.

Standalone construction: no integration root is modified.  Pure; no axioms.
-/

import Dregg2.Logic.ProofFheSharedOpening
import Dregg2.Metatheory.CertifiedPresentationChange
import Mathlib.Data.Fintype.Basic
import Mathlib.Tactic

namespace Dregg2.Metatheory.CertifiedRepresentationSearch

open CategoryTheory
open Dregg2.Metatheory.ArithmetizationCost
open Dregg2.Metatheory.CertifiedPresentationChange

set_option autoImplicit false

/-! ## 1. An executable finite arg-min, independent of representation type -/

/-- Prefer the left candidate on ties, making selection deterministic. -/
def prefer {Candidate : Type} (score : Candidate → Nat)
    (left right : Candidate) : Candidate :=
  if score left ≤ score right then left else right

/-- Executable minimum of a finite, explicitly enumerated candidate list. -/
def selectMin {Candidate : Type} (score : Candidate → Nat) :
    List Candidate → Option Candidate
  | [] => none
  | candidate :: candidates =>
      match selectMin score candidates with
      | none => some candidate
      | some best => some (prefer score candidate best)

theorem prefer_eq_left_or_right {Candidate : Type} (score : Candidate → Nat)
    (left right : Candidate) :
    prefer score left right = left ∨ prefer score left right = right := by
  by_cases h : score left ≤ score right
  · exact Or.inl (by simp [prefer, h])
  · exact Or.inr (by simp [prefer, h])

theorem prefer_score_le_left {Candidate : Type} (score : Candidate → Nat)
    (left right : Candidate) :
    score (prefer score left right) ≤ score left := by
  by_cases h : score left ≤ score right
  · simp [prefer, h]
  · simp [prefer, h]
    omega

theorem prefer_score_le_right {Candidate : Type} (score : Candidate → Nat)
    (left right : Candidate) :
    score (prefer score left right) ≤ score right := by
  by_cases h : score left ≤ score right
  · simp [prefer, h]
  · simp [prefer, h]

theorem selectMin_mem {Candidate : Type} (score : Candidate → Nat)
    {candidates : List Candidate} {best : Candidate}
    (hselect : selectMin score candidates = some best) : best ∈ candidates := by
  induction candidates generalizing best with
  | nil => simp [selectMin] at hselect
  | cons candidate candidates ih =>
      simp only [selectMin] at hselect
      cases htail : selectMin score candidates with
      | none =>
          simp [htail] at hselect
          subst best
          simp
      | some tailBest =>
          simp [htail] at hselect
          subst best
          rcases prefer_eq_left_or_right score candidate tailBest with hleft | hright
          · rw [hleft]
            simp
          · rw [hright]
            exact List.mem_cons_of_mem _ (ih htail)

theorem selectMin_eq_none_iff {Candidate : Type} (score : Candidate → Nat)
    (candidates : List Candidate) :
    selectMin score candidates = none ↔ candidates = [] := by
  cases candidates with
  | nil => simp [selectMin]
  | cons head tail =>
      cases htail : selectMin score tail <;> simp [selectMin, htail]

theorem selectMin_minimal {Candidate : Type} (score : Candidate → Nat)
    {candidates : List Candidate} {best : Candidate}
    (hselect : selectMin score candidates = some best) :
    ∀ candidate ∈ candidates, score best ≤ score candidate := by
  induction candidates generalizing best with
  | nil => simp [selectMin] at hselect
  | cons head tail ih =>
      simp only [selectMin] at hselect
      cases htail : selectMin score tail with
      | none =>
          have htailEmpty := (selectMin_eq_none_iff score tail).mp htail
          subst tail
          simp [selectMin] at hselect
          subst best
          intro candidate hmem
          simp at hmem
          subst candidate
          exact Nat.le_refl _
      | some tailBest =>
          simp [htail] at hselect
          subst best
          intro candidate hmem
          rcases List.mem_cons.mp hmem with rfl | htailMem
          · exact prefer_score_le_left score candidate tailBest
          · exact Nat.le_trans (prefer_score_le_right score head tailBest)
              (ih htail candidate htailMem)

theorem selectMin_pair_of_lt {Candidate : Type} (score : Candidate → Nat)
    (left right : Candidate) (hstrict : score left < score right) :
    selectMin score [left, right] = some left := by
  simp [selectMin, prefer, Nat.le_of_lt hstrict]

/-! ## 2. Finite graphs of certified changes -/

/-- An edge exposes one particular overhead certificate for its exact change.
The underlying `Change` already contains an existential resource bound; this
field makes the chosen bound executable by search. -/
structure CertifiedEdge {Statement : Type}
    (P Q : Presentation Statement) where
  change : Change P Q
  symbolicOverhead : Statement → BackendCost
  resourceBound : ∀ statement evidence,
    CostLE (Q.resources statement (change.mapEvidence statement evidence))
      (BackendCost.combine (P.resources statement evidence)
        (symbolicOverhead statement))

/-- A finite presentation graph.  Every hom-list is finite by construction,
and the node carrier has an explicit `Fintype` witness. -/
structure PresentationGraph (Statement : Type) where
  Node : Type
  nodeFintype : Fintype Node
  presentation : Node → Presentation Statement
  edges : ∀ source target,
    List (CertifiedEdge (presentation source) (presentation target))

namespace PresentationGraph

variable {Statement : Type}

instance (graph : PresentationGraph Statement) : Fintype graph.Node :=
  graph.nodeFintype

/-- Typed paths cannot compose mismatched evidence representations. -/
inductive Path (graph : PresentationGraph Statement) :
    graph.Node → graph.Node → Type
  | nil (node : graph.Node) : Path graph node node
  | step {source middle target : graph.Node} :
      CertifiedEdge (graph.presentation source) (graph.presentation middle) →
      Path graph middle target → Path graph source target

namespace Path

variable {graph : PresentationGraph Statement}
variable {sourceNode middleNode targetNode finalNode : graph.Node}

/-- The certified composite represented by a typed path. -/
def composite : {source target : graph.Node} → Path graph source target →
    Change (graph.presentation source) (graph.presentation target)
  | _, _, .nil _ => Change.id _
  | _, _, .step edge rest => Change.comp edge.change (composite rest)

/-- Symbolic path overhead, using the same monoidal combination as the backend
cost ledger. -/
def symbolicOverhead (statement : Statement) :
    {source target : graph.Node} → Path graph source target → BackendCost
  | _, _, .nil _ => BackendCost.zero
  | _, _, .step edge rest =>
      BackendCost.combine (edge.symbolicOverhead statement)
        (symbolicOverhead statement rest)

/-- The explicitly accumulated path cost really bounds the selected composite
change. -/
theorem resourceBound (path : Path graph sourceNode targetNode) (statement : Statement)
    (evidence : (graph.presentation sourceNode).Evidence statement) :
    CostLE
      ((graph.presentation targetNode).resources statement
        (path.composite.mapEvidence statement evidence))
      (BackendCost.combine ((graph.presentation sourceNode).resources statement evidence)
        (path.symbolicOverhead statement)) := by
  induction path with
  | nil node =>
      simpa [composite, symbolicOverhead, Change.id] using
        CostLE.combine_zero ((graph.presentation node).resources statement evidence)
  | @step source mid destination edge rest ih =>
      have hrest := ih (edge.change.mapEvidence statement evidence)
      have hmono := CostLE.combine_mono_right
        (edge.resourceBound statement evidence)
        (symbolicOverhead statement rest)
      apply CostLE.trans hrest
      simpa only [symbolicOverhead, BackendCost.combine_assoc] using hmono

/-- Exactness of the selected composite is inherited from categorical
composition; the optimizer contributes no semantic assumption. -/
theorem composite_acceptance_iff (path : Path graph sourceNode targetNode)
    (statement : Statement)
    (evidence : (graph.presentation sourceNode).Evidence statement) :
    (graph.presentation targetNode).accepts statement
        (path.composite.mapEvidence statement evidence) ↔
      (graph.presentation sourceNode).accepts statement evidence :=
  path.composite.acceptance_iff statement evidence

end Path

/-- Scalarization used only to rank symbolic vectors.  The complete vector is
retained on every edge/path; this transparent sum is not a latency claim. -/
def totalWork (cost : BackendCost) : Nat :=
  cost.equations + cost.multiplications + cost.witnesses +
    cost.maxDegree + cost.tableCells

def pathScore {graph : PresentationGraph Statement} {sourceNode targetNode : graph.Node}
    (statement : Statement) (path : Path graph sourceNode targetNode) : Nat :=
  totalWork (path.symbolicOverhead statement)

/-- Search a finite caller-supplied path enumeration. -/
def shortestEnumerated {graph : PresentationGraph Statement}
    {sourceNode targetNode : graph.Node} (statement : Statement) :
    List (Path graph sourceNode targetNode) →
      Option (Path graph sourceNode targetNode) :=
  selectMin (pathScore statement)

theorem shortestEnumerated_mem {graph : PresentationGraph Statement}
    {sourceNode targetNode : graph.Node} (statement : Statement)
    {candidates : List (Path graph sourceNode targetNode)}
    {best : Path graph sourceNode targetNode}
    (hbest : shortestEnumerated statement candidates = some best) :
    best ∈ candidates :=
  selectMin_mem (pathScore statement) hbest

theorem shortestEnumerated_minimal {graph : PresentationGraph Statement}
    {sourceNode targetNode : graph.Node} (statement : Statement)
    {candidates : List (Path graph sourceNode targetNode)}
    {best : Path graph sourceNode targetNode}
    (hbest : shortestEnumerated statement candidates = some best) :
    ∀ candidate ∈ candidates,
      pathScore statement best ≤ pathScore statement candidate :=
  selectMin_minimal (pathScore statement) hbest

theorem shortestEnumerated_composite_exact
    {graph : PresentationGraph Statement} {sourceNode targetNode : graph.Node}
    (statement : Statement)
    {candidates : List (Path graph sourceNode targetNode)}
    {best : Path graph sourceNode targetNode}
    (hbest : shortestEnumerated statement candidates = some best)
    (evidence : (graph.presentation sourceNode).Evidence statement) :
    (graph.presentation targetNode).accepts statement
        (best.composite.mapEvidence statement evidence) ↔
      (graph.presentation sourceNode).accepts statement evidence := by
  have _hmember := shortestEnumerated_mem statement hbest
  exact best.composite_acceptance_iff statement evidence

end PresentationGraph

/-! ## 3. The concrete direct-logic representation graph -/

namespace DirectGraph

open Dregg2.Metatheory.FOLArithmetizationCorrected
open CertifiedPresentationChange.DirectLogic

variable {Atom : Type}
variable {p : Nat} [Fact p.Prime]

inductive Node where
  | noWrap
  | booleanGraph
  | hybrid
  deriving DecidableEq, Repr

instance : Fintype Node :=
  Fintype.ofList [.noWrap, .booleanGraph, .hybrid] (by intro x; cases x <;> simp)

def presentationAt : Node → Presentation (Problem Atom p)
  | .noWrap => noWrapPresentation
  | .booleanGraph => booleanPresentation
  | .hybrid => hybridPresentation

noncomputable def noWrapBooleanEdge :
    CertifiedEdge (presentationAt (Atom := Atom) (p := p) .noWrap)
      (presentationAt (Atom := Atom) (p := p) .booleanGraph) where
  change := noWrapToBoolean
  symbolicOverhead := fun statement =>
    ArithmetizationCost.BooleanGraph.cost (toBoolean statement.formula)
  resourceBound := by
    intro statement evidence
    exact CostLE.right_le_combine
      (ArithmetizationCost.Positive.skeletonCost statement.formula)
      (ArithmetizationCost.BooleanGraph.cost (toBoolean statement.formula))

def noWrapHybridEdge :
    CertifiedEdge (presentationAt (Atom := Atom) (p := p) .noWrap)
      (presentationAt (Atom := Atom) (p := p) .hybrid) where
  change := noWrapToHybrid
  symbolicOverhead := fun _ => BackendCost.zero
  resourceBound := by
    intro statement evidence
    exact CostLE.combine_zero
      (ArithmetizationCost.Positive.skeletonCost statement.formula)

def booleanHybridEdge :
    CertifiedEdge (presentationAt (Atom := Atom) (p := p) .booleanGraph)
      (presentationAt (Atom := Atom) (p := p) .hybrid) where
  change := booleanToHybrid
  symbolicOverhead := fun _ => BackendCost.zero
  resourceBound := by
    intro statement evidence
    exact CostLE.combine_zero
      (ArithmetizationCost.BooleanGraph.cost (toBoolean statement.formula))

noncomputable def edges : (source target : Node) →
    List (CertifiedEdge (presentationAt (Atom := Atom) (p := p) source)
      (presentationAt (Atom := Atom) (p := p) target))
  | .noWrap, .booleanGraph => [noWrapBooleanEdge]
  | .noWrap, .hybrid => [noWrapHybridEdge]
  | .booleanGraph, .hybrid => [booleanHybridEdge]
  | .noWrap, .noWrap => []
  | .booleanGraph, .noWrap => []
  | .booleanGraph, .booleanGraph => []
  | .hybrid, .noWrap => []
  | .hybrid, .booleanGraph => []
  | .hybrid, .hybrid => []

noncomputable def graph : PresentationGraph (Problem Atom p) where
  Node := Node
  nodeFintype := inferInstance
  presentation := presentationAt
  edges := edges

end DirectGraph

/-! ## 4. Reuse the proof/FHE same-opening theorem as a graph edge -/

namespace SharedOpeningGraph

open Dregg2.Logic.ProofFheSharedOpening

variable {n : Nat}

def sourceMeaning (input : Instance n) : Prop :=
  input.opening.Canonical ∧
    Proof.eval input.opening.boolEnv input.source.formula = true

def proofPresentation : Presentation (Instance n) where
  meaning := sourceMeaning
  Evidence := fun _ => Unit
  accepts := fun input _ => ProofAccepts input
  resources := fun _ _ => BackendCost.zero

def fhePresentation : Presentation (Instance n) where
  meaning := sourceMeaning
  Evidence := fun _ => Unit
  accepts := fun input _ => fheOutput? input = some 1
  resources := fun _ _ => BackendCost.zero

/-- This arrow is exactly the existing shared-opening equivalence, merely
packaged as a presentation change. -/
def proofToFhe : Change (proofPresentation (n := n)) (fhePresentation (n := n)) where
  mapEvidence := fun _ evidence => evidence
  meaning_iff := fun _ => Iff.rfl
  acceptance_iff := fun input _ => (proofAccepts_iff_fheOutput_one input).symm
  resourceBound := ⟨fun _ => BackendCost.zero, fun _ _ =>
    CostLE.combine_zero BackendCost.zero⟩

inductive Node where
  | proof
  | fhe
  deriving DecidableEq, Repr

instance : Fintype Node :=
  Fintype.ofList [.proof, .fhe] (by intro x; cases x <;> simp)

def presentationAt : Node → Presentation (Instance n)
  | .proof => proofPresentation
  | .fhe => fhePresentation

def proofFheEdge :
    CertifiedEdge (presentationAt (n := n) .proof)
      (presentationAt (n := n) .fhe) where
  change := proofToFhe
  symbolicOverhead := fun _ => BackendCost.zero
  resourceBound := fun _ _ => CostLE.combine_zero BackendCost.zero

def edges : (source target : Node) →
    List (CertifiedEdge (presentationAt (n := n) source)
      (presentationAt (n := n) target))
  | .proof, .fhe => [proofFheEdge]
  | .proof, .proof => []
  | .fhe, .proof => []
  | .fhe, .fhe => []

def graph : PresentationGraph (Instance n) where
  Node := Node
  nodeFintype := inferInstance
  presentation := presentationAt
  edges := edges

theorem proofFheEdge_acceptance_exact (input : Instance n) :
    (presentationAt (n := n) .fhe).accepts input
        (proofFheEdge.change.mapEvidence input ()) ↔
      (presentationAt (n := n) .proof).accepts input () :=
  proofFheEdge.change.acceptance_iff input ()

end SharedOpeningGraph

/-! ## 5. Certified local formula-plan search -/

namespace LocalPlan

open Dregg2.Metatheory.FOLArithmetizationCorrected
open CertifiedPresentationChange.DirectLogic

variable {Atom : Type}
variable {p : Nat} [Fact p.Prime]

structure Candidate (statement : Problem Atom p)
    (formula : PositiveFormula Atom) where
  evidence : HybridEvidence statement formula

def Candidate.symbolicCost {statement : Problem Atom p}
    {formula : PositiveFormula Atom} (candidate : Candidate statement formula) :
    BackendCost :=
  candidate.evidence.resources

def Candidate.score {statement : Problem Atom p}
    {formula : PositiveFormula Atom} (candidate : Candidate statement formula) : Nat :=
  PresentationGraph.totalWork candidate.symbolicCost

/-- No-wrap is offered only when Lean can construct the required local bound
certificate.  An unsafe plan becomes `none`, not a weakened gate. -/
def noWrapCandidate? (statement : Problem Atom p)
    (formula : PositiveFormula Atom) : Option (Candidate statement formula) :=
  if hbound : PositiveFormula.residual statement.atomResidual formula < p then
    some ⟨.noWrap formula hbound⟩
  else
    none

theorem noWrapCandidate?_eq_none_iff (statement : Problem Atom p)
    (formula : PositiveFormula Atom) :
    noWrapCandidate? statement formula = none ↔
      ¬ PositiveFormula.residual statement.atomResidual formula < p := by
  simp [noWrapCandidate?]

/-- The all-Boolean candidate can only be constructed through an actual
`BoolGraph.Graph` witness.  Its atom canonicality is the `atomBound` field of
`Problem`, consumed by `eval_toBoolean_iff`. -/
noncomputable def booleanCandidate (statement : Problem Atom p)
    (formula : PositiveFormula Atom) : Candidate statement formula :=
  let evidence := canonicalBooleanEvidence statement formula
  ⟨.boolean formula evidence.out evidence.graph⟩

/-- The recursive certified selector from the presentation module is itself a
search candidate. -/
noncomputable def hybridCandidate (statement : Problem Atom p)
    (formula : PositiveFormula Atom) : Candidate statement formula :=
  ⟨selectLocal statement formula⟩

/-- Explicit finite root-plan enumeration. -/
noncomputable def enumerate (statement : Problem Atom p)
    (formula : PositiveFormula Atom) : List (Candidate statement formula) :=
  (noWrapCandidate? statement formula).toList ++
    [hybridCandidate statement formula, booleanCandidate statement formula]

noncomputable def compileBest? (statement : Problem Atom p)
    (formula : PositiveFormula Atom) : Option (Candidate statement formula) :=
  selectMin Candidate.score (enumerate statement formula)

theorem compileBest?_member (statement : Problem Atom p)
    (formula : PositiveFormula Atom) {best : Candidate statement formula}
    (hbest : compileBest? statement formula = some best) :
    best ∈ enumerate statement formula :=
  selectMin_mem Candidate.score hbest

theorem compileBest?_minimal (statement : Problem Atom p)
    (formula : PositiveFormula Atom) {best : Candidate statement formula}
    (hbest : compileBest? statement formula = some best) :
    ∀ candidate ∈ enumerate statement formula,
      best.score ≤ candidate.score :=
  selectMin_minimal Candidate.score hbest

/-- Every selected plan is exact independently of the score calculation. -/
theorem compileBest?_acceptance_exact (statement : Problem Atom p)
    (formula : PositiveFormula Atom) {best : Candidate statement formula}
    (_hbest : compileBest? statement formula = some best) :
    best.evidence.accepts ↔ PositiveFormula.Holds statement.truth formula :=
  HybridEvidence.accepts_iff best.evidence

/-! ### A concrete optimum which is genuinely hybrid -/

private instance primeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- Each atom residual is the canonical natural `3 < 5`, but their
conjunction residual is `3 + 3 = 6`, so root no-wrap is unavailable. -/
def mixedProblem : Problem Bool 5 where
  truth := fun _ => False
  atomResidual := fun _ => 3
  atomCorrect := by intro atom; simp
  atomBound := by intro atom; omega
  formula := .and (.atom false) (.atom true)

theorem mixed_root_unsafe :
    ¬ PositiveFormula.residual mixedProblem.atomResidual mixedProblem.formula < 5 := by
  norm_num [mixedProblem, PositiveFormula.residual]

theorem mixed_left_safe :
    PositiveFormula.residual mixedProblem.atomResidual (.atom false) < 5 := by
  norm_num [mixedProblem, PositiveFormula.residual]

theorem mixed_right_safe :
    PositiveFormula.residual mixedProblem.atomResidual (.atom true) < 5 := by
  norm_num [mixedProblem, PositiveFormula.residual]

noncomputable def mixedHybrid : Candidate mixedProblem mixedProblem.formula :=
  hybridCandidate mixedProblem mixedProblem.formula

noncomputable def mixedBoolean : Candidate mixedProblem mixedProblem.formula :=
  booleanCandidate mixedProblem mixedProblem.formula

noncomputable def mixedCandidates : List (Candidate mixedProblem mixedProblem.formula) :=
  enumerate mixedProblem mixedProblem.formula

theorem mixed_noWrap_rejected :
    noWrapCandidate? mixedProblem mixedProblem.formula = none :=
  (noWrapCandidate?_eq_none_iff mixedProblem mixedProblem.formula).2 mixed_root_unsafe

theorem mixedHybrid_is_genuinely_mixed :
    mixedHybrid.evidence.rootStrategy = .split := by
  exact selectLocal_splits_unsafe_and mixedProblem (.atom false) (.atom true)
    mixed_root_unsafe

theorem mixedHybrid_children_are_noWrap :
    selectLocal mixedProblem mixedProblem.formula =
        .and (selectLocal mixedProblem (.atom false))
          (selectLocal mixedProblem (.atom true)) ∧
      (selectLocal mixedProblem (.atom false)).rootStrategy = .noWrap ∧
      (selectLocal mixedProblem (.atom true)).rootStrategy = .noWrap :=
  selectLocal_unsafe_and_safe_children mixedProblem (.atom false) (.atom true)
    mixed_root_unsafe mixed_left_safe mixed_right_safe

theorem mixedHybrid_score : mixedHybrid.score = 0 := by
  simp [mixedHybrid, hybridCandidate, Candidate.score, Candidate.symbolicCost,
    PresentationGraph.totalWork, selectLocal, mixedProblem,
    PositiveFormula.residual, HybridEvidence.resources,
    ArithmetizationCost.Positive.skeletonCost,
    BackendCost.combine, BackendCost.zero]

theorem mixedBoolean_score : mixedBoolean.score = 23 := by
  simp [mixedBoolean, booleanCandidate, Candidate.score, Candidate.symbolicCost,
    PresentationGraph.totalWork, HybridEvidence.resources, mixedProblem,
    toBoolean, ArithmetizationCost.BooleanGraph.cost,
    ArithmetizationCost.zeroTestGateCost,
    ArithmetizationCost.booleanBinaryGateCost,
    BackendCost.combine]

theorem mixed_hybrid_strictly_beats_boolean :
    mixedHybrid.score < mixedBoolean.score := by
  rw [mixedHybrid_score, mixedBoolean_score]
  decide

theorem mixed_compileBest :
    compileBest? mixedProblem mixedProblem.formula = some mixedHybrid := by
  rw [compileBest?, enumerate, mixed_noWrap_rejected]
  simp only [Option.toList_none, List.nil_append]
  exact selectMin_pair_of_lt Candidate.score mixedHybrid mixedBoolean
    mixed_hybrid_strictly_beats_boolean

theorem mixed_compileBest_minimal :
    ∀ candidate ∈ mixedCandidates, mixedHybrid.score ≤ candidate.score := by
  exact compileBest?_minimal mixedProblem mixedProblem.formula mixed_compileBest

theorem mixed_compileBest_acceptance_exact :
    mixedHybrid.evidence.accepts ↔
      PositiveFormula.Holds mixedProblem.truth mixedProblem.formula :=
  compileBest?_acceptance_exact mixedProblem mixedProblem.formula mixed_compileBest

/-! ### Static range certificates: a true formula with a genuinely hybrid optimum -/

/-- Compile-time range metadata.  `atomUpper` is public and independent of the
actual atom value, while `atomLeUpper` connects it to the source instance. -/
structure StaticProblem (Atom : Type) (p : Nat) extends Problem Atom p where
  atomUpper : Atom → Nat
  atomLeUpper : ∀ atom, toProblem.atomResidual atom ≤ atomUpper atom

def staticResidual (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) : Nat :=
  PositiveFormula.residual statement.atomUpper formula

omit [Fact p.Prime] in
/-- Structural monotonicity turns a static upper bound into an actual no-wrap
certificate without inspecting whether the formula is true. -/
theorem residual_le_staticResidual (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) :
    PositiveFormula.residual statement.toProblem.atomResidual formula ≤
      staticResidual statement formula := by
  induction formula with
  | top => simp [staticResidual, PositiveFormula.residual]
  | bottom => simp [staticResidual, PositiveFormula.residual]
  | atom atom => exact statement.atomLeUpper atom
  | and left right ihLeft ihRight =>
      simp only [PositiveFormula.residual, staticResidual] at ihLeft ihRight ⊢
      omega
  | or left right ihLeft ihRight =>
      simp only [PositiveFormula.residual, staticResidual] at ihLeft ihRight ⊢
      exact Nat.mul_le_mul ihLeft ihRight

/-- Static no-wrap admission.  A candidate is absent when its public structural
bound is not below the field modulus. -/
def staticNoWrapCandidate? (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) :
    Option (Candidate statement.toProblem formula) :=
  if hbound : staticResidual statement formula < p then
    some ⟨.noWrap formula
      (lt_of_le_of_lt (residual_le_staticResidual statement formula) hbound)⟩
  else
    none

theorem staticNoWrapCandidate?_eq_none_iff (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) :
    staticNoWrapCandidate? statement formula = none ↔
      ¬ staticResidual statement formula < p := by
  simp [staticNoWrapCandidate?]

/-- Static per-subformula selection.  The decision at each node depends only
on declared range metadata, never on the truth value being proved. -/
noncomputable def selectStatic (statement : StaticProblem Atom p) :
    (formula : PositiveFormula Atom) →
      HybridEvidence statement.toProblem formula
  | .top =>
      if h : staticResidual statement .top < p then
        .noWrap .top
          (lt_of_le_of_lt (residual_le_staticResidual statement .top) h)
      else
        let evidence := canonicalBooleanEvidence statement.toProblem .top
        .boolean .top evidence.out evidence.graph
  | .bottom =>
      if h : staticResidual statement .bottom < p then
        .noWrap .bottom
          (lt_of_le_of_lt (residual_le_staticResidual statement .bottom) h)
      else
        let evidence := canonicalBooleanEvidence statement.toProblem .bottom
        .boolean .bottom evidence.out evidence.graph
  | .atom atom =>
      if h : staticResidual statement (.atom atom) < p then
        .noWrap (.atom atom)
          (lt_of_le_of_lt (residual_le_staticResidual statement (.atom atom)) h)
      else
        let evidence := canonicalBooleanEvidence statement.toProblem (.atom atom)
        .boolean (.atom atom) evidence.out evidence.graph
  | .and left right =>
      if h : staticResidual statement (.and left right) < p then
        .noWrap (.and left right)
          (lt_of_le_of_lt
            (residual_le_staticResidual statement (.and left right)) h)
      else
        .and (selectStatic statement left) (selectStatic statement right)
  | .or left right =>
      if h : staticResidual statement (.or left right) < p then
        .noWrap (.or left right)
          (lt_of_le_of_lt
            (residual_le_staticResidual statement (.or left right)) h)
      else
        .or (selectStatic statement left) (selectStatic statement right)

theorem selectStatic_accepts_iff (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) :
    (selectStatic statement formula).accepts ↔
      PositiveFormula.Holds statement.toProblem.truth formula :=
  HybridEvidence.accepts_iff (selectStatic statement formula)

theorem selectStatic_unsafe_and_safe_children (statement : StaticProblem Atom p)
    (left right : PositiveFormula Atom)
    (hroot : ¬ staticResidual statement (.and left right) < p)
    (hleft : staticResidual statement left < p)
    (hright : staticResidual statement right < p) :
    (selectStatic statement (.and left right)).rootStrategy = .split ∧
      (selectStatic statement left).rootStrategy = .noWrap ∧
      (selectStatic statement right).rootStrategy = .noWrap := by
  constructor
  · simp [selectStatic, hroot, HybridEvidence.rootStrategy]
  constructor
  · cases left <;> simp [selectStatic, hleft, HybridEvidence.rootStrategy]
  · cases right <;> simp [selectStatic, hright, HybridEvidence.rootStrategy]

noncomputable def staticHybridCandidate (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) : Candidate statement.toProblem formula :=
  ⟨selectStatic statement formula⟩

noncomputable def staticEnumerate (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) :
    List (Candidate statement.toProblem formula) :=
  (staticNoWrapCandidate? statement formula).toList ++
    [staticHybridCandidate statement formula,
      booleanCandidate statement.toProblem formula]

noncomputable def staticCompileBest? (statement : StaticProblem Atom p)
    (formula : PositiveFormula Atom) :
    Option (Candidate statement.toProblem formula) :=
  selectMin Candidate.score (staticEnumerate statement formula)

private instance staticPrimeFive : Fact (Nat.Prime 5) := ⟨by norm_num⟩

/-- The actual atoms are true (`residual = 0`), but their public upper bounds
are `3` each.  The root static bound is therefore `6 ≥ 5`, while both children
remain statically safe. -/
def acceptedStaticProblem : StaticProblem Bool 5 where
  truth := fun _ => True
  atomResidual := fun _ => 0
  atomCorrect := by intro atom; simp
  atomBound := by intro atom; omega
  formula := .and (.atom false) (.atom true)
  atomUpper := fun _ => 3
  atomLeUpper := by intro atom; omega

theorem acceptedStatic_source_true :
    PositiveFormula.Holds acceptedStaticProblem.toProblem.truth
      acceptedStaticProblem.toProblem.formula := by
  simp [acceptedStaticProblem, PositiveFormula.Holds]

theorem acceptedStatic_root_unsafe :
    ¬ staticResidual acceptedStaticProblem
      acceptedStaticProblem.toProblem.formula < 5 := by
  norm_num [acceptedStaticProblem, staticResidual, PositiveFormula.residual]

theorem acceptedStatic_left_safe :
    staticResidual acceptedStaticProblem (.atom false) < 5 := by
  norm_num [acceptedStaticProblem, staticResidual, PositiveFormula.residual]

theorem acceptedStatic_right_safe :
    staticResidual acceptedStaticProblem (.atom true) < 5 := by
  norm_num [acceptedStaticProblem, staticResidual, PositiveFormula.residual]

noncomputable def acceptedStaticHybrid :
    Candidate acceptedStaticProblem.toProblem
      acceptedStaticProblem.toProblem.formula :=
  staticHybridCandidate acceptedStaticProblem
    acceptedStaticProblem.toProblem.formula

noncomputable def acceptedStaticBoolean :
    Candidate acceptedStaticProblem.toProblem
      acceptedStaticProblem.toProblem.formula :=
  booleanCandidate acceptedStaticProblem.toProblem
    acceptedStaticProblem.toProblem.formula

theorem acceptedStatic_noWrap_rejected :
    staticNoWrapCandidate? acceptedStaticProblem
      acceptedStaticProblem.toProblem.formula = none :=
  (staticNoWrapCandidate?_eq_none_iff acceptedStaticProblem
    acceptedStaticProblem.toProblem.formula).2 acceptedStatic_root_unsafe

theorem acceptedStatic_is_genuinely_mixed :
    acceptedStaticHybrid.evidence.rootStrategy = .split ∧
      (selectStatic acceptedStaticProblem (.atom false)).rootStrategy = .noWrap ∧
      (selectStatic acceptedStaticProblem (.atom true)).rootStrategy = .noWrap :=
  selectStatic_unsafe_and_safe_children acceptedStaticProblem
    (.atom false) (.atom true) acceptedStatic_root_unsafe
    acceptedStatic_left_safe acceptedStatic_right_safe

theorem acceptedStaticHybrid_score : acceptedStaticHybrid.score = 0 := by
  simp [acceptedStaticHybrid, staticHybridCandidate, Candidate.score,
    Candidate.symbolicCost, PresentationGraph.totalWork, selectStatic,
    acceptedStaticProblem, staticResidual, PositiveFormula.residual,
    HybridEvidence.resources, ArithmetizationCost.Positive.skeletonCost,
    BackendCost.combine, BackendCost.zero]

theorem acceptedStaticBoolean_score : acceptedStaticBoolean.score = 23 := by
  simp [acceptedStaticBoolean, booleanCandidate, Candidate.score,
    Candidate.symbolicCost, PresentationGraph.totalWork,
    HybridEvidence.resources, acceptedStaticProblem, toBoolean,
    ArithmetizationCost.BooleanGraph.cost,
    ArithmetizationCost.zeroTestGateCost,
    ArithmetizationCost.booleanBinaryGateCost, BackendCost.combine]

theorem acceptedStatic_hybrid_strictly_beats_boolean :
    acceptedStaticHybrid.score < acceptedStaticBoolean.score := by
  rw [acceptedStaticHybrid_score, acceptedStaticBoolean_score]
  decide

theorem acceptedStatic_compileBest :
    staticCompileBest? acceptedStaticProblem
      acceptedStaticProblem.toProblem.formula = some acceptedStaticHybrid := by
  rw [staticCompileBest?, staticEnumerate, acceptedStatic_noWrap_rejected]
  simp only [Option.toList_none, List.nil_append]
  exact selectMin_pair_of_lt Candidate.score acceptedStaticHybrid
    acceptedStaticBoolean acceptedStatic_hybrid_strictly_beats_boolean

theorem acceptedStatic_compileBest_minimal :
    ∀ candidate ∈ staticEnumerate acceptedStaticProblem
        acceptedStaticProblem.toProblem.formula,
      acceptedStaticHybrid.score ≤ candidate.score :=
  selectMin_minimal Candidate.score acceptedStatic_compileBest

theorem acceptedStatic_compileBest_accepts :
    acceptedStaticHybrid.evidence.accepts :=
  (HybridEvidence.accepts_iff acceptedStaticHybrid.evidence).2
    acceptedStatic_source_true

end LocalPlan

#assert_all_clean [
  prefer_eq_left_or_right,
  prefer_score_le_left,
  prefer_score_le_right,
  selectMin_mem,
  selectMin_pair_of_lt,
  selectMin_minimal,
  PresentationGraph.Path.resourceBound,
  PresentationGraph.Path.composite_acceptance_iff,
  PresentationGraph.shortestEnumerated_mem,
  PresentationGraph.shortestEnumerated_minimal,
  PresentationGraph.shortestEnumerated_composite_exact,
  SharedOpeningGraph.proofFheEdge_acceptance_exact,
  LocalPlan.noWrapCandidate?_eq_none_iff,
  LocalPlan.compileBest?_member,
  LocalPlan.compileBest?_minimal,
  LocalPlan.compileBest?_acceptance_exact,
  LocalPlan.mixed_root_unsafe,
  LocalPlan.mixed_noWrap_rejected,
  LocalPlan.mixedHybrid_is_genuinely_mixed,
  LocalPlan.mixedHybrid_children_are_noWrap,
  LocalPlan.mixedHybrid_score,
  LocalPlan.mixedBoolean_score,
  LocalPlan.mixed_hybrid_strictly_beats_boolean,
  LocalPlan.mixed_compileBest,
  LocalPlan.mixed_compileBest_minimal,
  LocalPlan.mixed_compileBest_acceptance_exact,
  LocalPlan.residual_le_staticResidual,
  LocalPlan.staticNoWrapCandidate?_eq_none_iff,
  LocalPlan.selectStatic_accepts_iff,
  LocalPlan.selectStatic_unsafe_and_safe_children,
  LocalPlan.acceptedStatic_source_true,
  LocalPlan.acceptedStatic_root_unsafe,
  LocalPlan.acceptedStatic_noWrap_rejected,
  LocalPlan.acceptedStatic_is_genuinely_mixed,
  LocalPlan.acceptedStaticHybrid_score,
  LocalPlan.acceptedStaticBoolean_score,
  LocalPlan.acceptedStatic_hybrid_strictly_beats_boolean,
  LocalPlan.acceptedStatic_compileBest,
  LocalPlan.acceptedStatic_compileBest_minimal,
  LocalPlan.acceptedStatic_compileBest_accepts]

end Dregg2.Metatheory.CertifiedRepresentationSearch

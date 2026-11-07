/-
# Certified, indexed changes of presentation

This module turns the "choose a representation per subterm" idea into a small
compositional calculus.  A compiled fragment is indexed by its source formula
and records all three things which a backend claim needs:

* an observable acceptance proposition;
* an exact certificate relating that proposition to source semantics; and
* an explicit backend resource vector.

The four representation tags are intentionally not identified: dense
polynomials, materialized Boolean graphs, interaction nets, and natural
residuals remain different implementations even when their acceptance
propositions are equivalent.  A plan may stop at any subformula in any one of
those representations, or recursively split and pay an explicit recombination
cost.  `Plan.accepts_iff` is the global semantic preservation theorem.

Resource changes form a category and a symmetric tensor at the ledger level.
The tensor interchange law is what makes independently compiled subterms
compositional.  Search is only over a caller-supplied finite list and its
minimality theorem says exactly that -- never global backend optimality.

Finally, `free_glue_claim_is_false` is a concrete counterexample to scoring
meta-level conjunction for free.  Semantic `Prop` glue can be proof-free while
the materialized backend still needs a recombination equation.  Consequently
this calculus never turns semantic equivalence alone into a performance claim.

This is a standalone construction.  Backend adapters must instantiate
`Fragment`; this file does not pretend that an interaction net or polynomial
table has been emitted merely because its semantics is available.
-/

import Dregg2.Calculus.IntensionalCCCCategory
import Dregg2.Metatheory.CertifiedPresentationFibredCCC
import Dregg2.Metatheory.CertifiedRepresentationSearch

namespace Dregg2.Metatheory.CertifiedIndexedPresentationCompiler

open CategoryTheory
open Dregg2.Metatheory.ArithmetizationCost
open Dregg2.Metatheory.CertifiedPresentationChange
open Dregg2.Metatheory.FOLArithmetizationCorrected

set_option autoImplicit false

/-! ## 1. Resource morphisms -/

/-- A resource morphism says that a target ledger is bounded by a source
ledger plus an explicit overhead.  The overhead is data, not hidden in the
proof, so it can be inspected and ranked by a finite search. -/
structure ResourceMorphism (source target : BackendCost) where
  overhead : BackendCost
  bound : CostLE target (BackendCost.combine source overhead)

namespace ResourceMorphism

variable {a b c d a' b' c' d' : BackendCost}

@[ext]
theorem ext {f g : ResourceMorphism a b} (h : f.overhead = g.overhead) : f = g := by
  cases f
  cases g
  cases h
  rfl

private theorem combine_zero_right (cost : BackendCost) :
    BackendCost.combine cost BackendCost.zero = cost := by
  ext <;> simp [BackendCost.combine, BackendCost.zero]

private theorem zero_combine (cost : BackendCost) :
    BackendCost.combine BackendCost.zero cost = cost := by
  ext <;> simp [BackendCost.combine, BackendCost.zero]

/-- Identity change: no hidden conversion overhead. -/
def id (cost : BackendCost) : ResourceMorphism cost cost where
  overhead := BackendCost.zero
  bound := by
    rw [combine_zero_right]
    exact CostLE.refl cost

/-- Sequential conversion accumulates both explicit overheads. -/
def comp (f : ResourceMorphism a b) (g : ResourceMorphism b c) :
    ResourceMorphism a c where
  overhead := BackendCost.combine f.overhead g.overhead
  bound := by
    refine CostLE.trans g.bound ?_
    have hmono := CostLE.combine_mono_right f.bound g.overhead
    simpa only [BackendCost.combine_assoc] using hmono

/-- Monotonicity of the resource tensor in both arguments. -/
theorem combine_mono (hab : CostLE a b) (hcd : CostLE c d) :
    CostLE (BackendCost.combine a c) (BackendCost.combine b d) := by
  exact ⟨Nat.add_le_add hab.1 hcd.1,
    Nat.add_le_add hab.2.1 hcd.2.1,
    Nat.add_le_add hab.2.2.1 hcd.2.2.1,
    max_le_max hab.2.2.2.1 hcd.2.2.2.1,
    Nat.add_le_add hab.2.2.2.2 hcd.2.2.2.2⟩

/-- Independent subterm conversions tensor.  Both conversion overheads remain
visible in the result. -/
def tensor (f : ResourceMorphism a b) (g : ResourceMorphism c d) :
    ResourceMorphism (BackendCost.combine a c) (BackendCost.combine b d) where
  overhead := BackendCost.combine f.overhead g.overhead
  bound := by
    refine CostLE.trans (combine_mono f.bound g.bound) ?_
    have hreassociate :
        BackendCost.combine
            (BackendCost.combine a f.overhead)
            (BackendCost.combine c g.overhead) =
          BackendCost.combine
            (BackendCost.combine a c)
            (BackendCost.combine f.overhead g.overhead) := by
      ext <;> simp [BackendCost.combine, Nat.add_comm, Nat.add_left_comm,
        max_comm, max_left_comm]
    rw [hreassociate]
    exact CostLE.refl _

/-- Materializing one more backend layer after a compiled fragment. -/
def charge (source extra : BackendCost) :
    ResourceMorphism source (BackendCost.combine source extra) where
  overhead := extra
  bound := CostLE.refl _

/-- Always-valid conservative conversion: charge the entire target ledger as
overhead.  Backend-specific adapters can prove a tighter morphism, but may not
silently assume one. -/
def conservative (source target : BackendCost) : ResourceMorphism source target where
  overhead := target
  bound := CostLE.right_le_combine source target

@[simp]
theorem id_comp (f : ResourceMorphism a b) : comp (id a) f = f := by
  apply ext
  exact zero_combine f.overhead

@[simp]
theorem comp_id (f : ResourceMorphism a b) : comp f (id b) = f := by
  apply ext
  exact combine_zero_right f.overhead

theorem comp_assoc (f : ResourceMorphism a b) (g : ResourceMorphism b c)
    (h : ResourceMorphism c d) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  exact BackendCost.combine_assoc _ _ _

@[simp]
theorem tensor_id (left right : BackendCost) :
    tensor (id left) (id right) = id (BackendCost.combine left right) := by
  apply ext
  rfl

/-- Tensor respects sequential compilation.  This is the ledger-level
interchange law used by the indexed compiler. -/
theorem tensor_comp_interchange
    (f₁ : ResourceMorphism a b) (f₂ : ResourceMorphism b c)
    (g₁ : ResourceMorphism a' b') (g₂ : ResourceMorphism b' c') :
    tensor (comp f₁ f₂) (comp g₁ g₂) =
      comp (tensor f₁ g₁) (tensor f₂ g₂) := by
  apply ext
  ext <;> simp [comp, tensor, BackendCost.combine, Nat.add_comm,
    Nat.add_left_comm, max_comm, max_left_comm]

end ResourceMorphism

/-! ## 2. Indexed certified fragments and explicit conversions -/

/-- Four implementation families which must not be conflated merely because
they can denote the same logical predicate. -/
inductive Mode where
  | densePolynomial
  | booleanGraph
  | interactionNet
  | naturalResidual
  deriving DecidableEq, Repr

instance : Fintype Mode :=
  Fintype.ofList [.densePolynomial, .booleanGraph, .interactionNet, .naturalResidual]
    (by intro x; cases x <;> simp)

/-- One already-constructed backend fragment.  `semanticCertificate` is
proof-relevant assurance at the boundary; `resources` is the materialized
ledger whose costs may not be erased by that proof. -/
structure Fragment {Atom : Type} (truth : Atom → Prop)
    (formula : PositiveFormula Atom) (mode : Mode) where
  accepts : Prop
  resources : BackendCost
  semanticCertificate : accepts ↔ PositiveFormula.Holds truth formula

namespace Fragment

variable {Atom : Type} {truth : Atom → Prop}
variable {formula : PositiveFormula Atom} {sourceMode targetMode finalMode : Mode}

/-- A fragment viewed in the existing global presentation category.  The
statement is `Unit` because the formula index is already fixed. -/
def asPresentation (fragment : Fragment truth formula sourceMode) :
    Presentation Unit where
  meaning := fun _ => PositiveFormula.Holds truth formula
  Evidence := fun _ => Unit
  accepts := fun _ _ => fragment.accepts
  resources := fun _ _ => fragment.resources

/-- A backend conversion consists of the existing exact change of
presentation plus a separately inspectable resource morphism. -/
structure Conversion (source : Fragment truth formula sourceMode)
    (target : Fragment truth formula targetMode) where
  change : Change source.asPresentation target.asPresentation
  resource : ResourceMorphism source.resources target.resources

namespace Conversion

variable {source : Fragment truth formula sourceMode}
variable {middle : Fragment truth formula targetMode}
variable {target : Fragment truth formula finalMode}

@[ext]
theorem ext {f g : Conversion source middle}
    (hchange : f.change = g.change) (hresource : f.resource = g.resource) :
    f = g := by
  cases f
  cases g
  cases hchange
  cases hresource
  rfl

def id (source : Fragment truth formula sourceMode) : Conversion source source where
  change := Change.id _
  resource := ResourceMorphism.id _

def comp (f : Conversion source middle) (g : Conversion middle target) :
    Conversion source target where
  change := Change.comp f.change g.change
  resource := ResourceMorphism.comp f.resource g.resource

@[simp]
theorem id_comp (f : Conversion source middle) : comp (id source) f = f := by
  apply ext
  · exact Change.identity_then_change f.change
  · exact ResourceMorphism.id_comp f.resource

@[simp]
theorem comp_id (f : Conversion source middle) : comp f (id middle) = f := by
  apply ext
  · exact Change.change_then_identity f.change
  · exact ResourceMorphism.comp_id f.resource

theorem comp_assoc {fourthMode : Mode}
    {fourth : Fragment truth formula fourthMode}
    (f : Conversion source middle) (g : Conversion middle target)
    (h : Conversion target fourth) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  · exact Change.change_composition_associative f.change g.change h.change
  · exact ResourceMorphism.comp_assoc f.resource g.resource h.resource

/-- Exact fragment certificates induce the semantic half of a conversion,
but a caller must still supply the resource morphism. -/
def ofResource (source : Fragment truth formula sourceMode)
    (target : Fragment truth formula targetMode)
    (resource : ResourceMorphism source.resources target.resources) :
    Conversion source target where
  change := {
    mapEvidence := fun _ _ => ()
    meaning_iff := fun _ => Iff.rfl
    acceptance_iff := fun _ _ =>
      target.semanticCertificate.trans source.semanticCertificate.symm
    resourceBound := ⟨fun _ => resource.overhead, fun _ _ => resource.bound⟩ }
  resource := resource

theorem acceptance_preserved (conversion : Conversion source target) :
    target.accepts ↔ source.accepts :=
  conversion.change.acceptance_iff () ()

end Conversion

end Fragment

/-! ### Adapters for the already-formalized residual and Boolean graph routes -/

namespace DirectLogicAdapter

open Dregg2.Metatheory.CertifiedPresentationChange.DirectLogic

variable {Atom : Type} {p : Nat} [Fact p.Prime]

/-- An actual proof-carrying no-wrap residual fragment. -/
def naturalResidual (statement : Problem Atom p)
    (formula : PositiveFormula Atom) (evidence : NoWrapEvidence statement formula) :
    Fragment statement.truth formula .naturalResidual where
  accepts := noWrapAccepts statement formula evidence
  resources := ArithmetizationCost.Positive.skeletonCost formula
  semanticCertificate := noWrapAccepts_iff statement formula evidence

/-- An actual materialized inverse-witness Boolean graph fragment. -/
def booleanGraph (statement : Problem Atom p)
    (formula : PositiveFormula Atom) (evidence : BooleanEvidence statement formula) :
    Fragment statement.truth formula .booleanGraph where
  accepts := booleanAccepts statement formula evidence
  resources := ArithmetizationCost.BooleanGraph.cost (toBoolean formula)
  semanticCertificate := booleanAccepts_iff statement formula evidence

/-- Exactness gives the logical part of a residual-to-Boolean conversion.  In
the absence of a tighter backend theorem, this adapter honestly charges the
full Boolean target ledger. -/
def residualToBoolean (statement : Problem Atom p)
    (formula : PositiveFormula Atom) (residualEvidence : NoWrapEvidence statement formula)
    (booleanEvidence : BooleanEvidence statement formula) :
    Fragment.Conversion
      (naturalResidual statement formula residualEvidence)
      (booleanGraph statement formula booleanEvidence) :=
  Fragment.Conversion.ofResource _ _
    (ResourceMorphism.conservative _ _)

theorem residualToBoolean_acceptance (statement : Problem Atom p)
    (formula : PositiveFormula Atom) (residualEvidence : NoWrapEvidence statement formula)
    (booleanEvidence : BooleanEvidence statement formula) :
    (booleanGraph statement formula booleanEvidence).accepts ↔
      (naturalResidual statement formula residualEvidence).accepts :=
  (residualToBoolean statement formula residualEvidence booleanEvidence).acceptance_preserved

end DirectLogicAdapter

/-! ## 3. A fibred compiler with per-subterm choices -/

/-- Recombination is a backend operation, not meta-level punctuation.  Its
input proposition and output meaning are both certified and its cost is
carried explicitly. -/
structure Glue (input output : Prop) where
  accepts : Prop
  inputCertificate : accepts ↔ input
  semanticCertificate : accepts ↔ output
  resources : BackendCost

namespace Glue

/-- A canonical conjunction recombiner.  `resources` is supplied by the
backend adapter; it is never silently chosen as zero. -/
def conjunction (left right : Prop) (resources : BackendCost) :
    Glue (left ∧ right) (left ∧ right) where
  accepts := left ∧ right
  inputCertificate := Iff.rfl
  semanticCertificate := Iff.rfl
  resources := resources

/-- A canonical disjunction recombiner. -/
def disjunction (left right : Prop) (resources : BackendCost) :
    Glue (left ∨ right) (left ∨ right) where
  accepts := left ∨ right
  inputCertificate := Iff.rfl
  semanticCertificate := Iff.rfl
  resources := resources

end Glue

/-- An indexed compilation plan.  `whole` selects one of four presentations
for the current subformula.  `and` and `or` recursively select independent
plans and then perform an explicitly costed backend recombination. -/
inductive Plan {Atom : Type} (truth : Atom → Prop) :
    PositiveFormula Atom → Type
  | whole {formula : PositiveFormula Atom} (mode : Mode)
      (fragment : Fragment truth formula mode) : Plan truth formula
  | and {left right : PositiveFormula Atom}
      (leftPlan : Plan truth left) (rightPlan : Plan truth right)
      (glueCost : BackendCost) : Plan truth (.and left right)
  | or {left right : PositiveFormula Atom}
      (leftPlan : Plan truth left) (rightPlan : Plan truth right)
      (glueCost : BackendCost) : Plan truth (.or left right)

namespace Plan

variable {Atom : Type} {truth : Atom → Prop}

def accepts : {formula : PositiveFormula Atom} → Plan truth formula → Prop
  | _, .whole _ fragment => fragment.accepts
  | _, .and left right _ => left.accepts ∧ right.accepts
  | _, .or left right _ => left.accepts ∨ right.accepts

def resources : {formula : PositiveFormula Atom} → Plan truth formula → BackendCost
  | _, .whole _ fragment => fragment.resources
  | _, .and left right glueCost =>
      BackendCost.combine (BackendCost.combine left.resources right.resources) glueCost
  | _, .or left right glueCost =>
      BackendCost.combine (BackendCost.combine left.resources right.resources) glueCost

/-- The complete semantic preservation theorem for arbitrarily mixed plans. -/
theorem accepts_iff {formula : PositiveFormula Atom} (plan : Plan truth formula) :
    plan.accepts ↔ PositiveFormula.Holds truth formula := by
  induction plan with
  | whole mode fragment => exact fragment.semanticCertificate
  | and left right glueCost ihLeft ihRight =>
      simpa [accepts, PositiveFormula.Holds] using and_congr ihLeft ihRight
  | or left right glueCost ihLeft ihRight =>
      simpa [accepts, PositiveFormula.Holds] using or_congr ihLeft ihRight

/-- A plan is a certified change from a zero-ledger semantic specification to
its materialized backend ledger.  The certificate is derived compositionally:
independent children tensor, then the backend recombination is charged. -/
def materializationMorphism : {formula : PositiveFormula Atom} →
    (plan : Plan truth formula) →
      ResourceMorphism BackendCost.zero plan.resources
  | _, .whole _ fragment => {
      overhead := fragment.resources
      bound := by
        change CostLE fragment.resources
          (BackendCost.combine BackendCost.zero fragment.resources)
        simpa [BackendCost.combine, BackendCost.zero] using
          CostLE.refl fragment.resources }
  | _, .and left right glueCost =>
      ResourceMorphism.comp
        (ResourceMorphism.tensor left.materializationMorphism
          right.materializationMorphism)
        (ResourceMorphism.charge
          (BackendCost.combine left.resources right.resources) glueCost)
  | _, .or left right glueCost =>
      ResourceMorphism.comp
        (ResourceMorphism.tensor left.materializationMorphism
          right.materializationMorphism)
        (ResourceMorphism.charge
          (BackendCost.combine left.resources right.resources) glueCost)

/-- The recursive derivation exposes exactly the same full ledger as the plan;
there is no untracked remainder. -/
theorem materialization_overhead_eq_resources
    {formula : PositiveFormula Atom} (plan : Plan truth formula) :
    plan.materializationMorphism.overhead = plan.resources := by
  induction plan with
  | whole mode fragment => rfl
  | and left right glueCost ihLeft ihRight =>
      change BackendCost.combine
          (BackendCost.combine
            left.materializationMorphism.overhead
            right.materializationMorphism.overhead)
          glueCost = _
      rw [ihLeft, ihRight]
      rfl
  | or left right glueCost ihLeft ihRight =>
      change BackendCost.combine
          (BackendCost.combine
            left.materializationMorphism.overhead
            right.materializationMorphism.overhead)
          glueCost = _
      rw [ihLeft, ihRight]
      rfl

/-- Root observability for auditing a mixed plan. -/
def rootMode? : {formula : PositiveFormula Atom} → Plan truth formula → Option Mode
  | _, .whole mode _ => some mode
  | _, .and _ _ _ => none
  | _, .or _ _ _ => none

/-- Preorder listing of every selected backend mode. -/
def modes : {formula : PositiveFormula Atom} → Plan truth formula → List Mode
  | _, .whole mode _ => [mode]
  | _, .and left right _ => left.modes ++ right.modes
  | _, .or left right _ => left.modes ++ right.modes

/-- The resource recurrence exposes the honest recombination boundary. -/
theorem and_resources {left right : PositiveFormula Atom}
    (leftPlan : Plan truth left) (rightPlan : Plan truth right)
    (glueCost : BackendCost) :
    (Plan.and leftPlan rightPlan glueCost).resources =
      BackendCost.combine
        (BackendCost.combine leftPlan.resources rightPlan.resources) glueCost := rfl

theorem or_resources {left right : PositiveFormula Atom}
    (leftPlan : Plan truth left) (rightPlan : Plan truth right)
    (glueCost : BackendCost) :
    (Plan.or leftPlan rightPlan glueCost).resources =
      BackendCost.combine
        (BackendCost.combine leftPlan.resources rightPlan.resources) glueCost := rfl

/-- The conjunction node carries an inspectable semantic glue certificate in
addition to its resource charge. -/
def andGlueCertificate {left right : PositiveFormula Atom}
    (leftPlan : Plan truth left) (rightPlan : Plan truth right)
    (glueCost : BackendCost) :
    Glue (leftPlan.accepts ∧ rightPlan.accepts)
      (PositiveFormula.Holds truth (.and left right)) where
  accepts := leftPlan.accepts ∧ rightPlan.accepts
  inputCertificate := Iff.rfl
  semanticCertificate := by
    simpa [PositiveFormula.Holds] using
      and_congr (accepts_iff leftPlan) (accepts_iff rightPlan)
  resources := glueCost

/-- The disjunction node has the analogous certificate. -/
def orGlueCertificate {left right : PositiveFormula Atom}
    (leftPlan : Plan truth left) (rightPlan : Plan truth right)
    (glueCost : BackendCost) :
    Glue (leftPlan.accepts ∨ rightPlan.accepts)
      (PositiveFormula.Holds truth (.or left right)) where
  accepts := leftPlan.accepts ∨ rightPlan.accepts
  inputCertificate := Iff.rfl
  semanticCertificate := by
    simpa [PositiveFormula.Holds] using
      or_congr (accepts_iff leftPlan) (accepts_iff rightPlan)
  resources := glueCost

end Plan

/-! ## 4. Finite, explicitly relative search -/

namespace Search

open Dregg2.Metatheory.CertifiedRepresentationSearch

variable {Atom : Type} {truth : Atom → Prop}
variable {formula : PositiveFormula Atom}

def score (plan : Plan truth formula) : Nat :=
  PresentationGraph.totalWork plan.resources

/-- A finite search space is the enumeration itself.  No completeness claim
about all compilers is smuggled into this structure. -/
structure Space (truth : Atom → Prop) (formula : PositiveFormula Atom) where
  candidates : List (Plan truth formula)

def choose? (space : Space truth formula) : Option (Plan truth formula) :=
  selectMin score space.candidates

theorem choose_mem (space : Space truth formula) {best : Plan truth formula}
    (hbest : choose? space = some best) : best ∈ space.candidates :=
  selectMin_mem score hbest

/-- The only optimality theorem: `best` minimizes the declared score among the
explicit finite candidate list. -/
theorem choose_minimal_relative (space : Space truth formula)
    {best : Plan truth formula} (hbest : choose? space = some best) :
    ∀ candidate ∈ space.candidates, score best ≤ score candidate :=
  selectMin_minimal score hbest

/-- Optimization cannot alter source semantics. -/
theorem chosen_accepts_iff (space : Space truth formula)
    {best : Plan truth formula} (_hbest : choose? space = some best) :
    best.accepts ↔ PositiveFormula.Holds truth formula :=
  Plan.accepts_iff best

end Search

/-! ## 5. Honest boundaries and a concrete free-glue counterexample -/

namespace Boundary

def oneEquation : BackendCost := ⟨1, 0, 0, 1, 0⟩

def zeroFragment {Atom : Type} (truth : Atom → Prop)
    (formula : PositiveFormula Atom) (mode : Mode) :
    Fragment truth formula mode where
  accepts := PositiveFormula.Holds truth formula
  resources := BackendCost.zero
  semanticCertificate := Iff.rfl

def conjunctionPlan : Plan (fun _ : Unit => True)
    (.and (.atom ()) (.atom ())) :=
  .and
    (.whole .naturalResidual
      (zeroFragment (fun _ : Unit => True) (.atom ()) .naturalResidual))
    (.whole .interactionNet
      (zeroFragment (fun _ : Unit => True) (.atom ()) .interactionNet))
    oneEquation

/-- The actual backend ledger charges the recombination equation. -/
theorem conjunctionPlan_resources : conjunctionPlan.resources = oneEquation := by
  rfl

/-- The meta-level estimate which incorrectly treats conjunction as free. -/
def freeGlueEstimate : BackendCost := BackendCost.zero

/-- **Counterexample.**  The actual materialized plan is not bounded by the
zero-cost meta-level estimate: its equation and degree coordinates are both
strictly positive. -/
theorem free_glue_claim_is_false :
    ¬ CostLE conjunctionPlan.resources freeGlueEstimate := by
  simp [conjunctionPlan_resources, freeGlueEstimate, oneEquation,
    CostLE, BackendCost.zero]

def conversionSource : Fragment (fun _ : Unit => True) (.atom ())
    .naturalResidual :=
  zeroFragment (fun _ : Unit => True) (.atom ()) .naturalResidual

def conversionTarget : Fragment (fun _ : Unit => True) (.atom ())
    .densePolynomial where
  accepts := True
  resources := oneEquation
  semanticCertificate := by simp [PositiveFormula.Holds]

/-- Exact source meaning does not manufacture a free representation change.
These fragments accept exactly the same formula, but no zero-overhead resource
morphism can materialize the target's equation from the source's zero ledger. -/
theorem exact_semantics_but_no_free_conversion :
    (conversionTarget.accepts ↔ conversionSource.accepts) ∧
      ¬ ∃ conversion : ResourceMorphism conversionSource.resources
          conversionTarget.resources,
        conversion.overhead = BackendCost.zero := by
  constructor
  · simp [conversionTarget, conversionSource, zeroFragment,
      PositiveFormula.Holds]
  · rintro ⟨conversion, hzero⟩
    have hbound := conversion.bound
    rw [hzero] at hbound
    simp [conversionTarget, conversionSource, zeroFragment, oneEquation,
      CostLE, BackendCost.combine, BackendCost.zero] at hbound

/-- Semantics remains exact in the counterexample; the failure is specifically
the backend performance claim, not the logical conjunction. -/
theorem conjunctionPlan_accepts : conjunctionPlan.accepts := by
  exact (Plan.accepts_iff conjunctionPlan).2 (by
    simp [PositiveFormula.Holds])

/-- A four-way mixed plan witnesses that representation choice really is
indexed per subterm rather than fixed once at the root. -/
def fourWayPlan : Plan (fun _ : Fin 4 => True)
    (.and (.and (.atom 0) (.atom 1)) (.or (.atom 2) (.atom 3))) :=
  .and
    (.and
      (.whole .densePolynomial
        (zeroFragment (fun _ : Fin 4 => True) (.atom 0) .densePolynomial))
      (.whole .booleanGraph
        (zeroFragment (fun _ : Fin 4 => True) (.atom 1) .booleanGraph))
      oneEquation)
    (.or
      (.whole .interactionNet
        (zeroFragment (fun _ : Fin 4 => True) (.atom 2) .interactionNet))
      (.whole .naturalResidual
        (zeroFragment (fun _ : Fin 4 => True) (.atom 3) .naturalResidual))
      oneEquation)
    oneEquation

theorem fourWayPlan_modes : fourWayPlan.modes =
    [.densePolynomial, .booleanGraph, .interactionNet, .naturalResidual] := by
  rfl

theorem fourWayPlan_semantics : fourWayPlan.accepts := by
  exact (Plan.accepts_iff fourWayPlan).2 (by simp [PositiveFormula.Holds])

/-- Existing intensional compilation is a genuine strong-CCC implementation
available to an interaction-net adapter; this module does not replace it with
an extensional table. -/
theorem interaction_backend_has_strongCCC :
    Dregg2.Calculus.IntensionalCCCCategory.Compiler.StrongCCCPreservation :=
  Dregg2.Calculus.IntensionalCCCCategory.Compiler.strongCCC

/-- The categorical boundary remains: a global category mixing unrelated
meanings has no weak terminal.  Our indexed compiler therefore lives over one
fixed `truth` interpretation and formula fibre. -/
theorem global_CCC_obstruction_still_applies :
    ¬ ∃ terminal : Presentation Unit,
      Dregg2.Metatheory.CertifiedPresentationFibredCCC.WeakTerminal terminal :=
  Dregg2.Metatheory.CertifiedPresentationFibredCCC.no_weakTerminal

end Boundary

#assert_all_clean [
  ResourceMorphism.ext,
  ResourceMorphism.combine_mono,
  ResourceMorphism.id_comp,
  ResourceMorphism.comp_id,
  ResourceMorphism.comp_assoc,
  ResourceMorphism.tensor_id,
  ResourceMorphism.tensor_comp_interchange,
  Fragment.Conversion.ext,
  Fragment.Conversion.id_comp,
  Fragment.Conversion.comp_id,
  Fragment.Conversion.comp_assoc,
  Fragment.Conversion.acceptance_preserved,
  DirectLogicAdapter.residualToBoolean_acceptance,
  Plan.accepts_iff,
  Plan.materialization_overhead_eq_resources,
  Plan.and_resources,
  Plan.or_resources,
  Search.choose_mem,
  Search.choose_minimal_relative,
  Search.chosen_accepts_iff,
  Boundary.conjunctionPlan_resources,
  Boundary.free_glue_claim_is_false,
  Boundary.exact_semantics_but_no_free_conversion,
  Boundary.conjunctionPlan_accepts,
  Boundary.fourWayPlan_modes,
  Boundary.fourWayPlan_semantics,
  Boundary.interaction_backend_has_strongCCC,
  Boundary.global_CCC_obstruction_still_applies]

end Dregg2.Metatheory.CertifiedIndexedPresentationCompiler

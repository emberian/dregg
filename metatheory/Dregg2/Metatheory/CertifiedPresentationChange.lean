/-
# Certified changes of presentation for direct logic

This module isolates a positive principle suggested by the repaired direct-logic
arithmetizations: a logical predicate is not tied to one constraint language.
Instead, a *presentation* packages source meaning, its evidence type, an
acceptance relation, and an evidence-indexed resource ledger.  A certified
change of presentation maps evidence, preserves source meaning and acceptance
exactly, and carries a compositional resource bound.

The exact changes form a genuine category.  Two weaker interfaces expose the
sound-only and complete-only halves explicitly, so a backend boundary cannot
silently advertise an equivalence when only one direction has been proved.

The abstract calculus is instantiated with three constructions already proved
elsewhere in dregg:

* the natural-residual/no-wrap finite-field route;
* the inverse-witness Boolean constraint graph; and
* a hybrid evidence tree which chooses either route independently at every
  positive subformula.

The no-wrap bound is carried by the evidence.  Consequently this presentation
is complete for true propositions (their exact natural residual is zero) while
never manufacturing a finite-field interpretation for an unsafe false
residual.  The hybrid selector prefers no-wrap at a node exactly when its local
bound is certified, and otherwise recursively splits conjunctions/disjunctions
or falls back to the Boolean graph.  Its acceptance theorem is exact for every
such mixed tree.

Standalone construction: no integration root is modified.  Pure; no axioms.
-/

import Mathlib.CategoryTheory.Category.Basic
import Dregg2.Logic.BoolGraph
import Dregg2.Metatheory.ArithmetizationCost
import Dregg2.Metatheory.FOLArithmetizationCorrected
import Dregg2.Tactics

namespace Dregg2.Metatheory.CertifiedPresentationChange

open CategoryTheory
open Dregg2.Metatheory.FOLArithmetizationCorrected
open Dregg2.Metatheory.ArithmetizationCost

set_option autoImplicit false

/-! ## 1. Resource-aware presentations -/

/-- Componentwise comparison of symbolic backend costs.  Maximum degree is a
coordinate in the order; it is not added when fragments are combined. -/
def CostLE (left right : BackendCost) : Prop :=
  left.equations ≤ right.equations ∧
  left.multiplications ≤ right.multiplications ∧
  left.witnesses ≤ right.witnesses ∧
  left.maxDegree ≤ right.maxDegree ∧
  left.tableCells ≤ right.tableCells

namespace CostLE

theorem refl (cost : BackendCost) : CostLE cost cost := by
  exact ⟨Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _, Nat.le_refl _⟩

theorem trans {a b c : BackendCost} (hab : CostLE a b) (hbc : CostLE b c) :
    CostLE a c := by
  exact ⟨Nat.le_trans hab.1 hbc.1,
    Nat.le_trans hab.2.1 hbc.2.1,
    Nat.le_trans hab.2.2.1 hbc.2.2.1,
    Nat.le_trans hab.2.2.2.1 hbc.2.2.2.1,
    Nat.le_trans hab.2.2.2.2 hbc.2.2.2.2⟩

theorem combine_mono_right {a b : BackendCost} (hab : CostLE a b)
    (extra : BackendCost) :
    CostLE (BackendCost.combine a extra) (BackendCost.combine b extra) := by
  exact ⟨Nat.add_le_add_right hab.1 _,
    Nat.add_le_add_right hab.2.1 _,
    Nat.add_le_add_right hab.2.2.1 _,
    max_le_max_right _ hab.2.2.2.1,
    Nat.add_le_add_right hab.2.2.2.2 _⟩

theorem left_le_combine (left right : BackendCost) :
    CostLE left (BackendCost.combine left right) := by
  exact ⟨Nat.le_add_right _ _, Nat.le_add_right _ _, Nat.le_add_right _ _,
    le_max_left _ _, Nat.le_add_right _ _⟩

theorem right_le_combine (left right : BackendCost) :
    CostLE right (BackendCost.combine left right) := by
  exact ⟨Nat.le_add_left _ _, Nat.le_add_left _ _, Nat.le_add_left _ _,
    le_max_right _ _, Nat.le_add_left _ _⟩

theorem combine_zero (cost : BackendCost) :
    CostLE cost (BackendCost.combine cost BackendCost.zero) := by
  simpa [BackendCost.combine, BackendCost.zero] using refl cost

end CostLE

/-- A presentation of predicates over a fixed statement language.  Meaning is
part of the object rather than ambient prose; evidence and cost may depend on
the particular statement and witness. -/
structure Presentation (Statement : Type) where
  meaning : Statement → Prop
  Evidence : Statement → Type
  accepts : (statement : Statement) → Evidence statement → Prop
  resources : (statement : Statement) → Evidence statement → BackendCost

namespace Presentation

variable {Statement : Type}

/-- Every accepting witness denotes a true source statement. -/
def Sound (P : Presentation Statement) : Prop :=
  ∀ statement evidence, P.accepts statement evidence → P.meaning statement

/-- Every true source statement has an accepting witness. -/
def Complete (P : Presentation Statement) : Prop :=
  ∀ statement, P.meaning statement →
    ∃ evidence : P.Evidence statement, P.accepts statement evidence

/-- A presentation is exact when it is both sound and complete. -/
def Exact (P : Presentation Statement) : Prop := P.Sound ∧ P.Complete

end Presentation

/-! ## 2. Exact, sound-only, and complete-only changes -/

/-- A sound-only presentation change cannot introduce an accepting target
witness from a rejecting source witness. -/
structure SoundChange {Statement : Type}
    (P Q : Presentation Statement) where
  mapEvidence : ∀ statement, P.Evidence statement → Q.Evidence statement
  meaning_iff : ∀ statement, Q.meaning statement ↔ P.meaning statement
  acceptance_sound : ∀ statement evidence,
    Q.accepts statement (mapEvidence statement evidence) →
      P.accepts statement evidence

/-- A complete-only change cannot lose acceptance. -/
structure CompleteChange {Statement : Type}
    (P Q : Presentation Statement) where
  mapEvidence : ∀ statement, P.Evidence statement → Q.Evidence statement
  meaning_iff : ∀ statement, Q.meaning statement ↔ P.meaning statement
  acceptance_complete : ∀ statement evidence,
    P.accepts statement evidence →
      Q.accepts statement (mapEvidence statement evidence)

/-- An exact certified change of presentation.  Resource overhead is
existential/proof-relevant only at certification time, so arrow equality is
the actual witness transformer rather than an arbitrary choice of bound. -/
structure Change {Statement : Type} (P Q : Presentation Statement) where
  mapEvidence : ∀ statement, P.Evidence statement → Q.Evidence statement
  meaning_iff : ∀ statement, Q.meaning statement ↔ P.meaning statement
  acceptance_iff : ∀ statement evidence,
    Q.accepts statement (mapEvidence statement evidence) ↔
      P.accepts statement evidence
  resourceBound : ∃ overhead : Statement → BackendCost,
    ∀ statement evidence,
      CostLE (Q.resources statement (mapEvidence statement evidence))
        (BackendCost.combine (P.resources statement evidence) (overhead statement))

namespace Change

variable {Statement : Type}
variable {P Q R S : Presentation Statement}

instance (P Q : Presentation Statement) : CoeFun (Change P Q)
    (fun _ => ∀ statement, P.Evidence statement → Q.Evidence statement) :=
  ⟨Change.mapEvidence⟩

@[ext]
theorem ext {f g : Change P Q} (h : f.mapEvidence = g.mapEvidence) : f = g := by
  cases f with
  | mk ff fmeaning faccept fcost =>
    cases g with
    | mk gg gmeaning gaccept gcost =>
      cases h
      rfl

/-- Forget the completeness half of an exact change. -/
def toSound (f : Change P Q) : SoundChange P Q where
  mapEvidence := f.mapEvidence
  meaning_iff := f.meaning_iff
  acceptance_sound statement evidence := (f.acceptance_iff statement evidence).mp

/-- Forget the soundness half of an exact change. -/
def toComplete (f : Change P Q) : CompleteChange P Q where
  mapEvidence := f.mapEvidence
  meaning_iff := f.meaning_iff
  acceptance_complete statement evidence := (f.acceptance_iff statement evidence).mpr

def id (P : Presentation Statement) : Change P P where
  mapEvidence := fun _ evidence => evidence
  meaning_iff := fun _ => Iff.rfl
  acceptance_iff := fun _ _ => Iff.rfl
  resourceBound := ⟨fun _ => BackendCost.zero, fun _ evidence =>
    CostLE.combine_zero (P.resources _ evidence)⟩

def comp (f : Change P Q) (g : Change Q R) : Change P R where
  mapEvidence := fun statement evidence =>
    g.mapEvidence statement (f.mapEvidence statement evidence)
  meaning_iff := fun statement =>
    (g.meaning_iff statement).trans (f.meaning_iff statement)
  acceptance_iff := fun statement evidence =>
    (g.acceptance_iff statement (f.mapEvidence statement evidence)).trans
      (f.acceptance_iff statement evidence)
  resourceBound := by
    rcases f.resourceBound with ⟨fOverhead, hf⟩
    rcases g.resourceBound with ⟨gOverhead, hg⟩
    refine ⟨fun statement =>
      BackendCost.combine (fOverhead statement) (gOverhead statement), ?_⟩
    intro statement evidence
    refine CostLE.trans (hg statement (f.mapEvidence statement evidence)) ?_
    have hmono := CostLE.combine_mono_right (hf statement evidence)
      (gOverhead statement)
    simpa only [BackendCost.combine_assoc] using hmono

/-- Certified presentation changes form a genuine category. -/
instance categoryPresentation : Category (Presentation Statement) where
  Hom := Change
  id := id
  comp := comp
  id_comp := by
    intro X Y f
    apply ext
    rfl
  comp_id := by
    intro X Y f
    apply ext
    rfl
  assoc := by
    intro W X Y Z f g h
    apply ext
    rfl

@[simp]
theorem id_apply (P : Presentation Statement) (statement : Statement)
    (evidence : P.Evidence statement) :
    (𝟙 P : P ⟶ P).mapEvidence statement evidence = evidence := rfl

@[simp]
theorem comp_apply (f : P ⟶ Q) (g : Q ⟶ R) (statement : Statement)
    (evidence : P.Evidence statement) :
    (f ≫ g).mapEvidence statement evidence =
      g.mapEvidence statement (f.mapEvidence statement evidence) := rfl

theorem identity_then_change (f : Change P Q) : comp (id P) f = f := by
  apply ext
  rfl

theorem change_then_identity (f : Change P Q) : comp f (id Q) = f := by
  apply ext
  rfl

theorem change_composition_associative (f : Change P Q) (g : Change Q R)
    (h : Change R S) :
    comp (comp f g) h = comp f (comp g h) := by
  apply ext
  rfl

/-- Exact arrows may preserve different proof objects, but all parallel arrows
agree on the observable acceptance result. -/
def ObservationallyEquivalent (f g : Change P Q) : Prop :=
  ∀ statement evidence,
    Q.accepts statement (f.mapEvidence statement evidence) ↔
      Q.accepts statement (g.mapEvidence statement evidence)

theorem all_parallel_observationallyEquivalent (f g : Change P Q) :
    ObservationallyEquivalent f g := by
  intro statement evidence
  exact (f.acceptance_iff statement evidence).trans
    (g.acceptance_iff statement evidence).symm

end Change

/-! ## 3. A shared positive-formula problem family -/

namespace DirectLogic

open PositiveFormula
open Dregg2.Logic.BoolGraph

variable {Atom : Type}
variable {p : Nat} [Fact p.Prime]

/-- A direct-logic statement carries the atom semantics and exact natural
residuals.  The per-atom `< p` premise is precisely what makes the Boolean
graph's field zero tests agree with source atoms.  No whole-formula no-wrap
claim is assumed. -/
structure Problem (Atom : Type) (p : Nat) where
  truth : Atom → Prop
  atomResidual : Atom → Nat
  atomCorrect : ∀ atom, atomResidual atom = 0 ↔ truth atom
  atomBound : ∀ atom, atomResidual atom < p
  formula : PositiveFormula Atom

/-- Translate the positive source into the existing one-means-true Boolean
graph language. -/
def toBoolean : PositiveFormula Atom → Dregg2.Logic.BoolGraph.Formula Atom
  | PositiveFormula.top => Dregg2.Logic.BoolGraph.Formula.top
  | PositiveFormula.bottom => Dregg2.Logic.BoolGraph.Formula.bot
  | PositiveFormula.atom a => Dregg2.Logic.BoolGraph.Formula.atom a
  | PositiveFormula.and left right =>
      Dregg2.Logic.BoolGraph.Formula.and (toBoolean left) (toBoolean right)
  | PositiveFormula.or left right =>
      Dregg2.Logic.BoolGraph.Formula.or (toBoolean left) (toBoolean right)

def fieldAtom (statement : Problem Atom p) (atom : Atom) : ZMod p :=
  statement.atomResidual atom

/-- The source semantics is shared by all three presentations below. -/
def Meaning (statement : Problem Atom p) : Prop :=
  Holds statement.truth statement.formula

theorem eval_toBoolean_iff (statement : Problem Atom p)
    (formula : PositiveFormula Atom) :
    Eval (fieldAtom statement) (toBoolean formula) ↔
      Holds statement.truth formula := by
  induction formula with
  | top => simp [toBoolean, Dregg2.Logic.BoolGraph.Eval, Holds]
  | bottom => simp [toBoolean, Dregg2.Logic.BoolGraph.Eval, Holds]
  | atom atom =>
      change ((statement.atomResidual atom : ZMod p) = 0) ↔
        statement.truth atom
      rw [zmod_natCast_eq_zero_iff_of_lt (statement.atomBound atom)]
      exact statement.atomCorrect atom
  | and left right ihLeft ihRight =>
      simp only [toBoolean, Dregg2.Logic.BoolGraph.Eval, Holds, ihLeft, ihRight]
  | or left right ihLeft ihRight =>
      simp only [toBoolean, Dregg2.Logic.BoolGraph.Eval, Holds, ihLeft, ihRight]

/-! ## 4. Concrete presentation A: proof-carrying no-wrap -/

/-- A no-wrap certificate is evidence.  It can exist locally even when a
parent formula has no safe additive/product residual. -/
def NoWrapEvidence (statement : Problem Atom p)
    (formula : PositiveFormula Atom) : Type :=
  { _unit : Unit //
    PositiveFormula.residual statement.atomResidual formula < p }

def noWrapAccepts (statement : Problem Atom p) (formula : PositiveFormula Atom)
    (_evidence : NoWrapEvidence statement formula) : Prop :=
  ((↑(PositiveFormula.residual statement.atomResidual formula : Nat) : ZMod p) = 0)

theorem noWrapAccepts_iff (statement : Problem Atom p)
    (formula : PositiveFormula Atom) (evidence : NoWrapEvidence statement formula) :
    noWrapAccepts statement formula evidence ↔
      Holds statement.truth formula := by
  exact natural_residual_cast_sound statement.truth statement.atomResidual
    statement.atomCorrect formula evidence.property

def noWrapPresentation : Presentation (Problem Atom p) where
  meaning := Meaning
  Evidence := fun statement => NoWrapEvidence statement statement.formula
  accepts := fun statement evidence =>
    noWrapAccepts statement statement.formula evidence
  resources := fun statement _ =>
    ArithmetizationCost.Positive.skeletonCost statement.formula

theorem noWrap_sound : (noWrapPresentation (Atom := Atom) (p := p)).Sound := by
  intro statement evidence haccept
  exact (noWrapAccepts_iff statement statement.formula evidence).mp haccept

/-- True formulas always have a no-wrap witness: their exact natural
residual is literally zero, hence below every prime modulus. -/
theorem noWrap_complete :
    (noWrapPresentation (Atom := Atom) (p := p)).Complete := by
  intro statement hmeaning
  have hzero : PositiveFormula.residual statement.atomResidual statement.formula = 0 :=
    (PositiveFormula.residual_eq_zero_iff naturalLaws statement.truth
      statement.atomResidual (fun _ => trivial) statement.atomCorrect
      statement.formula).mpr hmeaning
  have hp : 0 < p := (Fact.out : p.Prime).pos
  let evidence : NoWrapEvidence statement statement.formula :=
    ⟨(), by simpa [hzero] using hp⟩
  exact ⟨evidence, (noWrapAccepts_iff statement statement.formula evidence).mpr hmeaning⟩

theorem noWrap_exact :
    (noWrapPresentation (Atom := Atom) (p := p)).Exact :=
  ⟨noWrap_sound, noWrap_complete⟩

/-! ## 5. Concrete presentation B: inverse-witness Boolean graph -/

/-- Evidence is a complete satisfying assignment for the existing relational
Boolean graph, including all intermediate and inverse witnesses. -/
structure BooleanEvidence (statement : Problem Atom p)
    (formula : PositiveFormula Atom) where
  out : ZMod p
  graph : Graph (fieldAtom statement) (toBoolean formula) out

def booleanAccepts (statement : Problem Atom p) (formula : PositiveFormula Atom)
    (evidence : BooleanEvidence statement formula) : Prop :=
  evidence.out = 1

theorem booleanAccepts_iff (statement : Problem Atom p)
    (formula : PositiveFormula Atom) (evidence : BooleanEvidence statement formula) :
    booleanAccepts statement formula evidence ↔
      Holds statement.truth formula := by
  exact (graph_sound evidence.graph).2.trans (eval_toBoolean_iff statement formula)

noncomputable def canonicalBooleanEvidence (statement : Problem Atom p)
    (formula : PositiveFormula Atom) : BooleanEvidence statement formula := by
  classical
  let chosen := Classical.choose
    (graph_complete (fieldAtom statement) (toBoolean formula))
  exact ⟨chosen,
    Classical.choose_spec (graph_complete (fieldAtom statement) (toBoolean formula))⟩

def booleanPresentation : Presentation (Problem Atom p) where
  meaning := Meaning
  Evidence := fun statement => BooleanEvidence statement statement.formula
  accepts := fun statement evidence =>
    booleanAccepts statement statement.formula evidence
  resources := fun statement _ =>
    ArithmetizationCost.BooleanGraph.cost (toBoolean statement.formula)

theorem boolean_sound : (booleanPresentation (Atom := Atom) (p := p)).Sound := by
  intro statement evidence haccept
  exact (booleanAccepts_iff statement statement.formula evidence).mp haccept

theorem boolean_complete :
    (booleanPresentation (Atom := Atom) (p := p)).Complete := by
  intro statement hmeaning
  let evidence := canonicalBooleanEvidence statement statement.formula
  exact ⟨evidence,
    (booleanAccepts_iff statement statement.formula evidence).mpr hmeaning⟩

theorem boolean_exact :
    (booleanPresentation (Atom := Atom) (p := p)).Exact :=
  ⟨boolean_sound, boolean_complete⟩

/-! ## 6. Concrete presentation C: per-subformula hybrid evidence -/

/-- A hybrid proof plan.  Each node may use a certified natural no-wrap gate,
an exact Boolean graph, or split into independently selected children. -/
inductive HybridEvidence (statement : Problem Atom p) :
    PositiveFormula Atom → Type
  | noWrap (formula : PositiveFormula Atom)
      (bound : PositiveFormula.residual statement.atomResidual formula < p) :
      HybridEvidence statement formula
  | boolean (formula : PositiveFormula Atom) (out : ZMod p)
      (graph : Graph (fieldAtom statement) (toBoolean formula) out) :
      HybridEvidence statement formula
  | and {left right : PositiveFormula Atom} :
      HybridEvidence statement left → HybridEvidence statement right →
      HybridEvidence statement (.and left right)
  | or {left right : PositiveFormula Atom} :
      HybridEvidence statement left → HybridEvidence statement right →
      HybridEvidence statement (.or left right)

def HybridEvidence.accepts {statement : Problem Atom p} :
    {formula : PositiveFormula Atom} → HybridEvidence statement formula → Prop
  | _, .noWrap formula _ =>
      ((↑(PositiveFormula.residual statement.atomResidual formula : Nat) : ZMod p) = 0)
  | _, .boolean _ out _ => out = 1
  | _, .and left right => left.accepts ∧ right.accepts
  | _, .or left right => left.accepts ∨ right.accepts

def HybridEvidence.resources {statement : Problem Atom p} :
    {formula : PositiveFormula Atom} → HybridEvidence statement formula → BackendCost
  | _, .noWrap formula _ => ArithmetizationCost.Positive.skeletonCost formula
  | _, .boolean formula _ _ => ArithmetizationCost.BooleanGraph.cost (toBoolean formula)
  | _, .and left right => BackendCost.combine left.resources right.resources
  | _, .or left right => BackendCost.combine left.resources right.resources

/-- **Hybrid selection theorem.**  Every independently mixed evidence tree is
exact; the proof is structural and imposes no uniform backend choice. -/
theorem HybridEvidence.accepts_iff {statement : Problem Atom p}
    {formula : PositiveFormula Atom} (evidence : HybridEvidence statement formula) :
    evidence.accepts ↔ Holds statement.truth formula := by
  induction evidence with
  | noWrap formula bound =>
      exact natural_residual_cast_sound statement.truth statement.atomResidual
        statement.atomCorrect formula bound
  | boolean formula out graph =>
      exact (graph_sound graph).2.trans (eval_toBoolean_iff statement formula)
  | and left right ihLeft ihRight =>
      simpa [HybridEvidence.accepts, Holds] using and_congr ihLeft ihRight
  | or left right ihLeft ihRight =>
      simpa [HybridEvidence.accepts, Holds] using or_congr ihLeft ihRight

/-- Observable strategy at the root of a hybrid evidence tree. -/
inductive RootStrategy where
  | noWrap
  | boolean
  | split
  deriving DecidableEq, Repr

def HybridEvidence.rootStrategy {statement : Problem Atom p}
    {formula : PositiveFormula Atom} : HybridEvidence statement formula → RootStrategy
  | .noWrap _ _ => .noWrap
  | .boolean _ _ _ => .boolean
  | .and _ _ => .split
  | .or _ _ => .split

/-- A total, executable-in-the-kernel policy: prefer a locally certified
no-wrap node; otherwise split positive connectives; otherwise use the total
Boolean graph. -/
noncomputable def selectLocal (statement : Problem Atom p) :
    (formula : PositiveFormula Atom) → HybridEvidence statement formula
  | .top =>
      if h : PositiveFormula.residual statement.atomResidual .top < p then
        .noWrap .top h
      else
        let evidence := canonicalBooleanEvidence statement .top
        .boolean .top evidence.out evidence.graph
  | .bottom =>
      if h : PositiveFormula.residual statement.atomResidual .bottom < p then
        .noWrap .bottom h
      else
        let evidence := canonicalBooleanEvidence statement .bottom
        .boolean .bottom evidence.out evidence.graph
  | PositiveFormula.atom a =>
      if h : PositiveFormula.residual statement.atomResidual (.atom a) < p then
        .noWrap (.atom a) h
      else
        let evidence := canonicalBooleanEvidence statement (.atom a)
        .boolean (.atom a) evidence.out evidence.graph
  | .and left right =>
      if h : PositiveFormula.residual statement.atomResidual (.and left right) < p then
        .noWrap (.and left right) h
      else
        .and (selectLocal statement left) (selectLocal statement right)
  | .or left right =>
      if h : PositiveFormula.residual statement.atomResidual (.or left right) < p then
        .noWrap (.or left right) h
      else
        .or (selectLocal statement left) (selectLocal statement right)

theorem selectLocal_prefers_noWrap (statement : Problem Atom p)
    (formula : PositiveFormula Atom)
    (hbound : PositiveFormula.residual statement.atomResidual formula < p) :
    (selectLocal statement formula).rootStrategy = .noWrap := by
  cases formula <;> simp [selectLocal, hbound, HybridEvidence.rootStrategy]

theorem selectLocal_splits_unsafe_and (statement : Problem Atom p)
    (left right : PositiveFormula Atom)
    (hunsafe : ¬ PositiveFormula.residual statement.atomResidual (.and left right) < p) :
    (selectLocal statement (.and left right)).rootStrategy = .split := by
  simp [selectLocal, hunsafe, HybridEvidence.rootStrategy]

theorem selectLocal_splits_unsafe_or (statement : Problem Atom p)
    (left right : PositiveFormula Atom)
    (hunsafe : ¬ PositiveFormula.residual statement.atomResidual (.or left right) < p) :
    (selectLocal statement (.or left right)).rootStrategy = .split := by
  simp [selectLocal, hunsafe, HybridEvidence.rootStrategy]

/-- A genuinely mixed selection: an unsafe conjunction is split, while each
safe child is independently compiled by the no-wrap route. -/
theorem selectLocal_unsafe_and_safe_children (statement : Problem Atom p)
    (left right : PositiveFormula Atom)
    (hunsafe : ¬ PositiveFormula.residual statement.atomResidual (.and left right) < p)
    (hleft : PositiveFormula.residual statement.atomResidual left < p)
    (hright : PositiveFormula.residual statement.atomResidual right < p) :
    selectLocal statement (.and left right) =
        .and (selectLocal statement left) (selectLocal statement right) ∧
      (selectLocal statement left).rootStrategy = .noWrap ∧
      (selectLocal statement right).rootStrategy = .noWrap := by
  refine ⟨by simp [selectLocal, hunsafe], ?_, ?_⟩
  · exact selectLocal_prefers_noWrap statement left hleft
  · exact selectLocal_prefers_noWrap statement right hright

theorem selectLocal_accepts_iff (statement : Problem Atom p)
    (formula : PositiveFormula Atom) :
    (selectLocal statement formula).accepts ↔
      Holds statement.truth formula :=
  HybridEvidence.accepts_iff (selectLocal statement formula)

def hybridPresentation : Presentation (Problem Atom p) where
  meaning := Meaning
  Evidence := fun statement => HybridEvidence statement statement.formula
  accepts := fun _ evidence => evidence.accepts
  resources := fun _ evidence => evidence.resources

theorem hybrid_sound : (hybridPresentation (Atom := Atom) (p := p)).Sound := by
  intro statement evidence haccept
  exact (HybridEvidence.accepts_iff evidence).mp haccept

theorem hybrid_complete :
    (hybridPresentation (Atom := Atom) (p := p)).Complete := by
  intro statement hmeaning
  let evidence := selectLocal statement statement.formula
  exact ⟨evidence, (HybridEvidence.accepts_iff evidence).mpr hmeaning⟩

theorem hybrid_exact :
    (hybridPresentation (Atom := Atom) (p := p)).Exact :=
  ⟨hybrid_sound, hybrid_complete⟩

/-! ## 7. Nontrivial certified changes between the concrete presentations -/

noncomputable def noWrapToBoolean :
    Change (noWrapPresentation (Atom := Atom) (p := p))
      (booleanPresentation (Atom := Atom) (p := p)) where
  mapEvidence := fun statement _ =>
    canonicalBooleanEvidence statement statement.formula
  meaning_iff := fun _ => Iff.rfl
  acceptance_iff := by
    intro statement evidence
    change booleanAccepts statement statement.formula
        (canonicalBooleanEvidence statement statement.formula) ↔
      noWrapAccepts statement statement.formula evidence
    exact (booleanAccepts_iff statement statement.formula _).trans
      (noWrapAccepts_iff statement statement.formula evidence).symm
  resourceBound := by
    refine ⟨fun statement =>
      ArithmetizationCost.BooleanGraph.cost (toBoolean statement.formula), ?_⟩
    intro statement evidence
    exact CostLE.right_le_combine
      (ArithmetizationCost.Positive.skeletonCost statement.formula)
      (ArithmetizationCost.BooleanGraph.cost (toBoolean statement.formula))

def noWrapToHybrid :
    Change (noWrapPresentation (Atom := Atom) (p := p))
      (hybridPresentation (Atom := Atom) (p := p)) where
  mapEvidence := fun statement evidence =>
    .noWrap statement.formula evidence.property
  meaning_iff := fun _ => Iff.rfl
  acceptance_iff := by
    intro statement evidence
    change noWrapAccepts statement statement.formula evidence ↔
      noWrapAccepts statement statement.formula evidence
    exact Iff.rfl
  resourceBound := by
    refine ⟨fun _ => BackendCost.zero, ?_⟩
    intro statement evidence
    exact CostLE.combine_zero
      (ArithmetizationCost.Positive.skeletonCost statement.formula)

def booleanToHybrid :
    Change (booleanPresentation (Atom := Atom) (p := p))
      (hybridPresentation (Atom := Atom) (p := p)) where
  mapEvidence := fun statement evidence =>
    .boolean statement.formula evidence.out evidence.graph
  meaning_iff := fun _ => Iff.rfl
  acceptance_iff := by
    intro statement evidence
    change booleanAccepts statement statement.formula evidence ↔
      booleanAccepts statement statement.formula evidence
    exact Iff.rfl
  resourceBound := by
    refine ⟨fun _ => BackendCost.zero, ?_⟩
    intro statement evidence
    exact CostLE.combine_zero
      (ArithmetizationCost.BooleanGraph.cost (toBoolean statement.formula))

/-- The direct no-wrap-to-hybrid route and the route through a Boolean graph
produce different proof objects, but are provably indistinguishable at the
acceptance boundary. -/
theorem noWrap_boolean_hybrid_triangle :
    Change.ObservationallyEquivalent
      (Change.comp (noWrapToBoolean (Atom := Atom) (p := p))
        (booleanToHybrid (Atom := Atom) (p := p)))
      (noWrapToHybrid (Atom := Atom) (p := p)) :=
  Change.all_parallel_observationallyEquivalent _ _

#assert_all_clean [
  CostLE.refl,
  CostLE.trans,
  CostLE.combine_mono_right,
  Change.ext,
  Change.identity_then_change,
  Change.change_then_identity,
  Change.change_composition_associative,
  Change.all_parallel_observationallyEquivalent,
  eval_toBoolean_iff,
  noWrapAccepts_iff,
  noWrap_sound,
  noWrap_complete,
  noWrap_exact,
  booleanAccepts_iff,
  boolean_sound,
  boolean_complete,
  boolean_exact,
  HybridEvidence.accepts_iff,
  selectLocal_prefers_noWrap,
  selectLocal_splits_unsafe_and,
  selectLocal_splits_unsafe_or,
  selectLocal_unsafe_and_safe_children,
  selectLocal_accepts_iff,
  hybrid_sound,
  hybrid_complete,
  hybrid_exact,
  noWrap_boolean_hybrid_triangle]

end DirectLogic

end Dregg2.Metatheory.CertifiedPresentationChange

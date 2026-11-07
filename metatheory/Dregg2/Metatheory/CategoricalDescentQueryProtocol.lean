/-
# Dregg2.Metatheory.CategoricalDescentQueryProtocol

This module isolates the categorical part of a local-query proof protocol from its
cryptographic realization.

The presentation-independent content is a finite coverage presentation: an invalid
family has at least one locally detectable obstruction.  Presentations and exact
changes of presentation form a category.  Obstruction predicates, miss events, and
protocols are natural under its morphisms, including a proved composition law.

The cryptographic content remains explicit and separate:

* `QueryOpeningScheme` and `PointBinding` model commitment/opening binding;
* `AcceptanceReduction` is the algebraic/OOD/low-degree reduction socket;
* `SamplerBound` is the finite transcript/query-sampling term; and
* OOD and low-degree budgets remain independent hypotheses.

Thus the categorical layer does not replace commitments, Fiat--Shamir, polynomials,
or FRI.  It says which local-to-global statement those mechanisms may instantiate.
The final section instantiates the construction to the existing finite patch-code
descent, including its nontrivial weighted-star counterexample.
-/
import Dregg2.Metatheory.RobustDescentTranscriptGame
import Dregg2.Metatheory.FinitePatchCodeDescent
import Dregg2.Realizability.Assemblies
import Mathlib.CategoryTheory.Category.Basic

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Metatheory.CategoricalDescentQueryProtocol

open CategoryTheory
open Dregg2.Metatheory.ProofObjectDescent
open Dregg2.Metatheory.RobustProofObjectDescent
open Dregg2.Metatheory.RobustDescentQueryGame
open Dregg2.Metatheory.RobustDescentTranscriptGame
open Dregg2.Metatheory.FinitePatchCodeDescent

universe u q v d p s

/-! ## 1. Coverage presentations form a category -/

/-- A finite presentation of one fixed invalidity predicate by local queries.

`detects` is the sheaf/code-theoretic tooth: invalidity has a local obstruction.
It contains no commitment, transcript, polynomial, or sampling assumption. -/
structure CoveragePresentation (Family : Type u) (Invalid : Family → Prop) where
  Query : Type q
  queryFintype : Fintype Query
  queryDecidableEq : DecidableEq Query
  bad : Family → Query → Prop
  badDecidable : ∀ family query, Decidable (bad family query)
  detects : ∀ family, Invalid family → ∃ query, bad family query

namespace CoveragePresentation

variable {Family : Type u} {Invalid : Family → Prop}

instance (P : CoveragePresentation.{u, q} Family Invalid) : Fintype P.Query :=
  P.queryFintype

instance (P : CoveragePresentation.{u, q} Family Invalid) : DecidableEq P.Query :=
  P.queryDecidableEq

/-- A change of coverage presentation is contravariant on queries: a query in the
target presentation is interpreted as a query in the source presentation.  Exact
reflection of `bad` is the naturality square. -/
structure Hom (P Q : CoveragePresentation.{u, q} Family Invalid) where
  map : Q.Query → P.Query
  bad_iff : ∀ family query, Q.bad family query ↔ P.bad family (map query)

@[ext]
theorem Hom.ext {P Q : CoveragePresentation.{u, q} Family Invalid}
    {f g : Hom P Q} (h : f.map = g.map) : f = g := by
  cases f
  cases g
  cases h
  rfl

/-- Coverage presentations and exact presentation maps form a genuine category. -/
instance categoryCoveragePresentation :
    Category (CoveragePresentation.{u, q} Family Invalid) where
  Hom := Hom
  id P :=
    { map := id
      bad_iff := fun _ _ => Iff.rfl }
  comp f g :=
    { map := f.map ∘ g.map
      bad_iff := fun family query =>
        (g.bad_iff family query).trans (f.bad_iff family (g.map query)) }
  id_comp f := Hom.ext rfl
  comp_id f := Hom.ext rfl
  assoc f g h := Hom.ext rfl

@[simp]
theorem id_map (P : CoveragePresentation.{u, q} Family Invalid) (query : P.Query) :
    (𝟙 P : P ⟶ P).map query = query := rfl

@[simp]
theorem comp_map {P Q R : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (g : Q ⟶ R) (query : R.Query) :
    (f ≫ g).map query = f.map (g.map query) := rfl

/-- The obstruction predicate attached to a presentation. -/
def obstruction (P : CoveragePresentation.{u, q} Family Invalid)
    (family : Family) : P.Query → Prop :=
  P.bad family

/-- The finite obstruction set attached to a presentation. -/
noncomputable def badSet (P : CoveragePresentation.{u, q} Family Invalid)
    (family : Family) : Finset P.Query := by
  classical
  exact Finset.univ.filter (P.bad family)

@[simp]
theorem mem_badSet (P : CoveragePresentation.{u, q} Family Invalid)
    (family : Family) (query : P.Query) :
    query ∈ P.badSet family ↔ P.bad family query := by
  simp [badSet]

/-- Local cover detection makes the obstruction set nonempty. -/
theorem badSet_nonempty (P : CoveragePresentation.{u, q} Family Invalid)
    (family : Family) (hinvalid : Invalid family) :
    (P.badSet family).Nonempty := by
  obtain ⟨query, hbad⟩ := P.detects family hinvalid
  exact ⟨query, (P.mem_badSet family query).2 hbad⟩

/-- **NATURALITY OF LOCAL OBSTRUCTIONS.** Reindexing a target query through a
presentation map preserves and reflects the obstruction predicate exactly. -/
theorem obstruction_natural {P Q : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (family : Family) :
    Q.obstruction family = P.obstruction family ∘ f.map := by
  funext query
  exact propext (f.bad_iff family query)

/-- Finite-set membership is the same naturality square.  We do not claim cardinalities
are preserved: a presentation map may duplicate source queries. -/
theorem mem_badSet_natural {P Q : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (family : Family) (query : Q.Query) :
    query ∈ Q.badSet family ↔ f.map query ∈ P.badSet family := by
  rw [Q.mem_badSet, P.mem_badSet]
  exact f.bad_iff family query

/-- Naturality is compositional under two successive changes of presentation. -/
theorem obstruction_natural_comp
    {P Q R : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (g : Q ⟶ R) (family : Family) :
    R.obstruction family = P.obstruction family ∘ f.map ∘ g.map := by
  rw [obstruction_natural g family, obstruction_natural f family]
  rfl

end CoveragePresentation

/-! ## 2. Query protocols pull back naturally -/

/-- Reindex only the query coordinate of an opening scheme.  The commitment and
opening relation are unchanged; hence this construction manufactures no binding. -/
def reindexScheme {Family : Type u} {Q R : Type q} {View : Type v}
    {Digest : Type d} {Proof : Type p}
    (map : R → Q) (S : QueryOpeningScheme Family Q View Digest Proof) :
    QueryOpeningScheme Family R View Digest Proof where
  commit := S.commit
  view family query := S.view family (map query)
  opens digest query view proof := S.opens digest (map query) view proof
  honestProof family query := S.honestProof family (map query)
  honest_opens family query := S.honest_opens family (map query)

theorem reindexScheme_pointBinding {Family : Type u} {Q R : Type q} {View : Type v}
    {Digest : Type d} {Proof : Type p}
    (map : R → Q) (S : QueryOpeningScheme Family Q View Digest Proof)
    (hbind : PointBinding S) :
    PointBinding (reindexScheme map S) := by
  intro family query view proof hopen
  exact hbind family (map query) view proof hopen

/-- Reindex a local rejection predicate along a query map. -/
def reindexTest {Q R : Type q} {View : Type v}
    (map : R → Q) (T : LocalTest Q View) : LocalTest R View where
  reject query view := T.reject (map query) view

/-- A local opening protocol realizing a coverage presentation.  `faithful` is the
precise bridge from the protocol's local rejection bit to the categorical obstruction.
It does not imply binding or any algebraic acceptance reduction. -/
structure PresentedProtocol {Family : Type u} {Invalid : Family → Prop}
    (P : CoveragePresentation.{u, q} Family Invalid)
    (View : Type v) (Digest : Type d) (Proof : Type p) where
  scheme : QueryOpeningScheme Family P.Query View Digest Proof
  test : LocalTest P.Query View
  faithful : ∀ family query,
    test.reject query (scheme.view family query) ↔ P.bad family query

namespace PresentedProtocol

variable {Family : Type u} {Invalid : Family → Prop}
variable {View : Type v} {Digest : Type d} {Proof : Type p}

/-- Pull a protocol back along an exact change of coverage presentation. -/
def pullback {P Q : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (L : PresentedProtocol P View Digest Proof) :
    PresentedProtocol Q View Digest Proof where
  scheme := reindexScheme f.map L.scheme
  test := reindexTest f.map L.test
  faithful family query :=
    (L.faithful family (f.map query)).trans (f.bad_iff family query).symm

/-- Pullback is unital: changing along the identity presentation changes no protocol. -/
@[simp]
theorem pullback_id (P : CoveragePresentation.{u, q} Family Invalid)
    (L : PresentedProtocol P View Digest Proof) :
    L.pullback (𝟙 P) = L := by
  cases L with
  | mk scheme test faithful =>
    cases scheme
    cases test
    rfl

/-- **COMPOSITIONALITY OF PROTOCOL PRESENTATION CHANGE.** Pulling through two
presentations is exactly pulling through their composite. -/
@[simp]
theorem pullback_comp {P Q R : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (g : Q ⟶ R) (L : PresentedProtocol P View Digest Proof) :
    (L.pullback f).pullback g = L.pullback (f ≫ g) := by
  cases L with
  | mk scheme test faithful =>
    cases scheme
    cases test
    rfl

/-- The protocol obstruction set is definitionally the presentation's bad set. -/
theorem obstructionSet_eq_badSet
    (P : CoveragePresentation.{u, q} Family Invalid)
    (L : PresentedProtocol P View Digest Proof) (family : Family) :
    obstructionSet L.scheme L.test family = P.badSet family := by
  ext query
  simp [obstructionSet, CoveragePresentation.badSet, L.faithful family query]

end PresentedProtocol

/-! ## 3. Naturality of the sampler event -/

section SamplerNaturality

variable {Family : Type u} {Invalid : Family → Prop}
variable {Seed : Type s} [Fintype Seed] [DecidableEq Seed]

/-- A sample misses the target obstruction iff its pointwise interpretation misses the
source obstruction.  This exact event equality is stronger and safer than a cardinality
comparison, and remains true when the query map duplicates source queries. -/
theorem misses_natural
    {P Q : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (family : Family) {k : ℕ} (sample : Fin k → Q.Query) :
    Misses (Q.badSet family) sample ↔
      Misses (P.badSet family) (fun i => f.map (sample i)) := by
  constructor <;> intro h i
  · intro hbad
    exact h i ((CoveragePresentation.mem_badSet_natural f family (sample i)).2 hbad)
  · intro hbad
    exact h i ((CoveragePresentation.mem_badSet_natural f family (sample i)).1 hbad)

/-- The seed-level miss event is natural under change of query presentation. -/
theorem missEvent_natural
    {P Q : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (family : Family) {k : ℕ}
    (queries : Seed → Fin k → Q.Query) :
    eventSeeds (fun seed => Misses (Q.badSet family) (queries seed)) =
      eventSeeds (fun seed =>
        Misses (P.badSet family) (fun i => f.map (queries seed i))) := by
  classical
  ext seed
  simp only [eventSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
  exact misses_natural f family (queries seed)

/-- The naturality square itself composes: mapping samples through `g` and then `f`
is literally mapping through `f ≫ g`. -/
theorem mappedQueries_comp
    {P Q R : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (g : Q ⟶ R) {k : ℕ}
    (queries : Seed → Fin k → R.Query) :
    (fun seed i => f.map (g.map (queries seed i))) =
      (fun seed i => (f ≫ g).map (queries seed i)) := rfl

end SamplerNaturality

/-! ## 4. Tripos predicates and assembly-tracked presentation maps -/

namespace RealizabilityLayer

open Dregg2.Realizability

variable {Family : Type u} {Invalid : Family → Prop}

/-- Read an obstruction predicate as a realizability truth value: a bad query is
realized by every PCA element and a good query by none.  This embeds the already
proved semantic predicate into the existing Set-indexed realizability doctrine; it
does not construct an associated topos. -/
noncomputable def obstructionPredicate (A : PCA.{u})
    (P : CoveragePresentation.{u, q} Family Invalid) (family : Family) :
    Pred A P.Query := by
  classical
  exact fun query => if P.bad family query then Set.univ else ∅

/-- **TRIPOS REINDEXING NATURALITY.** The realizability-valued obstruction predicate
pulls back exactly along a change of coverage presentation. -/
theorem obstructionPredicate_natural (A : PCA.{u}) (C : ChosenPairing A)
    (K : ChosenCurrying A C)
    {P Q : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (family : Family) :
    UFam.reindex (pcaEvidencedFrame A C K) f.map
        (obstructionPredicate A P family) =
      obstructionPredicate A Q family := by
  classical
  funext query
  by_cases hq : Q.bad family query
  · have hp : P.bad family (f.map query) := (f.bad_iff family query).mp hq
    simp [UFam.reindex, obstructionPredicate, hq, hp]
    rfl
  · have hp : ¬ P.bad family (f.map query) :=
      fun h => hq ((f.bad_iff family query).mpr h)
    simp [UFam.reindex, obstructionPredicate, hq, hp]
    rfl

/-- The obstruction predicate is classified by the existing UFam generic predicate.
This is the exact tripos-level statement available today; no tripos-to-topos
completion or elementary-topos theorem is claimed. -/
theorem obstructionPredicate_classified (A : PCA.{u}) (C : ChosenPairing A)
    (K : ChosenCurrying A C)
    (P : CoveragePresentation.{u, q} Family Invalid) (family : Family) :
    UFam.reindex (pcaEvidencedFrame A C K)
        (UFam.classify (pcaEvidencedFrame A C K)
          (obstructionPredicate A P family))
        (UFam.generic (pcaEvidencedFrame A C K)) =
      obstructionPredicate A P family :=
  pcaUFam_generic_classification A C K (obstructionPredicate A P family)

/-- A concrete realizer representation for the queries of one coverage presentation. -/
structure QueryRealization (A : PCA.{u})
    (P : CoveragePresentation.{u, q} Family Invalid) where
  Realizes : A.Carrier → P.Query → Prop
  realized : ∀ query, ∃ code, Realizes code query

namespace QueryRealization

/-- The query representation as an object of the already-formalized assembly category. -/
def assembly {A : PCA.{u}} {P : CoveragePresentation.{u, q} Family Invalid}
    (R : QueryRealization A P) : Assembly.{u, q} A where
  Carrier := P.Query
  Realizes := R.Realizes
  realized := R.realized

end QueryRealization

/-- An exact presentation map whose query interpreter is uniformly tracked by one PCA
program.  Tracking is extra executable evidence, not a consequence of coverage
naturality alone. -/
structure TrackedPresentationMap (A : PCA.{u})
    {P Q : CoveragePresentation.{u, q} Family Invalid}
    (RP : QueryRealization A P) (RQ : QueryRealization A Q) (f : P ⟶ Q) where
  hom : RQ.assembly ⟶ RP.assembly
  hom_eq_map : hom.toFun = f.map

namespace TrackedPresentationMap

/-- Identity presentation change is tracked by the identity assembly morphism. -/
def id (A : PCA.{u}) (P : CoveragePresentation.{u, q} Family Invalid)
    (RP : QueryRealization A P) :
    TrackedPresentationMap A RP RP (𝟙 P) where
  hom := 𝟙 RP.assembly
  hom_eq_map := by
    funext query
    rfl

/-- Uniformly tracked presentation interpreters compose in the assembly category,
in the same order as the contravariant query maps. -/
def comp (A : PCA.{u})
    {P Q R : CoveragePresentation.{u, q} Family Invalid}
    {RP : QueryRealization A P} {RQ : QueryRealization A Q}
    {RR : QueryRealization A R} {f : P ⟶ Q} {g : Q ⟶ R}
    (F : TrackedPresentationMap A RP RQ f)
    (G : TrackedPresentationMap A RQ RR g) :
    TrackedPresentationMap A RP RR (f ≫ g) where
  hom := G.hom ≫ F.hom
  hom_eq_map := by
    funext query
    exact (congrArg F.hom.toFun (congrFun G.hom_eq_map query)).trans
      (congrFun F.hom_eq_map (g.map query))

@[simp]
theorem id_toFun (A : PCA.{u}) (P : CoveragePresentation.{u, q} Family Invalid)
    (RP : QueryRealization A P) (query : P.Query) :
    (TrackedPresentationMap.id A P RP).hom.toFun query = query := rfl

@[simp]
theorem comp_toFun (A : PCA.{u})
    {P Q R : CoveragePresentation.{u, q} Family Invalid}
    {RP : QueryRealization A P} {RQ : QueryRealization A Q}
    {RR : QueryRealization A R} {f : P ⟶ Q} {g : Q ⟶ R}
    (F : TrackedPresentationMap A RP RQ f)
    (G : TrackedPresentationMap A RQ RR g) (query : R.Query) :
    (TrackedPresentationMap.comp A F G).hom.toFun query =
      f.map (g.map query) := by
  exact congrFun (TrackedPresentationMap.comp A F G).hom_eq_map query

end TrackedPresentationMap

end RealizabilityLayer

/-! ## 5. Factored soundness: cover detection + binding + sampler -/

/-- An explicit finite sampler term for one family and one presentation.  It is only a
counting claim about a fixed seed-to-query map.  A concrete Fiat--Shamir/RO argument must
justify why its transcript is represented by that seed distribution. -/
structure SamplerBound {Family : Type u} {Invalid : Family → Prop}
    (P : CoveragePresentation.{u, q} Family Invalid)
    (family : Family) (Seed : Type s) [Fintype Seed] [DecidableEq Seed]
    (k : ℕ) (queries : Seed → Fin k → P.Query) where
  budget : ℕ
  miss_le :
    (eventSeeds (fun seed => Misses (P.badSet family) (queries seed))).card ≤ budget

namespace SamplerBound

variable {Family : Type u} {Invalid : Family → Prop}
variable {Seed : Type s} [Fintype Seed] [DecidableEq Seed]

/-- Sampler bounds pull back exactly along presentation maps.  No new error term is
introduced: the miss events are equal by `missEvent_natural`. -/
def pullback
    {P Q : CoveragePresentation.{u, q} Family Invalid}
    (f : P ⟶ Q) (family : Family) {k : ℕ}
    (queries : Seed → Fin k → Q.Query)
    (B : SamplerBound P family Seed k
      (fun seed i => f.map (queries seed i))) :
    SamplerBound Q family Seed k queries where
  budget := B.budget
  miss_le := by
    rw [missEvent_natural f family queries]
    exact B.miss_le

/-- The exact sampler term for `k` independent uniform queries with replacement.  The
seed is the whole query vector, so this is an information-theoretic reference sampler,
not a Fiat--Shamir theorem. -/
noncomputable def independentUniform
    (P : CoveragePresentation.{u, q} Family Invalid) (family : Family) (k : ℕ) :
    SamplerBound P family (Fin k → P.Query) k (fun seed => seed) where
  budget := ((P.badSet family)ᶜ.card) ^ k
  miss_le := by
    have heq :
        eventSeeds (fun seed : Fin k → P.Query =>
          Misses (P.badSet family) seed) =
        missSamples (P.badSet family) k := rfl
    rw [heq, missSamples_card]

end SamplerBound

section FactoredSoundness

variable {Family : Type u} {Invalid : Family → Prop}
variable {View : Type v} {Digest : Type d} {Proof : Type p}
variable {Seed : Type s} [Fintype Seed] [DecidableEq Seed]

/-- A transcript witnesses a binding failure when some accepted opening changes the
precommitted local view.  A collision-resistance or vector-commitment game may bound
this event; the categorical layer does not. -/
def BindingFailureAtSeed
    {Query : Type q}
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (family : Family) {k : ℕ} (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof) (seed : Seed) : Prop :=
  ∃ i,
    S.opens (S.commit family) (queries seed i)
      (respond seed i).1 (respond seed i).2 ∧
    (respond seed i).1 ≠ S.view family (queries seed i)

/-- Locally accepted openings either miss every committed obstruction or exhibit the
explicit binding-failure event.  This is the eventwise version needed for
computational, rather than perfect, binding. -/
theorem locallyAccepts_misses_or_bindingFailure
    {Query : Type q} [Fintype Query] [DecidableEq Query]
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (family : Family) {k : ℕ}
    (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof) (seed : Seed)
    (hlocal : LocallyAccepts S T family queries respond seed) :
    Misses (obstructionSet S T family) (queries seed) ∨
      BindingFailureAtSeed S family queries respond seed := by
  classical
  by_cases hfailure : BindingFailureAtSeed S family queries respond seed
  · exact Or.inr hfailure
  · apply Or.inl
    intro i
    have hi := hlocal i
    have hview : (respond seed i).1 = S.view family (queries seed i) := by
      by_contra hne
      exact hfailure ⟨i, hi.1, hne⟩
    simp only [obstructionSet, Finset.mem_filter, Finset.mem_univ, true_and]
    intro hbad
    apply hi.2
    rw [hview]
    exact hbad

/-- Acceptance is contained in four explicit event classes: OOD exception,
low-degree exception, binding failure, or obstruction miss. -/
theorem acceptSeeds_subset_four_events
    {Query : Type q} [Fintype Query] [DecidableEq Query]
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (family : Family) {k : ℕ}
    (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction S T family queries respond
      accept oodBad lowDegreeBad) :
    eventSeeds accept ⊆
      ((eventSeeds oodBad ∪ eventSeeds lowDegreeBad) ∪
        eventSeeds (BindingFailureAtSeed S family queries respond)) ∪
          missSeedSet queries (obstructionSet S T family) := by
  intro seed hseed
  classical
  have haccept : accept seed := by simpa [eventSeeds] using hseed
  rcases hreduce seed haccept with hlocal | hood | hldt
  · rcases locallyAccepts_misses_or_bindingFailure
      S T family queries respond seed hlocal with hmiss | hbinding
    · simp [eventSeeds, missSeedSet, hmiss]
    · simp [eventSeeds, hbinding]
  · simp [eventSeeds, hood]
  · simp [eventSeeds, hldt]

/-- Exact finite cardinality bound with binding failure as a fourth independent
budget.  It makes no computational claim: a concrete commitment theorem must supply
`hbinding`. -/
theorem acceptSeed_card_le_budgets_with_binding
    {Query : Type q} [Fintype Query] [DecidableEq Query]
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (family : Family) {k : ℕ}
    (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction S T family queries respond
      accept oodBad lowDegreeBad)
    (oodBudget lowDegreeBudget bindingBudget queryBudget : ℕ)
    (hood : (eventSeeds oodBad).card ≤ oodBudget)
    (hldt : (eventSeeds lowDegreeBad).card ≤ lowDegreeBudget)
    (hbinding :
      (eventSeeds (BindingFailureAtSeed S family queries respond)).card ≤ bindingBudget)
    (hquery :
      (missSeedSet queries (obstructionSet S T family)).card ≤ queryBudget) :
    (eventSeeds accept).card ≤
      oodBudget + lowDegreeBudget + bindingBudget + queryBudget := by
  let Eood := eventSeeds oodBad
  let Eldt := eventSeeds lowDegreeBad
  let Ebind := eventSeeds (BindingFailureAtSeed S family queries respond)
  let Emiss := missSeedSet queries (obstructionSet S T family)
  have hsubset : eventSeeds accept ⊆ ((Eood ∪ Eldt) ∪ Ebind) ∪ Emiss :=
    acceptSeeds_subset_four_events S T family queries respond
      accept oodBad lowDegreeBad hreduce
  have haccept : (eventSeeds accept).card ≤ (((Eood ∪ Eldt) ∪ Ebind) ∪ Emiss).card :=
    Finset.card_le_card hsubset
  have houter : (((Eood ∪ Eldt) ∪ Ebind) ∪ Emiss).card ≤
      ((Eood ∪ Eldt) ∪ Ebind).card + Emiss.card := Finset.card_union_le _ _
  have hmiddle : ((Eood ∪ Eldt) ∪ Ebind).card ≤
      (Eood ∪ Eldt).card + Ebind.card := Finset.card_union_le _ _
  have hinner : (Eood ∪ Eldt).card ≤ Eood.card + Eldt.card := Finset.card_union_le _ _
  dsimp only [Eood, Eldt, Ebind, Emiss] at haccept houter hmiddle hinner
  omega

/-- **COMPUTATIONAL-BINDING SOCKET.** This is the deployed-shape factorization:
local detection plus separate OOD, low-degree, binding-failure, and sampler budgets.
Replacing `bindingBudget` by a collision-resistance advantage remains an external
cryptographic reduction, exactly where it belongs. -/
theorem factored_soundness_with_binding_budget
    (P : CoveragePresentation.{u, q} Family Invalid)
    (L : PresentedProtocol P View Digest Proof)
    (family : Family) (hinvalid : Invalid family)
    {k : ℕ} (queries : Seed → Fin k → P.Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction L.scheme L.test family queries respond
      accept oodBad lowDegreeBad)
    (oodBudget lowDegreeBudget bindingBudget : ℕ)
    (hood : (eventSeeds oodBad).card ≤ oodBudget)
    (hldt : (eventSeeds lowDegreeBad).card ≤ lowDegreeBudget)
    (hbinding :
      (eventSeeds
        (BindingFailureAtSeed L.scheme family queries respond)).card ≤ bindingBudget)
    (sampler : SamplerBound P family Seed k queries) :
    (P.badSet family).Nonempty ∧
      (eventSeeds accept).card ≤
        oodBudget + lowDegreeBudget + bindingBudget + sampler.budget := by
  constructor
  · exact P.badSet_nonempty family hinvalid
  · apply acceptSeed_card_le_budgets_with_binding L.scheme L.test family
      queries respond accept oodBad lowDegreeBad hreduce
      oodBudget lowDegreeBudget bindingBudget sampler.budget hood hldt hbinding
    rw [L.obstructionSet_eq_badSet P family]
    exact sampler.miss_le

/-- **PRESENTATION-INDEPENDENT FACTORED SOUNDNESS.**

For an invalid family:

1. the coverage presentation supplies a nonempty local obstruction set;
2. point binding prevents an adaptive opening from rewriting a queried local view;
3. the protocol-specific reduction isolates OOD and low-degree exceptional events; and
4. the sampler bound prices the exact event that every query misses the obstruction.

Only item 1 and the naturality laws are categorical/descent content.  Items 2--4 are
explicit cryptographic/probabilistic parameters. -/
theorem factored_soundness
    (P : CoveragePresentation.{u, q} Family Invalid)
    (L : PresentedProtocol P View Digest Proof)
    (family : Family) (hinvalid : Invalid family)
    (hbind : PointBinding L.scheme)
    {k : ℕ} (queries : Seed → Fin k → P.Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction L.scheme L.test family queries respond
      accept oodBad lowDegreeBad)
    (oodBudget lowDegreeBudget : ℕ)
    (hood : (eventSeeds oodBad).card ≤ oodBudget)
    (hldt : (eventSeeds lowDegreeBad).card ≤ lowDegreeBudget)
    (sampler : SamplerBound P family Seed k queries) :
    (P.badSet family).Nonempty ∧
      (eventSeeds accept).card ≤
        oodBudget + lowDegreeBudget + sampler.budget := by
  constructor
  · exact P.badSet_nonempty family hinvalid
  · apply acceptSeed_card_le_budgets L.scheme L.test hbind family queries respond
      accept oodBad lowDegreeBad hreduce oodBudget lowDegreeBudget sampler.budget
      hood hldt
    rw [L.obstructionSet_eq_badSet P family]
    exact sampler.miss_le

end FactoredSoundness

/-! ## 6. Finite patch-code instance -/

namespace FinitePatchInstance

open FinitePatchCode

variable {X : Type u} {I : Type q} {Symbol : Type v}
variable [DecidableEq X] [Fintype I] [DecidableEq I]

/-- Invalidity for a finite patch code includes the local-validity promise and says no
global codeword induces the submitted family. -/
def CodeInvalid (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol)) : Prop :=
  C.LocallyValid family ∧
    ¬ ∃ global : X → Symbol,
      C.IsCodeword global ∧
        RestrictsTo C.cover.patchSet (fun _ : X => Symbol) family global

/-- A locally valid family with no codeword amalgamation has no plain amalgamation. -/
theorem no_amalgamation_of_codeInvalid
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol))
    (hinvalid : CodeInvalid C family) :
    ¬ HasAmalgamation C.cover family := by
  rintro ⟨global, hrestrict⟩
  apply hinvalid.2
  refine ⟨global, ?_, hrestrict⟩
  intro i
  have hsection :
      (fun x (hx : x ∈ C.cover.patchSet i) => global x) = family i := by
    funext x hx
    exact hrestrict i x hx
  rw [hsection]
  exact hinvalid.1 i

/-- The complete overlap cover is a concrete coverage presentation of finite patch-code
invalidity.  This is the current patch-code setting, not a claimed HDX/LTC theorem. -/
noncomputable def completeOverlapPresentation
    (C : FinitePatchCode X I Symbol) :
    CoveragePresentation
      (SectionFamily C.cover (fun _ : X => Symbol)) (CodeInvalid C) where
  Query := I × I
  queryFintype := inferInstance
  queryDecidableEq := inferInstance
  bad := wholeOverlapReject
  badDecidable := fun _ _ => Classical.propDecidable _
  detects family hinvalid := by
    have hno := no_amalgamation_of_codeInvalid C family hinvalid
    rcases badEdges_nonempty_of_no_amalgamation C.cover family hno with ⟨query, hquery⟩
    refine ⟨query, ?_⟩
    classical
    simpa [overlapBadEdges] using hquery

/-- Generic boolean observation of an obstruction. -/
noncomputable def badBit
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol)) (query : I × I) : Bool := by
  classical
  exact decide (wholeOverlapReject family query)

/-- A transparent, information-theoretic reference protocol for the patch presentation.
Its digest is the whole family; it witnesses the wiring but is not a compressing commitment. -/
noncomputable def transparentProtocol
    (C : FinitePatchCode X I Symbol) :
    PresentedProtocol (completeOverlapPresentation C) Bool
      (SectionFamily C.cover (fun _ : X => Symbol)) Unit where
  scheme := Reference.transparentScheme (badBit C)
  test := { reject := fun _ bit => bit = true }
  faithful family query := by
    classical
    change (decide (wholeOverlapReject family query) = true) ↔
      wholeOverlapReject family query
    simp

/-- The transparent reference protocol is point-binding.  A deployed Merkle/FRI
opening must replace this theorem with its own computational binding game. -/
theorem transparentProtocol_pointBinding
    (C : FinitePatchCode X I Symbol) :
    PointBinding (transparentProtocol C).scheme :=
  Reference.transparentScheme_pointBinding (badBit C)

/-- The factored theorem specialized all the way to finite patch codes and their
transparent reference opening.  The only remaining terms are the protocol reduction,
the two algebraic-event budgets, and the sampler's exact miss-event budget. -/
theorem transparent_factored_soundness
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol))
    (hinvalid : CodeInvalid C family)
    {Seed : Type s} [Fintype Seed] [DecidableEq Seed]
    {k : ℕ}
    (queries : Seed → Fin k → (completeOverlapPresentation C).Query)
    (respond : TranscriptResponder Seed k Bool Unit)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction
      (transparentProtocol C).scheme (transparentProtocol C).test family
      queries respond accept oodBad lowDegreeBad)
    (oodBudget lowDegreeBudget : ℕ)
    (hood : (eventSeeds oodBad).card ≤ oodBudget)
    (hldt : (eventSeeds lowDegreeBad).card ≤ lowDegreeBudget)
    (sampler : SamplerBound (completeOverlapPresentation C) family Seed k queries) :
    ((completeOverlapPresentation C).badSet family).Nonempty ∧
      (eventSeeds accept).card ≤
        oodBudget + lowDegreeBudget + sampler.budget :=
  factored_soundness (completeOverlapPresentation C) (transparentProtocol C)
    family hinvalid (transparentProtocol_pointBinding C) queries respond
    accept oodBad lowDegreeBad hreduce oodBudget lowDegreeBudget hood hldt sampler

/-- Honest openings for the transparent protocol under the independent-uniform seed. -/
noncomputable def transparentHonestResponder
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol)) (k : ℕ) :
    TranscriptResponder
      (Fin k → (completeOverlapPresentation C).Query) k Bool Unit :=
  fun seed i =>
    ((transparentProtocol C).scheme.view family (seed i),
      (transparentProtocol C).scheme.honestProof family (seed i))

/-- Reference acceptance consists only of valid bound local openings and passing the
local obstruction test.  There are no OOD or low-degree coordinates in this toy
reference; deployed STARK acceptance uses `transparent_factored_soundness` instead. -/
noncomputable def transparentUniformAccept
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol)) (k : ℕ)
    (seed : Fin k → (completeOverlapPresentation C).Query) : Prop :=
  LocallyAccepts (transparentProtocol C).scheme (transparentProtocol C).test
    family (fun seed => seed) (transparentHonestResponder C family k) seed

/-- For honest transparent openings, local acceptance is exactly the obstruction-miss
event, not merely a subset of it. -/
theorem transparentUniformAccept_iff_misses
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol)) (k : ℕ)
    (seed : Fin k → (completeOverlapPresentation C).Query) :
    transparentUniformAccept C family k seed ↔
      Misses ((completeOverlapPresentation C).badSet family) seed := by
  constructor
  · intro haccept
    have hmiss := locallyAccepts_misses
      (transparentProtocol C).scheme (transparentProtocol C).test
      (transparentProtocol_pointBinding C) family (fun seed => seed)
      (transparentHonestResponder C family k) seed haccept
    rw [(transparentProtocol C).obstructionSet_eq_badSet
      (completeOverlapPresentation C) family] at hmiss
    exact hmiss
  · intro hmiss i
    constructor
    · exact (transparentProtocol C).scheme.honest_opens family (seed i)
    · intro hreject
      apply hmiss i
      apply ((completeOverlapPresentation C).mem_badSet family (seed i)).2
      apply ((transparentProtocol C).faithful family (seed i)).mp
      exact hreject

/-- Exact honest-reference acceptance count under independent uniform queries. -/
theorem transparent_uniform_acceptance_card
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol)) (k : ℕ) :
    (eventSeeds (transparentUniformAccept C family k)).card =
      (((completeOverlapPresentation C).badSet family)ᶜ.card) ^ k := by
  have hevents :
      eventSeeds (transparentUniformAccept C family k) =
        missSamples ((completeOverlapPresentation C).badSet family) k := by
    classical
    ext seed
    simp only [eventSeeds, missSamples, Finset.mem_filter, Finset.mem_univ, true_and]
    exact transparentUniformAccept_iff_misses C family k seed
  rw [hevents, missSamples_card]

/-- **CONCRETE UNIFORM REFERENCE BOUND.** For every invalid finite patch-code family,
the transparent reference protocol under `k` independent uniform complete-overlap
queries accepts on at most `|good queries|^k` query vectors. -/
theorem transparent_uniform_soundness
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol))
    (hinvalid : CodeInvalid C family) (k : ℕ) :
    ((completeOverlapPresentation C).badSet family).Nonempty ∧
      (eventSeeds (transparentUniformAccept C family k)).card ≤
        (((completeOverlapPresentation C).badSet family)ᶜ.card) ^ k := by
  let queries :
      (Fin k → (completeOverlapPresentation C).Query) →
        Fin k → (completeOverlapPresentation C).Query := fun seed => seed
  let respond := transparentHonestResponder C family k
  let accept := transparentUniformAccept C family k
  let never : (Fin k → (completeOverlapPresentation C).Query) → Prop := fun _ => False
  have hreduce : AcceptanceReduction
      (transparentProtocol C).scheme (transparentProtocol C).test family
      queries respond accept never never := by
    intro seed haccept
    exact Or.inl haccept
  have hnever : (eventSeeds never).card ≤ 0 := by
    simp [eventSeeds, never]
  have h := transparent_factored_soundness C family hinvalid queries respond
    accept never never hreduce 0 0 hnever hnever
    (SamplerBound.independentUniform (completeOverlapPresentation C) family k)
  simpa [queries, respond, accept, never, SamplerBound.independentUniform] using h

/-- One uniform overlap query has a genuinely subunit false-acceptance numerator:
because invalidity supplies a nonempty bad set, fewer than all query seeds accept. -/
theorem transparent_uniform_one_query_strict
    (C : FinitePatchCode X I Symbol)
    (family : SectionFamily C.cover (fun _ : X => Symbol))
    (hinvalid : CodeInvalid C family) :
    (eventSeeds (transparentUniformAccept C family 1)).card <
      Fintype.card (completeOverlapPresentation C).Query := by
  have h := transparent_uniform_soundness C family hinvalid 1
  have hquery : Nonempty (completeOverlapPresentation C).Query :=
    ⟨h.1.choose⟩
  have hlt :
      (((completeOverlapPresentation C).badSet family)ᶜ.card) <
        Fintype.card (completeOverlapPresentation C).Query := by
    rw [Finset.card_compl]
    exact Nat.sub_lt (Fintype.card_pos_iff.mpr hquery) (Finset.card_pos.mpr h.1)
  exact lt_of_le_of_lt (by simpa using h.2) hlt

end FinitePatchInstance

/-! ### Non-vacuity on the existing weighted-star patch code. -/

namespace WeightedStarInstance

open FinitePatchCodeDescent.WeightedStar
open FinitePatchInstance

theorem oneError_codeInvalid : CodeInvalid code oneError := by
  refine ⟨oneError_locallyValid, ?_⟩
  rintro ⟨global, _hcode, hrestrict⟩
  exact oneError_no_amalgamation ⟨global, hrestrict⟩

/-- The abstract detection theorem fires on the already-proved one-error patch family. -/
theorem oneError_badSet_nonempty :
    ((completeOverlapPresentation code).badSet oneError).Nonempty :=
  (completeOverlapPresentation code).badSet_nonempty oneError oneError_codeInvalid

/-- Consequently some concrete ordered patch pair detects the one-error family. -/
theorem oneError_has_bad_query :
    ∃ query : PatchId × PatchId, wholeOverlapReject oneError query := by
  rcases oneError_badSet_nonempty with ⟨query, hquery⟩
  exact ⟨query, ((completeOverlapPresentation code).mem_badSet oneError query).1 hquery⟩

/-- The existing weighted-star one-error family now has a concrete nontrivial
one-query soundness count for the unweighted complete-overlap reference sampler.
This does not reuse or silently flatten the source example's separate edge weights. -/
theorem oneError_uniform_one_query_strict :
    (eventSeeds
      (transparentUniformAccept code oneError 1)).card <
      Fintype.card (completeOverlapPresentation code).Query :=
  transparent_uniform_one_query_strict code oneError oneError_codeInvalid

end WeightedStarInstance

#assert_all_clean [
  CoveragePresentation.Hom.ext,
  CoveragePresentation.id_map,
  CoveragePresentation.comp_map,
  CoveragePresentation.mem_badSet,
  CoveragePresentation.badSet_nonempty,
  CoveragePresentation.obstruction_natural,
  CoveragePresentation.mem_badSet_natural,
  CoveragePresentation.obstruction_natural_comp,
  reindexScheme_pointBinding,
  PresentedProtocol.pullback_id,
  PresentedProtocol.pullback_comp,
  PresentedProtocol.obstructionSet_eq_badSet,
  misses_natural,
  missEvent_natural,
  mappedQueries_comp,
  SamplerBound.pullback,
  SamplerBound.independentUniform,
  RealizabilityLayer.obstructionPredicate_natural,
  RealizabilityLayer.obstructionPredicate_classified,
  RealizabilityLayer.TrackedPresentationMap.id_toFun,
  RealizabilityLayer.TrackedPresentationMap.comp_toFun,
  locallyAccepts_misses_or_bindingFailure,
  acceptSeeds_subset_four_events,
  acceptSeed_card_le_budgets_with_binding,
  factored_soundness_with_binding_budget,
  factored_soundness,
  FinitePatchInstance.no_amalgamation_of_codeInvalid,
  FinitePatchInstance.transparentProtocol_pointBinding,
  FinitePatchInstance.transparent_factored_soundness,
  FinitePatchInstance.transparentUniformAccept_iff_misses,
  FinitePatchInstance.transparent_uniform_acceptance_card,
  FinitePatchInstance.transparent_uniform_soundness,
  FinitePatchInstance.transparent_uniform_one_query_strict,
  WeightedStarInstance.oneError_codeInvalid,
  WeightedStarInstance.oneError_badSet_nonempty,
  WeightedStarInstance.oneError_has_bad_query,
  WeightedStarInstance.oneError_uniform_one_query_strict]

end Dregg2.Metatheory.CategoricalDescentQueryProtocol

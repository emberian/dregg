/-
# Dregg2.Metatheory.RealizabilityLocalRewriteOracle

This module gives one exact bridge from realizability descent to a finite local-query
protocol without choosing polynomials as the proof representation.

An `EffectiveLocalOracle` starts with redundant, intensional witnesses in an assembly.
An effective cover forgets representation details, while a uniformly tracked local
observer reads one finite query.  If that observer is invariant on cover fibres, the
kernel-pair coequalizer theorem descends it to semantic witnesses.  The descended
Boolean observer then induces a coverage presentation, a UFam obstruction predicate,
and a transparent reference opening protocol.

Only the following part is categorical/realizability content:

* executable lifting along the effective cover;
* kernel-pair invariance of the local observer; and
* unique descent of that observer to semantic witnesses.

Commitment binding, Fiat--Shamir sampling, OOD reduction, and FRI/low-degree soundness
are not derived here.  The final interaction-net instance is deliberately non-polynomial:
the oracle is a fixed finite table of local graph-rewrite receipts, queried by row.
-/
import Dregg2.Realizability.AssemblyRegularCoverage
import Dregg2.Metatheory.CategoricalDescentQueryProtocol
import Dregg2.Calculus.InteractionNetTrace

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Metatheory.RealizabilityLocalRewriteOracle

open CategoryTheory
open Dregg2.Realizability
open Dregg2.Metatheory.CategoricalDescentQueryProtocol
open Dregg2.Metatheory.RobustDescentQueryGame
open Dregg2.Metatheory.RobustDescentTranscriptGame

universe u v

/-! ## Effective-cover descent of a local oracle -/

/-- A representation-independent local oracle obtained from an intensional witness
representation.

`rawWitness` may contain sharing annotations, interaction-net addresses, evaluator
state, or any other non-polynomial proof object.  `quotient` forgets those choices.
The observer is executable as an assembly morphism and must agree whenever both its
query and the semantic witness agree. -/
structure EffectiveLocalOracle (A : PCA.{u}) (C : ChosenPairing A)
    (Query RawWitness Family View : Assembly.{u, v} A) where
  quotient : RawWitness ⟶ Family
  quotientCover : Assembly.EffectiveCover quotient
  rawObserve : Assembly.product C Query RawWitness ⟶ View
  representationInvariant :
    ∀ query query' raw raw',
      query = query' → quotient.toFun raw = quotient.toFun raw' →
        rawObserve.toFun (query, raw) = rawObserve.toFun (query', raw')

namespace EffectiveLocalOracle

variable {A : PCA.{u}} {C : ChosenPairing A}
variable {Query RawWitness Family View : Assembly.{u, v} A}

/-- Forget representation details while retaining the query coordinate. -/
def queryQuotient
    (O : EffectiveLocalOracle A C Query RawWitness Family View) :
    Assembly.product C Query RawWitness ⟶ Assembly.product C Query Family :=
  Assembly.pair C
    (Assembly.fst C Query RawWitness)
    (Assembly.snd C Query RawWitness ≫ O.quotient)

@[simp]
theorem queryQuotient_apply
    (O : EffectiveLocalOracle A C Query RawWitness Family View)
    (query : Query.Carrier) (raw : RawWitness.Carrier) :
    O.queryQuotient.toFun (query, raw) = (query, O.quotient.toFun raw) := rfl

/-- The product of a query with an effective witness cover is again an effective
cover.  The lifting program projects the query realizer, runs the witness lift, and
forks the two results. -/
theorem queryQuotient_effectiveCover
    (O : EffectiveLocalOracle A C Query RawWitness Family View) :
    Assembly.EffectiveCover O.queryQuotient := by
  rcases O.quotientCover with ⟨liftCode, hlift⟩
  refine ⟨C.fork C.fst (A.compose liftCode C.snd), ?_⟩
  rintro ⟨query, family⟩ r hr
  rcases hr with ⟨queryCode, hquery, familyCode, hfamily, rfl⟩
  rcases hlift family familyCode hfamily with
    ⟨raw, rawCode, hquot, hliftApp, hraw⟩
  refine ⟨(query, raw), C.pairVal queryCode rawCode, ?_, ?_, ?_⟩
  · simp [hquot]
    rfl
  · exact C.app_fork (C.app_fst queryCode familyCode)
      (A.app_compose (C.app_snd queryCode familyCode) hliftApp)
  · exact ⟨queryCode, hquery, rawCode, hraw, rfl⟩

/-- Fibre invariance is exactly the kernel-pair equation required for regular
descent. -/
theorem rawObserve_coequalizes
    (O : EffectiveLocalOracle A C Query RawWitness Family View) :
    Assembly.kernelPairFst C O.queryQuotient ≫ O.rawObserve =
      Assembly.kernelPairSnd C O.queryQuotient ≫ O.rawObserve := by
  apply Assembly.hom_eq_of_pointwise
  intro pair
  have hpair := pair.2
  change
    (pair.1.1.1, O.quotient.toFun pair.1.1.2) =
      (pair.1.2.1, O.quotient.toFun pair.1.2.2) at hpair
  have hquery : pair.1.1.1 = pair.1.2.1 :=
    congrArg (fun x : Query.Carrier × Family.Carrier => x.1) hpair
  have hfamily :
      O.quotient.toFun pair.1.1.2 = O.quotient.toFun pair.1.2.2 :=
    congrArg (fun x : Query.Carrier × Family.Carrier => x.2) hpair
  exact O.representationInvariant _ _ _ _ hquery hfamily

/-- The semantic local observer produced by effective-cover descent. -/
noncomputable def semanticObserve
    (O : EffectiveLocalOracle A C Query RawWitness Family View) :
    Assembly.product C Query Family ⟶ View :=
  Assembly.coverDesc C O.queryQuotient O.queryQuotient_effectiveCover
    O.rawObserve O.rawObserve_coequalizes

/-- **REALIZABILITY-TO-ORACLE BRIDGE.** Observing after quotienting is exactly
observing the intensional witness first.  This is an equality of tracked assembly
morphisms, not merely an extensional existence claim. -/
@[simp]
theorem semanticObserve_fac
    (O : EffectiveLocalOracle A C Query RawWitness Family View) :
    O.queryQuotient ≫ O.semanticObserve = O.rawObserve :=
  Assembly.coverDesc_fac C O.queryQuotient O.queryQuotient_effectiveCover
    O.rawObserve O.rawObserve_coequalizes

/-- Pointwise form of the bridge theorem. -/
theorem semanticObserve_spec
    (O : EffectiveLocalOracle A C Query RawWitness Family View)
    (query : Query.Carrier) (raw : RawWitness.Carrier) :
    O.semanticObserve.toFun (query, O.quotient.toFun raw) =
      O.rawObserve.toFun (query, raw) := by
  exact congrArg
    (fun f : Assembly.product C Query RawWitness ⟶ View =>
      f.toFun (query, raw)) O.semanticObserve_fac

/-- The descended observer is the unique tracked semantic observer compatible with
the raw one. -/
theorem semanticObserve_unique
    (O : EffectiveLocalOracle A C Query RawWitness Family View)
    (candidate : Assembly.product C Query Family ⟶ View)
    (hfac : O.queryQuotient ≫ candidate = O.rawObserve) :
    candidate = O.semanticObserve :=
  Assembly.coverDesc_unique C O.queryQuotient
    O.queryQuotient_effectiveCover O.rawObserve O.rawObserve_coequalizes
    candidate hfac

/-! ## The descended Boolean observer as logic and as a query protocol -/

section Boolean

variable {BoolView : Assembly.{u, v} A}
variable (decode : BoolView.Carrier → Bool)
variable (O : EffectiveLocalOracle A C Query RawWitness Family BoolView)

/-- Invalidity is existence of a rejecting local observation.  A richer application
may prove this equivalent to failure of a global rewrite/typing invariant. -/
def Invalid (family : Family.Carrier) : Prop :=
  ∃ query : Query.Carrier,
    decode (O.semanticObserve.toFun (query, family)) = true

/-- The finite descended observer is a coverage presentation.  Notice that this
construction does not mention a field, polynomial, circuit, or hash. -/
noncomputable def coverage [Fintype Query.Carrier] [DecidableEq Query.Carrier] :
    CoveragePresentation Family.Carrier (Invalid decode O) where
  Query := Query.Carrier
  queryFintype := inferInstance
  queryDecidableEq := inferInstance
  bad := fun family query =>
    decode (O.semanticObserve.toFun (query, family)) = true
  badDecidable := fun _ _ => inferInstance
  detects := fun _ hinvalid => hinvalid

/-- Interpret the descended bad bit as a realizability truth value. -/
noncomputable def obstructionPredicate [Fintype Query.Carrier]
    [DecidableEq Query.Carrier] (family : Family.Carrier) : Pred A Query.Carrier :=
  fun query =>
    if decode (O.semanticObserve.toFun (query, family)) = true then Set.univ else ∅

/-- The local obstruction is classified by the existing UFam generic predicate.
This is the logical/tripos component; it constructs no associated topos. -/
theorem obstructionPredicate_classified [Fintype Query.Carrier]
    [DecidableEq Query.Carrier] (K : ChosenCurrying A C)
    (family : Family.Carrier) :
    UFam.reindex (pcaEvidencedFrame A C K)
        (UFam.classify (pcaEvidencedFrame A C K)
          (obstructionPredicate decode O family))
        (UFam.generic (pcaEvidencedFrame A C K)) =
      obstructionPredicate decode O family :=
  pcaUFam_generic_classification A C K
    (obstructionPredicate decode O family)

/-- A transparent reference opening protocol for the descended observer.  Its digest
is the entire family, so it is information-theoretic scaffolding, not a commitment. -/
noncomputable def transparentProtocol [Fintype Query.Carrier]
    [DecidableEq Query.Carrier] :
    PresentedProtocol (coverage decode O) Bool Family.Carrier Unit where
  scheme :=
    RobustDescentQueryGame.Reference.transparentScheme
      (fun family query => decode (O.semanticObserve.toFun (query, family)))
  test := { reject := fun _ bit => bit = true }
  faithful := fun _ _ => Iff.rfl

/-- The whole-family transparent reference is point-binding.  A deployed succinct
protocol must replace this with a computational binding reduction. -/
theorem transparentProtocol_pointBinding [Fintype Query.Carrier]
    [DecidableEq Query.Carrier] :
    PointBinding (transparentProtocol decode O).scheme :=
  RobustDescentQueryGame.Reference.transparentScheme_pointBinding
    (fun family query => decode (O.semanticObserve.toFun (query, family)))

/-- Factored finite-seed soundness for the descended transparent reference.  The
categorical construction supplies the nonempty obstruction set.  The acceptance
reduction, OOD budget, low-degree/FRI budget, and sampler budget remain explicit
protocol inputs. -/
theorem transparent_factored_soundness [Fintype Query.Carrier]
    [DecidableEq Query.Carrier]
    (family : Family.Carrier) (hinvalid : Invalid decode O family)
    {Seed : Type v} [Fintype Seed] [DecidableEq Seed]
    {k : Nat} (queries : Seed → Fin k → Query.Carrier)
    (respond : TranscriptResponder Seed k Bool Unit)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction
      (transparentProtocol decode O).scheme
      (transparentProtocol decode O).test family queries respond
      accept oodBad lowDegreeBad)
    (oodBudget lowDegreeBudget : Nat)
    (hood : (eventSeeds oodBad).card ≤ oodBudget)
    (hldt : (eventSeeds lowDegreeBad).card ≤ lowDegreeBudget)
    (sampler : SamplerBound (coverage decode O) family Seed k queries) :
    ((coverage decode O).badSet family).Nonempty ∧
      (eventSeeds accept).card ≤
        oodBudget + lowDegreeBudget + sampler.budget :=
  factored_soundness (coverage decode O) (transparentProtocol decode O)
    family hinvalid (transparentProtocol_pointBinding decode O)
    queries respond accept oodBad lowDegreeBad hreduce oodBudget lowDegreeBudget
    hood hldt sampler

end Boolean

end EffectiveLocalOracle

/-! ## A non-polynomial interaction-net oracle -/

namespace InteractionRows

open Dregg2.Calculus.InteractionNetTrace

/-- One independently queryable local graph-rewrite receipt. -/
structure Row where
  before : Net
  cert : LocalCert
  after : Net
  deriving DecidableEq, Repr

/-- A fixed-size proof oracle is a table of local graph-rewrite receipts. -/
abbrev Oracle (n : Nat) := Fin n → Row

def reject (row : Row) : Bool := !row.cert.check row.before row.after

def twoRows (first second : Row) : Oracle 2 :=
  Fin.cases first (fun _ => second)

def goodFirst : Row :=
  ⟨Reference.start, Reference.reduceAnd, Reference.middle⟩

def goodSecond : Row :=
  ⟨Reference.middle, Reference.reduceNeg, Reference.finish⟩

def badSecond : Row :=
  ⟨Reference.start, Reference.reduceNeg, Reference.finish⟩

def goodOracle : Oracle 2 := twoRows goodFirst goodSecond
def badOracle : Oracle 2 := twoRows goodFirst badSecond

@[simp] theorem goodFirst_accepts : reject goodFirst = false := by decide
@[simp] theorem goodSecond_accepts : reject goodSecond = false := by decide
@[simp] theorem badSecond_rejects : reject badSecond = true := by decide

/-! ### Concrete unit-PCA assembly realization -/

/-- The indiscrete assembly over the one-point PCA.  It is used only as a finite,
nonvacuous model of the bridge's interfaces. -/
@[reducible] def unitAssembly (X : Type v) : Assembly.{0, v} PCA.unitPCA where
  Carrier := X
  Realizes := fun _ _ => True
  realized := fun _ => ⟨(), trivial⟩

@[reducible] def unitHom {X Y : Type v} (f : X → Y) : unitAssembly X ⟶ unitAssembly Y where
  toFun := f
  tracked := by
    refine ⟨(), ?_⟩
    intro x r hr
    exact ⟨(), trivial, trivial⟩

abbrev QueryAssembly : Assembly.{0, 0} PCA.unitPCA := unitAssembly (Fin 2)
abbrev RawAssembly : Assembly.{0, 0} PCA.unitPCA := unitAssembly (Oracle 2 × Bool)
abbrev FamilyAssembly : Assembly.{0, 0} PCA.unitPCA := unitAssembly (Oracle 2)
abbrev BoolAssembly : Assembly.{0, 0} PCA.unitPCA := unitAssembly Bool

instance queryFintype : Fintype QueryAssembly.Carrier := by
  change Fintype (Fin 2)
  infer_instance

instance queryDecidableEq : DecidableEq QueryAssembly.Carrier := by
  change DecidableEq (Fin 2)
  infer_instance

def secondQuery : QueryAssembly.Carrier := by
  change Fin 2
  exact 1

def quotient : RawAssembly ⟶ FamilyAssembly := unitHom Prod.fst

theorem quotient_effectiveCover : Assembly.EffectiveCover quotient := by
  refine ⟨(), ?_⟩
  intro family r hr
  exact ⟨(family, false), (), rfl, trivial, trivial⟩

def rawObserve :
    Assembly.product ChosenPairing.unitPairing QueryAssembly RawAssembly ⟶
      BoolAssembly where
  toFun := fun input => reject (input.2.1 input.1)
  tracked := by
    refine ⟨(), ?_⟩
    intro input r hr
    exact ⟨(), trivial, trivial⟩

/-- Redundant padding is erased by the cover and cannot affect a queried rewrite row. -/
def interactionOracle : EffectiveLocalOracle PCA.unitPCA
    ChosenPairing.unitPairing QueryAssembly RawAssembly FamilyAssembly BoolAssembly where
  quotient := quotient
  quotientCover := quotient_effectiveCover
  rawObserve := rawObserve
  representationInvariant := by
    intro query query' raw raw' hquery hfamily
    subst query'
    change raw.1 = raw'.1 at hfamily
    change reject (raw.1 query) = reject (raw'.1 query)
    rw [hfamily]

noncomputable abbrev interactionCoverage :=
  EffectiveLocalOracle.coverage (fun bit : Bool => bit) interactionOracle

noncomputable abbrev interactionProtocol :=
  EffectiveLocalOracle.transparentProtocol (fun bit : Bool => bit) interactionOracle

/-- Descent recovers the direct local checker on every semantic interaction oracle. -/
theorem semanticObserve_eq_reject (query : Fin 2) (family : Oracle 2) :
    interactionOracle.semanticObserve.toFun (query, family) =
      reject (family query) := by
  simpa [interactionOracle, quotient, rawObserve] using
    interactionOracle.semanticObserve_spec query (family, false)

theorem badOracle_invalid :
    EffectiveLocalOracle.Invalid (fun bit : Bool => bit) interactionOracle badOracle := by
  refine ⟨secondQuery, ?_⟩
  rw [semanticObserve_eq_reject]
  decide

theorem goodOracle_valid :
    ¬ EffectiveLocalOracle.Invalid (fun bit : Bool => bit) interactionOracle goodOracle := by
  rintro ⟨query, hbad⟩
  rw [semanticObserve_eq_reject] at hbad
  change Fin 2 at query
  fin_cases query
  · have h : reject goodFirst = true := by
      change reject goodFirst = true at hbad
      exact hbad
    rw [goodFirst_accepts] at h
    contradiction
  · have h : reject goodSecond = true := by
      change reject goodSecond = true at hbad
      exact hbad
    rw [goodSecond_accepts] at h
    contradiction

/-- The concrete bad interaction oracle has exactly one rejecting query. -/
theorem badOracle_badSet_card :
    (interactionCoverage.badSet badOracle).card = 1 := by
  rw [Finset.card_eq_one]
  refine ⟨secondQuery, ?_⟩
  ext query
  simp only [CoveragePresentation.mem_badSet]
  refine Iff.trans ?_ Finset.mem_singleton.symm
  change
    (interactionOracle.semanticObserve.toFun (query, badOracle) = true) ↔
      query = secondQuery
  refine Iff.trans (iff_of_eq (congrArg (· = true) (semanticObserve_eq_reject query badOracle))) ?_
  change Fin 2 at query
  fin_cases query
  · change reject goodFirst = true ↔ (0 : Fin 2) = (1 : Fin 2)
    rw [goodFirst_accepts]
    decide
  · change reject badSecond = true ↔ (1 : Fin 2) = (1 : Fin 2)
    rw [badSecond_rejects]
    decide

/-- Honest openings for the descended transparent reference protocol. -/
noncomputable def honestResponder (family : Oracle 2) (k : Nat) :
    TranscriptResponder (Fin k → Fin 2) k Bool Unit :=
  fun seed i =>
    (interactionProtocol.scheme.view family (seed i),
      interactionProtocol.scheme.honestProof family (seed i))

/-- Reference acceptance queries the local-rewrite table directly. -/
noncomputable def uniformAccept (family : Oracle 2) (k : Nat)
    (seed : Fin k → Fin 2) : Prop :=
  LocallyAccepts
    interactionProtocol.scheme interactionProtocol.test
    family (fun seed => seed) (honestResponder family k) seed

/-- For honest transparent openings, acceptance is exactly failure to sample a
rejecting interaction row. -/
theorem uniformAccept_iff_misses (family : Oracle 2) (k : Nat)
    (seed : Fin k → Fin 2) :
    uniformAccept family k seed ↔
      Misses
        (interactionCoverage.badSet family) seed := by
  constructor
  · intro haccept
    have hmiss := locallyAccepts_misses
      interactionProtocol.scheme interactionProtocol.test
      (EffectiveLocalOracle.transparentProtocol_pointBinding
        (fun bit : Bool => bit) interactionOracle)
      family (fun seed => seed) (honestResponder family k) seed haccept
    rw [interactionProtocol.obstructionSet_eq_badSet
      interactionCoverage family] at hmiss
    exact hmiss
  · intro hmiss i
    constructor
    · exact interactionProtocol.scheme.honest_opens family (seed i)
    · intro hreject
      apply hmiss i
      apply (interactionCoverage.mem_badSet family (seed i)).2
      exact (interactionProtocol.faithful family (seed i)).mp hreject

/-- With two independent uniform row queries, the transparent reference accepts the
bad two-row oracle on exactly one of four query vectors: both queries must hit the one
good row.  This is an exact finite count, not a FRI theorem. -/
theorem two_query_transparent_acceptance_card :
    (eventSeeds (uniformAccept badOracle 2)).card = 1 := by
  have hevents :
      eventSeeds (uniformAccept badOracle 2) =
        missSamples
          (interactionCoverage.badSet badOracle) 2 := by
    classical
    ext seed
    constructor
    · intro hseed
      have haccept : uniformAccept badOracle 2 seed := by
        simpa [eventSeeds] using hseed
      have hmiss := (uniformAccept_iff_misses badOracle 2 seed).mp haccept
      rw [missSamples_eq_piFinset]
      exact Fintype.mem_piFinset.mpr fun i => Finset.mem_compl.mpr (hmiss i)
    · intro hseed
      rw [missSamples_eq_piFinset] at hseed
      have hmiss : Misses (interactionCoverage.badSet badOracle) seed :=
        fun i => Finset.mem_compl.mp (Fintype.mem_piFinset.mp hseed i)
      have haccept := (uniformAccept_iff_misses badOracle 2 seed).mpr hmiss
      simpa [eventSeeds] using haccept
  rw [hevents]
  calc
    (missSamples (interactionCoverage.badSet badOracle) 2).card =
        (Fintype.card QueryAssembly.Carrier -
          (interactionCoverage.badSet badOracle).card) ^ 2 :=
      missSamples_card_sub (interactionCoverage.badSet badOracle) 2
    _ = (2 - 1) ^ 2 := by
      rw [badOracle_badSet_card]
      decide
    _ = 1 := by decide

end InteractionRows

#assert_all_clean [
  EffectiveLocalOracle.queryQuotient_apply,
  EffectiveLocalOracle.queryQuotient_effectiveCover,
  EffectiveLocalOracle.rawObserve_coequalizes,
  EffectiveLocalOracle.semanticObserve_fac,
  EffectiveLocalOracle.semanticObserve_spec,
  EffectiveLocalOracle.semanticObserve_unique,
  EffectiveLocalOracle.obstructionPredicate_classified,
  EffectiveLocalOracle.transparentProtocol_pointBinding,
  EffectiveLocalOracle.transparent_factored_soundness,
  InteractionRows.goodFirst_accepts,
  InteractionRows.goodSecond_accepts,
  InteractionRows.badSecond_rejects,
  InteractionRows.quotient_effectiveCover,
  InteractionRows.semanticObserve_eq_reject,
  InteractionRows.badOracle_invalid,
  InteractionRows.goodOracle_valid,
  InteractionRows.badOracle_badSet_card,
  InteractionRows.uniformAccept_iff_misses,
  InteractionRows.two_query_transparent_acceptance_card
]

end Dregg2.Metatheory.RealizabilityLocalRewriteOracle

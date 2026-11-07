/-
# Dregg2.Metatheory.RobustDescentQueryGame -- robust descent meets hidden local queries.

`RobustProofObjectDescent` identifies the finite set of overlap queries on which a submitted
family fails to glue.  This module supplies the next, deliberately probabilistic bridge:

* failure of global amalgamation gives a nonempty finite obstruction set;
* `k` hidden, independent, uniform queries miss a bad set `B` in exactly
  `(|Q| - |B|)^k` cases out of `|Q|^k`;
* a commitment is fixed before those queries are sampled;
* even a query-adaptive responder cannot replace an obstructed local view after seeing the query,
  provided the opening relation is point-binding; and
* consequently accepted samples are a subset of the exact miss set.

This is not deterministic total-object extraction.  In particular it does not contradict the
counterexamples in `FriColumnLogExtractHonest`: an invalid committed object can be accepted whenever
all sampled queries miss its obstruction set.  The theorem prices precisely that event.  Concrete
Merkle/FRI deployments must instantiate `PointBinding` with their computational binding game and
must establish that their verifier's local rejection predicate exposes the chosen obstruction set.
-/
import Dregg2.Metatheory.RobustProofObjectDescent
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Metatheory.RobustDescentQueryGame

open scoped BigOperators
open Dregg2.Metatheory.ProofObjectDescent
open Dregg2.Metatheory.RobustProofObjectDescent

universe u v w q d p

/-! ## 1. Failed gluing has a finite obstruction. -/

section Obstruction

variable {X : Type u} {I : Type v} [DecidableEq X] [Fintype I]
variable (C : FinCover X I) {A : X → Type w}

/-- Existence, rather than uniqueness, of a global section inducing the submitted local family. -/
def HasAmalgamation (s : SectionFamily C A) : Prop :=
  ∃ g : ∀ x, A x, RestrictsTo C.patchSet A s g

/-- **INVALID GLOBAL GLUING HAS TEETH.** If no global section restricts to `s`, then at least one
ordered overlap query witnesses disagreement.  This is the contrapositive of exact descent, not an
assumption that a sampled verifier queried every point. -/
theorem badEdge_card_pos_of_no_amalgamation (s : SectionFamily C A)
    (hno : ¬ HasAmalgamation C s) :
    0 < (overlapBadEdges C s).card := by
  have hne : overlapBadCount C s ≠ 0 := by
    intro hzero
    have hmatch : Matching C.patchSet A s :=
      (overlapBadCount_eq_zero_iff_matching C s).mp hzero
    obtain ⟨g, hg, _huniq⟩ :=
      (matching_iff_existsUnique_amalgamation C.toDataCover s).mp hmatch
    exact hno ⟨g, hg⟩
  exact Nat.pos_of_ne_zero (by simpa [overlapBadCount] using hne)

/-- The obstruction set is nonempty whenever global gluing fails. -/
theorem badEdges_nonempty_of_no_amalgamation (s : SectionFamily C A)
    (hno : ¬ HasAmalgamation C s) :
    (overlapBadEdges C s).Nonempty :=
  Finset.card_pos.mp (badEdge_card_pos_of_no_amalgamation C s hno)

end Obstruction

/-! ## 2. Exact hidden-query counting. -/

section Counting

variable {Query : Type q} [Fintype Query] [DecidableEq Query]

/-- A length-`k` sample misses `bad` when every independently sampled coordinate avoids it. -/
def Misses (bad : Finset Query) {k : ℕ} (sample : Fin k → Query) : Prop :=
  ∀ i, sample i ∉ bad

/-- The finite set of all with-replacement `k`-samples that miss `bad`. -/
noncomputable def missSamples (bad : Finset Query) (k : ℕ) : Finset (Fin k → Query) := by
  classical
  exact Finset.univ.filter (Misses bad)

/-- Missing `bad` is exactly choosing every query from its complement. -/
theorem missSamples_eq_piFinset (bad : Finset Query) (k : ℕ) :
    missSamples bad k = Fintype.piFinset (fun _ : Fin k => badᶜ) := by
  ext sample
  simp [missSamples, Misses]

/-- **EXACT MISS COUNT.** Among the `|Query|^k` uniform independent samples, precisely
`(|Query| - |bad|)^k` miss every obstruction.  No probability infrastructure or extraction
hypothesis is hidden in this identity. -/
theorem missSamples_card (bad : Finset Query) (k : ℕ) :
    (missSamples bad k).card = (badᶜ.card) ^ k := by
  rw [missSamples_eq_piFinset, Fintype.card_piFinset_const]

/-- The complement form of the exact count, exposing the obstruction cardinality itself. -/
theorem missSamples_card_sub (bad : Finset Query) (k : ℕ) :
    (missSamples bad k).card = (Fintype.card Query - bad.card) ^ k := by
  rw [missSamples_card, Finset.card_compl]

/-- The denominator paired with `missSamples_card_sub`: the with-replacement sample space has
exactly `|Query|^k` equiprobable points. -/
theorem allSamples_card (k : ℕ) :
    (Finset.univ : Finset (Fin k → Query)).card = (Fintype.card Query) ^ k := by
  rw [Finset.card_univ, Fintype.card_fun, Fintype.card_fin]

/-- A nonempty obstruction makes a single hidden query's miss set strictly smaller than the whole
query space.  Repetition then amplifies this exact finite deficit through `missSamples_card_sub`. -/
theorem one_query_miss_lt_total {bad : Finset Query} (hbad : bad.Nonempty) :
    (missSamples bad 1).card < Fintype.card Query := by
  rw [missSamples_card_sub, pow_one]
  exact Nat.sub_lt (Fintype.card_pos_iff.mpr ⟨hbad.choose⟩) (Finset.card_pos.mpr hbad)

end Counting

/-! ## 3. Commit before query; answer after query. -/

/-- A local-opening interface.  The prover commits to a complete `Family` before the verifier
chooses a query, but may choose the proposed `View` and opening `Proof` after seeing that query.

`honestProof` gives completeness.  Binding is intentionally a separate predicate below: real hash
commitments satisfy it only under an explicit computational binding assumption/game. -/
structure QueryOpeningScheme (Family : Type u) (Query : Type q) (View : Type v)
    (Digest : Type d) (Proof : Type p) where
  commit : Family → Digest
  view : Family → Query → View
  opens : Digest → Query → View → Proof → Prop
  honestProof : Family → Query → Proof
  honest_opens : ∀ s query, opens (commit s) query (view s query) (honestProof s query)

/-- Point binding at a precommitted family: no valid response to a later query can change that
query's committed view.  This is the exact anti-rewriting property consumed by the game theorem;
it is not asserted for any deployed hash in this module. -/
def PointBinding {Family : Type u} {Query : Type q} {View : Type v}
    {Digest : Type d} {Proof : Type p}
    (S : QueryOpeningScheme Family Query View Digest Proof) : Prop :=
  ∀ s query view proof, S.opens (S.commit s) query view proof → view = S.view s query

/-- A local tester rejects a view at a query. -/
structure LocalTest (Query : Type q) (View : Type v) where
  reject : Query → View → Prop

section Game

variable {Family : Type u} {Query : Type q} {View : Type v}
variable {Digest : Type d} {Proof : Type p}
variable [Fintype Query] [DecidableEq Query]

/-- The actual bad-query set of a committed family under a local test. -/
noncomputable def obstructionSet
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (s : Family) : Finset Query := by
  classical
  exact Finset.univ.filter (fun query => T.reject query (S.view s query))

/-- A responder is fully query-adaptive: after seeing `query`, it selects both a claimed local view
and an opening proof.  The commitment remains `S.commit s`. -/
abbrev Responder (Query : Type q) (View : Type v) (Proof : Type p) :=
  Query → View × Proof

/-- Acceptance of one post-commitment response: its opening verifies and its claimed view passes the
local test. -/
def AcceptsAt (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (s : Family) (R : Responder Query View Proof)
    (query : Query) : Prop :=
  S.opens (S.commit s) query (R query).1 (R query).2 ∧ ¬ T.reject query (R query).1

/-- Acceptance of all `k` hidden queries. -/
def AcceptsSample (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (s : Family) (R : Responder Query View Proof)
    {k : ℕ} (sample : Fin k → Query) : Prop :=
  ∀ i, AcceptsAt S T s R (sample i)

/-- **NO POST-QUERY REWRITING.** Under point binding, an accepted response cannot hide an
obstruction at the queried position, even though `R` was allowed to depend arbitrarily on the
revealed query. -/
theorem acceptsAt_not_obstructed
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (s : Family) (R : Responder Query View Proof) (query : Query)
    (hacc : AcceptsAt S T s R query) :
    ¬ T.reject query (S.view s query) := by
  intro hbad
  have hview : (R query).1 = S.view s query := hbind s query _ _ hacc.1
  apply hacc.2
  rw [hview]
  exact hbad

/-- Every accepted batch is in the exact finite miss set.  This is the bridge from cryptographic
binding to local-testing soundness; it deliberately concludes avoidance, not total extraction. -/
theorem acceptsSample_misses
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (s : Family) (R : Responder Query View Proof) {k : ℕ} (sample : Fin k → Query)
    (hacc : AcceptsSample S T s R sample) :
    Misses (obstructionSet S T s) sample := by
  intro i
  have hgood := acceptsAt_not_obstructed S T hbind s R (sample i) (hacc i)
  classical
  simpa [obstructionSet] using hgood

/-- Accepted samples for a fixed precommitment and an arbitrary adaptive responder. -/
noncomputable def acceptedSamples
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (s : Family) (R : Responder Query View Proof)
    (k : ℕ) : Finset (Fin k → Query) := by
  classical
  exact Finset.univ.filter (AcceptsSample S T s R)

/-- **FINITE GAME BOUND.** Point binding injects no probability magic: it proves the clean set
inclusion saying an adaptive prover's accepting samples are contained in the miss event. -/
theorem acceptedSamples_subset_misses
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (s : Family) (R : Responder Query View Proof) (k : ℕ) :
    acceptedSamples S T s R k ⊆ missSamples (obstructionSet S T s) k := by
  intro sample hs
  classical
  simp only [acceptedSamples, Finset.mem_filter, Finset.mem_univ, true_and] at hs
  simp only [missSamples, Finset.mem_filter, Finset.mem_univ, true_and]
  exact acceptsSample_misses S T hbind s R sample hs

/-- Therefore the exact miss count bounds acceptance, for every query-adaptive responder. -/
theorem acceptedSamples_card_le
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (s : Family) (R : Responder Query View Proof) (k : ℕ) :
    (acceptedSamples S T s R k).card ≤
      ((obstructionSet S T s)ᶜ.card) ^ k := by
  calc
    (acceptedSamples S T s R k).card ≤
        (missSamples (obstructionSet S T s) k).card :=
      Finset.card_le_card (acceptedSamples_subset_misses S T hbind s R k)
    _ = ((obstructionSet S T s)ᶜ.card) ^ k :=
      missSamples_card (obstructionSet S T s) k

end Game

/-! ## 4. The robust-descent adapter. -/

section DescentAdapter

variable {X : Type u} {I : Type q} [DecidableEq X] [Fintype I] [DecidableEq I]
variable (C : FinCover X I) {A : X → Type w}
variable {View : Type v} {Digest : Type d} {Proof : Type p}

/-- If the local tester exposes exactly whole-overlap disagreement, its game obstruction set is the
finite obstruction set already used by exact/robust descent. -/
theorem obstructionSet_eq_overlapBadEdges
    (S : QueryOpeningScheme (SectionFamily C A) (I × I) View Digest Proof)
    (T : LocalTest (I × I) View) (s : SectionFamily C A)
    (hfaithful : ∀ edge, T.reject edge (S.view s edge) ↔ wholeOverlapReject s edge) :
    obstructionSet S T s = overlapBadEdges C s := by
  classical
  ext edge
  simp [obstructionSet, overlapBadEdges, hfaithful edge]

/-- **ROBUST DESCENT QUERY GAME.** A non-gluable family has a positive obstruction count.  Once its
commitment is fixed, any adaptive responder accepted on `k` hidden queries succeeds on at most
`(|I×I| - |badEdges|)^k` samples.  This is the corrected probabilistic replacement for a false
deterministic claim that accepted spot checks extract a total globally glued object. -/
theorem invalid_gluing_acceptance_bound
    (S : QueryOpeningScheme (SectionFamily C A) (I × I) View Digest Proof)
    (T : LocalTest (I × I) View) (hbind : PointBinding S)
    (s : SectionFamily C A) (hno : ¬ HasAmalgamation C s)
    (hfaithful : ∀ edge, T.reject edge (S.view s edge) ↔ wholeOverlapReject s edge)
    (R : Responder (I × I) View Proof) (k : ℕ) :
    0 < (overlapBadEdges C s).card ∧
      (acceptedSamples S T s R k).card ≤
        ((overlapBadEdges C s)ᶜ.card) ^ k := by
  constructor
  · exact badEdge_card_pos_of_no_amalgamation C s hno
  · rw [← obstructionSet_eq_overlapBadEdges C S T s hfaithful]
    exact acceptedSamples_card_le S T hbind s R k

end DescentAdapter

/-! ## 5. Non-vacuous reference game. -/

namespace Reference

/-- A transparent, information-theoretically point-binding commitment.  It is a reference witness
for the game wiring, not a model of a compressing cryptographic digest. -/
def transparentScheme {Family : Type u} {Query : Type q} {View : Type v}
    (view : Family → Query → View) :
    QueryOpeningScheme Family Query View Family Unit where
  commit s := s
  view := view
  opens digest query claimed _ := claimed = view digest query
  honestProof _ _ := ()
  honest_opens _ _ := rfl

theorem transparentScheme_pointBinding {Family : Type u} {Query : Type q} {View : Type v}
    (view : Family → Query → View) :
    PointBinding (transparentScheme view) := by
  intro _s _query _claimed _proof hopen
  exact hopen

open Dregg2.Metatheory.RobustProofObjectDescent.UnitPair

/-- The committed view bit says whether this ordered overlap edge is obstructed. -/
noncomputable def edgeView
    (s : SectionFamily cover (fun _ : Unit => Bool)) (edge : Bool × Bool) : Bool := by
  classical
  exact decide (wholeOverlapReject s edge)

def rejectTrue : LocalTest (Bool × Bool) Bool where
  reject _ bit := bit = true

noncomputable def edgeScheme :
    QueryOpeningScheme (SectionFamily cover (fun _ : Unit => Bool))
      (Bool × Bool) Bool (SectionFamily cover (fun _ : Unit => Bool)) Unit :=
  transparentScheme edgeView

theorem edgeScheme_pointBinding : PointBinding edgeScheme :=
  transparentScheme_pointBinding edgeView

theorem edge_test_faithful (s : SectionFamily cover (fun _ : Unit => Bool)) (edge : Bool × Bool) :
    rejectTrue.reject edge (edgeScheme.view s edge) ↔ wholeOverlapReject s edge := by
  classical
  change decide (wholeOverlapReject s edge) = true ↔ wholeOverlapReject s edge
  simp

/-- The inconsistent two-patch family has exactly the two off-diagonal ordered edges as
obstructions. -/
theorem disagreeing_badEdges :
    overlapBadEdges cover disagreeing = {(false, true), (true, false)} := by
  classical
  ext edge
  rcases edge with ⟨i, j⟩
  cases i <;> cases j <;>
    simp only [overlapBadEdges, Finset.mem_filter, Finset.mem_univ, true_and] <;>
    simp [wholeOverlapReject, disagreeing, pairSection,
      FinCover.patchSet, cover, patch]

/-- Two hidden independent overlap queries miss the inconsistent family's two bad edges in exactly
`2^2 = 4` samples out of `4^2 = 16`. -/
theorem disagreeing_two_query_miss_card :
    (missSamples (overlapBadEdges cover disagreeing) 2).card = 4 := by
  rw [missSamples_card, disagreeing_badEdges]
  decide

/-- A maximally brazen post-query responder always claims "no obstruction".  At a genuinely bad
edge its opening cannot verify against the already fixed transparent commitment. -/
def denyEveryObstruction : Responder (Bool × Bool) Bool Unit := fun _ => (false, ())

theorem deny_bad_edge_rejected :
    ¬ AcceptsAt edgeScheme rejectTrue disagreeing denyEveryObstruction (false, true) := by
  classical
  simp [AcceptsAt, edgeScheme, transparentScheme, edgeView, rejectTrue,
    denyEveryObstruction, wholeOverlapReject, disagreeing, pairSection,
    cover, patch]

/-- The full bridge fires on the inconsistent family: positive obstruction count and an exact
four-sample upper bound for the adaptive denier at `k = 2`. -/
theorem disagreeing_game_bound :
    0 < (overlapBadEdges cover disagreeing).card ∧
      (acceptedSamples edgeScheme rejectTrue disagreeing denyEveryObstruction 2).card ≤ 4 := by
  have hno : ¬ HasAmalgamation cover disagreeing := by
    intro h
    obtain ⟨g, hg⟩ := h
    have hzero := zero_overlap_of_amalgamation cover disagreeing g hg
    rw [overlapBadCount, disagreeing_badEdges] at hzero
    norm_num at hzero
  have h := invalid_gluing_acceptance_bound cover edgeScheme rejectTrue edgeScheme_pointBinding
    disagreeing hno (edge_test_faithful disagreeing) denyEveryObstruction 2
  constructor
  · exact h.1
  · calc
      (acceptedSamples edgeScheme rejectTrue disagreeing denyEveryObstruction 2).card ≤
          ((overlapBadEdges cover disagreeing)ᶜ.card) ^ 2 := h.2
      _ = 4 := by rw [disagreeing_badEdges]; decide

end Reference

/-! ## 6. Axiom-hygiene pins. -/

#assert_all_clean [
  badEdge_card_pos_of_no_amalgamation,
  badEdges_nonempty_of_no_amalgamation,
  missSamples_card,
  missSamples_card_sub,
  allSamples_card,
  one_query_miss_lt_total,
  acceptsAt_not_obstructed,
  acceptsSample_misses,
  acceptedSamples_subset_misses,
  acceptedSamples_card_le,
  obstructionSet_eq_overlapBadEdges,
  invalid_gluing_acceptance_bound,
  Reference.transparentScheme_pointBinding,
  Reference.edge_test_faithful,
  Reference.disagreeing_badEdges,
  Reference.disagreeing_two_query_miss_card,
  Reference.deny_bad_edge_rejected,
  Reference.disagreeing_game_bound]

end Dregg2.Metatheory.RobustDescentQueryGame

/-
# Dregg2.Metatheory.RobustDescentTranscriptGame -- transcript-biased robust soundness.

This module composes `RobustDescentQueryGame` with DREGG's finite query-bias accounting.  The
protocol order is explicit: a family is committed first; a finite transcript seed then determines
the OOD/low-degree challenges and the local queries; only then may the prover choose query-adaptive
openings.  Point binding prevents those openings from rewriting the committed local views.

For an invalid object, a protocol-specific reduction may say that acceptance implies one of:

1. an OOD exceptional event;
2. a low-degree/folding exceptional event; or
3. successful locally bound openings at every sampled query.

The third event is contained in the obstruction-miss event.  We prove an exact finite union bound,
then instantiate its query term with the existing modular-reduction bias theorems, including the
sharp `N % m = 1` bound.  Nothing extracts a deterministic total column: a bad committed object may
still pass on a transcript whose queries miss every obstruction, and that event is the explicit
query term in the final inequality.
-/
import Dregg2.Metatheory.RobustDescentQueryGame
import Dregg2.Circuit.FriQueryBiasSharp
import Mathlib.Tactic.FinCases

set_option autoImplicit false
set_option linter.unusedSectionVars false

namespace Dregg2.Metatheory.RobustDescentTranscriptGame

open Dregg2.Metatheory.RobustDescentQueryGame
open Dregg2.Circuit.FriQuerySamplingBias
open Dregg2.Circuit.FriQueryBiasSharp

universe u q v d p s

/-! ## 1. Commit-before-seed transcript game. -/

section Transcript

variable {Family : Type u} {Query : Type q} {View : Type v}
variable {Digest : Type d} {Proof : Type p} {Seed : Type s}
variable [Fintype Query] [DecidableEq Query] [Fintype Seed] [DecidableEq Seed]

/-- A prover may use the entire revealed seed and the coordinate number when constructing each
opening.  This is strictly more adaptive than a response depending only on the derived query. -/
abbrev TranscriptResponder (Seed : Type s) (k : ℕ) (View : Type v) (Proof : Type p) :=
  Seed → Fin k → View × Proof

/-- Every response opens against the digest fixed as `S.commit family` before `seed`, and every
claimed local view passes the test. -/
def LocallyAccepts
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (family : Family) {k : ℕ}
    (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof) (seed : Seed) : Prop :=
  ∀ i,
    S.opens (S.commit family) (queries seed i) (respond seed i).1 (respond seed i).2 ∧
      ¬ T.reject (queries seed i) (respond seed i).1

/-- **ADAPTIVE REWRITING STILL FAILS.** Point binding forces every accepted transcript coordinate
to equal the committed view, even though the response can inspect the whole seed.  Therefore the
derived sample misses the committed family's obstruction set. -/
theorem locallyAccepts_misses
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (family : Family) {k : ℕ} (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof) (seed : Seed)
    (hacc : LocallyAccepts S T family queries respond seed) :
    Misses (obstructionSet S T family) (queries seed) := by
  intro i
  have hi := hacc i
  have hview : (respond seed i).1 = S.view family (queries seed i) :=
    hbind family (queries seed i) _ _ hi.1
  classical
  simp only [obstructionSet, Finset.mem_filter, Finset.mem_univ, true_and]
  intro hbad
  apply hi.2
  rw [hview]
  exact hbad

/-- Finite event set under the uniform seed distribution. -/
noncomputable def eventSeeds (P : Seed → Prop) : Finset Seed := by
  classical
  exact Finset.univ.filter P

/-- Uniform finite-seed probability, in the same cardinality-over-cardinality style used by the
OOD and FRI game modules. -/
noncomputable def uniformSeedProb (P : Seed → Prop) : ℝ :=
  ((eventSeeds P).card : ℝ) / (Fintype.card Seed : ℝ)

/-- Seeds whose derived query vector misses a chosen obstruction set. -/
noncomputable def missSeedSet {k : ℕ} (queries : Seed → Fin k → Query)
    (bad : Finset Query) : Finset Seed :=
  eventSeeds (fun seed => Misses bad (queries seed))

/-- A protocol-specific algebraic reduction socket.  For the fixed invalid family, full acceptance
must reduce to either locally valid bound openings, an OOD exceptional seed, or a low-degree/folding
exceptional seed.  The latter two predicates stay separate so their errors remain visible. -/
def AcceptanceReduction
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (family : Family) {k : ℕ}
    (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop) : Prop :=
  ∀ seed, accept seed →
    LocallyAccepts S T family queries respond seed ∨ oodBad seed ∨ lowDegreeBad seed

/-- The accepting seeds are contained in the union of the two algebraic exceptional events and the
query-miss event.  This is the event-level soundness statement before any numerical bounds. -/
theorem acceptSeeds_subset_exceptional_union_miss
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (family : Family) {k : ℕ} (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction S T family queries respond accept oodBad lowDegreeBad) :
    eventSeeds accept ⊆
      (eventSeeds oodBad ∪ eventSeeds lowDegreeBad) ∪
        missSeedSet queries (obstructionSet S T family) := by
  intro seed hseed
  classical
  have hacc : accept seed := by simpa [eventSeeds] using hseed
  rcases hreduce seed hacc with hlocal | hood | hldt
  · have hmiss := locallyAccepts_misses S T hbind family queries respond seed hlocal
    simp [eventSeeds, missSeedSet, hmiss]
  · simp [eventSeeds, hood]
  · simp [eventSeeds, hldt]

/-- **EXACT FINITE UNION BOUND.** False acceptance is at most the sum of the OOD-event count, the
low-degree-event count, and the exact query-miss count. -/
theorem acceptSeed_card_le_union
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (family : Family) {k : ℕ} (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction S T family queries respond accept oodBad lowDegreeBad) :
    (eventSeeds accept).card ≤
      (eventSeeds oodBad).card + (eventSeeds lowDegreeBad).card +
        (missSeedSet queries (obstructionSet S T family)).card := by
  calc
    (eventSeeds accept).card ≤
        ((eventSeeds oodBad ∪ eventSeeds lowDegreeBad) ∪
          missSeedSet queries (obstructionSet S T family)).card :=
      Finset.card_le_card
        (acceptSeeds_subset_exceptional_union_miss S T hbind family queries respond
          accept oodBad lowDegreeBad hreduce)
    _ ≤ (eventSeeds oodBad ∪ eventSeeds lowDegreeBad).card +
          (missSeedSet queries (obstructionSet S T family)).card :=
      Finset.card_union_le _ _
    _ ≤ (eventSeeds oodBad).card + (eventSeeds lowDegreeBad).card +
          (missSeedSet queries (obstructionSet S T family)).card := by
      gcongr
      exact Finset.card_union_le _ _

/-- A denominator-free budget form convenient for concrete cryptographic games. -/
theorem acceptSeed_card_le_budgets
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (family : Family) {k : ℕ} (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction S T family queries respond accept oodBad lowDegreeBad)
    (oodBudget lowDegreeBudget queryBudget : ℕ)
    (hood : (eventSeeds oodBad).card ≤ oodBudget)
    (hldt : (eventSeeds lowDegreeBad).card ≤ lowDegreeBudget)
    (hquery : (missSeedSet queries (obstructionSet S T family)).card ≤ queryBudget) :
    (eventSeeds accept).card ≤ oodBudget + lowDegreeBudget + queryBudget := by
  exact (acceptSeed_card_le_union S T hbind family queries respond accept oodBad lowDegreeBad
    hreduce).trans (by omega)

/-- The probability presentation of the same exact union bound. -/
theorem acceptProb_le_union
    (S : QueryOpeningScheme Family Query View Digest Proof)
    (T : LocalTest Query View) (hbind : PointBinding S)
    (family : Family) {k : ℕ} (queries : Seed → Fin k → Query)
    (respond : TranscriptResponder Seed k View Proof)
    (accept oodBad lowDegreeBad : Seed → Prop)
    (hreduce : AcceptanceReduction S T family queries respond accept oodBad lowDegreeBad) :
    uniformSeedProb accept ≤
      uniformSeedProb oodBad + uniformSeedProb lowDegreeBad +
        uniformSeedProb (fun seed => Misses (obstructionSet S T family) (queries seed)) := by
  have hnat := acceptSeed_card_le_union S T hbind family queries respond
    accept oodBad lowDegreeBad hreduce
  have hreal : ((eventSeeds accept).card : ℝ) ≤
      ((eventSeeds oodBad).card : ℝ) + ((eventSeeds lowDegreeBad).card : ℝ) +
        ((missSeedSet queries (obstructionSet S T family)).card : ℝ) := by
    exact_mod_cast hnat
  unfold uniformSeedProb
  have hdiv := div_le_div_of_nonneg_right hreal (by positivity : (0 : ℝ) ≤ Fintype.card Seed)
  rw [show missSeedSet queries (obstructionSet S T family) =
      eventSeeds (fun seed => Misses (obstructionSet S T family) (queries seed)) from rfl] at hdiv
  calc
    ((eventSeeds accept).card : ℝ) / (Fintype.card Seed : ℝ) ≤
        (((eventSeeds oodBad).card : ℝ) + ((eventSeeds lowDegreeBad).card : ℝ) +
          ((eventSeeds (fun seed =>
            Misses (obstructionSet S T family) (queries seed))).card : ℝ)) /
            (Fintype.card Seed : ℝ) := hdiv
    _ = ((eventSeeds oodBad).card : ℝ) / (Fintype.card Seed : ℝ) +
          ((eventSeeds lowDegreeBad).card : ℝ) / (Fintype.card Seed : ℝ) +
          ((eventSeeds (fun seed =>
            Misses (obstructionSet S T family) (queries seed))).card : ℝ) /
            (Fintype.card Seed : ℝ) := by ring

end Transcript

/-! ### Extra transcript coordinates.

OOD and folding challenges normally occupy additional Fiat--Shamir squeeze coordinates beyond the
`k` query-index squeezes.  The next identity shows that such coordinates product out of an event
depending only on the query marginal.  Thus the later query bound remains valid while `oodBad` and
`lowDegreeBad` may inspect the entire, correlated transcript. -/

section ProductLift

variable {Extra : Type u} {Base : Type q}
variable [Fintype Extra] [DecidableEq Extra] [Nonempty Extra]
variable [Fintype Base] [DecidableEq Base] [Nonempty Base]

theorem eventSeeds_snd_eq_product (P : Base → Prop) :
    eventSeeds (fun seed : Extra × Base => P seed.2) =
      (Finset.univ : Finset Extra) ×ˢ (eventSeeds P) := by
  classical
  ext seed
  simp [eventSeeds]

/-- Uniform extra transcript coordinates do not change the probability of a query-marginal event. -/
theorem uniformSeedProb_snd (P : Base → Prop) :
    uniformSeedProb (fun seed : Extra × Base => P seed.2) = uniformSeedProb P := by
  unfold uniformSeedProb
  rw [eventSeeds_snd_eq_product, Finset.card_product,
    Finset.card_univ, Fintype.card_prod]
  push_cast
  have hExtra : (Fintype.card Extra : ℝ) ≠ 0 := by positivity
  have hBase : (Fintype.card Base : ℝ) ≠ 0 := by positivity
  field_simp

end ProductLift

/-! ## 2. DREGG's modular-reduction query sampler. -/

section ModularBias

/-- A squeezed field representative reduced to one of `m` query indices. -/
def modQuery {N m : ℕ} (hm : 0 < m) (seed : Fin N) : Fin m :=
  ⟨seed.val % m, Nat.mod_lt _ hm⟩

/-- `k` independent squeeze values, each reduced modulo the query-domain size. -/
def modQueries {N m k : ℕ} (hm : 0 < m) (seed : Fin k → Fin N) : Fin k → Fin m :=
  fun i => modQuery hm (seed i)

/-- Natural-number residues corresponding to the complement of a bad query set. -/
def goodResidues {m : ℕ} (bad : Finset (Fin m)) : Finset ℕ :=
  badᶜ.image Fin.val

theorem mem_goodResidues_iff {N m : ℕ} (hm : 0 < m) (bad : Finset (Fin m)) (seed : Fin N) :
    seed.val % m ∈ goodResidues bad ↔ modQuery hm seed ∉ bad := by
  simp only [goodResidues, Finset.mem_image, Finset.mem_compl]
  constructor
  · rintro ⟨q, hq, hval⟩
    have heq : q = modQuery hm seed := Fin.ext hval
    simpa [heq] using hq
  · intro hq
    exact ⟨modQuery hm seed, hq, rfl⟩

theorem goodResidues_card {m : ℕ} (bad : Finset (Fin m)) :
    (goodResidues bad).card = badᶜ.card := by
  exact Finset.card_image_of_injective badᶜ Fin.val_injective

theorem goodResidues_card_le {m : ℕ} (bad : Finset (Fin m)) :
    (goodResidues bad).card ≤ m := by
  rw [goodResidues_card]
  simpa using Finset.card_le_univ badᶜ

/-- The generic miss event is definitionally the biased FRI survivor event after translating finite
queries to their natural residue representatives. -/
theorem mod_miss_event_eq {N m k : ℕ} (hm : 0 < m) (bad : Finset (Fin m)) :
    eventSeeds (fun seed : Fin k → Fin N => Misses bad (modQueries hm seed)) =
      Finset.univ.filter (fun seed : Fin k → Fin N =>
        ∀ i, (seed i).val % m ∈ goodResidues bad) := by
  classical
  ext seed
  simp only [eventSeeds, Finset.mem_filter, Finset.mem_univ, true_and]
  simp only [Misses, modQueries]
  exact forall_congr' (fun i => (mem_goodResidues_iff hm bad (seed i)).symm)

/-- Exact query-miss numerator under modularly reduced transcript seeds. -/
theorem mod_miss_event_card {N m k : ℕ} (hm : 0 < m) (bad : Finset (Fin m)) :
    (eventSeeds (fun seed : Fin k → Fin N => Misses bad (modQueries hm seed))).card =
      (Finset.univ.filter (fun a : Fin N => a.val % m ∈ goodResidues bad)).card ^ k := by
  rw [mod_miss_event_eq hm bad]
  exact biased_accepting_card N m k (goodResidues bad)

/-- **BIASED QUERY TERM.** The existing DREGG modular-reduction theorem bounds the query-miss
probability by `((1-δ)+m/N)^k`. -/
theorem mod_miss_prob_le {N m k : ℕ} (hN : 0 < N) (hm : 0 < m)
    (bad : Finset (Fin m)) (δ : ℝ)
    (hdensity : ((goodResidues bad).card : ℝ) / (m : ℝ) ≤ 1 - δ) :
    uniformSeedProb (fun seed : Fin k → Fin N => Misses bad (modQueries hm seed)) ≤
      ((1 - δ) + (m : ℝ) / (N : ℝ)) ^ k := by
  rw [uniformSeedProb, mod_miss_event_eq hm bad]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  exact biased_query_survival_pow_le N m k (goodResidues bad) δ hN hm
    (goodResidues_card_le bad) hdensity

/-- **SHARP BIASED QUERY TERM.** In the DREGG/BabyBear shape `N % m = 1`, only one residue is
heavy, so the strongest existing bound is `((1-δ)+δ/N)^k`. -/
theorem mod_miss_prob_le_sharp {N m k : ℕ} (hN : 0 < N) (hm : 0 < m)
    (hmod : N % m = 1) (bad : Finset (Fin m)) (δ : ℝ)
    (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hdensity : ((goodResidues bad).card : ℝ) / (m : ℝ) ≤ 1 - δ) :
    uniformSeedProb (fun seed : Fin k → Fin N => Misses bad (modQueries hm seed)) ≤
      ((1 - δ) + δ / (N : ℝ)) ^ k := by
  rw [uniformSeedProb, mod_miss_event_eq hm bad]
  simp only [Fintype.card_fun, Fintype.card_fin]
  push_cast
  exact biased_query_survival_sharp N m k (goodResidues bad) δ hN hm hmod hδ0 hδ1 hdensity

end ModularBias

/-! ## 3. Full transcript soundness with separate error terms. -/

section Composition

variable {Family : Type u} {View : Type v} {Digest : Type d} {Proof : Type p}
variable {N m k : ℕ}

/-- **HONEST BIAS-AWARE TRANSCRIPT SOUNDNESS.** For a fixed precommitted invalid object, any full
acceptance predicate satisfying the protocol reduction has probability at most

`epsilonOOD + epsilonLDT + ((1-delta) + m/N)^k`.

The first two terms are independent sockets for the existing OOD Schwartz--Zippel and FRI
low-degree/folding games.  The last term is the proved modular-reduction query bias.  Point binding
removes adaptive rewriting as an additional information-theoretic event; a computational deployment
must account separately for the advantage of breaking that binding premise. -/
theorem biased_transcript_soundness
    (hN : 0 < N) (hm : 0 < m)
    (S : QueryOpeningScheme Family (Fin m) View Digest Proof)
    (T : LocalTest (Fin m) View) (hbind : PointBinding S) (family : Family)
    (respond : TranscriptResponder (Fin k → Fin N) k View Proof)
    (accept oodBad lowDegreeBad : (Fin k → Fin N) → Prop)
    (hreduce : AcceptanceReduction S T family (modQueries hm) respond
      accept oodBad lowDegreeBad)
    (εOOD εLDT δ : ℝ)
    (hood : uniformSeedProb oodBad ≤ εOOD)
    (hldt : uniformSeedProb lowDegreeBad ≤ εLDT)
    (hdensity : ((goodResidues (obstructionSet S T family)).card : ℝ) / (m : ℝ)
      ≤ 1 - δ) :
    uniformSeedProb accept ≤
      εOOD + εLDT + ((1 - δ) + (m : ℝ) / (N : ℝ)) ^ k := by
  calc
    uniformSeedProb accept ≤ uniformSeedProb oodBad + uniformSeedProb lowDegreeBad +
        uniformSeedProb (fun seed =>
          Misses (obstructionSet S T family) (modQueries hm seed)) :=
      acceptProb_le_union S T hbind family (modQueries hm) respond
        accept oodBad lowDegreeBad hreduce
    _ ≤ εOOD + εLDT + ((1 - δ) + (m : ℝ) / (N : ℝ)) ^ k := by
      gcongr
      exact mod_miss_prob_le hN hm (obstructionSet S T family) δ hdensity

/-- The strongest existing `N % m = 1` composition uses the sharp DREGG bias term
`((1-δ)+δ/N)^k`. -/
theorem biased_transcript_soundness_sharp
    (hN : 0 < N) (hm : 0 < m) (hmod : N % m = 1)
    (S : QueryOpeningScheme Family (Fin m) View Digest Proof)
    (T : LocalTest (Fin m) View) (hbind : PointBinding S) (family : Family)
    (respond : TranscriptResponder (Fin k → Fin N) k View Proof)
    (accept oodBad lowDegreeBad : (Fin k → Fin N) → Prop)
    (hreduce : AcceptanceReduction S T family (modQueries hm) respond
      accept oodBad lowDegreeBad)
    (εOOD εLDT δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hood : uniformSeedProb oodBad ≤ εOOD)
    (hldt : uniformSeedProb lowDegreeBad ≤ εLDT)
    (hdensity : ((goodResidues (obstructionSet S T family)).card : ℝ) / (m : ℝ)
      ≤ 1 - δ) :
    uniformSeedProb accept ≤
      εOOD + εLDT + ((1 - δ) + δ / (N : ℝ)) ^ k := by
  calc
    uniformSeedProb accept ≤ uniformSeedProb oodBad + uniformSeedProb lowDegreeBad +
        uniformSeedProb (fun seed =>
          Misses (obstructionSet S T family) (modQueries hm seed)) :=
      acceptProb_le_union S T hbind family (modQueries hm) respond
        accept oodBad lowDegreeBad hreduce
    _ ≤ εOOD + εLDT + ((1 - δ) + δ / (N : ℝ)) ^ k := by
      gcongr
      exact mod_miss_prob_le_sharp hN hm hmod (obstructionSet S T family) δ hδ0 hδ1 hdensity

/-- **FULL-TRANSCRIPT SHARP COMPOSITION.** `Extra` holds every non-query Fiat--Shamir coordinate
(OOD points, folding challenges, batching challenges, and so on).  The exceptional predicates and
adaptive responder may inspect all of it.  Only the query vector projects to the final `k` squeeze
coordinates, whose sharp bias term is unchanged because the extra uniform coordinates product out.
No independence between the OOD and low-degree events is required by the union bound. -/
theorem biased_transcript_soundness_sharp_extra
    {Extra : Type s} [Fintype Extra] [DecidableEq Extra] [Nonempty Extra]
    (hN : 0 < N) (hm : 0 < m) (hmod : N % m = 1)
    (S : QueryOpeningScheme Family (Fin m) View Digest Proof)
    (T : LocalTest (Fin m) View) (hbind : PointBinding S) (family : Family)
    (respond : TranscriptResponder (Extra × (Fin k → Fin N)) k View Proof)
    (accept oodBad lowDegreeBad : (Extra × (Fin k → Fin N)) → Prop)
    (hreduce : AcceptanceReduction S T family
      (fun seed => modQueries hm seed.2) respond accept oodBad lowDegreeBad)
    (εOOD εLDT δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hood : uniformSeedProb oodBad ≤ εOOD)
    (hldt : uniformSeedProb lowDegreeBad ≤ εLDT)
    (hdensity : ((goodResidues (obstructionSet S T family)).card : ℝ) / (m : ℝ)
      ≤ 1 - δ) :
    uniformSeedProb accept ≤
      εOOD + εLDT + ((1 - δ) + δ / (N : ℝ)) ^ k := by
  let n0 : Fin N := ⟨0, hN⟩
  letI : Nonempty (Fin k → Fin N) := ⟨fun _ => n0⟩
  have hunion :
      uniformSeedProb accept ≤ uniformSeedProb oodBad + uniformSeedProb lowDegreeBad +
        uniformSeedProb (fun seed : Extra × (Fin k → Fin N) =>
          Misses (obstructionSet S T family) (modQueries hm seed.2)) :=
    acceptProb_le_union (Seed := Extra × (Fin k → Fin N)) (k := k)
      S T hbind family (fun seed => modQueries hm seed.2) respond
        accept oodBad lowDegreeBad hreduce
  calc
    uniformSeedProb accept ≤ uniformSeedProb oodBad + uniformSeedProb lowDegreeBad +
        uniformSeedProb (fun seed : Extra × (Fin k → Fin N) =>
          Misses (obstructionSet S T family) (modQueries hm seed.2)) := hunion
    _ = uniformSeedProb oodBad + uniformSeedProb lowDegreeBad +
        uniformSeedProb (fun seed : Fin k → Fin N =>
          Misses (obstructionSet S T family) (modQueries hm seed)) := by
      have hprod := uniformSeedProb_snd (Extra := Extra) (Base := Fin k → Fin N)
        (fun seed => Misses (obstructionSet S T family) (modQueries hm seed))
      rw [hprod]
    _ ≤ εOOD + εLDT + ((1 - δ) + δ / (N : ℝ)) ^ k := by
      gcongr
      exact mod_miss_prob_le_sharp hN hm hmod (obstructionSet S T family) δ hδ0 hδ1 hdensity

/-- **BABYBEAR/DREGG TRANSCRIPT BOUND.** At every realizable FRI domain
`1 ≤ logN ≤ 27`, `|BabyBear| % 2^logN = 1`; hence the complete transcript bound is

`epsilonOOD + epsilonLDT + ((1-delta) + delta/2013265921)^k`.

The query-bias defect is independent of trace height, exactly as proved by
`FriQueryBiasSharp.babybear_mod_two_pow_eq_one`. -/
theorem babybear_transcript_soundness_sharp_extra
    {Extra : Type s} [Fintype Extra] [DecidableEq Extra] [Nonempty Extra]
    (logN : ℕ) (hlo : 0 < logN) (hhi : logN ≤ 27)
    (S : QueryOpeningScheme Family (Fin (2 ^ logN)) View Digest Proof)
    (T : LocalTest (Fin (2 ^ logN)) View) (hbind : PointBinding S) (family : Family)
    (respond : TranscriptResponder (Extra × (Fin k → Fin 2013265921)) k View Proof)
    (accept oodBad lowDegreeBad : (Extra × (Fin k → Fin 2013265921)) → Prop)
    (hreduce : AcceptanceReduction S T family
      (fun seed => modQueries (pow_pos (by norm_num : 0 < (2 : ℕ)) logN) seed.2)
      respond accept oodBad lowDegreeBad)
    (εOOD εLDT δ : ℝ) (hδ0 : 0 ≤ δ) (hδ1 : δ ≤ 1)
    (hood : uniformSeedProb oodBad ≤ εOOD)
    (hldt : uniformSeedProb lowDegreeBad ≤ εLDT)
    (hdensity :
      ((goodResidues (obstructionSet S T family)).card : ℝ) / ((2 : ℝ) ^ logN) ≤ 1 - δ) :
    uniformSeedProb accept ≤
      εOOD + εLDT + ((1 - δ) + δ / (2013265921 : ℝ)) ^ k := by
  have hm : 0 < (2 : ℕ) ^ logN := pow_pos (by norm_num) logN
  have hdensity' :
      ((goodResidues (obstructionSet S T family)).card : ℝ) /
          (((2 : ℕ) ^ logN : ℕ) : ℝ) ≤ 1 - δ := by
    push_cast
    exact hdensity
  exact biased_transcript_soundness_sharp_extra
    (N := 2013265921) (m := 2 ^ logN) (k := k)
    (by norm_num) hm (babybear_mod_two_pow_eq_one logN hlo hhi)
    S T hbind family respond accept oodBad lowDegreeBad hreduce
    εOOD εLDT δ hδ0 hδ1 hood hldt hdensity'

end Composition

/-! ## 4. Non-vacuous finite transcript. -/

namespace Reference

open Dregg2.Metatheory.RobustDescentQueryGame.Reference

def toyView (_ : Unit) (query : Fin 2) : Bool := decide (query = 1)

def toyScheme : QueryOpeningScheme Unit (Fin 2) Bool Unit Unit :=
  transparentScheme toyView

def toyTest : LocalTest (Fin 2) Bool where
  reject _ bit := bit = true

theorem toyScheme_pointBinding : PointBinding toyScheme :=
  transparentScheme_pointBinding toyView

abbrev ToySeed := Fin 1 → Fin 5

def toyQueries : ToySeed → Fin 1 → Fin 2 := modQueries (by norm_num)

def toyRespond : TranscriptResponder ToySeed 1 Bool Unit := fun seed i =>
  (toyView () (toyQueries seed i), ())

def toyOodBad (seed : ToySeed) : Prop := (seed 0).val = 1
def toyLowDegreeBad (seed : ToySeed) : Prop := (seed 0).val = 3

def toyAccept (seed : ToySeed) : Prop :=
  LocallyAccepts toyScheme toyTest () toyQueries toyRespond seed ∨
    toyOodBad seed ∨ toyLowDegreeBad seed

def toySeed (value : Fin 5) : ToySeed := fun _ => value

theorem toySeed_eq_iff (seed : ToySeed) (value : Fin 5) :
    seed = toySeed value ↔ seed 0 = value := by
  constructor
  · intro h
    rw [h]
    rfl
  · intro h
    funext i
    fin_cases i
    exact h

theorem toyReduction : AcceptanceReduction toyScheme toyTest () toyQueries toyRespond
    toyAccept toyOodBad toyLowDegreeBad := by
  intro seed h
  exact h

theorem toy_obstructionSet : obstructionSet toyScheme toyTest () = {1} := by
  classical
  ext query
  fin_cases query <;> simp [obstructionSet, toyScheme, transparentScheme, toyView, toyTest]

theorem toy_ood_prob : uniformSeedProb toyOodBad = 1 / 5 := by
  have hset : eventSeeds toyOodBad = {toySeed 1} := by
    classical
    ext seed
    simp only [eventSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [toySeed_eq_iff]
    change (seed 0).val = (1 : Fin 5).val ↔ seed 0 = (1 : Fin 5)
    exact Fin.ext_iff.symm
  rw [uniformSeedProb, hset]
  norm_num [Fintype.card_fun]

theorem toy_lowDegree_prob : uniformSeedProb toyLowDegreeBad = 1 / 5 := by
  have hset : eventSeeds toyLowDegreeBad = {toySeed 3} := by
    classical
    ext seed
    simp only [eventSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_singleton]
    rw [toySeed_eq_iff]
    change (seed 0).val = (3 : Fin 5).val ↔ seed 0 = (3 : Fin 5)
    exact Fin.ext_iff.symm
  rw [uniformSeedProb, hset]
  norm_num [Fintype.card_fun]

theorem toy_density :
    ((goodResidues (obstructionSet toyScheme toyTest ())).card : ℝ) / 2 = 1 - (1 / 2 : ℝ) := by
  rw [toy_obstructionSet]
  have hc : (goodResidues ({1} : Finset (Fin 2))).card = 1 := by decide
  rw [hc]
  norm_num

theorem toy_locallyAccepts_iff (seed : ToySeed) :
    LocallyAccepts toyScheme toyTest () toyQueries toyRespond seed ↔
      (seed 0).val % 2 = 0 := by
  simp [LocallyAccepts, toyScheme, transparentScheme, toyView, toyTest,
    toyRespond, toyQueries, modQueries, modQuery, Fin.ext_iff]

theorem toy_misses_iff (seed : ToySeed) :
    Misses ({1} : Finset (Fin 2)) (toyQueries seed) ↔ (seed 0).val % 2 = 0 := by
  constructor
  · intro h
    have hi := h 0
    simp only [Finset.mem_singleton] at hi
    have hne : (seed 0).val % 2 ≠ 1 := by
      intro hv
      apply hi
      apply Fin.ext
      exact hv
    have hlt := Nat.mod_lt (seed 0).val (by norm_num : 0 < 2)
    omega
  · intro heven i
    have hi : i = 0 := Subsingleton.elim _ _
    subst i
    simp only [Finset.mem_singleton]
    intro heq
    have hv := congrArg Fin.val heq
    simp only [toyQueries, modQueries, modQuery] at hv
    norm_num at hv
    omega

/-- The sharp query term is attained: three of five squeezes reduce to the sole good residue `0`. -/
theorem toy_query_miss_prob :
    uniformSeedProb (fun seed : ToySeed =>
      Misses (obstructionSet toyScheme toyTest ()) (toyQueries seed)) = 3 / 5 := by
  rw [toy_obstructionSet]
  have hset : (eventSeeds (fun seed : ToySeed =>
      Misses ({1} : Finset (Fin 2)) (toyQueries seed))) =
      {toySeed 0, toySeed 2, toySeed 4} := by
    classical
    ext seed
    simp only [eventSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert, Finset.mem_singleton]
    rw [toySeed_eq_iff, toySeed_eq_iff, toySeed_eq_iff]
    rw [toy_misses_iff]
    constructor
    · intro heven
      have hval : (seed 0).val = 0 ∨ (seed 0).val = 2 ∨ (seed 0).val = 4 := by
        have hlt := (seed 0).isLt
        omega
      rcases hval with h0 | h2 | h4
      · exact Or.inl (Fin.ext h0)
      · exact Or.inr (Or.inl (Fin.ext h2))
      · exact Or.inr (Or.inr (Fin.ext h4))
    · rintro (h0 | h2 | h4)
      · simp [h0]
      · simp [h2]
      · simp [h4]
  rw [uniformSeedProb, hset]
  have hc : ({toySeed 0, toySeed 2, toySeed 4} : Finset ToySeed).card = 3 := by decide
  rw [hc]
  norm_num [Fintype.card_fun]

/-- Every one of the five seeds is accepted by exactly one of the three disjoint routes: local miss
at residues `0,2,4`, OOD at `1`, or low-degree at `3`.  Thus the three-term union bound is attained
exactly: `1 = 3/5 + 1/5 + 1/5`. -/
theorem toy_accept_prob : uniformSeedProb toyAccept = 1 := by
  have hset : eventSeeds toyAccept = Finset.univ := by
    classical
    ext seed
    simp only [eventSeeds, Finset.mem_filter, Finset.mem_univ, true_and,
      toyAccept, toy_locallyAccepts_iff, toyOodBad, toyLowDegreeBad]
    have hlt := (seed 0).isLt
    interval_cases hval : (seed 0).val <;> simp
  rw [uniformSeedProb, hset]
  norm_num [Fintype.card_fun]

/-- **NON-VACUOUS INSTANTIATED COMPOSITION.** At `N=5`, `m=2`, `k=1`, `delta=1/2`, the sharp query
term is `3/5`; the OOD and low-degree events each cost `1/5`; and the resulting soundness bound is
exactly one, attained by `toyAccept`.  All three addends are positive and load-bearing. -/
theorem toy_three_term_bound :
    uniformSeedProb toyAccept ≤
      (1 / 5 : ℝ) + 1 / 5 + ((1 - 1 / 2) + (1 / 2) / 5) ^ 1 := by
  apply biased_transcript_soundness_sharp (N := 5) (m := 2) (k := 1)
    (by norm_num) (by norm_num) (by norm_num)
    toyScheme toyTest toyScheme_pointBinding () toyRespond
    toyAccept toyOodBad toyLowDegreeBad toyReduction
    (1 / 5) (1 / 5) (1 / 2) (by norm_num) (by norm_num)
  · rw [toy_ood_prob]
  · rw [toy_lowDegree_prob]
  · exact toy_density.le

end Reference

/-! ## 5. Axiom-hygiene pins. -/

#assert_all_clean [
  locallyAccepts_misses,
  acceptSeeds_subset_exceptional_union_miss,
  acceptSeed_card_le_union,
  acceptSeed_card_le_budgets,
  acceptProb_le_union,
  eventSeeds_snd_eq_product,
  uniformSeedProb_snd,
  mem_goodResidues_iff,
  goodResidues_card,
  goodResidues_card_le,
  mod_miss_event_eq,
  mod_miss_event_card,
  mod_miss_prob_le,
  mod_miss_prob_le_sharp,
  biased_transcript_soundness,
  biased_transcript_soundness_sharp,
  biased_transcript_soundness_sharp_extra,
  babybear_transcript_soundness_sharp_extra,
  Reference.toyScheme_pointBinding,
  Reference.toy_obstructionSet,
  Reference.toy_ood_prob,
  Reference.toy_lowDegree_prob,
  Reference.toy_density,
  Reference.toy_query_miss_prob,
  Reference.toy_accept_prob,
  Reference.toy_three_term_bound]

end Dregg2.Metatheory.RobustDescentTranscriptGame

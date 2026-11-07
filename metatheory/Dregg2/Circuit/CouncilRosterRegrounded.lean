/-
# `Dregg2.Circuit.CouncilRosterRegrounded` — the `RosterCR` consumer RE-GROUNDED off the
FALSE-AS-NAMED injective floor onto a REAL collision game carrying an explicit `Eff`.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `RosterCR` site)

`CouncilCommit.RosterCR rosterHash := ∀ a b : List Guardian, rosterHash a = rosterHash b → a = b` is
stated as **injectivity** of the guardian-roster digest. `List Guardian` is INFINITE (any nonempty
`Guardian`) and the deployed digest lands in a BOUNDED range — a 256-bit BLAKE3 output, or a BabyBear
felt — so the floor is **FALSE at deployed parameters by pigeonhole** (§1,
`rosterCR_false_of_finite_range` / `rosterCR_false_blake3`). Its ONE consumer,
`CouncilCommit.recStateCommit_recovers_council_roster` — THE LIGHT-CLIENT PAYOFF, "a verified root
recovers the literal K-of-N guardian set" — is therefore **VACUOUSLY TRUE** at real parameters.
`#assert_axioms` is blind: the proof is clean (the crypto step is one `hRoster roster roster' _`); the
HYPOTHESIS is the flaw.

The carrier's own docstring gives FALSE COMFORT in the exact shape `HashFloorHonesty`'s header
predicts: it says `RosterCR` "at the deployed hash discharges to the Poseidon2/BLAKE3 floor". It does
not, and it cannot. At the deployed hash the floor is REFUTED — §1 proves it, from cardinality alone,
with no collision exhibited.

## The re-grounding (the `PreRotationKeySetRegrounded` / `Poseidon2KeyedBridge` pattern)

  * **§1 — FALSE AS NAMED.** The counting core (`HashFloorHonesty.not_injective_of_finite_range`)
    fires on `RosterCR` directly; `rosterCR_false_blake3` / `rosterCR_false_babyBear` are the deployed
    forms the carrier's docstring names.
  * **§2 — the KEYED family.** `RosterDeployment` bundles the deployed roster digest with its
    domain-separation tag space (the effective key — the standard keyed-from-unkeyed model) and the
    PUBLISHED roster at each sampled instance (the set the `council_commit` register commits to).
    `rosterFamily` lifts it to a `HashFloorHonesty.KeyedHashFamily`;
    `deployed_hash_is_family_instance` and `collisionGame_wins_iff` pin FAITHFULNESS — the game is
    about the function the identity cell computes.
  * **§3 — the ROSTER-SUBSTITUTION GAME.** A council substituter is a first-class λ-indexed adversary:
    handed a sampled tag, it presents TWO kernel states and the TWO guardian rosters their identity
    cells commit to, and WINS iff the REAL `CouncilCommit.councilCommitOf D.idCell` registers AGREE
    (what the root binding delivers) while the rosters DIFFER. That is the guardian swap
    `recStateCommit_recovers_council_roster` denies, scored on the deployed reader over real
    `RecordKernelState`s. `substitution_win_of_root_attack` PROVES a root-level attacker instantiates
    it, via the real `recStateCommit_recovers_council` — that theorem is what keeps this game anchored
    to the carrier instead of being a re-labelled copy of the collision relation.
  * **§4 — THE REDUCTION.** `substitutionToCollisionFinder` discards the states and keeps the rosters;
    `substitution_wins_imp` RE-DERIVES the win on the other side — the two commit equations plus the
    shared register give `D.hash t r = D.hash t r'` while the win gives `r ≠ r'`, which is exactly the
    crypto step the old keystone spent on `hRoster r r' (by rw [← hcommit, hcc, hcommit'])`.
    `substitution_adv_le` is the advantage inequality by `winProb_le_of_imp`. The reduction is the ONLY
    bridge between hypothesis and conclusion — §6's canary compiles that fact.
  * **§5 — the RE-GROUNDED CONSUMER.**
    `recStateCommit_recovers_council_roster_advantage_bound`: the Boolean "equal roots recover the SAME
    roster" becomes "the SAME roster EXCEPT with negligible probability", from the collision floor VIA
    the reduction.

## ⚑ THE `Eff` PARAMETER IS THE WHOLE HONESTY, AND IT IS UNDISCHARGED

The sweep's load-bearing result (`FloorGames` §2, `hard_top_iff_solvableFrac_negl`): at the
UNRESTRICTED adversary class a game floor IS the existence floor, so it is FALSE wherever collisions
exist — and §1 proves they exist at the deployed roster digest. §7 instantiates both poles at THIS
carrier: `roster_floor_top_false_of_compressing` (`Eff := ⊤` is FALSE at deployed parameters, routed
through the counting core — the deployed digest refutes it) and `roster_floor_bot_vacuous`
(`Eff := ⊥` is vacuous). So `Eff` is a PARAMETER, in the open, at every use site: this tree has no
cost model (`FloorGames` §8), and inventing a shallow imitation would be another costume. Hiding the
`Eff` dependence is the disease; naming it is the repair.

## Non-fake

The floor is REFUTABLE (`brokenRoster_floor_top_false`: a constant digest has a finder winning at
every tag, advantage `1`) and the reduction is LOAD-BEARING (§6's canary: the keystone does NOT follow
from the floor applied at some OTHER finder). The OLD `RosterCR` consumer is KEPT untouched in
`CouncilCommit`; the honest sibling is ADDED here. `#assert_all_clean`; no `sorry`, no fresh `axiom`.

## Coordination

This is the COUNCIL-ROSTER lane. The pre-rotation key-set carrier is
`Apps.PreRotationKeySetRegrounded` (the same repair, same shape, sibling `KeySetCR`); the queue-root
carriers are `Apps.QueueRootFloorRegrounded`; the STARK/FRI/Merkle hash consumers are
`Circuit.FloorRegroundedConsumers` / `Circuit.Poseidon2KeyedBridge`.

⚑ **THE SCOPE OF THIS REPAIR, STATED EXACTLY.** What re-grounds is the ROSTER-RECOVERY step — the one
and only step that consumes `RosterCR`: from the SHARED council commitment onward to "the guardian
rosters are equal". The step BEFORE it — equal verified roots ⟹ shared council commitment — is
`CouncilCommit.recStateCommit_recovers_council`, which rides the StateCommit CR set
(`compressInjective` on `cmb`/`compress`, `compressNInjective`, `cellLeafInjective`,
`RestHashIffFrame`). That leg is NOT re-grounded here and is NOT weakened here. It is carried as
EXPLICIT hypotheses on `substitution_win_of_root_attack` and nowhere else — deliberately NOT as fields
of `RosterDeployment`, where it would ride along unread.

Being honest about that leg: those are injectivity floors of compressing functions, so §1's counting
core applies to them for the same pigeonhole reason, and they are presumably false at deployed
parameters too. Re-grounding them is another cluster's lane (`Circuit.StateCommitFloorRegrounded`), not
this one. Naming the residual is the repair available here; laundering it would not be.
-/
import Dregg2.Circuit.CouncilCommit
import Dregg2.Circuit.StateCommit
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics

namespace Dregg2.Circuit.CouncilRosterRegrounded

open Dregg2.Exec
open Dregg2.Circuit.StateCommit
  (recStateCommit compressInjective compressNInjective cellLeafInjective RestHashIffFrame AccountsWF)
open Dregg2.Circuit.CouncilCommit
  (RosterCR councilCommitOf councilCommitField recStateCommit_recovers_council)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable
   HashCRHardQuant hashCRHardQuant_top_of_injective)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED: the injective `RosterCR` floor is refuted by the deployed digest.

`RosterCR rosterHash` IS `Function.Injective rosterHash` on the INFINITE `List Guardian`. The deployed
guardian-roster digest lands in a BOUNDED range (a 256-bit BLAKE3 output, or a BabyBear felt), so the
counting core fires — no digest collision need be exhibited; cardinality suffices, and is the honest
statement. -/

/-- A digest function into a BOUNDED integer window has FINITE range (`⊆ Ico 0 q`). The general form
of `HashFloorHonesty.finite_range_of_field_bound` — the domain is arbitrary here because the roster
digest's domain is `List Guardian`, not `List ℤ`. (Restated locally rather than imported across lanes:
this file's teeth should stand on their own counting core.) -/
theorem finite_range_of_bound {α : Type} (f : α → Int) (q : Int)
    (hb : ∀ x, 0 ≤ f x ∧ f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Ico (0 : Int) q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(hb x).1, (hb x).2⟩

/-- **TOOTH — `RosterCR` is FALSE for any range-bounded guardian-roster digest.** Literally the
counting core: the floor IS injectivity on `List Guardian`, which is infinite whenever `Guardian` is
inhabited (and a guardian council with no possible guardians is not a threat model), while a real
digest's range is finite. Stated in the same shape as the flagged siblings' teeth
(`HashFloorHonesty.poseidon2SpongeCR_false_of_finite_range`,
`PreRotationKeySetRegrounded.keySetCR_false_of_finite_range`). -/
theorem rosterCR_false_of_finite_range {Guardian : Type} [Nonempty Guardian]
    (rosterHash : List Guardian → Int) (hfin : (Set.range rosterHash).Finite) :
    ¬ RosterCR rosterHash :=
  fun hCR => not_injective_of_finite_range rosterHash hfin (fun a b h => hCR a b h)

/-- **TOOTH (deployed form) — `RosterCR` is FALSE at the deployed BLAKE3 roster digest.** A digest that
is a genuine 256-bit value (`0 ≤ · < 2²⁵⁶`) — i.e. every real `blake3` guardian-roster commitment, the
object `CouncilCommit`'s own docstring points at ("at the deployed hash it discharges to the
Poseidon2/BLAKE3 floor") — REFUTES the floor. The floor is not merely un-proven at the deployed hash;
it is provably FALSE there, so `recStateCommit_recovers_council_roster` is vacuous at real
parameters. -/
theorem rosterCR_false_blake3 {Guardian : Type} [Nonempty Guardian]
    (rosterHash : List Guardian → Int)
    (hb : ∀ r, 0 ≤ rosterHash r ∧ rosterHash r < (2 : Int) ^ 256) : ¬ RosterCR rosterHash :=
  rosterCR_false_of_finite_range rosterHash (finite_range_of_bound rosterHash _ hb)

/-- **TOOTH (Poseidon2 form) — `RosterCR` is FALSE at a BabyBear felt digest** (`p = 2³¹ − 2²⁷ + 1`),
the other deployment the carrier's docstring names. The `council_commit` register holds an `Int`; when
that `Int` is a felt, the roster space out-counts it immediately. -/
theorem rosterCR_false_babyBear {Guardian : Type} [Nonempty Guardian]
    (rosterHash : List Guardian → Int)
    (hb : ∀ r, 0 ≤ rosterHash r ∧ rosterHash r < (2013265921 : Int)) : ¬ RosterCR rosterHash :=
  rosterCR_false_of_finite_range rosterHash (finite_range_of_bound rosterHash _ hb)

/-- **THE COLLISION THE FALSITY EXHIBITS.** A range-bounded roster digest has, at every parameter, a
genuine collision — two DISTINCT guardian rosters with equal council commitments. This is the counting
core in the positive form the game floors below consume: it is what makes the `⊤`-class floor false
(§7), and therefore what makes the `Eff` parameter load-bearing rather than decorative. -/
theorem exists_collision_of_finite_range {Guardian : Type} [Nonempty Guardian]
    (rosterHash : List Guardian → Int) (hfin : (Set.range rosterHash).Finite) :
    ∃ p : List Guardian × List Guardian, p.1 ≠ p.2 ∧ rosterHash p.1 = rosterHash p.2 := by
  by_contra hno
  push_neg at hno
  refine not_injective_of_finite_range rosterHash hfin (fun a b hab => ?_)
  by_contra hne
  exact hno (a, b) hne hab

/-! ## §2 — the KEYED family: domain separation is the key.

The deployed roster digest is a FIXED unkeyed function; its effective key is the domain-separation tag
(the `TAG_*` derive-key prefix / HINTS roster-commitment domain) the deployment absorbs ahead of the
guardian set. Modelling that tag as the key is the standard keyed-from-unkeyed treatment
(`Poseidon2KeyedBridge` §1-§2) and is what stops the "hardcode a known collision" degeneracy that
collapses an unkeyed floor. -/

/-- **The deployed guardian-roster commitment scheme.** `hash` is the tag-keyed roster digest (the
deployed fixed function at each domain-separation tag); `Tag` is the finite, inhabited tag space the CR
game samples; `committed t` is the PUBLISHED guardian roster at the sampled instance `t` (the set the
identity cell's `council_commit` register commits to — the honest K-of-N quorum); `deployedTag` is the
tag the cell computes. -/
structure RosterDeployment (Guardian : Type) where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The tag-keyed guardian-roster digest — the deployed fixed function at each tag. -/
  hash : Tag → List Guardian → Int
  /-- The published guardian roster at the sampled instance (what `council_commit` commits to). -/
  committed : Tag → List Guardian
  /-- Decidable equality on guardians (the game checks two rosters are distinct). -/
  guardianDecEq : DecidableEq Guardian
  /-- The specific domain-separation tag the identity cell computes. -/
  deployedTag : Tag
  /-- **The identity cell** whose `council_commit` register carries the roster digest. The games below
  read `CouncilCommit.councilCommitOf idCell` off REAL kernel states at this cell — that is what
  anchors them to the deployed carrier rather than to a re-labelled copy of the collision relation. -/
  idCell : CellId

/-- **`rosterFamily D`** — the deployed roster digest lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. This is the object the collision floor `FloorGames.HashCRHardQuant` is realized
at for the real digest — at whatever adversary class `Eff` the reader is willing to price. -/
def rosterFamily {Guardian : Type} (D : RosterDeployment Guardian) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List Guardian
  Out := Int
  H := fun _ t r => D.hash t r
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := letI := D.guardianDecEq; inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The deployed FIXED digest IS the keyed family's instance at the deployed tag — a
definitional equality, no idealization. So the CR game below is a game about the very function the
identity cell computes into its `council_commit` register. -/
theorem deployed_hash_is_family_instance {Guardian : Type} (D : RosterDeployment Guardian) (n : ℕ) :
    D.hash D.deployedTag = (rosterFamily D).H n D.deployedTag := rfl

/-! ⚑ **THERE IS NO RUNG-1 BRIDGE HERE ANY MORE, AND THAT IS THE HONEST STATE (deleted 2026-07-28).**

A `rosterFamily_CR_of_rosterCR` stood at this point: `RosterCR` at every tag ⟹ the family's now-deleted
`HashFloorHonesty.CollisionResistant` floor, argued as "the OLD floor was STRICTLY STRONGER, so nothing
is lost re-grounding — a false hypothesis is replaced by one a real digest can satisfy". **Both ends of
that bridge are refuted, so it bought nothing.** Its source is refuted by §1 at the deployed digest; its
target was `HashCRHardQuant (rosterFamily D) (fun _ => True)` spelled without the `⊤`, and §7's first
tooth refutes THAT at the same range-bounded digest. A bridge from an empty hypothesis to a false
conclusion is not a re-grounding argument.

What stands in its place is what this file already carries and does not need a bridge to state: the
collision GAME below (§3) with its adversary class `Eff` written out at every use site, both poles of
that class PRICED as theorems (§7), and the §8 successor on the keyed-ROM floor, where the bound is
PROVED by the birthday argument instead of assumed. -/

/-! ## §3 — the roster COLLISION GAME and the COUNCIL-SUBSTITUTION GAME, as first-class objects. -/

/-- **THE ROSTER COLLISION GAME.** Instances are sampled domain-separation tags; the adversary outputs
two guardian rosters and WINS iff they are a GENUINE collision of the deployed digest at that tag —
distinct rosters, equal council commitments. This is the game the floor below quantifies over, with an
explicit adversary class. -/
def rosterCollisionGame {Guardian : Type} (D : RosterDeployment Guardian) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List Guardian × List Guardian
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2
  winsDec := fun _ t p => by
    letI := D.guardianDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine
collision of the real deployed roster digest. Not a docstring: the `Prop` itself. -/
theorem collisionGame_wins_iff {Guardian : Type} (D : RosterDeployment Guardian) (n : ℕ) (t : D.Tag)
    (p : List Guardian × List Guardian) :
    (rosterCollisionGame D).wins n t p ↔ (p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2) :=
  Iff.rfl

/-- **THE COUNCIL-SUBSTITUTION GAME.** The adversary is handed a sampled tag and presents TWO kernel
states together with the TWO guardian rosters their identity cells commit to. It WINS iff:

  1. state `k`'s `council_commit` register (the REAL `CouncilCommit.councilCommitOf D.idCell`) holds
     the digest of roster `r`,
  2. state `k'`'s holds the digest of roster `r'`,
  3. the two registers AGREE — **which is exactly what the root binding delivers**
     (`CouncilCommit.recStateCommit_recovers_council`: equal verified roots ⟹ equal council
     commitments), and
  4. the rosters nonetheless DIFFER.

A win is therefore a genuine guardian SWAP surviving the light client: two states a verifier cannot
tell apart by their council registers, exhibiting DIFFERENT K-of-N quorums. That is the attack
`CouncilCommit.recStateCommit_recovers_council_roster` denies — read off the deployed `councilCommitOf`
on real `RecordKernelState`s, not off a re-labelling of the collision relation.

⚑ Note conjunct 3 is a HYPOTHESIS of the game, not a consequence: this game is the roster-recovery
step FROM the shared council commitment onward. The root ⟹ shared-commitment step is
`recStateCommit_recovers_council` and rides the StateCommit CR set, which is another cluster's carrier
and out of scope here — `substitution_win_of_root_attack` below names that leg explicitly and shows a
root-level attacker instantiates this game. -/
def rosterSubstitutionGame {Guardian : Type} (D : RosterDeployment Guardian) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (RecordKernelState × RecordKernelState) × (List Guardian × List Guardian)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t a =>
    councilCommitOf D.idCell a.1.1 = D.hash t a.2.1 ∧
    councilCommitOf D.idCell a.1.2 = D.hash t a.2.2 ∧
    councilCommitOf D.idCell a.1.1 = councilCommitOf D.idCell a.1.2 ∧
    a.2.1 ≠ a.2.2
  winsDec := fun _ t a => by
    letI := D.guardianDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (2/2)** — a substitution win is, by `Iff.rfl`, a pair of real
kernel states whose REAL `council_commit` registers agree while committing to DIFFERENT guardian
rosters. The deployed reader `CouncilCommit.councilCommitOf` appears in the `Prop` itself. -/
theorem substitutionGame_wins_iff {Guardian : Type} (D : RosterDeployment Guardian) (n : ℕ)
    (t : D.Tag) (a : (RecordKernelState × RecordKernelState) × (List Guardian × List Guardian)) :
    (rosterSubstitutionGame D).wins n t a ↔
      (councilCommitOf D.idCell a.1.1 = D.hash t a.2.1 ∧
       councilCommitOf D.idCell a.1.2 = D.hash t a.2.2 ∧
       councilCommitOf D.idCell a.1.1 = councilCommitOf D.idCell a.1.2 ∧
       a.2.1 ≠ a.2.2) :=
  Iff.rfl

/-- **⚑ THE GAME IS ANCHORED ON THE REAL CARRIER — a ROOT-level attacker instantiates it.** Given the
StateCommit CR set and two `AccountsWF` states with EQUAL verified roots whose identity cells commit to
DIFFERENT rosters, the answer `((k, k'), (r, r'))` WINS the substitution game. The shared-commitment
conjunct is discharged HERE by `CouncilCommit.recStateCommit_recovers_council` — the real binding
lemma, on the real `recStateCommit`.

This is the theorem that stops the game from being a re-labelled mirror: it says the object the game
scores is reachable from the light-client attack `CouncilCommit` §1 is about.

⚑ **The StateCommit CR set is carried as EXPLICIT, UNDISCHARGED hypotheses** (`compressInjective`,
`compressNInjective`, `cellLeafInjective`, `RestHashIffFrame`). Those are ANOTHER cluster's floors —
and they are injectivity floors of compressing functions, so §1's counting core applies to them too.
Re-grounding them is NOT this lane's scope and they are NOT smuggled into `RosterDeployment` as
fields. Named, not hidden. -/
theorem substitution_win_of_root_attack {Guardian : Type} (D : RosterDeployment Guardian)
    (CH : CellId → Value → ℤ) (RH : RecordKernelState → ℤ) (cmb compress : ℤ → ℤ → ℤ)
    (compressN : List ℤ → ℤ)
    (hCmb : compressInjective cmb) (hCompress : compressInjective compress)
    (hCompressN : compressNInjective compressN) (hLeaf : cellLeafInjective CH)
    (hRest : Dregg2.Circuit.RestFrameFin.RestHashIffFrameFin RH)
    (n : ℕ) (t : D.Tag) (k k' : RecordKernelState) (turn : Turn) (r r' : List Guardian)
    (hwf : AccountsWF k) (hwf' : AccountsWF k')
    (hfin : Dregg2.Circuit.RestFrameFin.FiniteRepresentable k)
    (hfin' : Dregg2.Circuit.RestFrameFin.FiniteRepresentable k')
    (hcommit : councilCommitOf D.idCell k = D.hash t r)
    (hcommit' : councilCommitOf D.idCell k' = D.hash t r')
    (hroot : recStateCommit CH RH cmb compress compressN k turn
      = recStateCommit CH RH cmb compress compressN k' turn)
    (hne : r ≠ r') :
    (rosterSubstitutionGame D).wins n t ((k, k'), (r, r')) :=
  ⟨hcommit, hcommit',
   recStateCommit_recovers_council CH RH cmb compress compressN
     hCmb hCompress hCompressN hLeaf hRest k k' turn D.idCell hwf hwf' hfin hfin' hroot,
   hne⟩

/-! ## §4 — THE REDUCTION: a council substituter IS a roster collision finder. -/

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A council substituter becomes a roster collision finder
by DISCARDING the two kernel states and keeping the two rosters it committed them to. The states are
where the substituter's leverage lives — the finder never sees them — so the map is not a rename: it
throws structure away and the win must be RE-DERIVED on the other side (`substitution_wins_imp`). -/
def substitutionToCollisionFinder {Guardian : Type} (D : RosterDeployment Guardian)
    (A : Adversary (rosterSubstitutionGame D)) : Adversary (rosterCollisionGame D) where
  run := fun n t => ((A.run n t).2.1, (A.run n t).2.2)

/-- **⚑ WIN-PRESERVATION — the TRANSPORT step, and it is `recStateCommit_recovers_council_roster`'s own
crypto step.** Wherever the substituter wins, the extracted roster pair is a GENUINE collision of the
deployed digest. The derivation is exactly the one the old Boolean keystone performed under `RosterCR`:
the two `council_commit` registers read as `D.hash t r` and `D.hash t r'` (conjuncts 1 and 2), those
registers AGREE (conjunct 3, what the root binding delivers), therefore `D.hash t r = D.hash t r'` —
while the win forces `r ≠ r'`.

⚑ This is the whole reduction, and it does REAL work: the hypothesis is about `councilCommitOf` on two
kernel states, the conclusion about the digest at two rosters, and the three commit equations are what
carry one to the other. The old keystone spent this step on `hRoster r r' (by rw [← hcommit, hcc,
hcommit'])` and then had injectivity finish the job; here the same chain lands on a collision, and the
collision floor finishes it instead. -/
theorem substitution_wins_imp {Guardian : Type} (D : RosterDeployment Guardian)
    (A : Adversary (rosterSubstitutionGame D)) (n : ℕ) (t : D.Tag)
    (hwin : (rosterSubstitutionGame D).wins n t (A.run n t)) :
    (rosterCollisionGame D).wins n t ((substitutionToCollisionFinder D A).run n t) := by
  obtain ⟨hcommit, hcommit', hcc, hne⟩ := hwin
  refine ⟨hne, ?_⟩
  show D.hash t (A.run n t).2.1 = D.hash t (A.run n t).2.2
  rw [← hcommit, hcc, hcommit']

/-- **THE ADVANTAGE INEQUALITY.** The substituter's advantage is at most the extracted collision
finder's, at every parameter — both play over the SAME sampled tag space, and every tag the substituter
wins the extracted finder wins. A genuine reduction inequality over real game advantages. -/
theorem substitution_adv_le {Guardian : Type} (D : RosterDeployment Guardian)
    (A : Adversary (rosterSubstitutionGame D)) (n : ℕ) :
    gameAdv (rosterSubstitutionGame D) A n
      ≤ gameAdv (rosterCollisionGame D) (substitutionToCollisionFinder D A) n := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact substitution_wins_imp D A n t ht

/-! ## §5 — the RE-GROUNDED CONSUMER.

The Boolean keystone becomes an advantage bound, derived FROM the collision floor VIA the reduction.
The old statement is kept in `CouncilCommit`; this is its honest sibling. -/

/-- **⚑ RE-GROUNDED `CouncilCommit.recStateCommit_recovers_council_roster`.**

Under the roster collision floor at the game the reduction actually attacks, a council substituter
whose extracted finder is in the floor's adversary class has NEGLIGIBLE advantage.

**What changes, precisely.** The old keystone is Boolean: two states whose council registers agree
carry the SAME guardian roster — full stop, no exceptions. That is what INJECTIVITY buys, and
injectivity is FALSE at the deployed digest (§1), so the old statement bought it with an empty
hypothesis. The honest statement is the one a real digest can actually deliver: the SAME guardian
roster **EXCEPT with negligible probability**. A light client still reads off the literal K-of-N set
that blessed the recovery; what it now has is a computational guarantee with a stated failure
probability, instead of a certainty resting on a refuted premise.

⚑ The conclusion bounds the SUBSTITUTION game, whose win already presupposes the shared council
commitment. Composed with `substitution_win_of_root_attack`, that reads at the light client as: a
root-level attacker — equal verified roots, different guardian sets — has negligible advantage,
PROVIDED the root ⟹ shared-commitment leg holds (the StateCommit CR set, out of scope, see the
header).

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about the
substitution game, the hypothesis about the collision game, and `substitution_adv_le` is the only
bridge (§6's canary compiles that fact).

⚑ **`hEff` IS A PARAMETER HERE BECAUSE THIS IS THE STATEMENT AT AN ARBITRARY CLASS.** The DISCHARGED
form is §8's `recStateCommit_recovers_council_roster_rom`, on the keyed-ROM floor (PROVED — the
birthday bound), which replaced the deleted `IsPolyTime` discharge whose floor was refutable. §7
prices both poles of THIS statement's `Eff`: `⊤` makes it FALSE at the deployed digest, `⊥` vacuous. -/
theorem recStateCommit_recovers_council_roster_advantage_bound {Guardian : Type}
    (D : RosterDeployment Guardian) (Eff : Adversary (rosterCollisionGame D) → Prop)
    (A : Adversary (rosterSubstitutionGame D))
    (hEff : Eff (substitutionToCollisionFinder D A))
    (hcol : Hard (rosterCollisionGame D) Eff) :
    Negl (gameAdv (rosterSubstitutionGame D) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (rosterSubstitutionGame D) A n).1)
    (substitution_adv_le D A) (hcol _ hEff)

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at some OTHER finder.)** Strip the
reduction — try to conclude the substituter's negligibility from the collision floor applied at some
OTHER finder `B`, NOT the one extracted from the substituter — and the proof does not go through: the
floor bounds `B`, and only `substitution_adv_le` connects the EXTRACTED finder to the substitution
game. Under the OLD free hypothesis (`hRoster : RosterCR rosterHash`, with hypothesis and conclusion
sharing the same free `rosterHash`) this tooth was unwritable. It compiles now, and reds if a future
edit reconnects the games. -/
example {Guardian : Type} (D : RosterDeployment Guardian)
    (Eff : Adversary (rosterCollisionGame D) → Prop)
    (A : Adversary (rosterSubstitutionGame D))
    (B : Adversary (rosterCollisionGame D)) (hB : Eff B)
    (hcol : Hard (rosterCollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (rosterSubstitutionGame D) A) := hcol B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the collision floor at the EXTRACTED finder the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floor {Guardian : Type}
    (D : RosterDeployment Guardian) (Eff : Adversary (rosterCollisionGame D) → Prop)
    (A : Adversary (rosterSubstitutionGame D))
    (hEff : Eff (substitutionToCollisionFinder D A))
    (hcol : Hard (rosterCollisionGame D) Eff) :
    Negl (gameAdv (rosterSubstitutionGame D) A) :=
  recStateCommit_recovers_council_roster_advantage_bound D Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED: both poles proved at THIS carrier.

The sweep's deep result (`FloorGames` §2) says a game floor at the unrestricted class IS the existence
floor. Here is that theorem instantiated at the deployed roster digest, so a reader can price any `Eff`
exactly rather than take the residual on faith. -/

/-- **⚑ (TOOTH — the floor is FALSE at `Eff := ⊤` for the DEPLOYED digest.)** The real content, and the
reason `Eff` is not decoration: a range-bounded roster digest HAS a collision at every tag (§1's
counting core), so the collision game is always solvable, so the floor at the unrestricted adversary
class is FALSE — and the re-grounded consumer would be vacuous there. `Classical.choice` is the
adversary and no restatement of the win relation can see it coming. This is the price of `hEff`, stated
as a theorem instead of a promise. -/
theorem roster_floor_top_false_of_compressing {Guardian : Type} [Nonempty Guardian]
    (D : RosterDeployment Guardian) (hfin : ∀ t : D.Tag, (Set.range (D.hash t)).Finite) :
    ¬ Hard (rosterCollisionGame D) (fun _ => True) :=
  not_hard_top_of_always_solvable (rosterCollisionGame D)
    (fun _ => ⟨([], [])⟩)
    (fun n t => exists_collision_of_finite_range (D.hash t) (hfin t))

/-- **(TOOTH — the deployed BLAKE3 form of the same.)** A genuine 256-bit guardian-roster digest refutes
the unrestricted-class floor. The deployment the carrier's docstring names is exactly where `Eff := ⊤`
fails. -/
theorem roster_floor_top_false_blake3 {Guardian : Type} [Nonempty Guardian]
    (D : RosterDeployment Guardian)
    (hb : ∀ (t : D.Tag) (r : List Guardian), 0 ≤ D.hash t r ∧ D.hash t r < (2 : Int) ^ 256) :
    ¬ Hard (rosterCollisionGame D) (fun _ => True) :=
  roster_floor_top_false_of_compressing D
    (fun t => finite_range_of_bound (D.hash t) _ (fun r => hb t r))

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty adversary class the floor holds
for ANY deployment, including a completely broken digest. Recorded HONESTLY: a satisfiability witness
is worth nothing without the refutation beside it, and these two poles together are what make `Eff` a
dial rather than a costume. -/
theorem roster_floor_bot_vacuous {Guardian : Type} (D : RosterDeployment Guardian) :
    Hard (rosterCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floor is REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** roster deployment: the digest IGNORES the guardian set entirely, so every pair of
distinct rosters collides at every tag. The concrete shape of the threat `CouncilCommit` §2 is about —
a `council_commit` register that does not actually pin WHO. -/
def brokenRoster : RosterDeployment Int where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  hash := fun _ _ => 0
  committed := fun _ => []
  guardianDecEq := inferInstance
  deployedTag := ()
  idCell := 0

/-- A concrete identity state whose `council_commit` register reads `0` — the digest the broken
deployment produces for EVERY guardian roster. Two copies of it are a light client's nightmare: the
registers agree (as they must, they are the same state) while the rosters behind them are free. -/
def brokenIdState : RecordKernelState :=
  { accounts := {0}
    cell := fun _ => .record [("balance", .int 0), (councilCommitField, .int 0)]
    caps := fun _ => [] }

/-- **(TOOTH — the floor is REFUTABLE.)** The broken deployment's collision game is solvable at every
tag (`[0] ≠ [1]`, both digest to `0`), so it has no unrestricted-class floor. So the floor is a GENUINE
constraint — a broken digest refutes it — not vacuously true. -/
theorem brokenRoster_floor_top_false :
    ¬ Hard (rosterCollisionGame brokenRoster) (fun _ => True) :=
  not_hard_top_of_always_solvable (rosterCollisionGame brokenRoster)
    (fun _ => ⟨([], [])⟩)
    (fun _ _ => ⟨([0], [1]), by decide, rfl⟩)

/-- **(TOOTH — the SUBSTITUTION game is refutable on the broken deployment too.)** Against a digest
that ignores the guardian set, the substituter presenting the SAME identity state twice against the
DIFFERENT rosters `[0]` and `[1]` wins at every tag: both `council_commit` registers read `0`, they
trivially agree (conjunct 3 — precisely what a verified root would hand an attacker), and both rosters
digest to `0` — yet the guardian sets differ. So the re-grounded consumer's conclusion genuinely FAILS
on a broken carrier: the light client recovers a root, the root pins the council commitment, and the
commitment pins NOTHING about who the guardians are. The attack the game names is a real attack, not a
shape. -/
theorem brokenRoster_substitution_floor_top_false :
    ¬ Hard (rosterSubstitutionGame brokenRoster) (fun _ => True) :=
  not_hard_top_of_always_solvable (rosterSubstitutionGame brokenRoster)
    (fun _ => ⟨((brokenIdState, brokenIdState), ([], []))⟩)
    (fun _ _ => ⟨((brokenIdState, brokenIdState), ([0], [1])), rfl, rfl, rfl,
      by decide⟩)

/-! ### The floor is SATISFIABLE (the connection to the keyed-family treatment). -/

/-- **(TOOTH — the keyed family is SATISFIABLE on an injective deployment.)** A deployment whose per-tag
digest is injective discharges `HashCRHardQuant (rosterFamily D) (fun _ => True)` — the honest floor is
REALIZABLE, unlike the injective `RosterCR` at deployed parameters. ⚑ Recorded with its price: this is
the `⊤`-class object, which §7's first tooth proves FALSE at a range-bounded (i.e. real) digest — and
the `⊤` is now written into the statement instead of hidden behind a name. The satisfiability is honest
only as a non-emptiness check, never as evidence the deployed hash satisfies it. -/
theorem rosterFamily_CR_of_injective {Guardian : Type} (D : RosterDeployment Guardian)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hash t)) :
    HashCRHardQuant (rosterFamily D) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (rosterFamily D) (fun _ t => hinj t)

/-! ## §8 — ⚑ THE DISCHARGED HEADLINE, ON THE PROVED KEYED-ROM FLOOR.

The `IsPolyTime` discharge that stood here (`recStateCommit_recovers_council_roster_from_polyTime`)
carried `Hard (rosterCollisionGame D) (IsPolyTime …)` — FALSE at any range-bounded deployed digest by
the `Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` argument (`IsPolyTime`
prices answer SIZE; a `Classical.choice` `.pure`-leaf answering a fixed two-roster short collision is
in the class and wins with probability `1`), and no `Eff` repairs the fixed-hash game
(`Crypto.RomBindingReduction`'s header). It is DELETED. The successor lands the floor on a SAMPLED
oracle, where `KeyedRomFloor.keyedRom_hard` is a THEOREM.

⚑ THE MODELLING STEP, STATED: the deployed roster digest is idealised as a keyed RANDOM ORACLE at an
ASYMPTOTIC `Fin (2 ^ l)` width (the real digest is a fixed 256-bit value — no `l` coincides); the
message domain is the TRUNCATED deployed roster shape — rosters of length at most `m` over a FINITE
guardian-id space (`RomCarrierSites.BVec`, lossless by `bvecOfList_inj`). The substitution content
survives as the OPENING shape: the shared `council_commit` register IS a published digest, and the
substituter's two rosters are two openings of it — `romOpenGame`, the published value in the win
relation. The extractor that DROPS the two kernel states is the same structure-discarding map as
`substitutionToCollisionFinder`, now a `mapOut` (budget preserved). The fixed-hash content — §5's
`Eff`-parametric bound with `hEff` in the open, §7's poles — stays untouched beside it. -/

section RomSuccessor

open Dregg2.Crypto.RomCarrierSites
open Dregg2.Crypto.RomBindingReduction (RomCarrier)

variable {Guardian : Type}

/-- **THE ROSTER ROM FAMILY** — truncated guardian rosters under the ideal `λ`-bit digest, keyed by
the deployment's OWN tag space. `gFin` is the finite guardian-id space of the truncation (deployed
guardian ids are felts — a finite space). -/
abbrev rosterRomFamily (D : RosterDeployment Guardian) (tagDec : DecidableEq D.Tag)
    (gFin : Fintype Guardian) (m : ℕ) : Dregg2.Crypto.KeyedRomFloor.KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty
    (fun _ => BVec Guardian m)
    (fun _ => letI := gFin; letI := D.guardianDecEq; inferInstance)
    (fun _ => letI := D.guardianDecEq; inferInstance)
    (fun _ => ⟨(⟨0, Nat.succ_pos m⟩, fun _ => none)⟩)

/-- **THE COUNCIL-ROSTER CARRIER** — commitment `H (t, roster)`; identity encoding, injective on the
nose (the truncated roster IS the absorbed message). -/
def rosterRomCarrier (D : RosterDeployment Guardian) (tagDec : DecidableEq D.Tag)
    (gFin : Fintype Guardian) (m : ℕ) : RomCarrier (rosterRomFamily D tagDec gFin m) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => BVec Guardian m)
    (fun _ => letI := gFin; letI := D.guardianDecEq; inferInstance)
    (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The council-roster opening game at the sampled oracle: one PUBLISHED `council_commit` value,
opened by two DISTINCT truncated rosters. -/
abbrev rosterOpenRomGame (D : RosterDeployment Guardian) (tagDec : DecidableEq D.Tag)
    (gFin : Fintype Guardian) (m : ℕ) : Game :=
  romOpenGame (rosterRomFamily D tagDec gFin m) (rosterRomCarrier D tagDec gFin m)

/-- **⚑ THE SUBSTITUTION IS AN OPENING BREAK (at the sampled oracle).** Two DISTINCT truncated
rosters that both hash (under the sampled oracle, at one tag) to ONE published `council_commit`
register value ARE a win of the opening game — `substitution_win_of_root_attack`'s content with the
kernel states discharged into the published value. -/
theorem councilSubstitutionRom_is_open_break (D : RosterDeployment Guardian)
    (tagDec : DecidableEq D.Tag) (gFin : Fintype Guardian) (m : ℕ) (l : ℕ)
    (H : (rosterOpenRomGame D tagDec gFin m).Inst l) (t : D.Tag)
    {v w : BVec Guardian m} (hne : v ≠ w)
    (c : (rosterRomFamily D tagDec gFin m).toRomFamily.R l)
    (hv : H (t, v) = c) (hw : H (t, w) = c) :
    (rosterOpenRomGame D tagDec gFin m).wins l H (c, ((t, ()), v, w)) :=
  ⟨hne, hv, hw⟩

/-- **⚑⚑ THE DISCHARGED COUNCIL-ROSTER BINDING — ON THE PROVED FLOOR.** The successor of the deleted
`recStateCommit_recovers_council_roster_from_polyTime`: every query-bounded adversary that publishes
one `council_commit` value and opens it with two DISTINCT truncated rosters has NEGLIGIBLE advantage
— a guardian SWAP that survives the light client's root recovery is negligible, in the keyed ROM
model of the §-header. NO floor hypothesis, NO cost model. -/
theorem recStateCommit_recovers_council_roster_rom (D : RosterDeployment Guardian)
    (tagDec : DecidableEq D.Tag) (gFin : Fintype Guardian) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (rosterOpenRomGame D tagDec gFin m))
    (hA : RomOpenEff (rosterRomFamily D tagDec gFin m) (rosterRomCarrier D tagDec gFin m) Q A) :
    Negl (gameAdv (rosterOpenRomGame D tagDec gFin m) A) :=
  flat_open_binds D.Tag D.tagFintype tagDec D.tagNonempty _ _ _ _
    (rosterRomCarrier D tagDec gFin m) Q hQ A hA

/-- **(TOOTH — the admitted refuter-shape is DEFANGED, not excluded.)** The `0`-query constant
opener is IN the class at every budget, WINS at the constant oracle on distinct rosters, and its
advantage against the SAMPLED oracle is NEGLIGIBLE. -/
theorem rosterRom_constOpen_defanged (D : RosterDeployment Guardian)
    (tagDec : DecidableEq D.Tag) (gFin : Fintype Guardian) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (r : ∀ l, (rosterRomFamily D tagDec gFin m).toRomFamily.R l)
    (c : ∀ l, (rosterRomCarrier D tagDec gFin m).Ctx l)
    (v w : ∀ l, (rosterRomCarrier D tagDec gFin m).Val l) :
    RomOpenEff (rosterRomFamily D tagDec gFin m) (rosterRomCarrier D tagDec gFin m) Q
        (romOpenAdv _ _ (constOpenComp _ _ r c v w))
      ∧ Negl (gameAdv (rosterOpenRomGame D tagDec gFin m)
        (romOpenAdv _ _ (constOpenComp _ _ r c v w)))
      ∧ ∀ l, v l ≠ w l → 0 < gameAdv (rosterOpenRomGame D tagDec gFin m)
        (romOpenAdv _ _ (constOpenComp _ _ r c v w)) l :=
  ⟨constOpen_in_eff _ _ r c v w Q,
    constOpen_binds _ _ r c v w Q hQ
      (flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty _ _ _ _),
    fun l hvw => constOpen_gameAdv_pos _ _ r c v w l hvw⟩

/-- **(TOOTH — a non-negligible opener is OUTSIDE the class.)** -/
theorem rosterRom_nonNegl_opener_excluded (D : RosterDeployment Guardian)
    (tagDec : DecidableEq D.Tag) (gFin : Fintype Guardian) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (rosterOpenRomGame D tagDec gFin m))
    (hnn : ¬ Negl (gameAdv (rosterOpenRomGame D tagDec gFin m) A)) :
    ¬ RomOpenEff (rosterRomFamily D tagDec gFin m) (rosterRomCarrier D tagDec gFin m) Q A :=
  romOpen_forger_excluded _ _ Q hQ
    (flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty _ _ _ _) A hnn

end RomSuccessor

#assert_all_clean [
  councilSubstitutionRom_is_open_break,
  recStateCommit_recovers_council_roster_rom,
  rosterRom_constOpen_defanged,
  rosterRom_nonNegl_opener_excluded
]

#assert_all_clean [
  finite_range_of_bound,
  rosterCR_false_of_finite_range,
  rosterCR_false_blake3,
  rosterCR_false_babyBear,
  exists_collision_of_finite_range,
  deployed_hash_is_family_instance,
  collisionGame_wins_iff,
  substitutionGame_wins_iff,
  substitution_win_of_root_attack,
  substitution_wins_imp,
  substitution_adv_le,
  recStateCommit_recovers_council_roster_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  roster_floor_top_false_of_compressing,
  roster_floor_top_false_blake3,
  roster_floor_bot_vacuous,
  brokenRoster_floor_top_false,
  brokenRoster_substitution_floor_top_false,
  rosterFamily_CR_of_injective
]

end Dregg2.Circuit.CouncilRosterRegrounded

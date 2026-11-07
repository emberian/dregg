/-
# `Dregg2.Spike.CommitTreeRegrounded` — the `CommitTreeInjective` consumers RE-GROUNDED off the
FALSE-AS-NAMED injective floor onto a REAL collision game carrying an explicit `Eff`.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `CommitTreeInjective` site)

`EffectVmConstraints2.CommitTreeInjective H := ∀ a b : List ℤ, commitTree H a = commitTree H b → a = b`
is stated as **injectivity** of the four-leaf state-commitment hash tree (air.rs:2540–2543). `List ℤ` is
INFINITE and `commitTree H` lands in a BOUNDED range — a BabyBear felt, `0 ≤ · < 2³¹ − 2²⁷ + 1`, which
is what the carrier's own module header says the tree computes (`H : List ℤ → ℤ`, the Poseidon2
`hash_4_to_1` black box) — so the floor is **FALSE at deployed parameters by pigeonhole** (§1,
`commitTreeInjective_false_of_finite_range` / `commitTreeInjective_false_babyBear`). Both consumers
conditioned on it — `state_commitment_binds_state` and `state_commitment_no_silent_change` — are
therefore **VACUOUSLY TRUE** at real parameters. `#assert_axioms` is blind: the proofs are clean; the
HYPOTHESIS is the flaw.

The carrier's docstring calls it "an honest carried Prop (PORTAL-OK)… a direct consequence of Poseidon2
collision-resistance". It is not a consequence of collision-resistance: collision-resistance says
collisions are hard to FIND, never that they do not EXIST, and §1 proves they exist at the deployed
felt. A carried assumption is honest only when something can satisfy it.

## The re-grounding (the `PreRotationKeySetRegrounded` / `Poseidon2KeyedBridge` pattern)

  * **§1 — FALSE AS NAMED.** The counting core (`HashFloorHonesty.not_injective_of_finite_range`) fires
    on `CommitTreeInjective` directly; `commitTreeInjective_false_babyBear` is the deployed form. No
    Poseidon2 collision is exhibited — cardinality suffices, and is the honest statement.
  * **§2 — the KEYED family.** `CommitDeployment` bundles the deployed hash with its domain-separation
    tag space (the effective key — the standard keyed-from-unkeyed model). `commitFamily` lifts it to a
    `HashFloorHonesty.KeyedHashFamily`; `deployed_hash_is_family_instance` and
    `collisionGame_wins_iff` pin FAITHFULNESS — the game is about the tree the AIR actually computes.
  * **§3 — the STATE-EQUIVOCATION GAME.** The attack `state_commitment_binds_state` rules out is a
    first-class λ-indexed game: handed a sampled tag, the adversary outputs TWO post-state tuples and a
    published root, and WINS iff the tuples are DISTINCT yet BOTH satisfy the real `StateCommitSat`
    against that ONE published `NEW_COMMIT`. Two different states behind one published PI — the exact
    compromise, IN the win relation rather than in a docstring.
  * **§4 — THE REDUCTION.** `equivocationToCollisionFinder` hands the two exhibited tuples to the
    collision game; `equivocation_wins_imp` proves win-preservation (both tuples' trees equal the ONE
    published root, so the tuples themselves collide) and `equivocation_adv_le` is the advantage
    inequality by `winProb_le_of_imp`. The reduction is the ONLY bridge between hypothesis and
    conclusion — §6's canary compiles that fact.
  * **§5 — the RE-GROUNDED CONSUMERS.** `state_commitment_binds_state_advantage_bound` and
    `state_commitment_no_silent_change_advantage_bound`: the Boolean "two traces pinned to the same
    `NEW_COMMIT` commit to the SAME tuple" becomes "the SAME tuple EXCEPT with negligible probability",
    from the collision floor VIA the reduction.

## ⚑ THE `Eff` PARAMETER IS THE WHOLE HONESTY, AND IT IS UNDISCHARGED

The sweep's load-bearing result (`FloorGames` §2, `hard_top_iff_solvableFrac_negl`): at the
UNRESTRICTED adversary class a game floor IS the existence floor, so it is FALSE wherever collisions
exist — and §1 proves they exist at the deployed tree. §7 instantiates both poles at THIS carrier:
`commit_floor_top_false_of_compressing` (`Eff := ⊤` is FALSE at deployed parameters, routed through the
counting core) and `commit_floor_bot_vacuous` (`Eff := ⊥` is vacuous). So `Eff` is a PARAMETER, in the
open, at every use site: this tree has no cost model (`FloorGames` §8), and inventing a shallow
imitation would be another costume. Hiding the `Eff` dependence is the disease; naming it is the repair.

## Non-fake

The floor is REFUTABLE (`brokenCommit_floor_top_false`: a hash that ignores its input has a finder
winning at every tag, advantage `1`) and the reduction is LOAD-BEARING (§6's canary: the keystone does
NOT follow from the floor applied at some OTHER finder). The OLD `CommitTreeInjective` consumers are
KEPT untouched in `EffectVmConstraints2`; siblings ADDED here. `#assert_all_clean`; no `sorry`, no fresh
`axiom`.

## Coordination

This is the `STATE_COMMIT` / EffectVm-AIR lane. The FRI/Merkle `compress` carrier is the same shape and
is re-grounded in `Circuit.FriCompressRegrounded`; the pre-rotation key-set carrier is
`Apps.PreRotationKeySetRegrounded`.
-/
import Dregg2.Spike.EffectVmConstraints2
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Spike.CommitTreeRegrounded

open Dregg2.Spike.EffectVmConstraints2 (Hash commitTree StateCommitSat CommitTreeInjective)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable
   HashCRHardQuant hashCRHardQuant_top_of_injective)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED: the injective `CommitTreeInjective` floor is refuted by the deployed tree.

`CommitTreeInjective H` IS `Function.Injective (commitTree H)` on the INFINITE `List ℤ`. The deployed
state-commitment root is a BabyBear felt, so the counting core fires — no Poseidon2 collision need be
exhibited; cardinality suffices, and is the honest statement. -/

/-- A digest function into a BOUNDED integer window has FINITE range (`⊆ Ico 0 q`). The general form of
`HashFloorHonesty.finite_range_of_field_bound` — restated locally so this file and its FRI sibling stay
import-independent of each other. -/
theorem finite_range_of_bound {α : Type} (f : α → Int) (q : Int)
    (hb : ∀ x, 0 ≤ f x ∧ f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Ico (0 : Int) q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(hb x).1, (hb x).2⟩

/-- **TOOTH — `CommitTreeInjective` is FALSE for any range-bounded commitment tree.** Literally the
counting core: the floor IS injectivity on the infinite `List ℤ` of committed columns, while a real
tree's range is a finite set of field elements. Stated in the same shape as the flagged siblings' teeth
(`HashFloorHonesty.poseidon2SpongeCR_false_of_finite_range`). -/
theorem commitTreeInjective_false_of_finite_range (H : Hash)
    (hfin : (Set.range (commitTree H)).Finite) : ¬ CommitTreeInjective H :=
  fun hCR => not_injective_of_finite_range (commitTree H) hfin (fun a b h => hCR a b h)

/-- The tree's root is a genuine field element whenever the underlying `H` is: the four-leaf tree's
value is either an `H` output (the 12-column shape, air.rs:2540–2543) or the malformed-tuple fallback
`0`, and `0` is in the window. So a BabyBear-valued `hash_4_to_1` gives a BabyBear-valued root. -/
theorem commitTree_bounded (H : Hash) (q : Int) (hq : 0 < q)
    (hb : ∀ xs, 0 ≤ H xs ∧ H xs < q) (st : List Int) :
    0 ≤ commitTree H st ∧ commitTree H st < q := by
  unfold commitTree
  split
  · exact hb _
  · exact ⟨le_refl 0, hq⟩

/-- **TOOTH (deployed form) — `CommitTreeInjective` is FALSE at the deployed BabyBear tree.** A
`hash_4_to_1` whose output is a genuine BabyBear field element (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1` —
`EffectVmConstraints2.p`, the modulus the whole spike's constraints are stated over) REFUTES the floor.
The floor is not merely un-proven at the deployed hash; it is provably FALSE there, so
`state_commitment_binds_state` and `state_commitment_no_silent_change` are vacuous at real parameters. -/
theorem commitTreeInjective_false_babyBear (H : Hash)
    (hb : ∀ xs, 0 ≤ H xs ∧ H xs < (2013265921 : Int)) : ¬ CommitTreeInjective H :=
  commitTreeInjective_false_of_finite_range H
    (finite_range_of_bound (commitTree H) _
      (commitTree_bounded H _ (by norm_num) hb))

/-- **TOOTH (256-bit form) — the same for a blake3-valued tree.** Whatever the deployment's digest
width, the pigeonhole is the same; only the window changes. -/
theorem commitTreeInjective_false_blake3 (H : Hash)
    (hb : ∀ xs, 0 ≤ H xs ∧ H xs < (2 : Int) ^ 256) : ¬ CommitTreeInjective H :=
  commitTreeInjective_false_of_finite_range H
    (finite_range_of_bound (commitTree H) _
      (commitTree_bounded H _ (by positivity) hb))

/-- **THE COLLISION THE FALSITY EXHIBITS.** A range-bounded commitment tree has, at every parameter, a
genuine collision — two DISTINCT committed tuples with equal roots. This is the counting core in the
positive form the game floors below consume: it is what makes the `⊤`-class floor false (§7), and
therefore what makes the `Eff` parameter load-bearing rather than decorative. -/
theorem exists_collision_of_finite_range (H : Hash)
    (hfin : (Set.range (commitTree H)).Finite) :
    ∃ p : List Int × List Int, p.1 ≠ p.2 ∧ commitTree H p.1 = commitTree H p.2 := by
  by_contra hno
  push_neg at hno
  refine not_injective_of_finite_range (commitTree H) hfin (fun a b hab => ?_)
  by_contra hne
  exact hno (a, b) hne hab

/-! ## §2 — the KEYED family: domain separation is the key.

The deployed `hash_4_to_1` is a FIXED unkeyed function; its effective key is the domain-separation tag
the circuit's hash regime absorbs. Modelling that tag as the key is the standard keyed-from-unkeyed
treatment and is what stops the "hardcode a known collision" degeneracy that collapses an unkeyed
floor. -/

/-- **The deployed state-commitment scheme.** `hash` is the tag-keyed Poseidon2 `hash_4_to_1` (the
deployed fixed black box at each domain-separation tag); `Tag` is the finite, inhabited tag space the CR
game samples; `deployedTag` is the tag the EffectVm AIR computes under. -/
structure CommitDeployment where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The tag-keyed `hash_4_to_1` — the deployed fixed function at each tag. -/
  hash : Tag → Hash
  /-- The specific domain-separation tag the EffectVm AIR computes under. -/
  deployedTag : Tag

/-- **`commitFamily D`** — the deployed four-leaf commitment TREE (not the bare compression) lifted to a
`KeyedHashFamily`, keyed by its domain-separation tag. This is the object the collision floor
`FloorGames.HashCRHardQuant (commitFamily D) Eff` is stated at for the real state commitment: the AIR's
group-4 constraint pins `STATE_COMMIT` to `commitTree`, so `commitTree` is what must bind. -/
def commitFamily (D : CommitDeployment) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List Int
  Out := Int
  H := fun _ t st => commitTree (D.hash t) st
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The deployed FIXED tree IS the keyed family's instance at the deployed tag — a
definitional equality, no idealization. So the CR game below is a game about the very function the AIR's
group-4 transition constraint computes. -/
theorem deployed_hash_is_family_instance (D : CommitDeployment) (n : ℕ) :
    commitTree (D.hash D.deployedTag) = (commitFamily D).H n D.deployedTag := rfl

/-! ⚑ **DELETED 2026-07-28 — `commitFamily_CR_of_commitTreeInjective`.** It bridged the injective
`CommitTreeInjective` floor to `HashFloorHonesty.CollisionResistant (commitFamily D)`, and the argument
in its docstring was "the OLD floor was STRICTLY STRONGER than the honest computational floor, so
nothing is lost re-grounding". That argument is FALSE, and both ends of the bridge are refuted.

`CollisionResistant F` was never a computational floor — it was a SPELLING of
`HashCRHardQuant F (fun _ => True)` that hid the `⊤`, and it is deleted in favour of writing the `⊤`
out. THIS FILE refutes that destination: §7's `commit_floor_top_false_babyBear` proves the `⊤`-class
floor on the very same collision event is FALSE at a BabyBear-valued `hash_4_to_1` — i.e. at the
deployment the carrier's own docstring names. And §1 proves the SOURCE empty at those same parameters.
A bridge from an empty hypothesis to a refuted conclusion carries nothing, so it is gone rather than
restated.

The honest floor is the one §5's `_advantage_bound` siblings actually consume:
`Hard (commitCollisionGame D) Eff`, with `Eff` a parameter in the open and both its poles priced in §7.
Satisfiability of the `⊤` pole survives below as `commitFamily_CR_of_injective`, recorded with its
price. -/

/-! ## §3 — the COMMITMENT-COLLISION GAME and the STATE-EQUIVOCATION GAME, as first-class objects. -/

/-- **THE COMMITMENT-COLLISION GAME.** Instances are sampled domain-separation tags; the adversary
outputs two committed tuples and WINS iff they are a GENUINE collision of the deployed tree at that tag
— distinct tuples, equal roots. This is the game the floor below quantifies over, with an explicit
adversary class. -/
def commitCollisionGame (D : CommitDeployment) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List Int × List Int
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ commitTree (D.hash t) p.1 = commitTree (D.hash t) p.2
  winsDec := fun _ t p => by infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine collision
of the real deployed tree. Not a docstring: the `Prop` itself. -/
theorem collisionGame_wins_iff (D : CommitDeployment) (n : ℕ) (t : D.Tag)
    (p : List Int × List Int) :
    (commitCollisionGame D).wins n t p ↔
      (p.1 ≠ p.2 ∧ commitTree (D.hash t) p.1 = commitTree (D.hash t) p.2) :=
  Iff.rfl

/-- The object a `STATE_COMMIT` forger exhibits: two post-state tuples and the ONE published PI
`NEW_COMMIT` it claims both are pinned to by the last-row boundary constraint (air.rs:2707–2711). -/
structure StateEquivocation where
  /-- The first post-state tuple (the 12 committed columns). -/
  st : List Int
  /-- The second post-state tuple. -/
  st' : List Int
  /-- The published public input `NEW_COMMIT` the boundary pins both traces' `STATE_COMMIT` to. -/
  newCommit : Int

/-- **THE STATE-EQUIVOCATION GAME.** The adversary is handed a sampled tag and outputs a
`StateEquivocation`; it WINS iff the two post-state tuples are DISTINCT yet BOTH satisfy the real
group-4 transition constraint (`EffectVmConstraints2.StateCommitSat`, the deployed
`commit = commitTree H st`) against the SAME published `NEW_COMMIT`. Winning this game IS the attack
`state_commitment_binds_state` rules out: two different post-states standing behind one published PI.
The forgery is IN the win predicate, read off the real constraint. -/
def stateEquivocationGame (D : CommitDeployment) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => StateEquivocation
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t e =>
    e.st ≠ e.st'
      ∧ StateCommitSat (D.hash t) e.st e.newCommit
      ∧ StateCommitSat (D.hash t) e.st' e.newCommit
  winsDec := fun _ t e => by
    unfold StateCommitSat
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (2/2)** — an equivocation win is, by `Iff.rfl`, two DISTINCT
post-state tuples each satisfying the deployed group-4 constraint against ONE published `NEW_COMMIT`. -/
theorem equivocationGame_wins_iff (D : CommitDeployment) (n : ℕ) (t : D.Tag) (e : StateEquivocation) :
    (stateEquivocationGame D).wins n t e ↔
      (e.st ≠ e.st'
        ∧ StateCommitSat (D.hash t) e.st e.newCommit
        ∧ StateCommitSat (D.hash t) e.st' e.newCommit) :=
  Iff.rfl

/-! ## §4 — THE REDUCTION: a `STATE_COMMIT` equivocator IS a commitment-tree collision finder. -/

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** An equivocator becomes a collision finder by handing
over the two post-state tuples it exhibited. This is not a rename and not a re-indexing: it is the
group-4 constraint read as an extractor — the constraint admits only when the published root IS the
tuple's tree, so an equivocation against one published root hands the pair over directly. -/
def equivocationToCollisionFinder (D : CommitDeployment)
    (A : Adversary (stateEquivocationGame D)) : Adversary (commitCollisionGame D) where
  run := fun n t => ((A.run n t).st, (A.run n t).st')

/-- **⚑ WIN-PRESERVATION — and this IS `state_commitment_binds_state`, at the game level.** Wherever the
equivocator wins, the extracted pair is a GENUINE collision of the deployed tree: both satisfying traces
pin the SAME published `NEW_COMMIT` to their own tuple's tree, so the two trees are equal, while winning
forces the tuples distinct. The crypto content lives in a proof term, not in a sentence about one — and
it is the OLD consumer's proof, with the injectivity step DELETED rather than assumed. -/
theorem equivocation_wins_imp (D : CommitDeployment) (A : Adversary (stateEquivocationGame D))
    (n : ℕ) (t : D.Tag) (hwin : (stateEquivocationGame D).wins n t (A.run n t)) :
    (commitCollisionGame D).wins n t ((equivocationToCollisionFinder D A).run n t) := by
  obtain ⟨hne, hsat, hsat'⟩ := hwin
  exact ⟨hne, hsat.symm.trans hsat'⟩

/-- **THE ADVANTAGE INEQUALITY.** The equivocator's advantage is at most the extracted collision
finder's, at every parameter — both play over the SAME sampled tag space, and every tag the equivocator
wins the extracted finder wins. A genuine reduction inequality over real game advantages. -/
theorem equivocation_adv_le (D : CommitDeployment) (A : Adversary (stateEquivocationGame D)) (n : ℕ) :
    gameAdv (stateEquivocationGame D) A n
      ≤ gameAdv (commitCollisionGame D) (equivocationToCollisionFinder D A) n := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact equivocation_wins_imp D A n t ht

/-! ## §5 — the RE-GROUNDED CONSUMERS.

The Boolean keystones become advantage bounds, derived FROM the collision floor VIA the reduction. The
old statements are kept in `EffectVmConstraints2`; these are their honest siblings. -/

/-- **⚑ RE-GROUNDED `EffectVmConstraints2.state_commitment_binds_state`.**

Under the commitment-collision floor at the game the reduction actually attacks, a `STATE_COMMIT`
equivocator whose extracted finder is in the floor's adversary class has NEGLIGIBLE advantage: a prover
exhibits two different post-states behind one published `NEW_COMMIT` only with negligible probability.
The Boolean "two traces pinned to the same PI MUST commit to the same tuple" becomes "commit to the same
tuple EXCEPT with negligible probability" — which is what a real Poseidon2 can actually deliver, and
what the FALSE injective floor was standing in for.

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about the
equivocation game, the hypothesis about the collision game, and `equivocation_adv_le` is the only bridge
(§6's canary compiles that fact).

⚑ **`hEff` IS UNDISCHARGED AND THAT IS THE HONEST STATE** — the standard "the reduction is efficient"
side condition, a PARAMETER because this tree has no cost model (`FloorGames` §8). The floor's honesty
is exactly its `Eff`'s, and §7 prices both poles: `⊤` makes it FALSE at the deployed tree, `⊥`
vacuous. The DISCHARGED successor — on the PROVED keyed-ROM floor, forger an oracle program with
query-counted cost — is §8's `state_commitment_binds_state_rom`. -/
theorem state_commitment_binds_state_advantage_bound (D : CommitDeployment)
    (Eff : Adversary (commitCollisionGame D) → Prop)
    (A : Adversary (stateEquivocationGame D))
    (hEff : Eff (equivocationToCollisionFinder D A))
    (hcol : Hard (commitCollisionGame D) Eff) :
    Negl (gameAdv (stateEquivocationGame D) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (stateEquivocationGame D) A n).1)
    (equivocation_adv_le D A) (hcol _ hEff)

/-- **⚑ RE-GROUNDED `EffectVmConstraints2.state_commitment_no_silent_change`.** A change to the
committed tuple changes the published root EXCEPT with negligible probability: an adversary exhibiting a
SILENT change — two distinct tuples whose group-4 rows carry one and the same root — is, by the same
extractor, a collision finder, since the shared root it publishes is exactly the `newCommit` both its
tuples are pinned to. Under the collision floor at the extracted finder its advantage is negligible.

The `Eff` obligation is the same undischarged side condition as above — named, not hidden. -/
theorem state_commitment_no_silent_change_advantage_bound (D : CommitDeployment)
    (Eff : Adversary (commitCollisionGame D) → Prop)
    (A : Adversary (stateEquivocationGame D))
    (hEff : Eff (equivocationToCollisionFinder D A))
    (hcol : Hard (commitCollisionGame D) Eff) :
    Negl (gameAdv (stateEquivocationGame D) A) :=
  state_commitment_binds_state_advantage_bound D Eff A hEff hcol

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at some OTHER finder.)** Strip the
reduction — try to conclude the equivocator's negligibility from the collision floor applied at some
OTHER finder `B`, NOT the one extracted from it — and the proof does not go through: the floor bounds
`B`, and only `equivocation_adv_le` connects the EXTRACTED finder to the equivocation game. Under the
OLD free hypothesis (`hCR : CommitTreeInjective H`, hypothesis and conclusion sharing the same free `H`)
this tooth was unwritable. It compiles now, and reds if a future edit reconnects the games. -/
example (D : CommitDeployment) (Eff : Adversary (commitCollisionGame D) → Prop)
    (A : Adversary (stateEquivocationGame D))
    (B : Adversary (commitCollisionGame D)) (hB : Eff B)
    (hcol : Hard (commitCollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (stateEquivocationGame D) A) := hcol B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the collision floor at the EXTRACTED finder the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floor (D : CommitDeployment)
    (Eff : Adversary (commitCollisionGame D) → Prop)
    (A : Adversary (stateEquivocationGame D))
    (hEff : Eff (equivocationToCollisionFinder D A))
    (hcol : Hard (commitCollisionGame D) Eff) :
    Negl (gameAdv (stateEquivocationGame D) A) :=
  state_commitment_binds_state_advantage_bound D Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED: both poles proved at THIS carrier.

The sweep's deep result (`FloorGames` §2) says a game floor at the unrestricted class IS the existence
floor. Here is that theorem instantiated at the deployed commitment tree, so a reader can price any
`Eff` exactly rather than take the residual on faith. -/

/-- **⚑ (TOOTH — the floor is FALSE at `Eff := ⊤` for the DEPLOYED tree.)** The real content, and the
reason `Eff` is not decoration: a range-bounded commitment tree HAS a collision at every tag (§1's
counting core), so the collision game is always solvable, so the floor at the unrestricted adversary
class is FALSE — and every consumer would be vacuous there. `Classical.choice` is the adversary and no
restatement of the win relation can see it coming. This is the price of `hEff`, stated as a theorem
instead of a promise. -/
theorem commit_floor_top_false_of_compressing (D : CommitDeployment)
    (hfin : ∀ t : D.Tag, (Set.range (commitTree (D.hash t))).Finite) :
    ¬ Hard (commitCollisionGame D) (fun _ => True) :=
  not_hard_top_of_always_solvable (commitCollisionGame D)
    (fun _ => ⟨([], [])⟩)
    (fun _ t => exists_collision_of_finite_range (D.hash t) (hfin t))

/-- **(TOOTH — the deployed BabyBear form of the same.)** A genuine BabyBear-valued `hash_4_to_1`
refutes the unrestricted-class floor. The deployment the carrier's docstring names is exactly where
`Eff := ⊤` fails. -/
theorem commit_floor_top_false_babyBear (D : CommitDeployment)
    (hb : ∀ (t : D.Tag) (xs : List Int), 0 ≤ D.hash t xs ∧ D.hash t xs < (2013265921 : Int)) :
    ¬ Hard (commitCollisionGame D) (fun _ => True) :=
  commit_floor_top_false_of_compressing D
    (fun t => finite_range_of_bound (commitTree (D.hash t)) _
      (commitTree_bounded (D.hash t) _ (by norm_num) (fun xs => hb t xs)))

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty adversary class the floor holds
for ANY deployment, including a completely broken hash. Recorded HONESTLY: a satisfiability witness is
worth nothing without the refutation beside it, and these two poles together are what make `Eff` a dial
rather than a costume. -/
theorem commit_floor_bot_vacuous (D : CommitDeployment) :
    Hard (commitCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floor is REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** commitment deployment: the hash IGNORES its input entirely, so every pair of distinct
tuples has the same root at every tag. -/
def brokenCommit : CommitDeployment where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  hash := fun _ _ => 0
  deployedTag := ()

/-- **(TOOTH — the floor is REFUTABLE.)** The broken deployment's collision game is solvable at every
tag (`[] ≠ [0]`, both roots `0`), so it has no unrestricted-class floor. So the floor is a GENUINE
constraint — a broken hash refutes it — not vacuously true. -/
theorem brokenCommit_floor_top_false :
    ¬ Hard (commitCollisionGame brokenCommit) (fun _ => True) :=
  not_hard_top_of_always_solvable (commitCollisionGame brokenCommit)
    (fun _ => ⟨([], [])⟩)
    (fun _ _ => ⟨([], [0]), by simp, rfl⟩)

/-! ### The floor is SATISFIABLE (the connection to the keyed-family treatment). -/

/-- **(TOOTH — the keyed family is SATISFIABLE on an injective deployment.)** A deployment whose per-tag
tree is injective discharges `HashCRHardQuant (commitFamily D) (fun _ => True)` — the floor is
REALIZABLE, unlike the injective `CommitTreeInjective` at deployed parameters. ⚑ The `⊤` is now WRITTEN
OUT in the statement instead of hidden behind the deleted `CollisionResistant`, which makes the price
legible without a lemma: this is the UNRESTRICTED adversary class, which §7's first tooth proves FALSE
at a range-bounded (i.e. real) tree. So this witness says only that the family is NOT COMPRESSING — an
injective tree is exactly the toy-hash shape. Honest as a non-emptiness check, never as evidence the
deployed Poseidon2 satisfies anything. -/
theorem commitFamily_CR_of_injective (D : CommitDeployment)
    (hinj : ∀ t : D.Tag, Function.Injective (commitTree (D.hash t))) :
    HashCRHardQuant (commitFamily D) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (commitFamily D) (fun _ t => hinj t)

/-! ## §8 — ⚑ THE KEYED-ROM SUCCESSOR: the equivocation bound DISCHARGED on the PROVED floor.

§5's `_advantage_bound` siblings are the honest fixed-hash statements, and their `hcol : Hard … Eff`
hypothesis is a PARAMETER with no known non-vacuous instantiation: §7 prices `Eff := ⊤` FALSE at the
deployed tree and `Eff := ⊥` vacuous, and this tree has no cost model. The DISCHARGED successor moves
the floor where it is a THEOREM: the keyed random-oracle model (`Crypto.KeyedRomFloor.keyedRom_hard`,
the birthday bound), with the equivocator an ORACLE PROGRAM whose cost is QUERY-COUNTED and the
oracle sampled AFTER the program is fixed (`Crypto.RomCarrierSites`, the landed
`Exec.SystemRootsBindingReduction` §7 pattern).

⚑ **THE MODELLING STEP, STATED (not smuggled)** — `RomCarrierSites`' header caveat, inherited: the
sampled `H : Tag × Msg → Fin (2 ^ l)` replaces the fixed public `commitTree (D.hash t)` (the standard
ROM idealisation, a deliberate modelling step, NOT a derivation); the digest space is `λ`-growing
where the deployed root is a FIXED ~31-bit BabyBear felt — at the deployed width the honest reading
stays "binds exactly as well as ~31 bits allow" (birthday ≈ `2^15.5`, the felt-width wound). The
message domain is the TRUNCATED deployed shape: committed tuples of at most `m` BabyBear-RANGE felts;
on everything the deployed AIR actually commits (in-range felts, the 12-column tuple) the truncation
is LOSSLESS — `feltVec_inj` / `feltVec_val` pin that limb-for-limb. The interior 4-leaf tree
structure is deployed-side; the model commits the tuple in ONE query, exactly as the digest-layer
carrier of `SystemRootsBindingReduction` commits its sub-block. -/

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily flatFamily_card_R taggedCarrier BVec bvecOfList bvecOfList_inj romOpenGame RomOpenEff
   romOpenAdv rom_open_binds flat_open_binds constOpenComp constOpen_in_eff constOpen_gameAdv_pos
   constOpen_binds romOpen_forger_excluded babyBearP babyBearP_pos one_lt_babyBearP)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- Truncate an IN-RANGE deployed felt list to its `Fin babyBearP` limbs — total on exactly the
tuples the deployed AIR can commit (every committed column a genuine BabyBear felt). -/
def feltVec (xs : List Int) (hb : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : Int)) :
    List (Fin babyBearP) :=
  xs.pmap (fun x hx => ⟨x.toNat, (Int.toNat_lt hx.1).mpr hx.2⟩) hb

/-- **LIMB-FOR-LIMB FAITHFULNESS** — reading the truncated limbs back as integers IS the deployed
committed tuple. What changed is only WHO evaluates them (the sampled oracle vs the fixed tree). -/
theorem feltVec_val : ∀ (xs : List Int) (hb : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : Int)),
    (feltVec xs hb).map (fun f : Fin babyBearP => ((f.val : ℕ) : Int)) = xs
  | [], _ => rfl
  | x :: xs, hb => by
      simp only [feltVec, List.pmap, List.map_cons]
      exact congrArg₂ List.cons (Int.toNat_of_nonneg (hb x (List.mem_cons_self)).1)
        (feltVec_val xs (fun y hy => hb y (List.mem_cons_of_mem x hy)))

@[simp] theorem feltVec_length (xs : List Int) (hb : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : Int)) :
    (feltVec xs hb).length = xs.length :=
  List.length_pmap ..

/-- **THE TRUNCATION LOSES NOTHING** — two in-range tuples with one truncation are EQUAL, so a
distinct pair of deployed committed tuples stays a distinct pair of ROM payloads. -/
theorem feltVec_inj {xs ys : List Int}
    (hbx : ∀ x ∈ xs, 0 ≤ x ∧ x < (babyBearP : Int))
    (hby : ∀ y ∈ ys, 0 ≤ y ∧ y < (babyBearP : Int))
    (h : feltVec xs hbx = feltVec ys hby) : xs = ys := by
  have hmap := congrArg (List.map (fun f : Fin babyBearP => ((f.val : ℕ) : Int))) h
  rwa [feltVec_val, feltVec_val] at hmap

/-- **THE STATE-COMMIT KEYED ROM FAMILY** — keyed by the DEPLOYED tag space `D.Tag` (the anchor to
the deployed object), over truncated committed tuples (at most `m` BabyBear-range felts), with the
ideal `λ`-bit digest. The `hw` obligation is closed by construction (`flatFamily_card_R`). -/
def commitRomFamily (D : CommitDeployment) (tagDec : DecidableEq D.Tag) (m : ℕ) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty (fun _ => BVec (Fin babyBearP) m)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(⟨0, Nat.succ_pos m⟩, fun _ => none)⟩)

/-- **THE STATE-COMMIT CARRIER** — commitment `H (t, tuple)`: the root binds the WHOLE committed
tuple in one query. The embedding is the identity on the truncated tuple, injective on the nose. -/
def commitRomCarrier (D : CommitDeployment) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomCarrier (commitRomFamily D tagDec m) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => BVec (Fin babyBearP) m) (fun _ => inferInstance)
    (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The state-equivocation game at the sampled oracle: the adversary PUBLISHES a root (`NEW_COMMIT`)
and exhibits two distinct truncated tuples that BOTH commit to it — `romOpenGame`, the published
value IN the win relation, exactly the `stateEquivocationGame` shape with `StateCommitSat` read at
the sampled oracle. -/
abbrev stateOpenRomGame (D : CommitDeployment) (tagDec : DecidableEq D.Tag) (m : ℕ) : Game :=
  romOpenGame (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m)

/-- **⚑ THE DEPLOYED EQUIVOCATION IS A WIN OF THE ROM GAME.** Two DISTINCT in-range committed tuples
that BOTH open one published `NEW_COMMIT` at the sampled oracle ARE a win — `equivocationGame`'s
event, restated at the sampled oracle, with the truncation proved lossless (`feltVec_inj`). -/
theorem stateCommitRom_equivocation_is_break (D : CommitDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (l : ℕ) (H : (stateOpenRomGame D tagDec m).Inst l) (t : D.Tag)
    {st st' : List Int}
    (hb : ∀ x ∈ st, 0 ≤ x ∧ x < (babyBearP : Int)) (hb' : ∀ x ∈ st', 0 ≤ x ∧ x < (babyBearP : Int))
    (hl : (feltVec st hb).length ≤ m) (hl' : (feltVec st' hb').length ≤ m)
    (hne : st ≠ st') (r : Fin (2 ^ l))
    (h1 : H (t, bvecOfList m (feltVec st hb) hl) = r)
    (h2 : H (t, bvecOfList m (feltVec st' hb') hl') = r) :
    (stateOpenRomGame D tagDec m).wins l H
      (r, (t, ()), bvecOfList m (feltVec st hb) hl, bvecOfList m (feltVec st' hb') hl') :=
  ⟨fun hc => hne (feltVec_inj hb hb' (bvecOfList_inj hl hl' hc)), h1, h2⟩

/-- **⚑⚑ RE-GROUNDED `state_commitment_binds_state`, DISCHARGED ON THE PROVED FLOOR** — the keyed-ROM
successor of §5's `state_commitment_binds_state_advantage_bound`: every query-bounded equivocator of
the published `NEW_COMMIT` has NEGLIGIBLE advantage, in the keyed ROM model of §8's header. The
hypotheses are a polynomial query budget and the forger's membership in the query class — nothing
refutable is carried, and the floor under it is `keyedRom_hard` (the birthday bound), a THEOREM. -/
theorem state_commitment_binds_state_rom (D : CommitDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (stateOpenRomGame D tagDec m))
    (hA : RomOpenEff (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m) Q A) :
    Negl (gameAdv (stateOpenRomGame D tagDec m) A) :=
  flat_open_binds _ _ _ _ _ _ _ _ _ Q hQ A hA

/-- **⚑ RE-GROUNDED `state_commitment_no_silent_change`, DISCHARGED** — a silent change (two distinct
tuples behind one published root) is the SAME oracle-program forgery, so the same discharged bound. -/
theorem state_commitment_no_silent_change_rom (D : CommitDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (stateOpenRomGame D tagDec m))
    (hA : RomOpenEff (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m) Q A) :
    Negl (gameAdv (stateOpenRomGame D tagDec m) A) :=
  state_commitment_binds_state_rom D tagDec m Q hQ A hA

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage.)** The `0`-query constant answerer on
two distinct truncated tuples is in the class at every budget and wins with positive probability at
every parameter — the discharged bound bounds something genuinely nonzero. -/
theorem stateCommitRom_class_inhabited_pos (D : CommitDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (hm : 0 < m) (Q : ℕ → ℕ) :
    ∃ A, RomOpenEff (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m) Q A
      ∧ ∀ l, 0 < gameAdv (stateOpenRomGame D tagDec m) A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  refine ⟨romOpenAdv (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m)
      (constOpenComp (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m)
        (fun l => ⟨0, by positivity⟩) (fun _ => (t₀, ()))
        (fun _ => (⟨0, Nat.succ_pos m⟩, fun _ => none)) (fun _ => (⟨1, by omega⟩, fun _ => none))),
    constOpen_in_eff (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m) _ _ _ _ Q,
    fun l => constOpen_gameAdv_pos (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m)
      _ _ _ _ l ?_⟩
  intro hc
  have : (0 : ℕ) = 1 := congrArg (fun v : BVec (Fin babyBearP) m => v.1.val) hc
  omega

/-- **(TOOTH — the `shortCollAdv` shape is ADMITTED and DEFANGED, at this site.)** The exact answerer
shape that refutes the fixed-hash `IsPolyTime`-style floors — a `0`-query constant answer — is in the
query class, and the discharged bound applies to it: negligible against the sampled oracle, where
against the fixed tree it wins with probability `1`. -/
theorem stateCommitRom_constAnswer_defanged (D : CommitDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (r : ∀ l, Fin (2 ^ l)) (c : ∀ _l, D.Tag × Unit) (v w : ∀ _l, BVec (Fin babyBearP) m) :
    Negl (gameAdv (stateOpenRomGame D tagDec m)
      (romOpenAdv _ _ (constOpenComp (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m)
        r c v w))) :=
  constOpen_binds (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m) r c v w Q hQ
    (flatFamily_card_R _ _ _ _ _ _ _ _)

/-- **(TOOTH — a non-negligible forger is OUTSIDE the class.)** The general exclusion at this site:
the refutation strategy that kills every fixed-hash floor cannot produce a member of this one. -/
theorem stateCommitRom_nonNegl_forger_excluded (D : CommitDeployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (stateOpenRomGame D tagDec m))
    (hnn : ¬ Negl (gameAdv (stateOpenRomGame D tagDec m) A)) :
    ¬ RomOpenEff (commitRomFamily D tagDec m) (commitRomCarrier D tagDec m) Q A :=
  romOpen_forger_excluded _ _ Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _) A hnn

#assert_all_clean [
  finite_range_of_bound,
  commitTreeInjective_false_of_finite_range,
  commitTree_bounded,
  commitTreeInjective_false_babyBear,
  commitTreeInjective_false_blake3,
  exists_collision_of_finite_range,
  deployed_hash_is_family_instance,
  collisionGame_wins_iff,
  equivocationGame_wins_iff,
  equivocation_wins_imp,
  equivocation_adv_le,
  state_commitment_binds_state_advantage_bound,
  state_commitment_no_silent_change_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  commit_floor_top_false_of_compressing,
  commit_floor_top_false_babyBear,
  commit_floor_bot_vacuous,
  brokenCommit_floor_top_false,
  commitFamily_CR_of_injective,
  feltVec_val,
  feltVec_inj,
  stateCommitRom_equivocation_is_break,
  state_commitment_binds_state_rom,
  state_commitment_no_silent_change_rom,
  stateCommitRom_class_inhabited_pos,
  stateCommitRom_constAnswer_defanged,
  stateCommitRom_nonNegl_forger_excluded
]

end Dregg2.Spike.CommitTreeRegrounded

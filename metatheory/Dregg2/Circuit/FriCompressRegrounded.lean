/-
# `Dregg2.Circuit.FriCompressRegrounded` — the `CompressInjective` consumer RE-GROUNDED off the
FALSE-AS-NAMED injective floor onto a REAL Merkle-forgery game carrying an explicit `Eff`.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `CompressInjective` site)

`FriVerifier.CompressInjective compress := ∀ a b c d, compress a b = compress c d → a = c ∧ b = d` is
stated as **injectivity** of the Poseidon2 `TruncatedPermutation` — the 2-to-1 Merkle node compression.
`List F × List F` is INFINITE and the deployed compression emits a FIXED-WIDTH digest over a FINITE
field (`DIGEST_ELEMS` BabyBear lanes), so the floor is **FALSE at deployed parameters by pigeonhole**
(§1, `compressInjective_false_of_finite_range` / `compressInjective_false_of_digest_width`). Two field
elements do not fit in one without collision — that is what "compression" MEANS. The one consumer
conditioned on it, `merkleRecompute_binds` (the module's own "anti-forgery tooth"), is therefore
**VACUOUSLY TRUE** at real parameters. `#assert_axioms` is blind: the proof is clean; the HYPOTHESIS is
the flaw.

The carrier's docstring calls it "the `Poseidon2SpongeCR` carrier … NAMED, never an axiom". Naming is
not the issue: `Poseidon2SpongeCR` is itself proved FALSE for a range-bounded sponge by
`HashFloorHonesty.poseidon2SpongeCR_false_babyBear`, and this is the same predicate one arity down.
Collision-resistance says collisions are hard to FIND, never that they do not EXIST.

## The re-grounding (the `PreRotationKeySetRegrounded` pattern)

  * **§1 — FALSE AS NAMED.** The counting core (`HashFloorHonesty.not_injective_of_finite_range`) fires
    through the pair-flattening `fun p => compress p.1 p.2`, exactly as
    `HashFloorHonesty.compressInjective_false_of_finite_range` does for `StateCommit.compressInjective`;
    `compressInjective_false_of_digest_width` is the deployed form (a `Finite` field + a fixed digest
    width is all it takes).
  * **§2 — the KEYED family.** `CompressDeployment` bundles the deployed compression with its
    domain-separation tag space (the effective key — the standard keyed-from-unkeyed model), keyed on
    the PAIR domain so the family's `Input` is the compression's real 2-to-1 domain.
    `deployed_compress_is_family_instance` and `collisionGame_wins_iff` pin FAITHFULNESS.
  * **§3 — the MERKLE-FORGERY GAME.** Handed a sampled tag, the adversary outputs two leaves, a sibling
    path and a query index; it WINS iff the leaves are DISTINCT yet `merkleRecompute` (the REAL deployed
    recompute) carries both to the SAME root at that index over that path. That IS a Merkle opening
    forgery — a query opened to a value the committed tree does not contain — and it is what
    `merkleRecompute_binds` rules out. IN the win relation, not in a docstring.
  * **§4 — THE REDUCTION, AND IT PEELS THE WHOLE PATH.** `peelPath` walks the forged opening level by
    level and RETURNS the first genuine `compress` collision: at each level the two accumulators enter
    `compress` against the SAME sibling, so either the outputs already collide on distinct inputs (the
    collision, returned) or the outputs stay distinct and the walk descends with the invariant intact.
    `peelPath_wins` is that induction — the DUAL of `merkleRecompute_binds`'s, at the same recursion
    over the path, with the injectivity step replaced by the extraction it was hiding.
    `merkle_adv_le` is the advantage inequality by `winProb_le_of_imp`. Nothing is stated at the
    one-step level; the full path is peeled.
  * **§5 — the RE-GROUNDED CONSUMER.** `merkleRecompute_binds_advantage_bound`: the Boolean "two leaves
    that recompute to the same root ARE equal" becomes "an attacker opens a query to a forged value only
    with negligible probability", from the collision floor VIA the reduction.

## ⚑ THE `Eff` PARAMETER IS THE WHOLE HONESTY, AND IT IS UNDISCHARGED

The sweep's load-bearing result (`FloorGames` §2, `hard_top_iff_solvableFrac_negl`): at the UNRESTRICTED
adversary class a game floor IS the existence floor, so it is FALSE wherever collisions exist — and §1
proves they exist at any fixed-width compression. §7 instantiates both poles at THIS carrier:
`compress_floor_top_false_of_compressing` (`Eff := ⊤` is FALSE at deployed parameters) and
`compress_floor_bot_vacuous` (`Eff := ⊥` is vacuous). So `Eff` is a PARAMETER, in the open, at every use
site: this tree has no cost model (`FloorGames` §8), and inventing a shallow imitation would be another
costume. Hiding the `Eff` dependence is the disease; naming it is the repair.

## Non-fake

The floor is REFUTABLE (`brokenCompress_floor_top_false`: a compression that ignores its inputs has a
finder winning at every tag, advantage `1`) and the reduction is LOAD-BEARING (§6's canary: the keystone
does NOT follow from the floor applied at some OTHER finder). The OLD `merkleRecompute_binds` is KEPT
untouched in `FriVerifier`; its sibling is ADDED here. `#assert_all_clean`; no `sorry`, no fresh
`axiom`.

## Coordination

This is the FRI/Merkle `compress` lane. The `STATE_COMMIT` tree carrier is the same shape and is
re-grounded in `Spike.CommitTreeRegrounded`; the pre-rotation key-set carrier is
`Apps.PreRotationKeySetRegrounded`.
-/
import Mathlib.Data.Set.Finite.List
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Crypto.RomMerkleOpening

namespace Dregg2.Circuit.FriCompressRegrounded

-- `merkleRecompute_binds` was opened here and is DELETED (it was vacuous under `CompressInjective`;
-- this module's `peelPath` extractor replaces it with no assumption on `compress`).
open Dregg2.Circuit.FriVerifier (CompressInjective merkleRecompute merkleVerify)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable
   HashCRHardQuant hashCRHardQuant_top_of_injective)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED: the injective `CompressInjective` floor is refuted by the deployed
compression.

`CompressInjective compress` says the 2-to-1 map `(a, b) ↦ compress a b` is injective on the INFINITE
`List F × List F`. The deployed `TruncatedPermutation` emits a FIXED-WIDTH digest over a FINITE field,
so its range is finite and the counting core fires — no Poseidon2 collision need be exhibited;
cardinality suffices, and is the honest statement. -/

/-- A function into the fixed-width lists of a FINITE alphabet has FINITE range. The general form of
`HashFloorHonesty.finite_range_of_field_bound` for a DIGEST-valued (rather than felt-valued) hash —
restated locally so this file and its `STATE_COMMIT` sibling stay import-independent of each other. -/
theorem finite_range_of_width {F : Type} [Finite F] {α : Type} (f : α → List F) (w : ℕ)
    (hw : ∀ x, (f x).length = w) : (Set.range f).Finite := by
  refine (List.finite_length_eq F w).subset ?_
  rintro _ ⟨x, rfl⟩
  exact hw x

/-- **TOOTH — `CompressInjective` is FALSE for any range-bounded 2-to-1 compression.** Literally the
counting core, routed through the pair-flattening `fun p => compress p.1 p.2` — the same route
`HashFloorHonesty.compressInjective_false_of_finite_range` takes for `StateCommit.compressInjective`,
this being the identical predicate at the identical arity. The `a = c ∧ b = d` conclusion of the floor
is exactly injectivity of the flattened map, so the floor hands the counting core its hypothesis. -/
theorem compressInjective_false_of_finite_range {F : Type} [Nonempty F]
    (compress : List F → List F → List F)
    (hfin : (Set.range (fun p : List F × List F => compress p.1 p.2)).Finite) :
    ¬ CompressInjective compress := by
  intro hci
  refine not_injective_of_finite_range (fun p : List F × List F => compress p.1 p.2) hfin ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  obtain ⟨h1, h2⟩ := hci a b c d heq
  simp [h1, h2]

/-- **TOOTH (deployed form) — `CompressInjective` is FALSE at the deployed Poseidon2 compression.** The
`TruncatedPermutation` over a FINITE field emitting a FIXED digest width (`DIGEST_ELEMS` BabyBear lanes)
refutes the floor. Nothing about Poseidon2's algebra is needed: a finite alphabet and a constant output
length are the whole hypothesis, and every real Merkle node compression has both. The floor is not
merely un-proven at the deployed hash; it is provably FALSE there, so `merkleRecompute_binds` is vacuous
at real parameters. -/
theorem compressInjective_false_of_digest_width {F : Type} [Finite F] [Nonempty F]
    (compress : List F → List F → List F) (w : ℕ)
    (hw : ∀ a b : List F, (compress a b).length = w) :
    ¬ CompressInjective compress :=
  compressInjective_false_of_finite_range compress
    (finite_range_of_width (fun p : List F × List F => compress p.1 p.2) w (fun p => hw p.1 p.2))

/-- **TOOTH (the deployed constant) — `CompressInjective` is FALSE at a Poseidon2-w16 8-lane digest.**
The deployed `MerkleTreeMmcs` compression over BabyBear emits `DIGEST_ELEMS = 8` felts. Spelled out so
the refutation names the deployment rather than a schema. -/
theorem compressInjective_false_poseidon2_digest {F : Type} [Finite F] [Nonempty F]
    (compress : List F → List F → List F)
    (hw : ∀ a b : List F, (compress a b).length = 8) :
    ¬ CompressInjective compress :=
  compressInjective_false_of_digest_width compress 8 hw

/-- **THE COLLISION THE FALSITY EXHIBITS.** A range-bounded compression has, at every parameter, a
genuine collision — two DISTINCT input pairs with equal digests. This is the counting core in the
positive form the game floors below consume: it is what makes the `⊤`-class floor false (§7), and
therefore what makes the `Eff` parameter load-bearing rather than decorative. -/
theorem exists_collision_of_finite_range {F : Type} [Nonempty F]
    (compress : List F → List F → List F)
    (hfin : (Set.range (fun p : List F × List F => compress p.1 p.2)).Finite) :
    ∃ q : (List F × List F) × (List F × List F),
      q.1 ≠ q.2 ∧ compress q.1.1 q.1.2 = compress q.2.1 q.2.2 := by
  by_contra hno
  push_neg at hno
  refine not_injective_of_finite_range (fun p : List F × List F => compress p.1 p.2) hfin
    (fun a b hab => ?_)
  by_contra hne
  exact hno (a, b) hne hab

/-! ## §2 — the KEYED family: domain separation is the key.

The deployed `TruncatedPermutation` is a FIXED unkeyed function; its effective key is the
domain-separation tag / parameter regime the Poseidon2 instance is instantiated at. Modelling that tag
as the key is the standard keyed-from-unkeyed treatment (`Poseidon2KeyedBridge` §1-§2) and is what stops
the "hardcode a known collision" degeneracy that collapses an unkeyed floor. -/

/-- **The deployed Merkle node compression.** `compress` is the tag-keyed `TruncatedPermutation` (the
deployed fixed function at each domain-separation tag); `Tag` is the finite, inhabited tag space the CR
game samples; `deployedTag` is the tag the FRI verifier's `MerkleTreeMmcs` computes under. `fieldDecEq`
is the field's decidable equality — the real BabyBear has it, and both the game (which checks two leaves
are distinct) and the extractor (which detects the level the collision lands on) need it. -/
structure CompressDeployment (F : Type) where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The tag-keyed 2-to-1 compression — the deployed fixed function at each tag. -/
  compress : Tag → List F → List F → List F
  /-- Decidable equality on field elements (the game checks two leaves are distinct). -/
  fieldDecEq : DecidableEq F
  /-- The specific domain-separation tag the FRI verifier computes under. -/
  deployedTag : Tag

/-- **`compressFamily D`** — the deployed compression lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag, on its REAL 2-to-1 domain `List F × List F`. This is the object the collision
floor `FloorGames.HashCRHardQuant` is realized at for the real Merkle node hash — at whatever adversary
class `Eff` the reader is willing to price. -/
def compressFamily {F : Type} (D : CompressDeployment F) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List F × List F
  Out := List F
  H := fun _ t p => D.compress t p.1 p.2
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := letI := D.fieldDecEq; inferInstance
  outDecEq := letI := D.fieldDecEq; inferInstance

/-- **FAITHFULNESS.** The deployed FIXED compression IS the keyed family's instance at the deployed tag
— a definitional equality, no idealization. So the CR game below is a game about the very function the
FRI verifier's Merkle recompute calls. -/
theorem deployed_compress_is_family_instance {F : Type} (D : CompressDeployment F) (n : ℕ) :
    (fun p : List F × List F => D.compress D.deployedTag p.1 p.2)
      = (compressFamily D).H n D.deployedTag := rfl

/-! ⚑ **THERE IS NO RUNG-1 BRIDGE HERE ANY MORE, AND THAT IS THE HONEST STATE (deleted 2026-07-28).**

A `compressFamily_CR_of_compressInjective` stood at this point: `CompressInjective` at every tag ⟹ the
family's now-deleted `HashFloorHonesty.CollisionResistant` floor, argued as "the OLD floor was STRICTLY
STRONGER, so nothing is lost re-grounding — a false hypothesis is replaced by one a real hash can
satisfy". **Both ends of that bridge are refuted, so it bought nothing.** Its source is refuted by §1 at
any fixed-width digest; its target was `HashCRHardQuant (compressFamily D) (fun _ => True)` spelled
without the `⊤`, and §7's first tooth refutes THAT at the same compression. A bridge from an empty
hypothesis to a false conclusion is not a re-grounding argument.

What stands in its place is what this file already carries and does not need a bridge to state: the
collision GAME below (§3) with its adversary class `Eff` written out at every use site, both poles of
that class PRICED as theorems (§7), and the §8 successor on the keyed-ROM floor, where the bound is
PROVED by the birthday argument instead of assumed. -/

/-! ## §3 — the COMPRESSION-COLLISION GAME and the MERKLE-FORGERY GAME, as first-class objects. -/

/-- **THE COMPRESSION-COLLISION GAME.** Instances are sampled domain-separation tags; the adversary
outputs two input PAIRS and WINS iff they are a GENUINE collision of the deployed compression at that
tag — distinct pairs, equal digests. This is the game the floor below quantifies over, with an explicit
adversary class. -/
def compressCollisionGame {F : Type} (D : CompressDeployment F) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (List F × List F) × (List F × List F)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t q => q.1 ≠ q.2 ∧ D.compress t q.1.1 q.1.2 = D.compress t q.2.1 q.2.2
  winsDec := fun _ t q => by
    letI := D.fieldDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine collision
of the real deployed compression. Not a docstring: the `Prop` itself. -/
theorem collisionGame_wins_iff {F : Type} (D : CompressDeployment F) (n : ℕ) (t : D.Tag)
    (q : (List F × List F) × (List F × List F)) :
    (compressCollisionGame D).wins n t q ↔
      (q.1 ≠ q.2 ∧ D.compress t q.1.1 q.1.2 = D.compress t q.2.1 q.2.2) :=
  Iff.rfl

/-- The object a Merkle forger exhibits: a query index, TWO candidate leaves, and the sibling path it
opens them along. Winning means both leaves open to the same committed root at that index — so the
verifier's `merkleVerify` accepts BOTH, and the query is not bound to a value. -/
structure MerkleForgery (F : Type) where
  /-- The query's domain index (the transcript-derived `qidx` entry the opening is checked at). -/
  index : Nat
  /-- The first candidate leaf. -/
  leaf1 : List F
  /-- The second candidate leaf. -/
  leaf2 : List F
  /-- The sibling path the two leaves are opened along. -/
  siblings : List (List F)

/-- **THE MERKLE-FORGERY GAME.** The adversary is handed a sampled tag and outputs a `MerkleForgery`; it
WINS iff the two leaves are DISTINCT yet the REAL deployed `merkleRecompute` carries both to the SAME
root at that index over that path. Winning IS the attack `merkleRecompute_binds` rules out: an opening
that does not bind its leaf, so a query can be answered with a forged value the committed tree never
contained. The forgery is IN the win predicate, read off the real recompute. -/
def merkleForgeryGame {F : Type} (D : CompressDeployment F) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => MerkleForgery F
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t fg =>
    fg.leaf1 ≠ fg.leaf2
      ∧ merkleRecompute (D.compress t) fg.index fg.leaf1 fg.siblings
          = merkleRecompute (D.compress t) fg.index fg.leaf2 fg.siblings
  winsDec := fun _ t fg => by
    letI := D.fieldDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (2/2)** — a forgery win is, by `Iff.rfl`, two DISTINCT leaves that
the deployed recompute carries to ONE root at ONE index over ONE path. -/
theorem forgeryGame_wins_iff {F : Type} (D : CompressDeployment F) (n : ℕ) (t : D.Tag)
    (fg : MerkleForgery F) :
    (merkleForgeryGame D).wins n t fg ↔
      (fg.leaf1 ≠ fg.leaf2
        ∧ merkleRecompute (D.compress t) fg.index fg.leaf1 fg.siblings
            = merkleRecompute (D.compress t) fg.index fg.leaf2 fg.siblings) :=
  Iff.rfl

/-- **A FORGERY WIN MEANS THE VERIFIER ACCEPTS BOTH OPENINGS.** The game is not about an abstract root:
whatever root the first leaf opens to, the deployed `merkleVerify` — the very Boolean the FRI query
check calls — accepts the SECOND leaf against it too. So the win relation is the verifier's own accept
condition, twice, on distinct leaves. -/
theorem forgery_win_fools_merkleVerify {F : Type} [DecidableEq F] (D : CompressDeployment F)
    (n : ℕ) (t : D.Tag) (fg : MerkleForgery F) (hwin : (merkleForgeryGame D).wins n t fg) :
    merkleVerify (D.compress t) fg.index fg.leaf1 fg.siblings
        (merkleRecompute (D.compress t) fg.index fg.leaf1 fg.siblings) = true
      ∧ merkleVerify (D.compress t) fg.index fg.leaf2 fg.siblings
          (merkleRecompute (D.compress t) fg.index fg.leaf1 fg.siblings) = true := by
  obtain ⟨_, hroot⟩ := hwin
  refine ⟨by simp [merkleVerify], ?_⟩
  simp [merkleVerify, hroot]

/-! ## §4 — THE REDUCTION: a Merkle forger IS a compression collision finder, and the WHOLE PATH is
peeled.

This is the part the OLD carrier hid. `merkleRecompute_binds` induces over the path and, at every level,
SPENDS the injectivity hypothesis to walk the equality back down. Injectivity is false, so that proof
buys nothing at deployed parameters. The same induction run the other way EXTRACTS: at each level the
two accumulators are compressed against the SAME sibling on the SAME side (the index bit is shared —
both leaves are opened at the same query index), so at each level either the digests already agree on
distinct inputs — a genuine collision, RETURNED — or they disagree, and the walk descends with "the
accumulators are distinct" restored. The path is finite, and the root equality at the bottom forbids the
walk from descending forever with distinct accumulators. So the collision is always found. -/

/-- **THE EXTRACTOR.** Walk the forged opening from the leaves toward the root, at each level pairing
each accumulator with the shared sibling on the side the index bit selects, and RETURN the first level
whose two `compress` inputs already agree in output. If none does, the walk descends on the two (now
distinct) digests. The `[]` case is unreachable under a winning forgery (`peelPath_wins`'s `nil` branch
discharges it: with no path the recompute IS the leaf, so equal roots means equal leaves) and returns a
degenerate pair rather than inventing one.

Structural recursion on the path — the SAME recursion `merkleRecompute`/`merkleRecompute_binds` run
on. -/
def peelPath {F : Type} [DecidableEq F] (compress : List F → List F → List F) :
    Nat → List F → List F → List (List F) → (List F × List F) × (List F × List F)
  | _, l1, l2, [] => ((l1, l1), (l2, l2))
  | idx, l1, l2, s :: rest =>
      if idx % 2 = 0 then
        if compress l1 s = compress l2 s then ((l1, s), (l2, s))
        else peelPath compress (idx / 2) (compress l1 s) (compress l2 s) rest
      else
        if compress s l1 = compress s l2 then ((s, l1), (s, l2))
        else peelPath compress (idx / 2) (compress s l1) (compress s l2) rest

/-- **⚑ THE EXTRACTION — the full path peel, and this IS `merkleRecompute_binds` inverted.**

From DISTINCT leaves that recompute to the SAME root, `peelPath` returns a GENUINE `compress` collision:
two distinct input pairs with equal digests. The induction is `merkleRecompute_binds`'s, over the same
path, at the same index arithmetic — with the step that CONSUMED `hinj` replaced by the extraction
`hinj` was standing in for. The `nil` case is where the two proofs meet: there the recompute is the
identity, so equal roots force equal leaves, contradicting distinctness; `merkleRecompute_binds` reads
that as its base case, this reads it as the reason the walk cannot run off the end of the path.

Nothing here is stated at the one-step level and nothing is assumed about `compress`. -/
theorem peelPath_wins {F : Type} [DecidableEq F] (compress : List F → List F → List F) :
    ∀ (siblings : List (List F)) (idx : Nat) (l1 l2 : List F),
      l1 ≠ l2 →
      merkleRecompute compress idx l1 siblings = merkleRecompute compress idx l2 siblings →
      (peelPath compress idx l1 l2 siblings).1 ≠ (peelPath compress idx l1 l2 siblings).2
        ∧ compress (peelPath compress idx l1 l2 siblings).1.1
              (peelPath compress idx l1 l2 siblings).1.2
            = compress (peelPath compress idx l1 l2 siblings).2.1
                (peelPath compress idx l1 l2 siblings).2.2 := by
  intro siblings
  induction siblings with
  | nil =>
      intro idx l1 l2 hne h
      exact absurd (by simpa [merkleRecompute] using h) hne
  | cons s rest ih =>
      intro idx l1 l2 hne h
      unfold merkleRecompute at h
      by_cases hb : idx % 2 = 0
      · simp only [hb, if_true] at h
        by_cases hc : compress l1 s = compress l2 s
        · have hpp : peelPath compress idx l1 l2 (s :: rest) = ((l1, s), (l2, s)) := by
            simp only [peelPath, hb, hc, if_true]
          rw [hpp]
          exact ⟨fun heq => hne (congrArg Prod.fst heq), hc⟩
        · have hpp : peelPath compress idx l1 l2 (s :: rest)
              = peelPath compress (idx / 2) (compress l1 s) (compress l2 s) rest := by
            simp only [peelPath, hb, hc, if_true, if_false]
          rw [hpp]
          exact ih (idx / 2) _ _ hc h
      · simp only [hb, if_false] at h
        by_cases hc : compress s l1 = compress s l2
        · have hpp : peelPath compress idx l1 l2 (s :: rest) = ((s, l1), (s, l2)) := by
            simp only [peelPath, hb, hc, if_true, if_false]
          rw [hpp]
          exact ⟨fun heq => hne (congrArg Prod.snd heq), hc⟩
        · have hpp : peelPath compress idx l1 l2 (s :: rest)
              = peelPath compress (idx / 2) (compress s l1) (compress s l2) rest := by
            simp only [peelPath, hb, hc, if_false]
          rw [hpp]
          exact ih (idx / 2) _ _ hc h

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A Merkle forger becomes a compression collision finder
by peeling the path of the opening it forged. This is not a rename and not a re-indexing: it runs the
real `merkleRecompute`'s own recursion over the forger's own sibling path and returns the level the
collision lands on. -/
def merkleToCollisionFinder {F : Type} (D : CompressDeployment F)
    (A : Adversary (merkleForgeryGame D)) : Adversary (compressCollisionGame D) where
  run := fun n t =>
    letI := D.fieldDecEq
    peelPath (D.compress t) (A.run n t).index (A.run n t).leaf1 (A.run n t).leaf2
      (A.run n t).siblings

/-- **⚑ WIN-PRESERVATION — and this IS `merkleRecompute_binds`, at the game level.** Wherever the forger
wins, the extracted pair is a GENUINE collision of the deployed compression at the sampled tag. The
crypto content lives in a proof term, not in a sentence about one. -/
theorem merkle_wins_imp {F : Type} (D : CompressDeployment F)
    (A : Adversary (merkleForgeryGame D)) (n : ℕ) (t : D.Tag)
    (hwin : (merkleForgeryGame D).wins n t (A.run n t)) :
    (compressCollisionGame D).wins n t ((merkleToCollisionFinder D A).run n t) := by
  letI := D.fieldDecEq
  obtain ⟨hne, hroot⟩ := hwin
  exact peelPath_wins (D.compress t) (A.run n t).siblings (A.run n t).index
    (A.run n t).leaf1 (A.run n t).leaf2 hne hroot

/-- **THE ADVANTAGE INEQUALITY.** The forger's advantage is at most the extracted collision finder's, at
every parameter — both play over the SAME sampled tag space, and every tag the forger wins the extracted
finder wins. A genuine reduction inequality over real game advantages. -/
theorem merkle_adv_le {F : Type} (D : CompressDeployment F)
    (A : Adversary (merkleForgeryGame D)) (n : ℕ) :
    gameAdv (merkleForgeryGame D) A n
      ≤ gameAdv (compressCollisionGame D) (merkleToCollisionFinder D A) n := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact merkle_wins_imp D A n t ht

/-! ## §5 — the RE-GROUNDED CONSUMER.

The Boolean keystone becomes an advantage bound, derived FROM the collision floor VIA the reduction. The
old statement is kept in `FriVerifier`; this is its honest sibling. -/

/-- **⚑ RE-GROUNDED `FriVerifier.merkleRecompute_binds`.**

Under the compression-collision floor at the game the reduction actually attacks, a Merkle forger whose
extracted finder is in the floor's adversary class has NEGLIGIBLE advantage: an attacker opens a FRI
query to a forged leaf only with negligible probability. The Boolean "two leaves that recompute the same
root at the same index over the same path ARE equal" becomes "are equal EXCEPT with negligible
probability" — which is what a real Poseidon2 can actually deliver, and what the FALSE injective floor
was standing in for.

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about the
forgery game, the hypothesis about the collision game, and `merkle_adv_le` is the only bridge (§6's
canary compiles that fact).

⚑ **`hEff` IS A PARAMETER HERE BECAUSE THIS IS THE STATEMENT AT AN ARBITRARY CLASS.** §8 DISCHARGES it
at `Eff := IsPolyTime`, deriving the peeled finder's efficiency from the forger's instead of assuming
it. The floor's honesty is exactly its `Eff`'s, and §7 prices both poles: `⊤` makes it FALSE at the
deployed compression, `⊥` vacuous. -/
theorem merkleRecompute_binds_advantage_bound {F : Type} (D : CompressDeployment F)
    (Eff : Adversary (compressCollisionGame D) → Prop)
    (A : Adversary (merkleForgeryGame D))
    (hEff : Eff (merkleToCollisionFinder D A))
    (hcol : Hard (compressCollisionGame D) Eff) :
    Negl (gameAdv (merkleForgeryGame D) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (merkleForgeryGame D) A n).1)
    (merkle_adv_le D A) (hcol _ hEff)

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at some OTHER finder.)** Strip the
reduction — try to conclude the forger's negligibility from the collision floor applied at some OTHER
finder `B`, NOT the one extracted by peeling its path — and the proof does not go through: the floor
bounds `B`, and only `merkle_adv_le` connects the EXTRACTED finder to the forgery game. Under the OLD
free hypothesis (`hinj : CompressInjective compress`, hypothesis and conclusion sharing the same free
`compress`) this tooth was unwritable. It compiles now, and reds if a future edit reconnects the
games. -/
example {F : Type} (D : CompressDeployment F) (Eff : Adversary (compressCollisionGame D) → Prop)
    (A : Adversary (merkleForgeryGame D))
    (B : Adversary (compressCollisionGame D)) (hB : Eff B)
    (hcol : Hard (compressCollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (merkleForgeryGame D) A) := hcol B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the collision floor at the EXTRACTED finder the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floor {F : Type} (D : CompressDeployment F)
    (Eff : Adversary (compressCollisionGame D) → Prop)
    (A : Adversary (merkleForgeryGame D))
    (hEff : Eff (merkleToCollisionFinder D A))
    (hcol : Hard (compressCollisionGame D) Eff) :
    Negl (gameAdv (merkleForgeryGame D) A) :=
  merkleRecompute_binds_advantage_bound D Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED: both poles proved at THIS carrier.

The sweep's deep result (`FloorGames` §2) says a game floor at the unrestricted class IS the existence
floor. Here is that theorem instantiated at the deployed compression, so a reader can price any `Eff`
exactly rather than take the residual on faith. -/

/-- **⚑ (TOOTH — the floor is FALSE at `Eff := ⊤` for the DEPLOYED compression.)** The real content, and
the reason `Eff` is not decoration: a range-bounded compression HAS a collision at every tag (§1's
counting core), so the collision game is always solvable, so the floor at the unrestricted adversary
class is FALSE — and every consumer would be vacuous there. `Classical.choice` is the adversary and no
restatement of the win relation can see it coming. This is the price of `hEff`, stated as a theorem
instead of a promise. -/
theorem compress_floor_top_false_of_compressing {F : Type} [Nonempty F] (D : CompressDeployment F)
    (hfin : ∀ t : D.Tag, (Set.range (fun p : List F × List F => D.compress t p.1 p.2)).Finite) :
    ¬ Hard (compressCollisionGame D) (fun _ => True) :=
  not_hard_top_of_always_solvable (compressCollisionGame D)
    (fun _ => ⟨(([], []), ([], []))⟩)
    (fun _ t => exists_collision_of_finite_range (D.compress t) (hfin t))

/-- **(TOOTH — the deployed fixed-digest-width form of the same.)** A genuine Poseidon2
`TruncatedPermutation` over a finite field, emitting a constant digest width, refutes the
unrestricted-class floor. The deployment the carrier's docstring names is exactly where `Eff := ⊤`
fails. -/
theorem compress_floor_top_false_of_digest_width {F : Type} [Finite F] [Nonempty F]
    (D : CompressDeployment F) (w : ℕ)
    (hw : ∀ (t : D.Tag) (a b : List F), (D.compress t a b).length = w) :
    ¬ Hard (compressCollisionGame D) (fun _ => True) :=
  compress_floor_top_false_of_compressing D
    (fun t => finite_range_of_width (fun p : List F × List F => D.compress t p.1 p.2) w
      (fun p => hw t p.1 p.2))

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty adversary class the floor holds for
ANY deployment, including a completely broken compression. Recorded HONESTLY: a satisfiability witness is
worth nothing without the refutation beside it, and these two poles together are what make `Eff` a dial
rather than a costume. -/
theorem compress_floor_bot_vacuous {F : Type} (D : CompressDeployment F) :
    Hard (compressCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floor is REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** compression deployment: the node hash IGNORES both inputs entirely, so every pair of
distinct input pairs collides at every tag. -/
def brokenCompress : CompressDeployment Int where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  compress := fun _ _ _ => []
  fieldDecEq := inferInstance
  deployedTag := ()

/-- **(TOOTH — the floor is REFUTABLE.)** The broken deployment's collision game is solvable at every tag
(`([0], []) ≠ ([1], [])`, both compressing to `[]`), so it has no unrestricted-class floor. So the floor
is a GENUINE constraint — a broken compression refutes it — not vacuously true. -/
theorem brokenCompress_floor_top_false :
    ¬ Hard (compressCollisionGame brokenCompress) (fun _ => True) :=
  not_hard_top_of_always_solvable (compressCollisionGame brokenCompress)
    (fun _ => ⟨(([], []), ([], []))⟩)
    (fun _ _ => ⟨(([0], []), ([1], [])), by simp, rfl⟩)

/-- **(TOOTH — the broken deployment ALSO forges a Merkle opening.)** The refutation is not confined to
the collision game: under a compression that ignores its inputs, two DISTINCT leaves recompute to the
same root over a one-level path, so the forgery game is solvable too — the attack the re-grounded
keystone bounds is REAL, and a broken hash performs it. -/
theorem brokenCompress_forgery_solvable (n : ℕ) (t : brokenCompress.Tag) :
    ∃ fg, (merkleForgeryGame brokenCompress).wins n t fg :=
  ⟨{ index := 0, leaf1 := [0], leaf2 := [1], siblings := [[]] }, by simp, rfl⟩

/-! ### The floor is SATISFIABLE (the connection to the keyed-family treatment). -/

/-- **(TOOTH — the keyed family is SATISFIABLE on an injective deployment.)** A deployment whose per-tag
compression is injective discharges `HashCRHardQuant (compressFamily D) (fun _ => True)` — the honest
floor is REALIZABLE, unlike the injective `CompressInjective` at deployed parameters. ⚑ Recorded with
its price: this is the `⊤`-class object, which §7's first tooth proves FALSE at a fixed-width (i.e.
real) compression — and the `⊤` is now written into the statement instead of hidden behind a name. An
injective compression is exactly the toy-hash shape; the satisfiability is honest only as a
non-emptiness check, never as evidence the deployed Poseidon2 satisfies it. -/
theorem compressFamily_CR_of_injective {F : Type} (D : CompressDeployment F)
    (hinj : ∀ t : D.Tag, Function.Injective (fun p : List F × List F => D.compress t p.1 p.2)) :
    HashCRHardQuant (compressFamily D) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (compressFamily D) (fun _ t => hinj t)

/-! ## §8 — `hEff` DISCHARGED: the path peel's efficiency is a THEOREM.

§5 states the bound at an ARBITRARY adversary class, so it carries `hEff`. `Dregg2.Crypto.CostAdversary`
now gives `Eff` content at COST-VECTOR resolution, and the FRI reduction is a pure output reshaping of
the forger's answer with the sampled tag passed through — an `Adversary.postMap` — so
`isPolyTime_postMap` turns `hEff` into a consequence of "the Merkle forger is efficient".

⚑ **The one thing the peel needs that the fixed-width reductions do not is a DIGEST WIDTH.** `peelPath`
does not merely re-slice its input: it RECOMPUTES, so the pair it returns can contain accumulators the
forger never wrote. `peelPath_len_le` proves those accumulators are bounded — by `w`, the deployed
`DIGEST_ELEMS` width of the Poseidon2 `TruncatedPermutation`. That is the ONE per-site input, and it is
a SATISFIED deployment contract (the real compression emits a fixed-width digest), NOT a crypto floor:
it is the same fact §1 uses to REFUTE `CompressInjective`, here used to bound work rather than to
refute binding. Everything else is derived. -/

/-- **THE FORGERY GAME'S ANSWER ENCODING.** A forged opening costs, to write down, its two candidate
leaves and its whole sibling path. Concrete on purpose: the size measure belongs to the GAME
(`CostAdversary` design commitment 4); a degenerate `sz := 0` would make the peel's output free. -/
def merkleAnsSize {F : Type} (D : CompressDeployment F) : AnsSize (merkleForgeryGame D) :=
  fun _ (fg : MerkleForgery F) =>
    fg.leaf1.length + fg.leaf2.length + (fg.siblings.map List.length).sum

/-- **THE COLLISION GAME'S ANSWER ENCODING** — the two claimed 2-to-1 input pairs. -/
def compressAnsSize {F : Type} (D : CompressDeployment F) : AnsSize (compressCollisionGame D) :=
  fun _ (q : (List F × List F) × (List F × List F)) =>
    q.1.1.length + q.1.2.length + q.2.1.length + q.2.2.length

/-- A sibling on the forged path is no longer than the whole path. -/
theorem sibling_len_le_sum {F : Type} {siblings : List (List F)} {s : List F} (hs : s ∈ siblings) :
    s.length ≤ (siblings.map List.length).sum := by
  refine List.single_le_sum (fun _ _ => Nat.zero_le _) _ ?_
  simp only [List.mem_map]
  exact ⟨s, hs, rfl⟩

/-- **⚑ THE PATH PEEL DOES NOT BLOW UP.** Every list `peelPath` can return is either one the forger
supplied (a leaf, or a sibling) or an ACCUMULATOR — and an accumulator is a `compress` output, hence
bounded by the deployed digest width. So under one uniform bound `m` on the leaves, the siblings and the
digest width, all four returned lists are `≤ m`. This is the output-size obligation the cost model's
`reshape`-leaf charge creates, discharged by induction over the SAME path the peel walks. -/
theorem peelPath_len_le {F : Type} [DecidableEq F] (compress : List F → List F → List F) (m : ℕ)
    (hw : ∀ xs ys : List F, (compress xs ys).length ≤ m) :
    ∀ (siblings : List (List F)) (idx : Nat) (l1 l2 : List F),
      l1.length ≤ m → l2.length ≤ m → (∀ s ∈ siblings, s.length ≤ m) →
      (peelPath compress idx l1 l2 siblings).1.1.length ≤ m ∧
        (peelPath compress idx l1 l2 siblings).1.2.length ≤ m ∧
          (peelPath compress idx l1 l2 siblings).2.1.length ≤ m ∧
            (peelPath compress idx l1 l2 siblings).2.2.length ≤ m := by
  intro siblings
  induction siblings with
  | nil =>
      intro idx l1 l2 h1 h2 _
      have hnil : peelPath compress idx l1 l2 [] = ((l1, l1), (l2, l2)) := rfl
      rw [hnil]
      exact ⟨h1, h1, h2, h2⟩
  | cons s rest ih =>
      intro idx l1 l2 h1 h2 hs
      have hsm : s.length ≤ m := hs s (by simp)
      have hrest : ∀ x ∈ rest, x.length ≤ m := fun x hx => hs x (List.mem_cons_of_mem _ hx)
      by_cases hb : idx % 2 = 0
      · by_cases hc : compress l1 s = compress l2 s
        · have hpp : peelPath compress idx l1 l2 (s :: rest) = ((l1, s), (l2, s)) := by
            simp only [peelPath, hb, hc, if_true]
          rw [hpp]
          exact ⟨h1, hsm, h2, hsm⟩
        · have hpp : peelPath compress idx l1 l2 (s :: rest)
              = peelPath compress (idx / 2) (compress l1 s) (compress l2 s) rest := by
            simp only [peelPath, hb, hc, if_true, if_false]
          rw [hpp]
          exact ih (idx / 2) _ _ (hw _ _) (hw _ _) hrest
      · by_cases hc : compress s l1 = compress s l2
        · have hpp : peelPath compress idx l1 l2 (s :: rest) = ((s, l1), (s, l2)) := by
            simp only [peelPath, hb, hc, if_true, if_false]
          rw [hpp]
          exact ⟨hsm, h1, hsm, h2⟩
        · have hpp : peelPath compress idx l1 l2 (s :: rest)
              = peelPath compress (idx / 2) (compress s l1) (compress s l2) rest := by
            simp only [peelPath, hb, hc, if_false]
          rw [hpp]
          exact ih (idx / 2) _ _ (hw _ _) (hw _ _) hrest

/-- **⚑⚑ THE DISCHARGED FRI MERKLE-OPENING BINDING — ON THE PROVED FLOOR.** The successor of the
deleted `merkleRecompute_binds_from_polyTime`, whose floor
`Hard (compressCollisionGame D) (IsPolyTime …)` is the same disease
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` refutes at the deployed
sponge: `IsPolyTime` prices answer SIZE, so a `Classical.choice` `.pure`-leaf answering a fixed short
collision of the FIXED compression is in the class and wins with probability `1` — and no
query-counted `Eff` repairs the fixed-function game (`Crypto.RomBindingReduction`'s header). The
floor must move to a SAMPLED oracle.

This is that move, keyed by the deployment's OWN tag space: a query-bounded forger that opens one
committed FRI layer root at one query — one shared (index-bit, sibling) path of pinned depth `d` —
to two DISTINCT leaves has NEGLIGIBLE advantage, closed from `KeyedRomFloor.keyedRom_hard` (the
birthday bound, PROVED) through `RomMerkleOpening`'s walking extractor, whose `2·d` re-descent is
PAID inside the polynomial total `Q'`. NO floor hypothesis, NO cost model.

⚑ THE MODELLING STEP, STATED: the deployed `w`-felt `TruncatedPermutation` digest is idealised as
ONE `λ`-bit sampled value `Fin (2 ^ l)` — there is no `l` at which they coincide, and at the
deployed width the honest reading stays "binds exactly as well as the digest width allows". The
fixed-hash content of this module is unchanged beside it: the unconditional peel (§5) and the
`Eff`-parametric `merkleRecompute_binds_advantage_bound` with `hEff` in the open. -/
theorem merkleRecompute_binds_rom {F : Type} (D : CompressDeployment F)
    (tagDec : DecidableEq D.Tag) (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (Dregg2.Crypto.RomMerkleOpening.merkleOpenRomGame
      D.Tag D.tagFintype tagDec D.tagNonempty d))
    (hA : Dregg2.Crypto.RomCarrierSites.RomForgeryEff
      (Dregg2.Crypto.RomMerkleOpening.merkleRomFamily D.Tag D.tagFintype tagDec D.tagNonempty)
      (Dregg2.Crypto.RomMerkleOpening.merkleOpenForgery D.Tag D.tagFintype tagDec D.tagNonempty d)
      Q A) :
    Negl (gameAdv (Dregg2.Crypto.RomMerkleOpening.merkleOpenRomGame
      D.Tag D.tagFintype tagDec D.tagNonempty d) A) :=
  Dregg2.Crypto.RomMerkleOpening.merkleOpenRom_binds D.Tag D.tagFintype tagDec D.tagNonempty
    d Q Q' hle hQ' A hA

/-- **(TOOTH — the class the floor is instantiated at is NOT EMPTY.)** Together with
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is excluded) this pins the instantiated
floor strictly between §7's two poles. -/
theorem compressFloor_isPolyTime_inhabited {F : Type} (D : CompressDeployment F) :
    IsPolyTime (compressAnsSize D)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => ((([] : List F), ([] : List F)), (([] : List F), ([] : List F))))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [compressAnsSize]⟩

#assert_all_clean [
  sibling_len_le_sum,
  peelPath_len_le,
  merkleRecompute_binds_rom,
  compressFloor_isPolyTime_inhabited
]

#assert_all_clean [
  finite_range_of_width,
  compressInjective_false_of_finite_range,
  compressInjective_false_of_digest_width,
  compressInjective_false_poseidon2_digest,
  exists_collision_of_finite_range,
  deployed_compress_is_family_instance,
  collisionGame_wins_iff,
  forgeryGame_wins_iff,
  forgery_win_fools_merkleVerify,
  peelPath_wins,
  merkle_wins_imp,
  merkle_adv_le,
  merkleRecompute_binds_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  compress_floor_top_false_of_compressing,
  compress_floor_top_false_of_digest_width,
  compress_floor_bot_vacuous,
  brokenCompress_floor_top_false,
  brokenCompress_forgery_solvable,
  compressFamily_CR_of_injective
]

end Dregg2.Circuit.FriCompressRegrounded

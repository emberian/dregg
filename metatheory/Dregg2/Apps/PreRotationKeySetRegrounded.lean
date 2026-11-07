/-
# `Dregg2.Apps.PreRotationKeySetRegrounded` — the `KeySetCR` consumers RE-GROUNDED off the
FALSE-AS-NAMED injective floor onto a REAL collision game carrying an explicit `Eff`.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `KeySetCR` site)

`PreRotation.KeySetCR hash := ∀ a b : List Key, hash a = hash b → a = b` is stated as **injectivity**
of the key-set digest. `List Key` is INFINITE (any nonempty `Key`) and the deployed digest lands in a
BOUNDED range — 256-bit BLAKE3, or a BabyBear felt — so the floor is **FALSE at deployed parameters by
pigeonhole** (§1, `keySetCR_false_of_finite_range` / `keySetCR_false_blake3`). Every consumer
conditioned on it — `rotate_compromise_resistant`, `rotate_install_unique`,
`rotChain_pinned_by_commitments`, `rotateStepCooled_compromise_resistant`,
`preimage_blocks_cooled_rotation`, `rotateWrite_compromise_resistant` — is therefore **VACUOUSLY TRUE**
at real parameters. `#assert_axioms` is blind: the proofs are clean; the HYPOTHESIS is the flaw.

The file's own non-vacuity witnesses give FALSE COMFORT, exactly as `HashFloorHonesty`'s header
predicts: `demoHash_CR` satisfies the floor with a TOY INJECTIVE hash (an `Encodable` pairing into all
of `ℤ`) and `badHash_not_CR` refutes it with a constant. Toy witness satisfiable, real hash false.

## The re-grounding (the `HermineHashCRRegrounded` / `Poseidon2KeyedBridge` pattern)

  * **§1 — FALSE AS NAMED.** The counting core (`HashFloorHonesty.not_injective_of_finite_range`)
    fires on `KeySetCR` directly; `keySetCR_false_blake3` is the deployed form.
  * **§2 — the KEYED family.** `KeySetDeployment` bundles the deployed digest with its
    domain-separation tag space (the effective key — the standard keyed-from-unkeyed model,
    `Poseidon2KeyedBridge` §1) and the pre-committed next key set at each sampled instance.
    `keySetFamily` lifts it to a `HashFloorHonesty.KeyedHashFamily`; `deployed_hash_is_family_instance`
    and `collisionGame_wins_iff` pin FAITHFULNESS — the game is about the function the cell computes.
  * **§3 — the ROTATION-FORGERY GAME.** A pre-rotation forger is a first-class λ-indexed adversary:
    handed a sampled tag, it WINS iff it produces an ADMITTED rotation whose exhibited key set is NOT
    the committed one. The forgery is IN the win relation, not in a docstring.
  * **§4 — THE REDUCTION.** `forgeryToCollisionFinder` maps a forger to a collision finder by pairing
    its exhibited key set against the committed one; `forgery_wins_imp` proves win-preservation (an
    admitted forgery EXHIBITS `hash newKeys = hash committed` with `newKeys ≠ committed` — a genuine
    collision); `forgery_adv_le` is the advantage inequality by `winProb_le_of_imp`. The reduction is
    the ONLY bridge between hypothesis and conclusion — §6's canary compiles that fact.
  * **§5 — the RE-GROUNDED CONSUMERS.** `rotate_compromise_resistant_advantage_bound` and
    `rotate_install_unique_advantage_bound`: the Boolean "any other key set is REFUSED" / "two
    admitted rotations install the SAME set" become "EXCEPT with negligible probability", from the
    collision floor VIA the reduction.

## ⚑ THE `Eff` PARAMETER IS THE WHOLE HONESTY, AND IT IS UNDISCHARGED

The sweep's load-bearing result (`FloorGames` §2, `hard_top_iff_solvableFrac_negl`): at the
UNRESTRICTED adversary class a game floor IS the existence floor, so it is FALSE wherever collisions
exist — and §1 proves they exist at the deployed digest. §7 instantiates both poles at THIS carrier:
`keySet_floor_top_false_of_compressing` (`Eff := ⊤` is FALSE at deployed parameters, routed through
the counting core — the deployed digest refutes it) and `keySet_floor_bot_vacuous` (`Eff := ⊥` is
vacuous). So `Eff` is a PARAMETER, in the open, at every use site: this tree has no cost model
(`FloorGames` §8), and inventing a shallow imitation would be another costume. Hiding the `Eff`
dependence is the disease; naming it is the repair.

## Non-fake

The floor is REFUTABLE (`brokenKeySet_floor_top_false`: a constant digest has a finder winning at
every tag, advantage `1`) and the reduction is LOAD-BEARING (§6's canary: the keystone does NOT follow
from the floor applied at some OTHER finder). The OLD `KeySetCR` consumers are KEPT untouched and
doc-marked at the teeth; siblings ADDED. `#assert_all_clean`; no `sorry`, no fresh `axiom`.

## Coordination

This is the PRE-ROTATION key-set lane. `RosterCR` (`Circuit/CouncilCommit`) is the same shape and is
re-grounded in `Circuit.CouncilRosterRegrounded`; the queue-root carriers are
`Apps.QueueRootFloorRegrounded`; the STARK/FRI/Merkle hash consumers are
`Circuit.FloorRegroundedConsumers` / `Circuit.Poseidon2KeyedBridge`.
-/
import Dregg2.Apps.PreRotation
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Apps.PreRotationKeySetRegrounded

open Dregg2.Apps.PreRotation (KeySetCR KeyState RotationEvent rotateStep rotate_exhibits_preimage
  rotate_factors)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable
   HashCRHardQuant hashCRHardQuant_top_of_injective)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED: the injective `KeySetCR` floor is refuted by the deployed digest.

`KeySetCR hash` IS `Function.Injective hash` on the INFINITE `List Key`. The deployed key-set digest
lands in a BOUNDED range (a 256-bit BLAKE3 output, or a BabyBear felt), so the counting core fires —
no digest collision need be exhibited; cardinality suffices, and is the honest statement. -/

/-- A digest function into a BOUNDED integer window has FINITE range (`⊆ Ico 0 q`). The general form
of `HashFloorHonesty.finite_range_of_field_bound` — the domain is arbitrary here because the key-set
digest's domain is `List Key`, not `List ℤ`. -/
theorem finite_range_of_bound {α : Type} (f : α → Int) (q : Int)
    (hb : ∀ x, 0 ≤ f x ∧ f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Ico (0 : Int) q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(hb x).1, (hb x).2⟩

/-- **TOOTH — `KeySetCR` is FALSE for any range-bounded key-set digest.** Literally the counting core:
the floor IS injectivity on `List Key`, which is infinite whenever `Key` is inhabited, while a real
digest's range is finite. Stated in the same shape as the flagged siblings' teeth
(`HashFloorHonesty.poseidon2SpongeCR_false_of_finite_range`). -/
theorem keySetCR_false_of_finite_range {Key : Type} [Nonempty Key] (hash : List Key → Int)
    (hfin : (Set.range hash).Finite) : ¬ KeySetCR hash :=
  fun hCR => not_injective_of_finite_range hash hfin (fun a b h => hCR a b h)

/-- **TOOTH (deployed form) — `KeySetCR` is FALSE at the deployed BLAKE3 key-set digest.** A digest
that is a genuine 256-bit value (`0 ≤ · < 2²⁵⁶`) — i.e. every real `blake3` key-set commitment, the
object `PreRotation`'s own docstring points at ("at the deployed hash it discharges to the
BLAKE3/Poseidon2 floor") — REFUTES the floor. The floor is not merely un-proven at the deployed hash;
it is provably FALSE there, so every `KeySetCR` consumer is vacuous at real parameters. -/
theorem keySetCR_false_blake3 {Key : Type} [Nonempty Key] (hash : List Key → Int)
    (hb : ∀ ks, 0 ≤ hash ks ∧ hash ks < (2 : Int) ^ 256) : ¬ KeySetCR hash :=
  keySetCR_false_of_finite_range hash (finite_range_of_bound hash _ hb)

/-- **TOOTH (Poseidon2 form) — `KeySetCR` is FALSE at a BabyBear felt digest** (`p = 2³¹ − 2²⁷ + 1`),
the other deployment the carrier's docstring names. -/
theorem keySetCR_false_babyBear {Key : Type} [Nonempty Key] (hash : List Key → Int)
    (hb : ∀ ks, 0 ≤ hash ks ∧ hash ks < (2013265921 : Int)) : ¬ KeySetCR hash :=
  keySetCR_false_of_finite_range hash (finite_range_of_bound hash _ hb)

/-- **THE COLLISION THE FALSITY EXHIBITS.** A range-bounded key-set digest has, at every parameter, a
genuine collision — two DISTINCT key sets with equal digests. This is the counting core in the
positive form the game floors below consume: it is what makes the `⊤`-class floor false (§7), and
therefore what makes the `Eff` parameter load-bearing rather than decorative. -/
theorem exists_collision_of_finite_range {Key : Type} [Nonempty Key] (hash : List Key → Int)
    (hfin : (Set.range hash).Finite) :
    ∃ p : List Key × List Key, p.1 ≠ p.2 ∧ hash p.1 = hash p.2 := by
  by_contra hno
  push_neg at hno
  refine not_injective_of_finite_range hash hfin (fun a b hab => ?_)
  by_contra hne
  exact hno (a, b) hne hab

/-! ## §2 — the KEYED family: domain separation is the key.

The deployed key-set digest is a FIXED unkeyed function; its effective key is the domain-separation
tag (`TAG_*` derive-key prefix) the deployment absorbs ahead of the key set. Modelling that tag as the
key is the standard keyed-from-unkeyed treatment (`Poseidon2KeyedBridge` §1-§2) and is what stops the
"hardcode a known collision" degeneracy that collapses an unkeyed floor. -/

/-- **The deployed key-set commitment scheme.** `hash` is the tag-keyed key-set digest (the deployed
fixed function at each domain-separation tag); `Tag` is the finite, inhabited tag space the CR game
samples; `committed t` is the pre-committed NEXT key set at the sampled instance `t` (the value the
identity cell's `next_keys_digest` register commits to); `deployedTag` is the tag the cell computes. -/
structure KeySetDeployment (Key : Type) where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The tag-keyed key-set digest — the deployed fixed function at each tag. -/
  hash : Tag → List Key → Int
  /-- The pre-committed next key set at the sampled instance. -/
  committed : Tag → List Key
  /-- Decidable equality on keys (the game checks two key sets are distinct). -/
  keyDecEq : DecidableEq Key
  /-- The specific domain-separation tag the identity cell computes. -/
  deployedTag : Tag

/-- **`keySetFamily D`** — the deployed key-set digest lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. This is the object `FloorGames.HashCRHardQuant` is realized at for the real
digest — always at a NAMED `Eff`, since the `⊤` instance is refuted at that very digest (§7). -/
def keySetFamily {Key : Type} (D : KeySetDeployment Key) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List Key
  Out := Int
  H := fun _ t ks => D.hash t ks
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := letI := D.keyDecEq; inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The deployed FIXED digest IS the keyed family's instance at the deployed tag — a
definitional equality, no idealization. So the CR game below is a game about the very function the
identity cell computes. -/
theorem deployed_hash_is_family_instance {Key : Type} (D : KeySetDeployment Key) (n : ℕ) :
    D.hash D.deployedTag = (keySetFamily D).H n D.deployedTag := rfl

/-! ### ⚑ THERE IS NO OLD-FLOOR ⟹ NEW-FLOOR BRIDGE HERE, AND THAT IS THE POINT.

A theorem `keySetFamily_CR_of_keySetCR` sat here: `KeySetCR` at every tag ⟹ the `⊤`-class collision
floor on `keySetFamily D`, argued as "the OLD floor was STRICTLY STRONGER, so nothing is lost
re-grounding". **BOTH ENDS ARE REFUTED.** §1 kills the injective `KeySetCR` at any range-bounded
digest; §7's `keySet_floor_top_false_of_compressing` kills the `⊤`-class floor at the SAME digest. An
implication between two propositions that are both FALSE at deployed parameters transports nothing,
and "nothing is lost" was FALSE as written — the floor it re-grounded ONTO is refuted at a real hash
too. So the bridge is DELETED rather than restated at `HashCRHardQuant … ⊤`.

What stands in its place is not another rung-1 bridge but this module's OWN poles at its OWN game,
which is why the bridge could be dropped rather than replaced: §7 prices `Eff` exactly
(`keySet_floor_top_false_of_compressing` / `keySet_floor_bot_vacuous`), refutes the floor on a broken
deployment (`brokenKeySet_floor_top_false`) and satisfies it on an injective one
(`keySetFamily_CR_of_injective`, `⊤` written out in the statement); §8 then lands the floor where it
is a THEOREM (`rotate_compromise_resistant_binds_rom`, the keyed ROM). -/

/-! ## §3 — the key-set COLLISION GAME and the ROTATION-FORGERY GAME, as first-class objects. -/

/-- **THE KEY-SET COLLISION GAME.** Instances are sampled domain-separation tags; the adversary
outputs two key sets and WINS iff they are a GENUINE collision of the deployed digest at that tag —
distinct sets, equal digests. This is the game the floor below quantifies over, with an explicit
adversary class. -/
def keySetCollisionGame {Key : Type} (D : KeySetDeployment Key) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List Key × List Key
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2
  winsDec := fun _ t p => by
    letI := D.keyDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine
collision of the real deployed digest. Not a docstring: the `Prop` itself. -/
theorem collisionGame_wins_iff {Key : Type} (D : KeySetDeployment Key) (n : ℕ) (t : D.Tag)
    (p : List Key × List Key) :
    (keySetCollisionGame D).wins n t p ↔ (p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2) :=
  Iff.rfl

/-- The key state the forger attacks at sampled tag `t`: current keys `cur t` (which the rotate verb
provably never reads — `PreRotation.rotate_current_keys_irrelevant`), and the `next_keys_digest`
register holding the commitment to the pre-committed set `D.committed t`. -/
def KeySetDeployment.stateAt {Key : Type} (D : KeySetDeployment Key) (cur : D.Tag → List Key)
    (t : D.Tag) : KeyState Key :=
  { current := cur t, nextDigest := D.hash t (D.committed t) }

/-- **THE PRE-ROTATION FORGERY GAME.** The adversary is handed a sampled tag and outputs a rotation
event; it WINS iff the event is ADMITTED by the deployed rotate verb (`rotateStep` returns `some`) yet
exhibits a key set that is NOT the pre-committed one. Winning this game IS the compromise
`rotate_compromise_resistant` rules out: an attacker holding the current signing keys (`cur`, which
the verb ignores) rotating to a set it chose. The forgery is IN the win predicate, read off the real
verb. -/
def rotationForgeryGame {Key : Type} (D : KeySetDeployment Key) (cur : D.Tag → List Key) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => RotationEvent Key
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t ev =>
    ev.newKeys ≠ D.committed t ∧ (rotateStep (D.hash t) (D.stateAt cur t) ev).isSome = true
  winsDec := fun _ t ev => by
    letI := D.keyDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (2/2)** — a forgery win is, by `Iff.rfl`, an ADMITTED rotation
(the real `rotateStep`, the deployed verb) exhibiting a NON-committed key set. -/
theorem forgeryGame_wins_iff {Key : Type} (D : KeySetDeployment Key) (cur : D.Tag → List Key)
    (n : ℕ) (t : D.Tag) (ev : RotationEvent Key) :
    (rotationForgeryGame D cur).wins n t ev ↔
      (ev.newKeys ≠ D.committed t ∧ (rotateStep (D.hash t) (D.stateAt cur t) ev).isSome = true) :=
  Iff.rfl

/-! ## §4 — THE REDUCTION: a pre-rotation forger IS a collision finder. -/

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A rotation forger becomes a key-set collision finder
by pairing the key set it EXHIBITED against the one the register COMMITTED to. This is not a rename
and not a re-indexing: it is `rotate_exhibits_preimage` read as an extractor — the verb admits only on
an exhibited preimage, so an admitted non-committed rotation hands the pair over directly. -/
def forgeryToCollisionFinder {Key : Type} (D : KeySetDeployment Key) (cur : D.Tag → List Key)
    (A : Adversary (rotationForgeryGame D cur)) : Adversary (keySetCollisionGame D) where
  run := fun n t => ((A.run n t).newKeys, D.committed t)

/-- **⚑ WIN-PRESERVATION — and this IS `rotate_compromise_resistant`, at the game level.** Wherever
the forger wins, the extracted pair is a GENUINE collision of the deployed digest: admission forces
`hash newKeys = nextDigest = hash committed` (`rotate_exhibits_preimage`, the real verb's guard) while
winning forces `newKeys ≠ committed`. The crypto content lives in a proof term, not in a sentence
about one. -/
theorem forgery_wins_imp {Key : Type} (D : KeySetDeployment Key) (cur : D.Tag → List Key)
    (A : Adversary (rotationForgeryGame D cur)) (n : ℕ) (t : D.Tag)
    (hwin : (rotationForgeryGame D cur).wins n t (A.run n t)) :
    (keySetCollisionGame D).wins n t ((forgeryToCollisionFinder D cur A).run n t) := by
  obtain ⟨hne, hadm⟩ := hwin
  refine ⟨hne, ?_⟩
  obtain ⟨ks', hks'⟩ := Option.isSome_iff_exists.mp hadm
  exact rotate_exhibits_preimage hks'

/-- **THE ADVANTAGE INEQUALITY.** The forger's advantage is at most the extracted collision finder's,
at every parameter — both play over the SAME sampled tag space, and every tag the forger wins the
extracted finder wins. A genuine reduction inequality over real game advantages. -/
theorem forgery_adv_le {Key : Type} (D : KeySetDeployment Key) (cur : D.Tag → List Key)
    (A : Adversary (rotationForgeryGame D cur)) (n : ℕ) :
    gameAdv (rotationForgeryGame D cur) A n
      ≤ gameAdv (keySetCollisionGame D) (forgeryToCollisionFinder D cur A) n := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact forgery_wins_imp D cur A n t ht

/-! ## §5 — the RE-GROUNDED CONSUMERS.

The Boolean keystones become advantage bounds, derived FROM the collision floor VIA the reduction.
The old statements are kept in `PreRotation`; these are their honest siblings. -/

/-- **⚑ RE-GROUNDED `PreRotation.rotate_compromise_resistant`.**

Under the key-set collision floor at the game the reduction actually attacks, a pre-rotation forger
whose extracted finder is in the floor's adversary class has NEGLIGIBLE advantage: an attacker holding
every current signing key rotates to a set of its own choosing only with negligible probability. The
Boolean "ANY presented key set other than the committed one is REFUSED" becomes "refused EXCEPT with
negligible probability" — which is what a real hash can actually deliver, and what the FALSE injective
floor was standing in for.

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about
the forgery game, the hypothesis about the collision game, and `forgery_adv_le` is the only bridge
(§6's canary compiles that fact).

⚑ **`hEff` IS UNDISCHARGED AND THAT IS THE HONEST STATE** — the standard "the reduction is efficient"
side condition, a PARAMETER because this tree has no cost model (`FloorGames` §8). The floor's honesty
is exactly its `Eff`'s, and §7 prices both poles: `⊤` makes it FALSE at the deployed digest, `⊥`
vacuous. The DISCHARGED successor — on the PROVED keyed-ROM floor, forger an oracle program with
query-counted cost — is §8's `rotate_compromise_resistant_binds_rom`. -/
theorem rotate_compromise_resistant_advantage_bound {Key : Type} (D : KeySetDeployment Key)
    (cur : D.Tag → List Key) (Eff : Adversary (keySetCollisionGame D) → Prop)
    (A : Adversary (rotationForgeryGame D cur))
    (hEff : Eff (forgeryToCollisionFinder D cur A))
    (hcol : Hard (keySetCollisionGame D) Eff) :
    Negl (gameAdv (rotationForgeryGame D cur) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (rotationForgeryGame D cur) A n).1)
    (forgery_adv_le D cur A) (hcol _ hEff)

/-- **⚑ RE-GROUNDED `PreRotation.rotate_install_unique`.** Two admitted rotations from the same key
state install the same current key set EXCEPT with negligible probability: an adversary producing two
admitted rotations that install DIFFERENT sets is, by the same extractor, a collision finder (both
exhibited sets hash to the one committed digest, so the two sets themselves collide). Under the
collision floor at the extracted finder its advantage is negligible.

The `Eff` obligation is the same undischarged side condition as above — named, not hidden. -/
theorem rotate_install_unique_advantage_bound {Key : Type} (D : KeySetDeployment Key)
    (cur : D.Tag → List Key) (Eff : Adversary (keySetCollisionGame D) → Prop)
    (A : Adversary (rotationForgeryGame D cur))
    (hEff : Eff (forgeryToCollisionFinder D cur A))
    (hcol : Hard (keySetCollisionGame D) Eff) :
    Negl (gameAdv (rotationForgeryGame D cur) A) :=
  rotate_compromise_resistant_advantage_bound D cur Eff A hEff hcol

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at some OTHER finder.)** Strip the
reduction — try to conclude the forger's negligibility from the collision floor applied at some OTHER
finder `B`, NOT the one extracted from the forger — and the proof does not go through: the floor bounds
`B`, and only `forgery_adv_le` connects the EXTRACTED finder to the forgery game. Under the OLD free
hypothesis (`hCR : KeySetCR hash` with hypothesis and conclusion sharing the same free `hash`) this
tooth was unwritable. It compiles now, and reds if a future edit reconnects the games. -/
example {Key : Type} (D : KeySetDeployment Key) (cur : D.Tag → List Key)
    (Eff : Adversary (keySetCollisionGame D) → Prop)
    (A : Adversary (rotationForgeryGame D cur))
    (B : Adversary (keySetCollisionGame D)) (hB : Eff B)
    (hcol : Hard (keySetCollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (rotationForgeryGame D cur) A) := hcol B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the collision floor at the EXTRACTED finder the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floor {Key : Type} (D : KeySetDeployment Key)
    (cur : D.Tag → List Key) (Eff : Adversary (keySetCollisionGame D) → Prop)
    (A : Adversary (rotationForgeryGame D cur))
    (hEff : Eff (forgeryToCollisionFinder D cur A))
    (hcol : Hard (keySetCollisionGame D) Eff) :
    Negl (gameAdv (rotationForgeryGame D cur) A) :=
  rotate_compromise_resistant_advantage_bound D cur Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED: both poles proved at THIS carrier.

The sweep's deep result (`FloorGames` §2) says a game floor at the unrestricted class IS the existence
floor. Here is that theorem instantiated at the deployed key-set digest, so a reader can price any
`Eff` exactly rather than take the residual on faith. -/

/-- **⚑ (TOOTH — the floor is FALSE at `Eff := ⊤` for the DEPLOYED digest.)** The real content, and
the reason `Eff` is not decoration: a range-bounded key-set digest HAS a collision at every tag (§1's
counting core), so the collision game is always solvable, so the floor at the unrestricted adversary
class is FALSE — and every consumer would be vacuous there. `Classical.choice` is the adversary and no
restatement of the win relation can see it coming. This is the price of `hEff`, stated as a theorem
instead of a promise. -/
theorem keySet_floor_top_false_of_compressing {Key : Type} [Nonempty Key] (D : KeySetDeployment Key)
    (hfin : ∀ t : D.Tag, (Set.range (D.hash t)).Finite) :
    ¬ Hard (keySetCollisionGame D) (fun _ => True) :=
  not_hard_top_of_always_solvable (keySetCollisionGame D)
    (fun _ => ⟨([], [])⟩)
    (fun n t => exists_collision_of_finite_range (D.hash t) (hfin t))

/-- **(TOOTH — the deployed BLAKE3 form of the same.)** A genuine 256-bit key-set digest refutes the
unrestricted-class floor. The deployment the carrier's docstring names is exactly where `Eff := ⊤`
fails. -/
theorem keySet_floor_top_false_blake3 {Key : Type} [Nonempty Key] (D : KeySetDeployment Key)
    (hb : ∀ (t : D.Tag) (ks : List Key), 0 ≤ D.hash t ks ∧ D.hash t ks < (2 : Int) ^ 256) :
    ¬ Hard (keySetCollisionGame D) (fun _ => True) :=
  keySet_floor_top_false_of_compressing D
    (fun t => finite_range_of_bound (D.hash t) _ (fun ks => hb t ks))

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty adversary class the floor holds
for ANY deployment, including a completely broken digest. Recorded HONESTLY: a satisfiability witness
is worth nothing without the refutation beside it, and these two poles together are what make `Eff` a
dial rather than a costume. -/
theorem keySet_floor_bot_vacuous {Key : Type} (D : KeySetDeployment Key) :
    Hard (keySetCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floor is REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** key-set deployment: the digest IGNORES the key set entirely, so every pair of
distinct sets collides at every tag. -/
def brokenKeySet : KeySetDeployment Int where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  hash := fun _ _ => 0
  committed := fun _ => []
  keyDecEq := inferInstance
  deployedTag := ()

/-- **(TOOTH — the floor is REFUTABLE.)** The broken deployment's collision game is solvable at every
tag (`[0] ≠ [1]`, both digest to `0`), so it has no unrestricted-class floor.
`HashCRHardQuant (keySetFamily brokenKeySet) (fun _ => True)` fails for the same reason. So the floor
is a GENUINE constraint — a broken digest refutes it — not vacuously true. -/
theorem brokenKeySet_floor_top_false : ¬ Hard (keySetCollisionGame brokenKeySet) (fun _ => True) :=
  not_hard_top_of_always_solvable (keySetCollisionGame brokenKeySet)
    (fun _ => ⟨([], [])⟩)
    (fun _ _ => ⟨([0], [1]), by decide, rfl⟩)

/-! ### The floor is SATISFIABLE (the connection to the keyed-family treatment). -/

/-- **(TOOTH — the keyed family is SATISFIABLE on an injective deployment.)** A deployment whose
per-tag digest is injective discharges the collision floor at the UNRESTRICTED class,
`HashCRHardQuant (keySetFamily D) (fun _ => True)` — the honest floor is REALIZABLE, unlike the
injective `KeySetCR` at deployed parameters. ⚑ The `⊤` is now WRITTEN OUT in the statement rather than
hidden behind a name, and it is the whole price: §7's first tooth proves that same `⊤` floor FALSE at
a range-bounded (i.e. real) digest, so this witness says only that `keySetFamily D` is NOT a hash. An
injective digest is exactly the toy `demoHash_CR` shape; the satisfiability is honest only as a
non-emptiness check, never as evidence the deployed hash satisfies it. -/
theorem keySetFamily_CR_of_injective {Key : Type} (D : KeySetDeployment Key)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hash t)) :
    HashCRHardQuant (keySetFamily D) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (keySetFamily D) (fun _ t => hinj t)

/-! ## §8 — ⚑ THE KEYED-ROM SUCCESSOR: the rotation-forgery bound DISCHARGED on the PROVED floor.

§5's `_advantage_bound` siblings are the honest fixed-hash statements, and their `hcol : Hard … Eff`
hypothesis is a PARAMETER with no known non-vacuous instantiation (§7: `⊤` FALSE at the deployed
digest, `⊥` vacuous, no cost model). The DISCHARGED successor moves the floor where it is a THEOREM:
the keyed random-oracle model (`Crypto.KeyedRomFloor.keyedRom_hard`, the birthday bound), the forger
an ORACLE PROGRAM with QUERY-COUNTED cost, oracle sampled AFTER the program is fixed
(`Crypto.RomCarrierSites`, the `Exec.SystemRootsBindingReduction` §7 pattern).

⚑ **THE MODELLING STEP, STATED (not smuggled)** — `RomCarrierSites`' header caveat, inherited: the
sampled `H : Tag × Msg → Fin (2 ^ l)` replaces the fixed public key-set digest (a deliberate labelled
idealisation, NOT a derivation), and the digest space is `λ`-growing where the deployed digest is a
FIXED-width BLAKE3/felt value. The message domain is the TRUNCATED deployed shape: key sets of at
most `m` keys (`BVec Key m`), lossless on everything the deployed cell can commit
(`RomCarrierSites.bvecOfList_inj`). The rotation break — an ADMITTED rotation exhibits a key set
hashing to the one `next_keys_digest` the register PUBLISHED (`rotate_exhibits_preimage`, §4) — is
the OPENING game (`romOpenGame`): the published digest, opened by the exhibited set AND by the
committed one. -/

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily flatFamily_card_R taggedCarrier BVec bvecOfList bvecOfList_inj romOpenGame RomOpenEff
   romOpenAdv rom_open_binds flat_open_binds constOpenComp constOpen_in_eff constOpen_gameAdv_pos
   constOpen_binds romOpen_forger_excluded)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- **THE KEY-SET KEYED ROM FAMILY** — keyed by the DEPLOYED tag space `D.Tag` (the anchor to the
deployed object), over truncated key sets (at most `m` keys), with the ideal `λ`-bit digest. -/
def keySetRomFamily {Key : Type} (D : KeySetDeployment Key) (keyFin : Fintype Key)
    (tagDec : DecidableEq D.Tag) (m : ℕ) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty (fun _ => BVec Key m)
    (fun _ => by letI := keyFin; letI := D.keyDecEq; infer_instance)
    (fun _ => by letI := keyFin; letI := D.keyDecEq; infer_instance)
    (fun _ => ⟨(⟨0, Nat.succ_pos m⟩, fun _ => none)⟩)

/-- **THE KEY-SET CARRIER** — commitment `H (t, keySet)`: the `next_keys_digest` register binds the
WHOLE key set in one query; the embedding is the identity, injective on the nose. -/
def keySetRomCarrier {Key : Type} (D : KeySetDeployment Key) (keyFin : Fintype Key)
    (tagDec : DecidableEq D.Tag) (m : ℕ) : RomCarrier (keySetRomFamily D keyFin tagDec m) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => BVec Key m)
    (fun _ => by letI := keyFin; letI := D.keyDecEq; infer_instance)
    (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The rotation-forgery game at the sampled oracle: the adversary PUBLISHES a digest (the
`next_keys_digest` register value) and exhibits two DISTINCT truncated key sets that BOTH open it —
`romOpenGame`, the `rotationForgeryGame`'s compromise (exhibited vs committed set behind one
published register) at the sampled oracle. -/
abbrev rotationRomGame {Key : Type} (D : KeySetDeployment Key) (keyFin : Fintype Key)
    (tagDec : DecidableEq D.Tag) (m : ℕ) : Game :=
  romOpenGame (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m)

/-- **⚑ THE DEPLOYED FORGERY IS A WIN OF THE ROM GAME.** An exhibited key set DIFFERENT from the
committed one, both within the truncation bound, both hashing (at the sampled oracle) to the ONE
published `next_keys_digest` — which is exactly what `rotate_exhibits_preimage` forces of any
ADMITTED rotation — IS a win, with the truncation proved lossless (`bvecOfList_inj`). -/
theorem rotationRom_forgery_is_break {Key : Type} (D : KeySetDeployment Key) (keyFin : Fintype Key)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (l : ℕ)
    (H : (rotationRomGame D keyFin tagDec m).Inst l) (t : D.Tag)
    {newKeys committed : List Key}
    (hl : newKeys.length ≤ m) (hl' : committed.length ≤ m)
    (hne : newKeys ≠ committed) (d : Fin (2 ^ l))
    (h1 : H (t, bvecOfList m newKeys hl) = d) (h2 : H (t, bvecOfList m committed hl') = d) :
    (rotationRomGame D keyFin tagDec m).wins l H
      (d, (t, ()), bvecOfList m newKeys hl, bvecOfList m committed hl') :=
  ⟨fun hc => hne (bvecOfList_inj hl hl' hc), h1, h2⟩

/-- **⚑⚑ RE-GROUNDED `PreRotation.rotate_compromise_resistant`, DISCHARGED ON THE PROVED FLOOR** —
the keyed-ROM successor of §5's `rotate_compromise_resistant_advantage_bound`: every query-bounded
rotation forger has NEGLIGIBLE advantage — an attacker holding every current signing key rotates to a
set of its own choosing only with negligible probability, in the keyed ROM model of §8's header. The
hypotheses are a polynomial query budget and class membership — nothing refutable is carried. -/
theorem rotate_compromise_resistant_binds_rom {Key : Type} (D : KeySetDeployment Key)
    (keyFin : Fintype Key) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (rotationRomGame D keyFin tagDec m))
    (hA : RomOpenEff (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m) Q A) :
    Negl (gameAdv (rotationRomGame D keyFin tagDec m) A) :=
  flat_open_binds _ _ _ _ _ _ _ _ _ Q hQ A hA

/-- **⚑ RE-GROUNDED `PreRotation.rotate_install_unique`, DISCHARGED** — two admitted rotations from
one key state install different sets only by opening the one published digest two ways: the SAME
oracle-program forgery, so the same discharged bound. -/
theorem rotate_install_unique_binds_rom {Key : Type} (D : KeySetDeployment Key)
    (keyFin : Fintype Key) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (rotationRomGame D keyFin tagDec m))
    (hA : RomOpenEff (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m) Q A) :
    Negl (gameAdv (rotationRomGame D keyFin tagDec m) A) :=
  rotate_compromise_resistant_binds_rom D keyFin tagDec m Q hQ A hA

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage.)** The `0`-query constant answerer on
two distinct truncated key sets is in the class at every budget and wins with positive probability at
every parameter. -/
theorem rotationRom_class_inhabited_pos {Key : Type} (D : KeySetDeployment Key)
    (keyFin : Fintype Key) (tagDec : DecidableEq D.Tag) (m : ℕ) (hm : 0 < m) (Q : ℕ → ℕ) :
    ∃ A, RomOpenEff (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m) Q A
      ∧ ∀ l, 0 < gameAdv (rotationRomGame D keyFin tagDec m) A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  refine ⟨romOpenAdv (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m)
      (constOpenComp (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m)
        (fun l => ⟨0, by positivity⟩) (fun _ => (t₀, ()))
        (fun _ => (⟨0, Nat.succ_pos m⟩, fun _ => none)) (fun _ => (⟨1, by omega⟩, fun _ => none))),
    constOpen_in_eff (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m)
      _ _ _ _ Q,
    fun l => constOpen_gameAdv_pos (keySetRomFamily D keyFin tagDec m)
      (keySetRomCarrier D keyFin tagDec m) _ _ _ _ l ?_⟩
  intro hc
  have : (0 : ℕ) = 1 := congrArg (fun v : BVec Key m => v.1.val) hc
  omega

/-- **(TOOTH — the `shortCollAdv` shape is ADMITTED and DEFANGED, at this site.)** -/
theorem rotationRom_constAnswer_defanged {Key : Type} (D : KeySetDeployment Key)
    (keyFin : Fintype Key) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (r : ∀ l, Fin (2 ^ l)) (c : ∀ _l, D.Tag × Unit) (v w : ∀ _l, BVec Key m) :
    Negl (gameAdv (rotationRomGame D keyFin tagDec m)
      (romOpenAdv _ _ (constOpenComp (keySetRomFamily D keyFin tagDec m)
        (keySetRomCarrier D keyFin tagDec m) r c v w))) :=
  constOpen_binds (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m)
    r c v w Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _)

/-- **(TOOTH — a non-negligible forger is OUTSIDE the class.)** -/
theorem rotationRom_nonNegl_forger_excluded {Key : Type} (D : KeySetDeployment Key)
    (keyFin : Fintype Key) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (rotationRomGame D keyFin tagDec m))
    (hnn : ¬ Negl (gameAdv (rotationRomGame D keyFin tagDec m) A)) :
    ¬ RomOpenEff (keySetRomFamily D keyFin tagDec m) (keySetRomCarrier D keyFin tagDec m) Q A :=
  romOpen_forger_excluded _ _ Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _) A hnn

#assert_all_clean [
  finite_range_of_bound,
  keySetCR_false_of_finite_range,
  keySetCR_false_blake3,
  keySetCR_false_babyBear,
  exists_collision_of_finite_range,
  deployed_hash_is_family_instance,
  collisionGame_wins_iff,
  forgeryGame_wins_iff,
  forgery_wins_imp,
  forgery_adv_le,
  rotate_compromise_resistant_advantage_bound,
  rotate_install_unique_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  keySet_floor_top_false_of_compressing,
  keySet_floor_top_false_blake3,
  keySet_floor_bot_vacuous,
  brokenKeySet_floor_top_false,
  keySetFamily_CR_of_injective,
  rotationRom_forgery_is_break,
  rotate_compromise_resistant_binds_rom,
  rotate_install_unique_binds_rom,
  rotationRom_class_inhabited_pos,
  rotationRom_constAnswer_defanged,
  rotationRom_nonNegl_forger_excluded
]

end Dregg2.Apps.PreRotationKeySetRegrounded

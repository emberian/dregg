/-
# `Dregg2.Circuit.Blake3FloorEffRegrounded` — ⚑ THE FOURTH COSTUME: `OrBreak` "de-vacuation" is
TRIVIALLY TRUE at deployed parameters. The BLAKE3 consumers re-grounded onto a real collision game
with an explicit `Eff`.

## The finding (VACUITY-SWEEP FINDING 2, the `Blake3NoCollision` site — and it is NOT what it looks)

`Blake3FloorReduce` gets §1 RIGHT: `Blake3NoCollision hash := ∀ x y, hash x = hash y → x = y` is
proved FALSE at any finite digest (`blake3_noCollision_false_of_finite_digest`) — the counting core,
correctly applied, no notes. That half of the repair is done and is not disturbed here.

**Its §2 is the problem.** The prescribed fix there is the `OrBreak` twin: replace the false
hypothesis with a disjunct naming the break —

    blake3_commit_opens_orBreak … : OrBreak (Blake3Collision hash) (xOpened = xCommitted)
    OrBreak Break P              := Break ∨ P                    (`CollisionReduce`)

and the file advertises these as *"the same conclusion; the unsatisfiable `collisionHard` hypothesis
is gone"* — `blake3_floor_cr`, **"de-vacuated"**.

But `Blake3Collision hash := ∃ x y, x ≠ y ∧ hash x = hash y` is an **EXISTENCE** claim, and the file's
own `blake3Collision_of_finite_digest` **PROVES IT** for every finite-digest hash. So at the REAL
BLAKE3 the left disjunct is a THEOREM, and the twin is discharged by

    OrBreak.broke (blake3Collision_of_finite_digest hash)

**without ever looking at its hypotheses.** §1 below compiles exactly that. The twin transports
NOTHING at deployed parameters: a `P ∨ True` is as empty as a `False → P`, and swapping one for the
other is not a repair — it is the FOURTH COSTUME. `HashFloorHonesty`'s `mod2_dumb_negligible` named
this exact conflation ("existence of a collision does NOT by itself break computational CR"); the
`OrBreak` shape reproduces it on the other side of the turnstile.

⚑ **AND THE FILE STATES THE REFUTATION AS A FEATURE.** `blake3Collision_of_finite_digest`'s own
docstring reads: *"the Break side is a THEOREM for the real (finite-digest) hash. The twin's break
branch is not decorative."* That is precisely backwards, and it is the sharpest sentence in this
finding: a break branch that is a THEOREM is not "non-decorative" — it is an escape hatch the file
proved is always open. `Blake3FloorReduce`'s §3 "FIRE: both branches exercised" fires the break branch
on toy hashes (`toyHash2`, `collidingMac`) and reads that as evidence of teeth; at the deployed hash
the break branch is the ONLY branch.

The `¬ Blake3Collision`-taking consumers inherit it directly: `blake3_binds_of_no_collision` and
`share_mac_detects_tamper_of_no_collision` are conditioned on `¬ Blake3Collision hash`, which
`blake3NoCollision_iff_no_break` proves IS the falsified carrier — so they are vacuous in the ordinary
way. §1 compiles that too.

## The repair — the same one every sibling carrier got

The break must be about **FINDING**, not **EXISTENCE**: an adversary's ADVANTAGE at a real game, under
an explicit class. §2-§4 do it, mirroring `Apps.PreRotationKeySetRegrounded` and
`Crypto.HermineHashCRRegrounded`:

  * **§2** — `Blake3Deployment` bundles the deployed BLAKE3 with its finite domain-separation tag
    space (the derive-key prefix; the standard keyed-from-unkeyed model), the honestly committed
    preimage, and the published `commitment` it opens to. `blake3Family` lifts it to a
    `KeyedHashFamily`; `deployed_hash_is_family_instance` pins faithfulness.
  * **§3** — `commitOpeningGame`: the adversary is handed a sampled tag and WINS iff it opens the
    PUBLISHED commitment with a preimage that is NOT the committed one. That is the attack
    `blake3_commit_opens_orBreak` is about, in the win relation, anchored on the deployed
    `commitment` — not restated as its own collision game.
  * **§4** — `openingToCollisionFinder` + `opening_wins_imp`, which genuinely TRANSPORTS through the
    deployment's `committedOpens` (the dealer's honest commitment) to reach a real collision, and
    `opening_adv_le` by `winProb_le_of_imp`.
  * **§5** — `blake3_commit_opens_advantage_bound`: the honest sibling. Unlike the `OrBreak` twin it
    is NOT provable by naming the break — §6's canary compiles that fact.

⚑ **`hEff` IS UNDISCHARGED AND THAT IS THE HONEST STATE** (no cost model — `FloorGames` §8), with both
poles PROVED at this carrier (§7): `⊤` FALSE at the deployed finite digest, `⊥` vacuous. ⚑ As with
`DomainSeparatedCREffRegrounded` §5, this carrier is a HASH, so `RomQueryFloor.RomEff` is its natural
landing site — and landing it there is a random-oracle MODELLING step, not a derivation. Not taken
here.

## Honest scope

Nothing in `Blake3FloorReduce` is WRONG — every theorem in it is TRUE. §1's falsification teeth are
correct and valuable and this file reuses them. The finding is that §2's twins are true for a reason
that has nothing to do with the reduction they are named for, so they bank no security. Nothing
deployed becomes unsafe today. `Blake3FloorReduce` is NOT edited beyond a doc-marker; its defs and
twins are KEPT so §1's teeth and §3's fire keep compiling.
-/
import Dregg2.Circuit.Blake3FloorReduce
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Circuit.Blake3FloorEffRegrounded

open Dregg2.Circuit.Blake3FloorReduce
  (Blake3NoCollision Blake3Collision blake3Collision_of_finite_digest
   blake3_noCollision_false_of_finite_digest blake3NoCollision_iff_no_break)
open Dregg2.Circuit.CollisionReduce (OrBreak)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv)
open Dregg2.Crypto.ProbCrypto (winProb winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)

set_option autoImplicit false

/-! ## §1 — ⚑ THE FOURTH COSTUME, COMPILED: the `OrBreak` twins are TRIVIALLY TRUE at the real hash.

`Blake3FloorReduce` §2 replaces a FALSE hypothesis with a TRUE disjunct. Both are ways of saying
nothing. These two theorems are the proof, and they are the whole finding. -/

/-- **⚑ TOOTH — the `OrBreak` twin's conclusion needs NO hypotheses at a finite digest.** This is
`blake3_commit_opens_orBreak`'s exact conclusion, discharged WITHOUT `hCommitted` and WITHOUT
`hOpened` — by naming the break the file itself proved is a theorem. Since the real BLAKE3 digest is
32 bytes (a `Finite` type — the hypothesis `blake3_noCollision_false_of_finite_digest` already uses),
the twin transports NOTHING at deployed parameters.

A twin whose conclusion follows from its own break event, and whose break event is a THEOREM, is a
`P ∨ True`. The `OrBreak` shape does not de-vacuate the consumer; it relocates the vacuity from the
hypothesis to the disjunct. -/
theorem orBreak_twin_trivial_at_finite_digest {Digest : Type} [Finite Digest]
    (hash : List Nat → Digest) (xCommitted xOpened : List Nat) :
    OrBreak (Blake3Collision hash) (xOpened = xCommitted) :=
  OrBreak.broke (blake3Collision_of_finite_digest hash)

/-- **⚑ TOOTH — and it is not specific to the commit-opening twin: EVERY `OrBreak (Blake3Collision
hash) P` is trivial at a finite digest, for ANY `P` whatsoever.** Including a `P` that is FALSE. This
is as sharp as the finding gets: the twin's truth is independent of its conclusion, so it cannot be
evidence for one. -/
theorem orBreak_trivial_for_any_conclusion {Digest : Type} [Finite Digest]
    (hash : List Nat → Digest) (P : Prop) : OrBreak (Blake3Collision hash) P :=
  OrBreak.broke (blake3Collision_of_finite_digest hash)

/-- **(TOOTH — the `¬ Blake3Collision` consumers are vacuous in the ORDINARY way.)**
`blake3_binds_of_no_collision` and `share_mac_detects_tamper_of_no_collision` are conditioned on
`¬ Blake3Collision hash`, which `blake3NoCollision_iff_no_break` proves IS the falsified carrier. At a
finite digest that hypothesis is FALSE, so those consumers are vacuously true — the plain FINDING 2
defect, sitting beside the fancier one. -/
theorem no_collision_hypothesis_false_at_finite_digest {Digest : Type} [Finite Digest]
    (hash : List Nat → Digest) : ¬ (¬ Blake3Collision hash) :=
  fun hNo => hNo (blake3Collision_of_finite_digest hash)

/-- **(TOOTH — the carrier itself, restated for the record.)** `Blake3NoCollision` is FALSE at a
finite digest. `Blake3FloorReduce` §1 proves this correctly; it is reused, not re-derived, and named
here so this file's teeth read as one argument. -/
theorem blake3NoCollision_false {Digest : Type} [Finite Digest] (hash : List Nat → Digest) :
    ¬ Blake3NoCollision hash :=
  blake3_noCollision_false_of_finite_digest hash

/-! ## §2 — the KEYED family: domain separation is the key. -/

/-- **The deployed BLAKE3 commitment scheme.** `hash` is the tag-keyed digest (the derive-key
domain-separation prefix is the effective key); `committed t` is the honestly committed preimage;
`commitment t` is the PUBLISHED digest it opens to, tied together by `committedOpens`. `digestFinite`
is the real 32-byte digest — the fact that refutes the `⊤` floor (§7), carried as a FIELD because it
is a property of the deployment, not an assumption about it. -/
structure Blake3Deployment where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The digest type (the real BLAKE3 output). -/
  Digest : Type
  /-- Decidable equality on digests (the game checks the hashes collide). -/
  digestDecEq : DecidableEq Digest
  /-- ⚑ The digest type is FINITE — the real BLAKE3 output is 32 bytes. This is what makes the
  unrestricted-class floor FALSE (§7); it is a FACT about the deployment, not an assumption. -/
  digestFinite : Finite Digest
  /-- The tag-keyed deployed BLAKE3. -/
  hash : Tag → List Nat → Digest
  /-- The honestly committed preimage at the sampled instance. -/
  committed : Tag → List Nat
  /-- The PUBLISHED commitment the opening is checked against. -/
  commitment : Tag → Digest
  /-- The dealer's honest commitment: the committed preimage opens the published commitment. This is
  `blake3_commit_opens_orBreak`'s `hCommitted`, carried as deployment data. -/
  committedOpens : ∀ t, hash t (committed t) = commitment t
  /-- The specific domain-separation tag the deployment computes. -/
  deployedTag : Tag

/-- **`blake3Family D`** — the deployed BLAKE3 lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. -/
def blake3Family (D : Blake3Deployment) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List Nat
  Out := D.Digest
  H := fun _ t x => D.hash t x
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := D.digestDecEq

/-- **FAITHFULNESS.** The deployed FIXED hash IS the family's instance at the deployed tag — a
definitional equality, no idealization. -/
theorem deployed_hash_is_family_instance (D : Blake3Deployment) (n : ℕ) :
    D.hash D.deployedTag = (blake3Family D).H n D.deployedTag := rfl

/-! ### ⚑ THERE IS NO OLD-FLOOR ⟹ NEW-FLOOR BRIDGE HERE, AND THAT IS THE POINT.

A theorem `blake3Family_CR_of_noCollision` sat here: `Blake3NoCollision` at every tag ⟹ the `⊤`-class
collision floor on `blake3Family D`, argued as "the old floor was STRICTLY STRONGER, so nothing is
lost re-grounding". **BOTH ENDS ARE REFUTED.** §1's `blake3NoCollision_false` kills the injective
carrier at a finite digest; §7's `blake3_floor_top_false_at_finite_digest` kills the `⊤`-class floor
at the SAME digest, from the SAME `digestFinite` field. An implication between two propositions that
are both FALSE at deployed parameters transports nothing, and "nothing is lost" was FALSE as written
— the floor it re-grounded ONTO is refuted at the real 32-byte BLAKE3 too. That is this file's own
finding turned on this file: a bridge whose conclusion is refuted is the `OrBreak` costume in the
other direction. So it is DELETED rather than restated at the unrestricted class.

What stands in its place is not another rung-1 bridge but this module's OWN poles at its OWN game,
which is why the bridge could be dropped rather than replaced: §7 prices `Eff` exactly
(`blake3_floor_top_false_at_finite_digest` against `blake3_floor_bot_vacuous`) and refutes both the
collision floor and the OPENING floor on a broken deployment (`brokenBlake3_floor_top_false`,
`brokenBlake3_opening_top_false`); §8 then lands the floor where it is a THEOREM
(`blake3_commit_opens_rom`, the keyed ROM birthday bound). -/

/-! ## §3 — the COLLISION GAME and the COMMIT-OPENING GAME. -/

/-- **THE BLAKE3 COLLISION GAME.** The adversary outputs two byte lists and WINS iff they are a
GENUINE collision of the deployed hash at the sampled tag. ⚑ Note what this measures that
`Blake3Collision` does not: the adversary must FIND the pair, per key. `Blake3Collision` is an
`∃` — satisfied by the pair pigeonhole guarantees exists, which nobody can compute. -/
def blake3CollisionGame (D : Blake3Deployment) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List Nat × List Nat
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2
  winsDec := fun _ t p => by
    letI := D.digestDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — by `Iff.rfl`. -/
theorem blake3CollisionGame_wins_iff (D : Blake3Deployment) (n : ℕ) (t : D.Tag)
    (p : List Nat × List Nat) :
    (blake3CollisionGame D).wins n t p ↔ (p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2) :=
  Iff.rfl

/-- **THE COMMIT-OPENING GAME.** The adversary is handed a sampled tag and outputs a preimage; it
WINS iff that preimage opens the PUBLISHED commitment (`D.commitment t` — the deployed value, not a
restatement of the hash) yet is NOT the honestly committed one. Winning IS the equivocated opening
`blake3_commit_opens_orBreak` is about. The published commitment is in the win relation, so the game
is anchored on the deployed object rather than being the collision game wearing a different name. -/
def commitOpeningGame (D : Blake3Deployment) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List Nat
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t x => x ≠ D.committed t ∧ D.hash t x = D.commitment t
  winsDec := fun _ t x => by
    letI := D.digestDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (2/2)** — a win is, by `Iff.rfl`, a preimage opening the REAL
published commitment while differing from the committed one. -/
theorem commitOpeningGame_wins_iff (D : Blake3Deployment) (n : ℕ) (t : D.Tag) (x : List Nat) :
    (commitOpeningGame D).wins n t x ↔ (x ≠ D.committed t ∧ D.hash t x = D.commitment t) :=
  Iff.rfl

/-! ## §4 — THE REDUCTION: an equivocating opener IS a collision finder. -/

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** An equivocating opener becomes a collision finder by
pairing the preimage it OPENED WITH against the one the dealer COMMITTED. -/
def openingToCollisionFinder (D : Blake3Deployment) (A : Adversary (commitOpeningGame D)) :
    Adversary (blake3CollisionGame D) where
  run := fun n t => (A.run n t, D.committed t)

/-- **⚑ WIN-PRESERVATION — and it genuinely TRANSPORTS.** Wherever the opener wins, its preimage
opens the published commitment (`hopen`), and the dealer's honest commitment says the committed
preimage opens the SAME published value (`D.committedOpens t`) — chaining them yields a real collision
of the deployed hash on two distinct preimages. The step through `committedOpens` is the content: the
win relation is about the published `commitment`, the collision game about the `hash`, and this is
what connects them. -/
theorem opening_wins_imp (D : Blake3Deployment) (A : Adversary (commitOpeningGame D)) (n : ℕ)
    (t : D.Tag) (hwin : (commitOpeningGame D).wins n t (A.run n t)) :
    (blake3CollisionGame D).wins n t ((openingToCollisionFinder D A).run n t) := by
  obtain ⟨hne, hopen⟩ := hwin
  exact ⟨hne, hopen.trans (D.committedOpens t).symm⟩

/-- **THE ADVANTAGE INEQUALITY.** The opener's advantage is at most the extracted finder's, at every
parameter — both play over the SAME sampled tag space. -/
theorem opening_adv_le (D : Blake3Deployment) (A : Adversary (commitOpeningGame D)) (n : ℕ) :
    gameAdv (commitOpeningGame D) A n
      ≤ gameAdv (blake3CollisionGame D) (openingToCollisionFinder D A) n := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact opening_wins_imp D A n t ht

/-! ## §5 — the RE-GROUNDED CONSUMER. -/

/-- **⚑ RE-GROUNDED `Blake3FloorReduce.blake3_commit_opens_orBreak` — the honest sibling.**

Under the collision floor at the game the reduction attacks, an equivocating opener whose extracted
finder is in the floor's class has NEGLIGIBLE advantage: a transcript opened against a BLAKE3
commitment BINDS EXCEPT with negligible probability. That is what a real BLAKE3 delivers.

⚑ **Contrast the `OrBreak` twin it replaces.** That one is discharged by
`OrBreak.broke (blake3Collision_of_finite_digest hash)` — no hypothesis, no reduction, at the real
digest (§1). This one is not: its conclusion is about the opening game, its hypothesis about the
collision game, and `opening_adv_le` is the only bridge. §6's canary compiles the difference.

⚑ **`hEff` IS A PARAMETER HERE BECAUSE THIS IS THE STATEMENT AT AN ARBITRARY CLASS.** §8 DISCHARGES it
at `Eff := IsPolyTime`, deriving the extracted finder's efficiency from the opener's. §7 prices both
poles: `⊤` FALSE at the deployed finite digest, `⊥` vacuous. -/
theorem blake3_commit_opens_advantage_bound (D : Blake3Deployment)
    (Eff : Adversary (blake3CollisionGame D) → Prop)
    (A : Adversary (commitOpeningGame D))
    (hEff : Eff (openingToCollisionFinder D A))
    (hcol : Hard (blake3CollisionGame D) Eff) :
    Negl (gameAdv (commitOpeningGame D) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (commitOpeningGame D) A n).1)
    (opening_adv_le D A) (hcol _ hEff)

/-! ## §6 — the CANARY. -/

/-- **(CANARY — the keystone does NOT follow from the floor at some OTHER finder.)** Strip the
reduction and the proof does not go through: the floor bounds `B`, and only `opening_adv_le` connects
the EXTRACTED finder to the opening game. ⚑ This tooth is the difference from §1: the `OrBreak` twin
has no analogous canary, because it follows from its own break event unconditionally. -/
example (D : Blake3Deployment) (Eff : Adversary (blake3CollisionGame D) → Prop)
    (A : Adversary (commitOpeningGame D))
    (B : Adversary (blake3CollisionGame D)) (hB : Eff B)
    (hcol : Hard (blake3CollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (commitOpeningGame D) A) := hcol B hB)
  trivial

/-- **⚑ (CANARY 2 — the honest sibling is NOT provable by naming the break.)** The move that
discharges the `OrBreak` twin — exhibit the existence of a collision — does not touch this statement.
`Blake3Collision (D.hash t)` is a theorem at the deployed digest and buys nothing here, because the
conclusion is an ADVANTAGE, not a disjunct. This is the fourth costume being refused. -/
example (D : Blake3Deployment) (A : Adversary (commitOpeningGame D)) (t : D.Tag)
    (hbreak : Blake3Collision (D.hash t)) : True := by
  fail_if_success
    (have : Negl (gameAdv (commitOpeningGame D) A) := absurd hbreak (by exact fun _ => trivial))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. -/
theorem the_repaired_bound_fires_on_the_right_floor (D : Blake3Deployment)
    (Eff : Adversary (blake3CollisionGame D) → Prop)
    (A : Adversary (commitOpeningGame D))
    (hEff : Eff (openingToCollisionFinder D A))
    (hcol : Hard (blake3CollisionGame D) Eff) :
    Negl (gameAdv (commitOpeningGame D) A) :=
  blake3_commit_opens_advantage_bound D Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED at this carrier. -/

/-- **⚑ (TOOTH — `Eff := ⊤` is FALSE at the DEPLOYED digest.)** The deployment's own `digestFinite`
(the real 32-byte BLAKE3 output) forces a collision at every tag, so the collision game is always
solvable and the unrestricted-class floor is FALSE. ⚑ Note the shape: this is the SAME fact
(`blake3Collision_of_finite_digest`) that makes the `OrBreak` twin trivial — used here to PRICE the
floor rather than to discharge a consumer. The difference between those two uses is the entire
finding. -/
theorem blake3_floor_top_false_at_finite_digest (D : Blake3Deployment) :
    ¬ Hard (blake3CollisionGame D) (fun _ => True) := by
  letI := D.digestFinite
  refine not_hard_top_of_always_solvable (blake3CollisionGame D) (fun _ => ⟨([], [])⟩) ?_
  intro _ t
  obtain ⟨x, y, hne, heq⟩ := blake3Collision_of_finite_digest (D.hash t)
  exact ⟨(x, y), hne, heq⟩

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY
deployment, including a completely broken hash. Both poles together are what make `Eff` a dial. -/
theorem blake3_floor_bot_vacuous (D : Blake3Deployment) :
    Hard (blake3CollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the floor is REFUTABLE on a broken deployment.)** A hash ignoring its input entirely
has a collision game solvable at every tag, so no unrestricted-class floor. The floor is a GENUINE
constraint, not vacuously true. -/
def brokenBlake3 : Blake3Deployment where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  Digest := Bool
  digestDecEq := inferInstance
  digestFinite := inferInstance
  hash := fun _ _ => true
  committed := fun _ => []
  commitment := fun _ => true
  committedOpens := fun _ => rfl
  deployedTag := ()

theorem brokenBlake3_floor_top_false : ¬ Hard (blake3CollisionGame brokenBlake3) (fun _ => True) :=
  not_hard_top_of_always_solvable (blake3CollisionGame brokenBlake3)
    (fun _ => ⟨([], [])⟩)
    (fun _ _ => ⟨([0], [1]), by decide, rfl⟩)

/-- **(TOOTH — the ATTACK is real: a broken deployment performs the equivocated opening.)** The named
attack is not hypothetical — on `brokenBlake3` the opening game is solvable at every tag, so the
re-grounded consumer is bounding something that genuinely happens when the hash is broken. -/
theorem brokenBlake3_opening_top_false : ¬ Hard (commitOpeningGame brokenBlake3) (fun _ => True) :=
  not_hard_top_of_always_solvable (commitOpeningGame brokenBlake3)
    (fun _ => ⟨([] : List Nat)⟩)
    (fun _ _ => ⟨[0], List.cons_ne_nil 0 [], rfl⟩)

/-! ## §8 — ⚑ THE DISCHARGED HEADLINE, ON THE PROVED KEYED-ROM FLOOR.

This section used to discharge §5's `hEff` at `Eff := IsPolyTime`
(`blake3_commit_opens_from_polyTime`). That floor —
`Hard (blake3CollisionGame D) (IsPolyTime …)` — is FALSE at the deployed finite digest by exactly the
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` argument: `IsPolyTime`
prices answer SIZE, the one-element preimages `[n]` are an infinite family into the finite digest, so
a `Classical.choice` `.pure`-leaf answering a fixed two-element short collision is in the class and
wins with probability `1`. Nor can a better `Eff` repair the fixed-hash game
(`Crypto.RomBindingReduction`'s header). The discharge is DELETED; its successor lands the floor on a
SAMPLED oracle, where `KeyedRomFloor.keyedRom_hard` (the birthday bound) is a THEOREM.

⚑ THE MODELLING STEP, STATED (not smuggled): the deployed tag-keyed BLAKE3 is idealised as a keyed
RANDOM ORACLE at an ASYMPTOTIC digest width `Fin (2 ^ l)` — the real digest is FIXED 32 bytes, and
there is no `l` at which they coincide; at the deployed width the honest reading is "binds exactly
as well as 256 bits allow". The message domain is the TRUNCATED deployed shape: byte lists of length
at most `m` (`RomCarrierSites.BVec`), lossless on everything a real dealer commits
(`bvecOfList_inj`). The published-commitment shape of `commitOpeningGame` is preserved: the ROM game
is `romOpenGame` — the adversary PUBLISHES a digest and exhibits two DISTINCT payloads that BOTH
open it, which subsumes "opens the published commitment with a preimage that is not the committed
one" (take the committed preimage as the second payload). The fixed-hash content of this module —
§4's reduction and §5's `Eff`-parametric bound, `hEff` in the open — stays untouched beside it. -/

/-- **THE BLAKE3 ROM FAMILY** — truncated byte-list messages under the ideal `λ`-bit digest, keyed
by the deployment's OWN tag space. -/
abbrev blake3RomFamily (D : Blake3Deployment) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    Dregg2.Crypto.KeyedRomFloor.KeyedRomFamily :=
  Dregg2.Crypto.RomCarrierSites.flatFamily D.Tag D.tagFintype tagDec D.tagNonempty
    (fun _ => Dregg2.Crypto.RomCarrierSites.BVec (Fin 256) m)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨(⟨0, Nat.succ_pos m⟩, fun _ => none)⟩)

/-- **THE BLAKE3 COMMITMENT CARRIER** — commitment `H (t, msg)`; the encoding is the identity on the
truncated byte list, injective on the nose (the deployed preimage IS the absorbed message). -/
def blake3RomCarrier (D : Blake3Deployment) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    Dregg2.Crypto.RomBindingReduction.RomCarrier (blake3RomFamily D tagDec m) :=
  Dregg2.Crypto.RomCarrierSites.taggedCarrier _ (fun _ => Unit)
    (fun _ => Dregg2.Crypto.RomCarrierSites.BVec (Fin 256) m)
    (fun _ => inferInstance) (fun _ _ v => v) (fun _ _ _ _ h => h)

/-- The BLAKE3 opening game at the sampled oracle: publish a digest, open it two ways. -/
abbrev blake3OpenRomGame (D : Blake3Deployment) (tagDec : DecidableEq D.Tag) (m : ℕ) : Game :=
  Dregg2.Crypto.RomCarrierSites.romOpenGame (blake3RomFamily D tagDec m)
    (blake3RomCarrier D tagDec m)

/-- **⚑⚑ THE DISCHARGED BLAKE3 COMMITMENT BINDING — ON THE PROVED FLOOR.** The successor of the
deleted `blake3_commit_opens_from_polyTime`: every query-bounded opener that publishes one digest
and opens it to two DISTINCT truncated preimages has NEGLIGIBLE advantage — a transcript opened
against a BLAKE3 commitment binds except with negligible probability, in the keyed ROM model of
§8's header. NO floor hypothesis, NO cost model: `rom_open_binds`, hence `keyedRom_hard`, hence the
birthday bound. -/
theorem blake3_commit_opens_rom (D : Blake3Deployment) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (blake3OpenRomGame D tagDec m))
    (hA : Dregg2.Crypto.RomCarrierSites.RomOpenEff (blake3RomFamily D tagDec m)
      (blake3RomCarrier D tagDec m) Q A) :
    Negl (gameAdv (blake3OpenRomGame D tagDec m) A) :=
  Dregg2.Crypto.RomCarrierSites.flat_open_binds D.Tag D.tagFintype tagDec D.tagNonempty
    _ _ _ _ (blake3RomCarrier D tagDec m) Q hQ A hA

/-- **(TOOTH — the admitted refuter-shape is DEFANGED, not excluded.)** The `0`-query constant
opener — the exact shape whose fixed short collision refutes the `IsPolyTime` floor with
probability `1` against the fixed hash — is IN the class at every budget, WINS at the constant
oracle on distinct payloads, and its advantage against the SAMPLED oracle is NEGLIGIBLE. -/
theorem blake3Rom_constOpen_defanged (D : Blake3Deployment) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (r : ∀ l, (blake3RomFamily D tagDec m).toRomFamily.R l)
    (c : ∀ l, (blake3RomCarrier D tagDec m).Ctx l)
    (v w : ∀ l, (blake3RomCarrier D tagDec m).Val l) :
    Dregg2.Crypto.RomCarrierSites.RomOpenEff (blake3RomFamily D tagDec m)
        (blake3RomCarrier D tagDec m) Q
        (Dregg2.Crypto.RomCarrierSites.romOpenAdv _ _
          (Dregg2.Crypto.RomCarrierSites.constOpenComp _ _ r c v w))
      ∧ Negl (gameAdv (blake3OpenRomGame D tagDec m)
        (Dregg2.Crypto.RomCarrierSites.romOpenAdv _ _
          (Dregg2.Crypto.RomCarrierSites.constOpenComp _ _ r c v w)))
      ∧ ∀ l, v l ≠ w l → 0 < gameAdv (blake3OpenRomGame D tagDec m)
        (Dregg2.Crypto.RomCarrierSites.romOpenAdv _ _
          (Dregg2.Crypto.RomCarrierSites.constOpenComp _ _ r c v w)) l :=
  ⟨Dregg2.Crypto.RomCarrierSites.constOpen_in_eff _ _ r c v w Q,
    Dregg2.Crypto.RomCarrierSites.constOpen_binds _ _ r c v w Q hQ
      (Dregg2.Crypto.RomCarrierSites.flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty
        _ _ _ _),
    fun l hvw =>
      Dregg2.Crypto.RomCarrierSites.constOpen_gameAdv_pos _ _ r c v w l hvw⟩

/-- **(TOOTH — a non-negligible opener is OUTSIDE the class.)** The refutation strategy that killed
the `IsPolyTime` floor cannot produce a member of this one. -/
theorem blake3Rom_nonNegl_opener_excluded (D : Blake3Deployment) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (blake3OpenRomGame D tagDec m))
    (hnn : ¬ Negl (gameAdv (blake3OpenRomGame D tagDec m) A)) :
    ¬ Dregg2.Crypto.RomCarrierSites.RomOpenEff (blake3RomFamily D tagDec m)
      (blake3RomCarrier D tagDec m) Q A :=
  Dregg2.Crypto.RomCarrierSites.romOpen_forger_excluded _ _ Q hQ
    (Dregg2.Crypto.RomCarrierSites.flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty
      _ _ _ _) A hnn

#assert_all_clean [
  blake3_commit_opens_rom,
  blake3Rom_constOpen_defanged,
  blake3Rom_nonNegl_opener_excluded
]

#assert_all_clean [
  orBreak_twin_trivial_at_finite_digest,
  orBreak_trivial_for_any_conclusion,
  no_collision_hypothesis_false_at_finite_digest,
  blake3NoCollision_false,
  deployed_hash_is_family_instance,
  blake3CollisionGame_wins_iff,
  commitOpeningGame_wins_iff,
  opening_wins_imp,
  opening_adv_le,
  blake3_commit_opens_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  blake3_floor_top_false_at_finite_digest,
  blake3_floor_bot_vacuous,
  brokenBlake3_floor_top_false,
  brokenBlake3_opening_top_false
]

end Dregg2.Circuit.Blake3FloorEffRegrounded

/-
# `Dregg2.Circuit.InjectiveFloorRegrounded` — VACUITY-SWEEP FINDING-2, CLUSTER 1: the three
highest-value injective-hash floor carriers RE-GROUNDED off their free `FooCR` hypotheses onto REAL
collision GAMES, with the `Eff` obligation in the open.

## The bug this closes

`docs/deos/VACUITY-SWEEP.md` FINDING 2 censused ~20 carriers with the shape

    def FooCR (h : A → B) : Prop := ∀ a b, h a = h b → a = b

still doc-marked "REALIZABLE", none re-grounded. Every one is `Function.Injective` of a COMPRESSING
map, hence **FALSE at deployed BabyBear parameters by pigeonhole** — so every consumer conditioned on
one is VACUOUSLY TRUE at real parameters, and `#assert_axioms` is blind to it (axiom-clean ≠
hypothesis-free). This file repairs the three highest-value carriers:

| carrier | site | why it is the priority |
|---|---|---|
| `Poseidon2WideCR` | `Emit/EffectVmEmitRotationR:256` | the most load-bearing unflagged carrier (7 hypothesis uses); its own docstring calls it "the EXACT analogue of `Poseidon2SpongeCR`" — which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` had ALREADY proved false. The analogy was exact; the conclusion did not travel. |
| `Compress8CR` (a FIELD of NOTHING as of 2026-07-20) | `DeployedCapTree` §5b, `DeployedHeapTree` §H, `DeployedFieldsTree` §F | it WAS a FIELD of all THREE 8-felt tree structures (`Cap8Scheme`/`Heap8Scheme`/`Fields8Scheme`, each `chip8CR`), so EVERY 8-felt cap/heap/fields theorem carried it and a real deployed VALUE COULD NOT EXIST for any of them. All three fields are gone; each tree's binding is EXTRACTED AS DATA (`capOpen8_binds_leaf_or_collides` / `heapOpen8_binds_leaf_or_collides` / `fieldsOpen8_binds_leaf_or_collides`) and `deployedCap8Scheme` / `deployedHeap8Scheme` / `deployedFields8Scheme` are real inhabitants whose own chip the teeth refute. The probabilistic residual below is unchanged and still the right home for the advantage bound. |
| `compress4Injective` | `CommitDifferential:82` | the deployed `hash_4_to_1` cell-commitment tree's binding floor. |

## ⚑ Why this is NOT "the `CollisionResistant` treatment"

The obvious repair — re-seat the consumers on `HashFloorHonesty.CollisionResistant`, as
`FloorRegroundedConsumers` / `Poseidon2KeyedBridge` did for the four FLAGGED carriers — **reproduces the
disease**. `CollisionResistant F` was the collision floor at the UNRESTRICTED adversary class wearing a
name that hid the `⊤`, and `FloorGames.hashCRHardQuant_top_false_of_compressing` proves THAT false for
any compressing family: the `Classical.choice` finder that outputs a collision at every key IS a
`CollisionFinder`. Toy witness satisfiable, real hash false — for the third time in a row.

⚑ That diagnosis was accepted and acted on: `CollisionResistant` was DELETED outright on 2026-07-28,
along with the `↔` that used to be needed to see the `⊤`. Nothing below changed shape — this file never
stood on it — but the `⊤` is now written out in every statement that means it, which is the whole point
the section was making.

`FloorGames.hard_top_iff_solvableFrac_negl` settles it for good: at the unrestricted class EVERY game
floor IS the probabilistic existence floor, so **no restatement of the win relation escapes** (the `↔`
is an `↔`). The only honest escape is `Eff` — the standard form's "for every EFFICIENT adversary" —
which this tree cannot give content to (`FloorGames` §8: no cost model). So this file does what
`HermineHashCRRegrounded` does, and nothing cleverer:

  * the floor is `FloorGames.HashCRHardQuant F Eff` — a REAL collision game at an EXPLICIT adversary
    class, never a `⊤`-class floor under an alias (what `CollisionResistant` was), never a free `FooCR`;
  * the consumer's break is a first-class `Game`, so the forgery is IN the win relation;
  * the reduction is an EXTRACTOR — a map of adversaries, a Lean function — plus a win-preservation
    theorem and an advantage inequality. Hypothesis and conclusion are about DIFFERENT games, so the
    floor cannot be its own conclusion (the `P → P` shape FINDING 1 documented);
  * the `hEff` obligation ("the extracted finder is in the class") is UNDISCHARGED, a PARAMETER, in
    the open at every use site — the honest name for "the reduction is efficient";
  * BOTH poles are proved for each floor: `Eff := ⊤` is FALSE at deployed BabyBear parameters (routed
    through the sweep's OWN teeth — `VacuitySweepTeeth.poseidon2WideCR_false_babyBear`,
    `compress8CR_false_babyBear`, and §2.1's `compress4_not_injective_babyBear`), `Eff := ⊥` is
    vacuous (`hard_bot_vacuous`). A reader can price any instantiation exactly.

## What is re-grounded, per carrier

  * **§2 `Compress8CR` (the `Cap8Scheme` FIELD is now DELETED)** — this section re-grounds the
    width-specific obligations the native-8-felt cap/heap/fields tree used to ride (the former
    `nodeOf8_injective` / `capLeafDigest8_injective`, now the unconditional
    `nodeOf8_binds_or_collides` / `capLeafDigest8_binds_or_collides`). Break game: two DISTINCT 8-felt
    child pairs with an equal `node8` image. Extractor `node8BreakToFinder`: hand back
    `(pack8 l₁ r₁, pack8 l₂ r₂)` — a genuine chip collision by `pack8_inj`'s contrapositive. The
    Boolean binding is no longer assumed anywhere in the CAP tree, so this section now PRICES the
    collision disjunct rather than substituting for a deleted hypothesis.
  * **§2 `compress4Injective` (the carrier is now DELETED)** — it used to condition
    `effectVmCommit_binds_all` / `_binds_record_digest` / `_binds_cap_root` (the audit-P0-2 anti-ghost
    teeth). Break game: two DISTINCT 13-limb claims with an equal deployed commitment. Extractor
    `commit4Find`: the TREE TRACE — root quad, else head quad, else the two body quads — the
    `effectVmCommit_collision_of_ne` case analysis written as a FUNCTION. The algebraic consumers were
    REPLACED in place by the unconditional
    `CommitDifferential.effectVmCommit_binds_record_digest_or_collides` / `_binds_cap_root_or_collides`
    (bind, or EXHIBIT the collision — no floor at all); this section prices the residual.
  * **§5 `Poseidon2WideCR`** — `chainFrom8_inj` / `wireCommitR8_binds` (the faithful ~124-bit
    commitment the light client trusts). Break game: two DISTINCT `(limbs, iroot)` claims of equal limb
    length with an equal `wireCommitR8`. Extractor `wireCommit8Find`: the CHAIN WALK
    (`chainCollFind`) — step the two chains together and return the first step whose `permW` arguments
    collide, else the two heads.

⚑ The extractors are **constructive functions**, not `Classical.choose` of an existential. This
matters: `CommitFaithfulRegrounded`'s pre-existing reductions land in `Compress4Collision h4 := ∃ …` /
`WireCommit8Collision permW := ∃ …`, which are EXISTENCE props — TRUE unconditionally at deployed
parameters by pigeonhole, so a disjunct returning one carries no content there (`FloorGames` §2 is
exactly this observation). An extractor that is a MAP OF ADVERSARIES lands in a game advantage instead,
which is the object a floor can bind.

## Non-fake

Each carrier carries a CANARY (§2.4/§3.4/§5.6): strip the reduction — apply the floor at some OTHER
finder — and the keystone does NOT follow (`fail_if_success`); plus the POSITIVE pole (the RIGHT floor
at the EXTRACTED finder DOES discharge it), because a gate that refuses everything is a broken keystone,
not a fixed one. The OLD injective-floor consumers are KEPT UNTOUCHED — this file only ADDS siblings;
the three carriers' docstrings now point at these teeth. `#assert_all_clean`; no `sorry`, no fresh
`axiom`.
-/
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.RomChainedReduction
import Dregg2.Circuit.VacuitySweepTeeth
import Dregg2.Circuit.CommitDifferential
import Dregg2.Circuit.DeployedCapTree
import Dregg2.Circuit.Emit.EffectVmEmitRotationR
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Circuit.InjectiveFloorRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_le_of_imp negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous hashGame HashCRHardQuant)
open Dregg2.Circuit.DeployedCapTree (Digest8 Compress8CR CapLeaf leafFields leafFields_inj)
open Dregg2.Circuit.DeployedCapTree.Cap8Scheme (pack8 pack8_inj)
open Dregg2.Circuit.CommitDifferential (effectVmCommit h4q)
open Dregg2.Circuit.Emit.EffectVmEmitRotationR
  (Poseidon2Width8 chainFrom8 chainFrom8_len chainFrom8_snoc wireCommitR8 chunk31
   chunk31_length chunk31_flatten IsCollW chainCollFind chainCollFind_spec wireCommit8Find
   wireCommit8Find_spec WireColl)
open Dregg2.Circuit.VacuitySweepTeeth (babyBearP widePerm_not_injective_babyBear compress8CR_false_babyBear)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)

set_option autoImplicit false

/-! ## §0 — the shared spine: the honest floor, and the price of its `Eff`.

Every carrier below lands on ONE object: `FloorGames.HashCRHardQuant F Eff` — the collision game of a
keyed family `F` at an explicit adversary class `Eff`. This section states the two poles once, so each
carrier can price its own instantiation by citing them. -/

/-- **THE ⊤ POLE, ONCE.** The collision floor at the UNRESTRICTED adversary class is FALSE for any
COMPRESSING family — a collision at every key (which pigeonhole forces at deployed parameters, and which
is the defining property of a hash) makes the `Classical.choice` finder win with probability `1`. This is
`FloorGames.hashCRHardQuant_top_false_of_compressing`, re-exported at this file's spine; every carrier's
"false at deployed BabyBear params" tooth routes through it. It is the price of `hEff`, stated as a
theorem instead of a promise.

⚑ It used to reach the upstream tooth by rewriting across `collisionResistant_iff_hashCRHardQuant_top`,
because upstream stated the tooth about `CollisionResistant`. That name is DELETED (2026-07-28) and the
tooth is stated at `⊤` directly, so the transport is gone and the `⊤` is written out on both sides. -/
theorem hashCRHardQuant_top_false_of_compressing (F : KeyedHashFamily) (hin : Nonempty F.Input)
    (hcol : ∀ l (k : F.Key l), ∃ x y : F.Input, x ≠ y ∧ F.H l k x = F.H l k y) :
    ¬ HashCRHardQuant F (fun _ => True) :=
  Dregg2.Crypto.FloorGames.hashCRHardQuant_top_false_of_compressing F hin hcol

/-- **THE ⊥ POLE, ONCE.** At the empty adversary class the floor holds for ANY family, including a
completely broken one — so a satisfiability witness is worth nothing without the refutation beside it.
Recorded so that `Eff` cannot be quietly filled with nothing. -/
theorem hashCRHardQuant_bot_vacuous (F : KeyedHashFamily) :
    HashCRHardQuant F (fun _ => False) :=
  hard_bot_vacuous _

/-- **A NON-INJECTIVE hash HAS a collision.** The bridge from the sweep's teeth (which refute
`Function.Injective`-shaped floors) to the compressing hypothesis `hashCRHardQuant_top_false_of_compressing`
consumes. Pure logic: unfolding the negated injectivity statement yields the colliding pair. -/
theorem exists_collision_of_not_injective {α β : Type} {h : α → β}
    (hni : ¬ (∀ x y : α, h x = h y → x = y)) : ∃ x y : α, x ≠ y ∧ h x = h y := by
  by_contra hcon
  push_neg at hcon
  exact hni (fun x y hxy => by
    by_contra hne
    exact absurd hxy (hcon x y hne))

/-! ## §1 — carrier 2 (`Compress8CR`): the deployed arity-16 chip, as a KEYED family.

`Compress8CR f := ∀ a b : List ℤ, f a = f b → a = b` (`DeployedCapTree:630`) is `Function.Injective f`
on the INFINITE `List ℤ`, and the deployed `chip_absorb_all_lanes` squeezes 8 BOUNDED BabyBear lanes —
`VacuitySweepTeeth.compress8CR_false_babyBear` refutes it. It USED TO BE a FIELD of `Cap8Scheme`, so a
real deployed `Cap8Scheme` VALUE could not exist: not a hypothesis on a theorem but a non-inhabitable
structure field. ⚑ THAT FIELD IS NOW DELETED (2026-07-20) — `Cap8Scheme` carries only the chip,
`DeployedCapTree.deployedCap8Scheme` is a real inhabitant, and the tree's binding is extracted as data.
`Chip8Keyed` below predates the deletion and remains the right shape for the GAME (a keyed family with a
sampled tag), which `Cap8Scheme` deliberately is not. -/

/-- **THE DEPLOYED ARITY-16 CHIP, KEYED — and carrying NO CR field.** The deployed
`descriptor_ir2::chip_absorb_all_lanes` at each domain-separation tag, plus the tag space the collision
game samples. INHABITED by the real chip: it asserts nothing false about it. (`Cap8Scheme` used to
bundle `chip8CR : Compress8CR chipAbsorb8` — a field the deployed chip REFUTES, so that structure had no
deployed value; the field is now deleted and `Cap8Scheme` is inhabited too. The two types differ in
PURPOSE, not in honesty: this one is keyed, for the game.) -/
structure Chip8Keyed where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The keyed 8-output chip absorb; at `deployedTag` this IS the Rust `chip_absorb_all_lanes`. -/
  chipAbsorb8At : Tag → List ℤ → Digest8
  /-- The specific tag the deployment computes at this use-site. -/
  deployedTag : Tag

/-- The DEPLOYED fixed chip the prover actually computes — the family instance at the deployed tag. -/
def Chip8Keyed.deployedChip (D : Chip8Keyed) : List ℤ → Digest8 := D.chipAbsorb8At D.deployedTag

/-- **`chip8Family D`** — the deployed chip lifted to a `HashFloorHonesty.KeyedHashFamily`, keyed by its
domain-separation tag. Input `List ℤ` (the chip's absorbed block), output `Digest8` (the 8 squeezed
BabyBear lanes). This is the object the honest floor is stated at. -/
def chip8Family (D : Chip8Keyed) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List ℤ
  Out := Digest8
  H := fun _ t xs => D.chipAbsorb8At t xs
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The DEPLOYED fixed chip IS the keyed family's instance at the deployed tag — a
definitional equality, no idealization. So the collision game below is a game about the very function
`cap_root.rs` computes. -/
theorem deployedChip_is_family_instance (D : Chip8Keyed) (n : ℕ) :
    D.deployedChip = (chip8Family D).H n D.deployedTag := rfl

/-- The deployed 8-felt internal node at tag `t`: the arity-16 chip absorb over `pack8 l r = L8 ‖ R8`
(`cap_root.rs::cap_node8`). The `Cap8Scheme.nodeOf8` shape, off the non-inhabitable structure. -/
def Chip8Keyed.nodeAt (D : Chip8Keyed) (t : D.Tag) (l r : Digest8) : Digest8 :=
  D.chipAbsorb8At t (pack8 l r)

/-- The deployed 8-felt leaf digest at tag `t`: the chip absorb over the 7 leaf fields
(`cap_root.rs::CapLeaf::digest`). -/
def Chip8Keyed.leafAt (D : Chip8Keyed) (t : D.Tag) (l : CapLeaf) : Digest8 :=
  D.chipAbsorb8At t (leafFields l)

/-! ### §1.1 — the node8 break, as a first-class game. -/

/-- **THE `node8` BREAK GAME.** The adversary is handed a sampled domain-separation tag and WINS iff it
outputs two DISTINCT 8-felt child pairs that the deployed `node8` maps to the SAME digest — i.e. it
breaks exactly the former `Cap8Scheme.nodeOf8_injective` (now `nodeOf8_binds_or_collides`'s left disjunct), the width-specific obligation the whole native-8-felt
cap/heap/fields tree rides. The break is IN the win relation; nothing here is a docstring. -/
def node8BreakGame (D : Chip8Keyed) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (Digest8 × Digest8) × (Digest8 × Digest8)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    c.1 ≠ c.2 ∧ D.nodeAt t c.1.1 c.1.2 = D.nodeAt t c.2.1 c.2.2
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the break game's win relation is a genuine violation of
the `node8` binding on the real deployed node. -/
theorem node8BreakGame_wins_iff (D : Chip8Keyed) (l : ℕ) (t : D.Tag)
    (c : (Digest8 × Digest8) × (Digest8 × Digest8)) :
    (node8BreakGame D).wins l t c ↔
      (c.1 ≠ c.2 ∧ D.nodeAt t c.1.1 c.1.2 = D.nodeAt t c.2.1 c.2.2) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A `node8`-injectivity breaker becomes a chip-collision
finder by handing back the two PACKED blocks `(pack8 l₁ r₁, pack8 l₂ r₂)`. This is not a re-indexing and
not a rename: it is the `pack8` composition step `nodeOf8_binds_or_collides` performs, written as a function into
the collision game of the real chip. -/
def node8BreakToFinder (D : Chip8Keyed) (A : Adversary (node8BreakGame D)) :
    Adversary (hashGame (chip8Family D)) where
  run := fun l t => let c := A.run l t; (pack8 c.1.1 c.1.2, pack8 c.2.1 c.2.2)

/-- **⚑ THE REDUCTION IS WIN-PRESERVING — and this is the `node8` binding, contraposed.** Wherever the
breaker wins, the two packed blocks ARE a genuine chip collision: they are DISTINCT (`pack8_inj`'s
contrapositive — equal packs force equal children) and their chip images are EQUAL (that IS the equal
`node8`). The cap-tree content lives in a proof term, not in a sentence about one. -/
theorem node8_wins_imp (D : Chip8Keyed) (A : Adversary (node8BreakGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (node8BreakGame D).wins l t (A.run l t)) :
    (hashGame (chip8Family D)).wins l t ((node8BreakToFinder D A).run l t) := by
  obtain ⟨hne, heq⟩ := hwin
  refine ⟨fun hpack => hne ?_, heq⟩
  obtain ⟨hl, hr⟩ := pack8_inj hpack
  exact Prod.ext hl hr

/-- **THE ADVANTAGE INEQUALITY.** The `node8` breaker's advantage is at most the extracted chip-collision
finder's, at every parameter — the two games play over the SAME sampled tag space, and every tag the
breaker wins the extracted finder wins. A genuine reduction inequality over real game advantages. -/
theorem node8_adv_le (D : Chip8Keyed) (A : Adversary (node8BreakGame D)) (l : ℕ) :
    gameAdv (node8BreakGame D) A l ≤ gameAdv (hashGame (chip8Family D)) (node8BreakToFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact node8_wins_imp D A l t ht

/-- **⚑ THE PRICE OF THE `node8` COLLISION DISJUNCT — from the CHIP's collision floor, VIA the reduction.**

Under the collision floor of the DEPLOYED chip at the class `Eff`, a `node8`-injectivity breaker whose
extracted finder is in that class has NEGLIGIBLE advantage: the native-8-felt cap tree's per-node
anti-ghost peel holds EXCEPT with negligible probability. The Boolean "equal `node8` ⟹ equal children"
becomes the negligible advantage — and, unlike its `Compress8CR` predecessor, this statement rests on a
hypothesis the deployed chip does NOT refute, and is FALSE if you delete the reduction (§2.4's canary).

⚑ **THE `hEff` OBLIGATION IS UNDISCHARGED AND THAT IS THE HONEST STATE.** It says the extracted finder
is in the class the floor quantifies over — the standard "the reduction is efficient". It is a
PARAMETER, in the open, at the use site, because this tree has no cost model (`FloorGames` §8). The
floor is priced exactly by §2.5: `⊤` FALSE at deployed BabyBear params, `⊥` vacuous. -/
theorem node8_injective_advantage_bound (D : Chip8Keyed)
    (Eff : Adversary (hashGame (chip8Family D)) → Prop)
    (A : Adversary (node8BreakGame D))
    (hEff : Eff (node8BreakToFinder D A))
    (hCR : HashCRHardQuant (chip8Family D) Eff) :
    Negl (gameAdv (node8BreakGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (node8BreakGame D) A l).1)
    (node8_adv_le D A) (hCR _ hEff)

/-! ### §1.2 — the leaf twin (the former `capLeafDigest8_injective`, now `capLeafDigest8_binds_or_collides`). -/

/-- **THE LEAF BREAK GAME.** The adversary WINS iff it outputs two DISTINCT `CapLeaf`s whose deployed
8-felt leaf digests collide — exactly a break of the leaf binding (`capLeafDigest8_binds_or_collides`'s left disjunct). -/
def leaf8BreakGame (D : Chip8Keyed) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => CapLeaf × CapLeaf
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c => c.1 ≠ c.2 ∧ D.leafAt t c.1 = D.leafAt t c.2
  winsDec := fun _ t c => inferInstance

/-- **THE LEAF EXTRACTOR.** A leaf-injectivity breaker becomes a chip-collision finder by handing back
the two `leafFields` blocks — the composition step `capLeafDigest8_binds_or_collides` performs, as a function. It is LITERALLY the extractor `DeployedCapTree.Cap8Scheme.leafColl8Find`. -/
def leaf8BreakToFinder (D : Chip8Keyed) (A : Adversary (leaf8BreakGame D)) :
    Adversary (hashGame (chip8Family D)) where
  run := fun l t => let c := A.run l t; (leafFields c.1, leafFields c.2)

/-- **WIN-PRESERVATION — the leaf binding, contraposed.** Distinct leaves have distinct
`leafFields` (`leafFields_inj`), and equal leaf digests are equal chip images. -/
theorem leaf8_wins_imp (D : Chip8Keyed) (A : Adversary (leaf8BreakGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (leaf8BreakGame D).wins l t (A.run l t)) :
    (hashGame (chip8Family D)).wins l t ((leaf8BreakToFinder D A).run l t) := by
  obtain ⟨hne, heq⟩ := hwin
  exact ⟨fun hf => hne (leafFields_inj hf), heq⟩

theorem leaf8_adv_le (D : Chip8Keyed) (A : Adversary (leaf8BreakGame D)) (l : ℕ) :
    gameAdv (leaf8BreakGame D) A l ≤ gameAdv (hashGame (chip8Family D)) (leaf8BreakToFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact leaf8_wins_imp D A l t ht

/-- **⚑ THE PRICE OF THE LEAF COLLISION DISJUNCT.** Under the deployed chip's collision floor,
a leaf-digest equivocator has negligible advantage. Same honest `hEff` obligation as §1.1. -/
theorem leaf8_injective_advantage_bound (D : Chip8Keyed)
    (Eff : Adversary (hashGame (chip8Family D)) → Prop)
    (A : Adversary (leaf8BreakGame D))
    (hEff : Eff (leaf8BreakToFinder D A))
    (hCR : HashCRHardQuant (chip8Family D) Eff) :
    Negl (gameAdv (leaf8BreakGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (leaf8BreakGame D) A l).1)
    (leaf8_adv_le D A) (hCR _ hEff)

/-! ### §1.3 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: try to conclude the `node8` breaker's negligibility from the chip's collision floor applied at
some OTHER finder `B`, not the one EXTRACTED from the breaker. It does not go through — `hCR B hB` proves
`Negl` of the WRONG advantage, and only `node8_adv_le` connects the extracted finder to the break game.

This tooth was IMPOSSIBLE to write under the old free `Compress8CR` hypothesis, where the consumer's
hypothesis and conclusion were the same object; it compiles now, and reds if a future edit reconnects
the games. -/
example (D : Chip8Keyed) (Eff : Adversary (hashGame (chip8Family D)) → Prop)
    (A : Adversary (node8BreakGame D))
    (B : Adversary (hashGame (chip8Family D))) (hB : Eff B)
    (hCR : HashCRHardQuant (chip8Family D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (node8BreakGame D) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a broken
keystone, not a fixed one. With the chip's collision floor at the EXTRACTED finder, the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_node8_bound_fires (D : Chip8Keyed)
    (Eff : Adversary (hashGame (chip8Family D)) → Prop)
    (A : Adversary (node8BreakGame D))
    (hEff : Eff (node8BreakToFinder D A))
    (hCR : HashCRHardQuant (chip8Family D) Eff) :
    Negl (gameAdv (node8BreakGame D) A) :=
  node8_injective_advantage_bound D Eff A hEff hCR

/-! ### §1.4 — both poles of the chip floor, PROVED (the price of `hEff`). -/

/-- **⚑ THE ⊤ POLE — the chip's collision floor is FALSE at the REAL BabyBear parameters.** If every
tag's chip squeezes 8 genuine BabyBear lanes — i.e. the DEPLOYED `chip_absorb_all_lanes` — then it is
non-injective (`VacuitySweepTeeth.compress8CR_false_babyBear`, the counting core), so a collision exists
at every key and the floor at `Eff := ⊤` is FALSE.

This is the honest price of `hEff`, and it is the SAME refutation that killed `Compress8CR`: what the
re-grounding buys is not a floor the deployed chip satisfies at ⊤ — no such floor exists (`FloorGames`
§2) — it is that the residual is now ONE named parameter with both poles proved, instead of a structure
field the deployed chip refutes. -/
theorem chip8_floor_top_false_babyBear (D : Chip8Keyed)
    (hb : ∀ (t : D.Tag) (xs : List ℤ) (i : Fin 8), 0 ≤ D.chipAbsorb8At t xs i ∧
      D.chipAbsorb8At t xs i < babyBearP) :
    ¬ HashCRHardQuant (chip8Family D) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨([] : List ℤ)⟩ (fun l t => ?_)
  exact exists_collision_of_not_injective (compress8CR_false_babyBear (D.chipAbsorb8At t) (hb t))

/-- **THE ⊥ POLE — vacuous.** Recorded so the satisfiability of the floor cannot be mistaken for
evidence: at the empty class it holds for a completely broken chip too. -/
theorem chip8_floor_bot_vacuous (D : Chip8Keyed) :
    HashCRHardQuant (chip8Family D) (fun _ => False) :=
  hashCRHardQuant_bot_vacuous _

/-! ## §2 — carrier 3 (`compress4Injective`, DELETED): the deployed `hash_4_to_1` commitment tree.

The carrier was `compress4Injective h4 := ∀ a b c d a' b' c' d', h4 a b c d = h4 a' b' c' d' → a = a' ∧ …`
— injectivity of the 4-to-1 compress on the INFINITE `ℤ⁴`, doc-marked "REALIZABLE — the `hash_4_to_1`
the circuit verifies". §2.1 proves that FALSE at the deployed BabyBear parameters, by the same counting
core that killed the flagged four, so the carrier has been REMOVED from `CommitDifferential` and its
consumers restated unconditionally. This section supplies the probabilistic residual. -/

/-! ### §2.1 — the FALSIFIABILITY TOOTH: 4-to-1 injectivity is FALSE at deployed params.

`VacuitySweepTeeth` proved the two representatives (`Poseidon2WideCR`, `Compress8CR`) false and left
the rest of the class "known by class argument, only two proved here". This was the third, and it is
mechanical exactly as the sweep predicted: the counting core plus the carrier's own bounded range.

⚑ The named carrier `CommitDifferential.compress4Injective` these teeth used to refute has since been
DELETED (its consumers now carry no floor — `effectVmCommit_binds_record_digest_or_collides` and
`_binds_cap_root_or_collides` are unconditional and EXHIBIT the collision). The teeth are RETAINED,
restated about the underlying map `h4q h4` itself, because they are the reason the deletion was
correct: the record must outlive the carrier. -/

/-- `ℤ × ℤ × ℤ × ℤ` is infinite (the first coordinate already is) — the counting core's domain premise.
`local`, deliberately: this file is imported by the `Dregg2` root, and a GLOBAL `Infinite` instance
would perturb instance resolution tree-wide for a fact needed only in §2.1. -/
local instance : Infinite (ℤ × ℤ × ℤ × ℤ) :=
  Infinite.of_injective (fun n : ℤ => (n, 0, 0, 0)) (fun a b h => by simpa using h)

/-- **TOOTH — 4-to-1 injectivity is FALSE for a range-bounded compress.** Literally
`not_injective_of_finite_range` on the uncurried map: the deleted floor WAS injectivity on the
infinite `ℤ⁴`. The exact shape of `HashFloorHonesty.compressInjective_false_of_finite_range`, one
arity up. -/
theorem compress4_not_injective_of_finite_range (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hfin : (Set.range (h4q h4)).Finite) : ¬ Function.Injective (h4q h4) :=
  not_injective_of_finite_range (h4q h4) hfin

/-- **⚑ TOOTH (deployed form) — 4-to-1 injectivity is FALSE at the REAL BabyBear parameters.** A
`hash_4_to_1` whose output is a genuine BabyBear field element (`0 ≤ · < p`, `p = 2³¹ − 2²⁷ + 1`) — i.e.
the deployed Poseidon2 `hash_4_to_1`, KAT-locked to Plonky3 — REFUTES the floor whose docstring once
called it "REALIZABLE". Four field elements do not fit in one without collision.

This is why `CommitDifferential.compress4Injective` was DELETED rather than kept "for the record":
every theorem that carried it — the audit-P0-2 anti-ghost teeth — was VACUOUSLY TRUE at deployed
parameters. Their unconditional replacements carry no floor; §2.2–§2.5 price the residual. -/
theorem compress4_not_injective_babyBear (h4 : ℤ → ℤ → ℤ → ℤ → ℤ)
    (hb : ∀ a b c d, 0 ≤ h4 a b c d ∧ h4 a b c d < babyBearP) :
    ¬ Function.Injective (h4q h4) := by
  refine compress4_not_injective_of_finite_range h4 ?_
  refine (Set.finite_Ico (0 : ℤ) babyBearP).subset ?_
  rintro _ ⟨⟨a, b, c, d⟩, rfl⟩
  exact ⟨(hb a b c d).1, (hb a b c d).2⟩

/-! ### §2.2 — the deployed `hash_4_to_1`, as a KEYED family, and the 13-limb claim. -/

/-- **THE DEPLOYED 4-TO-1 COMPRESS, KEYED — carrying NO CR field.** The Rust
`poseidon2::hash_4_to_1` at each domain-separation tag (the deployment uses the SAME primitive at four
distinct tree positions — the three intermediates and the root — which is what a tag ranges over). -/
structure H4Keyed where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The keyed 4-to-1 compress; at `deployedTag` this IS the Rust `hash_4_to_1`. -/
  h4At : Tag → ℤ → ℤ → ℤ → ℤ → ℤ
  /-- The specific tag the deployment computes at this use-site. -/
  deployedTag : Tag

/-- The DEPLOYED fixed 4-to-1 compress the prover actually computes. -/
def H4Keyed.deployedH4 (D : H4Keyed) : ℤ → ℤ → ℤ → ℤ → ℤ := D.h4At D.deployedTag

/-- **`h4Family D`** — the deployed `hash_4_to_1` lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. Input `ℤ⁴` (the four absorbed felts), output `ℤ` (the BabyBear field element). -/
def h4Family (D : H4Keyed) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := ℤ × ℤ × ℤ × ℤ
  Out := ℤ
  H := fun _ t q => h4q (D.h4At t) q
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The DEPLOYED fixed compress IS the family's instance at the deployed tag,
definitionally — the collision game is a game about the function `cell_state.rs` computes. -/
theorem deployedH4_is_family_instance (D : H4Keyed) (n : ℕ) (q : ℤ × ℤ × ℤ × ℤ) :
    h4q D.deployedH4 q = (h4Family D).H n D.deployedTag q := rfl

/-- **THE DEPLOYED 13-LIMB CLAIM** — `[balLo, balHi, nonce, fields[0..8], capRoot, recordDigest]`, the
ordered limb list `CellState::compute_commitment` absorbs (`CommitDifferential.effectVmLimbs`). -/
structure Claim13 where
  /-- The low balance limb. -/
  bl : ℤ
  /-- The high balance limb. -/
  bh : ℤ
  /-- The nonce limb. -/
  n : ℤ
  /-- The eight welded user fields `fields[0..8]`. -/
  f : Fin 8 → ℤ
  /-- The cap-tree root limb. -/
  cr : ℤ
  /-- The authority-residue limb (`compute_authority_digest_felt`), absorbed at index 12. -/
  rd : ℤ
  deriving DecidableEq

/-- Claim extensionality: equal limbs force an equal claim. -/
theorem Claim13.ext' {c c' : Claim13} (h1 : c.bl = c'.bl) (h2 : c.bh = c'.bh) (h3 : c.n = c'.n)
    (hf : c.f = c'.f) (h5 : c.cr = c'.cr) (h6 : c.rd = c'.rd) : c = c' := by
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := c
  obtain ⟨b1, b2, b3, b4, b5, b6⟩ := c'
  simp only at h1 h2 h3 hf h5 h6
  subst h1; subst h2; subst h3; subst hf; subst h5; subst h6
  rfl

/-- The deployed cell commitment of a claim at tag `t` — `CommitDifferential.effectVmCommit`, the
FAITHFUL Lean model of `CellState::compute_commitment`, over the keyed compress. -/
def Claim13.commitAt (D : H4Keyed) (t : D.Tag) (c : Claim13) : ℤ :=
  effectVmCommit (D.h4At t) c.bl c.bh c.n c.f c.cr c.rd

/-! ### §2.3 — the commitment break, as a first-class game, and the TREE-TRACE extractor. -/

/-- **THE CELL-COMMITMENT BREAK GAME.** The adversary is handed a sampled domain-separation tag and WINS
iff it outputs two DISTINCT 13-limb claims with the SAME deployed commitment — i.e. it breaks exactly
`effectVmCommit_binds_all`. A win is the audit-P0-2 anti-ghost forgery: two cells differing in their
authority residue (or any limb) that commit identically. -/
def commit4BreakGame (D : H4Keyed) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => Claim13 × Claim13
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c => c.1 ≠ c.2 ∧ Claim13.commitAt D t c.1 = Claim13.commitAt D t c.2
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the real
deployed cell commitment. -/
theorem commit4BreakGame_wins_iff (D : H4Keyed) (l : ℕ) (t : D.Tag) (c : Claim13 × Claim13) :
    (commit4BreakGame D).wins l t c ↔
      (c.1 ≠ c.2 ∧ Claim13.commitAt D t c.1 = Claim13.commitAt D t c.2) :=
  Iff.rfl

/-- **⚑ THE TREE-TRACE EXTRACTOR.** Given two claims with an equal commitment, LOCATE the colliding
`h4` node and return its two arguments: the ROOT quad `(inter1, inter2, inter3, recordDigest)` if those
differ; else the HEAD quad `(balLo, balHi, nonce, fields[0])`; else the two BODY quads. This is
`CommitFaithfulRegrounded.effectVmCommit_collision_of_ne`'s case analysis written as a FUNCTION — which
is the whole point: that theorem lands in `Compress4Collision h4 := ∃ …`, an EXISTENCE prop that is
unconditionally TRUE at deployed parameters by pigeonhole, so it cannot be what a floor binds. A MAP OF
ADVERSARIES lands in a game advantage, which can be. -/
def commit4Find (h4 : ℤ → ℤ → ℤ → ℤ → ℤ) (c c' : Claim13) :
    (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ) :=
  let i1 := h4 c.bl c.bh c.n (c.f 0)
  let i2 := h4 (c.f 1) (c.f 2) (c.f 3) (c.f 4)
  let i3 := h4 (c.f 5) (c.f 6) (c.f 7) c.cr
  let i1' := h4 c'.bl c'.bh c'.n (c'.f 0)
  let i2' := h4 (c'.f 1) (c'.f 2) (c'.f 3) (c'.f 4)
  let i3' := h4 (c'.f 5) (c'.f 6) (c'.f 7) c'.cr
  if ((i1, i2, i3, c.rd) : ℤ × ℤ × ℤ × ℤ) ≠ ((i1', i2', i3', c'.rd) : ℤ × ℤ × ℤ × ℤ) then
    ((i1, i2, i3, c.rd), (i1', i2', i3', c'.rd))
  else if ((c.bl, c.bh, c.n, c.f 0) : ℤ × ℤ × ℤ × ℤ)
      ≠ ((c'.bl, c'.bh, c'.n, c'.f 0) : ℤ × ℤ × ℤ × ℤ) then
    ((c.bl, c.bh, c.n, c.f 0), (c'.bl, c'.bh, c'.n, c'.f 0))
  else if ((c.f 1, c.f 2, c.f 3, c.f 4) : ℤ × ℤ × ℤ × ℤ)
      ≠ ((c'.f 1, c'.f 2, c'.f 3, c'.f 4) : ℤ × ℤ × ℤ × ℤ) then
    ((c.f 1, c.f 2, c.f 3, c.f 4), (c'.f 1, c'.f 2, c'.f 3, c'.f 4))
  else
    ((c.f 5, c.f 6, c.f 7, c.cr), (c'.f 5, c'.f 6, c'.f 7, c'.cr))

/-- **⚑ THE EXTRACTOR IS CORRECT — the tree trace always lands on a REAL `h4` collision.** Given two
DISTINCT claims with an EQUAL commitment, `commit4Find` returns two DISTINCT quads with an EQUAL `h4`
image. Each branch is a node of the deployed tree: the root's equality IS the commitment equality; a
head/body quad's image is the corresponding intermediate, equal by the root branch's failure; and the
final branch is unreachable because all-quads-equal forces the claims equal (`Claim13.ext'`). -/
theorem commit4Find_spec (h4 : ℤ → ℤ → ℤ → ℤ → ℤ) {c c' : Claim13} (hne : c ≠ c')
    (heq : effectVmCommit h4 c.bl c.bh c.n c.f c.cr c.rd
         = effectVmCommit h4 c'.bl c'.bh c'.n c'.f c'.cr c'.rd) :
    (commit4Find h4 c c').1 ≠ (commit4Find h4 c c').2 ∧
      h4q h4 (commit4Find h4 c c').1 = h4q h4 (commit4Find h4 c c').2 := by
  simp only [effectVmCommit] at heq
  simp only [commit4Find, h4q]
  split_ifs with h1 h2 h3
  · exact ⟨h1, heq⟩
  · -- the root quads are EQUAL, so the three intermediates and `rd` agree; the head quads differ.
    simp only [ne_eq, not_not, Prod.mk.injEq] at h1
    exact ⟨h2, h1.1⟩
  · simp only [ne_eq, not_not, Prod.mk.injEq] at h1
    exact ⟨h3, h1.2.1⟩
  · -- all four quads equal ⇒ every limb equal ⇒ the claims are equal, contradicting `hne`.
    simp only [ne_eq, not_not, Prod.mk.injEq] at h1 h2 h3
    refine ⟨fun hlast => absurd ?_ hne, h1.2.2.1⟩
    simp only [Prod.mk.injEq] at hlast h2 h3
    refine Claim13.ext' h2.1 h2.2.1 h2.2.2.1 ?_ hlast.2.2.2 h1.2.2.2
    funext i
    fin_cases i
    · exact h2.2.2.2
    · exact h3.1
    · exact h3.2.1
    · exact h3.2.2.1
    · exact h3.2.2.2
    · exact hlast.1
    · exact hlast.2.1
    · exact hlast.2.2.1

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A commitment equivocator becomes an `h4`-collision
finder by running the tree trace on its two claims. -/
def commit4BreakToFinder (D : H4Keyed) (A : Adversary (commit4BreakGame D)) :
    Adversary (hashGame (h4Family D)) where
  run := fun l t => let c := A.run l t; commit4Find (D.h4At t) c.1 c.2

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every tag the equivocator wins, the
extracted finder wins the `h4` collision game: `commit4Find_spec` at the adversary's actual output. -/
theorem commit4_wins_imp (D : H4Keyed) (A : Adversary (commit4BreakGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (commit4BreakGame D).wins l t (A.run l t)) :
    (hashGame (h4Family D)).wins l t ((commit4BreakToFinder D A).run l t) :=
  commit4Find_spec (D.h4At t) hwin.1 hwin.2

/-- **THE ADVANTAGE INEQUALITY.** The equivocator's advantage is at most the extracted `h4`-collision
finder's, at every parameter — over the SAME sampled tag space. -/
theorem commit4_adv_le (D : H4Keyed) (A : Adversary (commit4BreakGame D)) (l : ℕ) :
    gameAdv (commit4BreakGame D) A l ≤ gameAdv (hashGame (h4Family D)) (commit4BreakToFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact commit4_wins_imp D A l t ht

/-- **⚑ RE-GROUNDED `CommitDifferential.effectVmCommit_binds_all` — from the `h4` collision floor, VIA
the reduction.**

Under the DEPLOYED `hash_4_to_1`'s collision floor at the class `Eff`, a cell-commitment equivocator
whose extracted finder is in that class has NEGLIGIBLE advantage: the deployed commitment pins EVERY
limb — the balance, the nonce, the eight user fields, the cap root, and the authority residue — except
with negligible probability. The audit-P0-2 anti-ghost tooth (`_binds_record_digest`: tampering the
authority residue provably MOVES the commitment) survives as a concrete-security statement, on a
hypothesis the deployed `hash_4_to_1` does NOT refute.

⚑ `hEff` is UNDISCHARGED — the standard "the reduction is efficient", a PARAMETER, in the open
(`FloorGames` §8). The floor is priced by §2.5. -/
theorem effectVmCommit_binds_all_advantage_bound (D : H4Keyed)
    (Eff : Adversary (hashGame (h4Family D)) → Prop)
    (A : Adversary (commit4BreakGame D))
    (hEff : Eff (commit4BreakToFinder D A))
    (hCR : HashCRHardQuant (h4Family D) Eff) :
    Negl (gameAdv (commit4BreakGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (commit4BreakGame D) A l).1)
    (commit4_adv_le D A) (hCR _ hEff)

/-! ### §2.4 — the CANARY + the positive pole. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** The `h4`
collision floor at some OTHER finder `B` cannot close the equivocator's negligibility: only
`commit4_adv_le` connects the EXTRACTED finder to the break game. Unwritable under the old free
`compress4Injective` hypothesis (now deleted). -/
example (D : H4Keyed) (Eff : Adversary (hashGame (h4Family D)) → Prop)
    (A : Adversary (commit4BreakGame D))
    (B : Adversary (hashGame (h4Family D))) (hB : Eff B)
    (hCR : HashCRHardQuant (h4Family D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (commit4BreakGame D) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** -/
theorem the_repaired_commit4_bound_fires (D : H4Keyed)
    (Eff : Adversary (hashGame (h4Family D)) → Prop)
    (A : Adversary (commit4BreakGame D))
    (hEff : Eff (commit4BreakToFinder D A))
    (hCR : HashCRHardQuant (h4Family D) Eff) :
    Negl (gameAdv (commit4BreakGame D) A) :=
  effectVmCommit_binds_all_advantage_bound D Eff A hEff hCR

/-! ### §2.5 — both poles of the `h4` floor, PROVED. -/

/-- **⚑ THE ⊤ POLE — the `h4` collision floor is FALSE at the REAL BabyBear parameters**, routed through
§2.1's new tooth. The price of `hEff`, as a theorem. -/
theorem h4_floor_top_false_babyBear (D : H4Keyed)
    (hb : ∀ (t : D.Tag) (a b c d : ℤ), 0 ≤ D.h4At t a b c d ∧ D.h4At t a b c d < babyBearP) :
    ¬ HashCRHardQuant (h4Family D) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))⟩
    (fun l t => ?_)
  exact exists_collision_of_not_injective (h := h4q (D.h4At t))
    (compress4_not_injective_babyBear (D.h4At t) (hb t))

/-- **THE ⊥ POLE — vacuous.** -/
theorem h4_floor_bot_vacuous (D : H4Keyed) :
    HashCRHardQuant (h4Family D) (fun _ => False) :=
  hashCRHardQuant_bot_vacuous _

/-! ## §3 — carrier 1 (`Poseidon2WideCR`): the faithful 8-felt chained wire commitment.

THE most load-bearing unflagged carrier (7 hypothesis uses, across
`Emit/EffectVmEmitRotationWide`, `Emit/CapOpenEmit`, `Market/WideCommitBoundary`,
`Market/ShieldedRingEndpointDescriptor`, `Deos/SettleEscrowSatWideDescriptor`). Its docstring calls it
"the EXACT analogue of `Poseidon2SpongeCR`" — which `HashFloorHonesty.poseidon2SpongeCR_false_babyBear`
had ALREADY proved FALSE. The analogy was exact; the conclusion did not travel.
`VacuitySweepTeeth.poseidon2WideCR_false_babyBear` refutes it at the deployed width-8 BabyBear squeeze.

The consumers `chainFrom8_inj` / `wireCommitR8_binds` peeled the chain from the OUTSIDE in, applying
`hCR` at each step. The honest re-grounding must therefore WALK the chain and LOCATE the colliding
step — `chainCollFind` is that walk, as a function.

⚑ **§3.1/§3.2 MOVED.** `IsCollW`, `chainCollFind`(`_spec`), `wireCommit8Find`(`_spec`) now live in
`Emit/EffectVmEmitRotationR`, beside the commitment they are about. They had to move when the false
`Poseidon2WideCR` carrier was DELETED: the deployed keystone there is now
`wireCommitR8_binds_or_collides`, stated UNCONDITIONALLY in terms of the extractor, so the extractor
cannot live in a file that imports it. They are re-opened below. §3.3 onward is unchanged — it prices
the residual probabilistically, which is the part a game, not an extractor, has to do. -/

/-! ### §3.3 — the deployed wide permutation, as a KEYED family. -/

/-- **THE DEPLOYED WIDE PERMUTATION, KEYED — carrying NO CR field.** The Rust
`poseidon2::single_perm_compress` at each domain-separation tag. `width8At` IS carried, and is NOT a
false floor: it is the deployed output-width contract (`single_perm_compress` reads `state[0..8]`),
SATISFIED by the real permutation — it is what keeps the carrier 8-wide throughout (the anti-laundering
invariant, no narrow intermediate). Only the INJECTIVITY claim is dropped, because only that one is
false. -/
structure WideKeyed where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The keyed wide permutation; at `deployedTag` this IS the Rust `single_perm_compress`. -/
  permWAt : Tag → List ℤ → List ℤ
  /-- The DEPLOYED, SATISFIED width contract: every squeeze is exactly 8 felts. Not a crypto floor. -/
  width8At : ∀ t, Poseidon2Width8 (permWAt t)
  /-- The specific tag the deployment computes at this use-site. -/
  deployedTag : Tag

/-- The DEPLOYED fixed wide permutation the prover actually computes. -/
def WideKeyed.deployedPermW (D : WideKeyed) : List ℤ → List ℤ := D.permWAt D.deployedTag

/-- **`wideFamily D`** — the deployed wide permutation lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. Input and output `List ℤ` (the argument list, and the 8 squeezed lanes). -/
def wideFamily (D : WideKeyed) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List ℤ
  Out := List ℤ
  H := fun _ t xs => D.permWAt t xs
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The DEPLOYED fixed permutation IS the family's instance at the deployed tag. -/
theorem deployedPermW_is_family_instance (D : WideKeyed) (n : ℕ) :
    D.deployedPermW = (wideFamily D).H n D.deployedTag := rfl

/-! ### §3.4 — the wire-commit break, as a first-class game. -/

/-- **THE `wireCommitR8` BREAK GAME.** The adversary is handed a sampled domain-separation tag and WINS
iff it outputs two claims `(limbs, iroot)` of EQUAL limb length that are DISTINCT yet carry the SAME
8-felt chained wire commitment — i.e. it breaks exactly `wireCommitR8_binds`, the genuine ~124-bit
binding the light client trusts. The equal-length side condition is the deployed one
(`wireCommitR8_binds`'s `hlen`: the rotated surface has a fixed limb count). -/
def wireCommitBreakGame (D : WideKeyed) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => (List ℤ × ℤ) × (List ℤ × ℤ)
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c =>
    c.1.1.length = c.2.1.length ∧ c.1 ≠ c.2 ∧
      wireCommitR8 (D.permWAt t) c.1.1 c.1.2 = wireCommitR8 (D.permWAt t) c.2.1 c.2.2
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine equivocation of the real
deployed faithful wire commitment. -/
theorem wireCommitBreakGame_wins_iff (D : WideKeyed) (l : ℕ) (t : D.Tag)
    (c : (List ℤ × ℤ) × (List ℤ × ℤ)) :
    (wireCommitBreakGame D).wins l t c ↔
      (c.1.1.length = c.2.1.length ∧ c.1 ≠ c.2 ∧
        wireCommitR8 (D.permWAt t) c.1.1 c.1.2 = wireCommitR8 (D.permWAt t) c.2.1 c.2.2) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A wire-commit equivocator becomes a `permW`-collision
finder by running the chain walk on its two claims. -/
def wireBreakToFinder (D : WideKeyed) (A : Adversary (wireCommitBreakGame D)) :
    Adversary (hashGame (wideFamily D)) where
  run := fun l t => let c := A.run l t; wireCommit8Find (D.permWAt t) c.1.1 c.1.2 c.2.1 c.2.2

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every tag the equivocator wins, the
extracted finder wins the `permW` collision game: `wireCommit8Find_spec` at the adversary's actual
output. The `(l, ir) ≠ (l', ir')` the extractor needs is the claim inequality, by `Prod.ext`. -/
theorem wire_wins_imp (D : WideKeyed) (A : Adversary (wireCommitBreakGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (wireCommitBreakGame D).wins l t (A.run l t)) :
    (hashGame (wideFamily D)).wins l t ((wireBreakToFinder D A).run l t) := by
  obtain ⟨hlen, hne, heq⟩ := hwin
  exact wireCommit8Find_spec (D.permWAt t) (D.width8At t) hlen
    (fun hc => hne (Prod.ext hc.1 hc.2)) heq

/-- **THE ADVANTAGE INEQUALITY.** The equivocator's advantage is at most the extracted `permW`-collision
finder's, at every parameter — over the SAME sampled tag space. -/
theorem wire_adv_le (D : WideKeyed) (A : Adversary (wireCommitBreakGame D)) (l : ℕ) :
    gameAdv (wireCommitBreakGame D) A l
      ≤ gameAdv (hashGame (wideFamily D)) (wireBreakToFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact wire_wins_imp D A l t ht

/-- **⚑ RE-GROUNDED `Emit.EffectVmEmitRotationR.wireCommitR8_binds` — from the WIDE permutation's
collision floor, VIA the reduction.**

Under the DEPLOYED `single_perm_compress`'s collision floor at the class `Eff`, a wire-commit
equivocator whose extracted finder is in that class has NEGLIGIBLE advantage: the faithful 8-felt
chained commitment pins the WHOLE limb list AND the iroot except with negligible probability. This is
the ~124-bit binding the light client trusts, restated on a hypothesis the deployed permutation does NOT
refute — and it is the one that carried SEVEN hypothesis uses across the wide emission lane, the
cap-open lane, the Market boundary and the Deos settle descriptors.

⚑ `hEff` is UNDISCHARGED — a PARAMETER, in the open (`FloorGames` §8). Priced by §3.6. -/
theorem wireCommitR8_binds_advantage_bound (D : WideKeyed)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (wireCommitBreakGame D))
    (hEff : Eff (wireBreakToFinder D A))
    (hCR : HashCRHardQuant (wideFamily D) Eff) :
    Negl (gameAdv (wireCommitBreakGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (wireCommitBreakGame D) A l).1)
    (wire_adv_le D A) (hCR _ hEff)

/-! ### §3.5 — the CANARY + the positive pole. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at ANOTHER finder.)** Only
`wire_adv_le` connects the EXTRACTED finder to the break game. Unwritable under the old free
`Poseidon2WideCR` hypothesis, where the seven consumers' hypothesis WAS their conclusion's ground. -/
example (D : WideKeyed) (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (wireCommitBreakGame D))
    (B : Adversary (hashGame (wideFamily D))) (hB : Eff B)
    (hCR : HashCRHardQuant (wideFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (wireCommitBreakGame D) A) := hCR B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** -/
theorem the_repaired_wire_bound_fires (D : WideKeyed)
    (Eff : Adversary (hashGame (wideFamily D)) → Prop)
    (A : Adversary (wireCommitBreakGame D))
    (hEff : Eff (wireBreakToFinder D A))
    (hCR : HashCRHardQuant (wideFamily D) Eff) :
    Negl (gameAdv (wireCommitBreakGame D) A) :=
  wireCommitR8_binds_advantage_bound D Eff A hEff hCR

/-! ### §3.6 — both poles of the wide floor, PROVED. -/

/-- **⚑ THE ⊤ POLE — the wide permutation's collision floor is FALSE at the REAL BabyBear parameters**,
routed through the sweep's OWN tooth (`VacuitySweepTeeth.poseidon2WideCR_false_babyBear`): an 8-lane
squeeze into bounded lanes has finite range, and `List ℤ` is infinite. The price of `hEff`, as a
theorem — and the exact refutation that killed `Poseidon2WideCR`. What the re-grounding buys is not a
floor the deployed permutation satisfies at ⊤ (no such floor exists — `FloorGames` §2); it is that the
residual is now ONE named parameter with both poles proved, instead of seven consumers silently
conditioned on a hypothesis the deployed hash refutes. -/
theorem wide_floor_top_false_babyBear (D : WideKeyed)
    (hb : ∀ (t : D.Tag) (xs : List ℤ), ∀ x ∈ D.permWAt t xs, 0 ≤ x ∧ x < babyBearP) :
    ¬ HashCRHardQuant (wideFamily D) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨([] : List ℤ)⟩ (fun l t => ?_)
  exact exists_collision_of_not_injective
    (widePerm_not_injective_babyBear (D.permWAt t) (D.width8At t) (hb t))

/-- **THE ⊥ POLE — vacuous.** -/
theorem wide_floor_bot_vacuous (D : WideKeyed) :
    HashCRHardQuant (wideFamily D) (fun _ => False) :=
  hashCRHardQuant_bot_vacuous _

/-! ## §4 — the DISCHARGED headlines: every binding keystone lands on the PROVED keyed-ROM floor.

§1–§3 each close with an `Eff`-parametric advantage bound carrying `hEff : Eff (extracted finder)`
in the open — the honest fixed-hash content, KEPT beside this section. §4 holds their DISCHARGED
successors. The `IsPolyTime` discharges that historically stood here (`node8_binds_from_polyTime`,
`leaf8_binds_from_polyTime`, `effectVmCommit_binds_all_from_polyTime`,
`wireCommitR8_binds_from_polyTime`) instantiated each collision floor at
`Eff := IsPolyTime (AnsSize)` — a floor class REFUTED at every fixed public hash
(`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`;
`Market.WideCommitBoundary.stateCommit_floor_polyTime_false_babyBear` proves it AT this very wire
break game's family): `IsPolyTime` prices answer SIZE, so a `Classical.choice` `.pure`-leaf
answering a fixed short collision of the fixed function is IN the class and wins with probability
`1`. No `Eff` repairs a fixed-hash game (`Crypto.RomBindingReduction`'s header). ALL FOUR are
DELETED, each in the same commit its successor landed:

  * `node8` / leaf → §4.1's `RomSuccessor` section (`node8_binds_rom` / `leaf8_binds_rom`, flat
    carriers over the chip's own tag space);
  * the cell commitment → §4.2's `RomSuccessorCommit4` (`effectVmCommit_binds_all_rom`: the
    TWO-CARRIER union bound over ONE family — `chained_rom_binds` — because WHICH inner `h4` call
    collides depends on the sampled oracle's answers);
  * the chained wire commitment → §4.4's `RomSuccessorWire` (`wireCommitR8_binds_rom`: the
    CHAIN-WALK extractor that re-walks both chains and PAYS its own queries — `romChained_binds`).

What remains of the cost-model era, kept deliberately: the proved OUTPUT-SIZE facts about the
fixed-hash extractors (`pack8_length`, §4.3's `wireCommit8Find_len_le` — facts about §1–§3's
extractors, still true of the deployed schedule), and the `_isPolyTime_inhabited` teeth, which pin
the REFUTED class strictly between the poles §1.4/§2.5/§3.6 price — so a reader can see the
refuted class was never `⊥` and the refutation was earned, not vacuous. -/

/-! ⚑ **STATUS OF THIS SECTION (2026-07-24): the repoint is COMPLETE — no `_from_polyTime`
discharge remains in this file.** Every successor is a LABELLED idealisation, never a derivation
(`RomCarrierSites` header): the sampled `H : Tag × Msg → Fin (2 ^ l)` idealises the deployed
Poseidon2 digest at an ASYMPTOTIC width — there is NO `l` at which `Fin (2 ^ l)` is the deployed
~31-bit BabyBear felt (the felt-width wound, said out loud). A `_binds_rom` proves binding in the
keyed-ROM model at that width, NOT any statement about the fixed deployed permutation; CR of a
fixed public function is a conjecture, not a Lean theorem. The fixed-hash residual is priced, per
family, by the ⊤/⊥ poles and the `Eff`-parametric advantage bounds kept beside it. -/

/-! ### §4.1 — the arity-16 chip: `node8` and the leaf. -/

/-- **THE CHIP COLLISION GAME'S ANSWER ENCODING** — the two claimed absorbed blocks, at their genuine
lengths. Concrete on purpose: the size measure belongs to the GAME (`CostAdversary` design commitment 4);
leaving it open would let a degenerate `sz := 0` make the reduction's output free again. -/
def chip8AnsSize (D : Chip8Keyed) : AnsSize (hashGame (chip8Family D)) :=
  fun _ (p : List ℤ × List ℤ) => p.1.length + p.2.length

/-- The deployed pack is exactly the two 8-felt children concatenated — the extractor's output size,
proved off `pack8` rather than assumed. -/
theorem pack8_length (l r : Digest8) : (pack8 l r).length = 16 := by
  simp [pack8]

/-- The deployed leaf block is exactly the seven `cap_root.rs` fields. -/
theorem leafFields_length (l : CapLeaf) : (leafFields l).length = 7 := rfl

/-! ### ⚑ THE DISCHARGED `node8`/leaf HEADLINES, ON THE PROVED KEYED-ROM FLOOR.

The `IsPolyTime` discharges that stood here (`node8_binds_from_polyTime`,
`leaf8_binds_from_polyTime`) carried `HashCRHardQuant (chip8Family D) (IsPolyTime …)` — the floor
class `Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` refutes (`IsPolyTime`
prices answer SIZE; a `Classical.choice` `.pure`-leaf answering a fixed short collision of the fixed
chip is in the class and wins with probability `1`), and no `Eff` repairs the fixed-hash game
(`Crypto.RomBindingReduction`'s header). DELETED. The successors land on a SAMPLED oracle keyed by
the chip's OWN tag space, where `KeyedRomFloor.keyedRom_hard` (the birthday bound) is a THEOREM.

⚑ THE MODELLING STEP, STATED: the deployed 8-felt chip digest is idealised as ONE `λ`-bit sampled
value `Fin (2 ^ l)` (no `l` coincides with the deployed ~248-bit 8-felt digest — the felt-width
discipline, said out loud); the message domain is the TRUNCATED deployed absorb schedule,
length-separated exactly as deployed: the 16-felt packed node block (`pack8 l r` — two 8-felt
children, `Fin.append`) and the 7-felt leaf block, domain-separated by constructor. The fixed-hash
content — §1/§2's `Eff`-parametric bounds with `hEff` in the open, the extractors, the poles —
stays untouched beside it. -/

section RomSuccessor

open Dregg2.Crypto.RomCarrierSites hiding babyBearP
open Dregg2.Crypto.RomBindingReduction

/-- The truncated chip messages: a packed two-child node block (16 range felts, the two 8-felt
children appended in order) or a 7-felt leaf block. -/
abbrev Chip8RomMsg : Type :=
  (Fin (8 + 8) → Fin Dregg2.Crypto.RomCarrierSites.babyBearP)
    ⊕ (Fin 7 → Fin Dregg2.Crypto.RomCarrierSites.babyBearP)

/-- The chip ROM family — keyed by the DEPLOYED chip's own tag space. -/
abbrev chip8RomFamily (D : Chip8Keyed) (tagDec : DecidableEq D.Tag) :
    Dregg2.Crypto.KeyedRomFloor.KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty (fun _ => Chip8RomMsg)
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inr (fun _ => ⟨0, by norm_num [Dregg2.Crypto.RomCarrierSites.babyBearP]⟩)⟩)

/-- **THE `node8` CARRIER** — commitment `H (t, inl (append l r))`: the node digest binds BOTH
ordered children. `Fin.append` is the `pack8` layout; its injectivity in the pair is the same
layout fact `pack8_inj` carries at the deployed lists. -/
def node8RomCarrier (D : Chip8Keyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (chip8RomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit)
    (fun _ => (Fin 8 → Fin Dregg2.Crypto.RomCarrierSites.babyBearP)
      × (Fin 8 → Fin Dregg2.Crypto.RomCarrierSites.babyBearP))
    (fun _ => inferInstance)
    (fun _ _ v => Sum.inl (Fin.append v.1 v.2))
    (fun _ _ a b h => by
      have happ : Fin.append a.1 a.2 = Fin.append b.1 b.2 := Sum.inl_injective h
      refine Prod.ext (funext fun i => ?_) (funext fun i => ?_)
      · have := congrFun happ (Fin.castAdd 8 i)
        rwa [Fin.append_left, Fin.append_left] at this
      · have := congrFun happ (Fin.natAdd 8 i)
        rwa [Fin.append_right, Fin.append_right] at this)

/-- **THE LEAF CARRIER** — commitment `H (t, inr leaf)`: the leaf digest binds all seven
`cap_root.rs` fields (the truncated `leafFields` block; identity embedding, injective on the nose —
`leafFields_inj`'s content at the truncated widths). -/
def leaf8RomCarrier (D : Chip8Keyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (chip8RomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit)
    (fun _ => Fin 7 → Fin Dregg2.Crypto.RomCarrierSites.babyBearP)
    (fun _ => inferInstance)
    (fun _ _ v => Sum.inr v)
    (fun _ _ _ _ h => Sum.inr_injective h)

/-- **⚑⚑ THE `node8` BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`node8_binds_from_polyTime`: every query-bounded forger that equivocates one node digest between
two DISTINCT ordered child pairs has NEGLIGIBLE advantage. NO floor hypothesis. -/
theorem node8_binds_rom (D : Chip8Keyed) (tagDec : DecidableEq D.Tag) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (chip8RomFamily D tagDec) (node8RomCarrier D tagDec)))
    (hA : RomCarrierEff (chip8RomFamily D tagDec) (node8RomCarrier D tagDec) Q A) :
    Negl (gameAdv (romCarrierGame (chip8RomFamily D tagDec) (node8RomCarrier D tagDec)) A) :=
  flatSite_binds D.Tag D.tagFintype tagDec D.tagNonempty _ _ _ _
    (node8RomCarrier D tagDec) Q hQ A hA

/-- **⚑⚑ THE LEAF BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`leaf8_binds_from_polyTime`. -/
theorem leaf8_binds_rom (D : Chip8Keyed) (tagDec : DecidableEq D.Tag) (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (chip8RomFamily D tagDec) (leaf8RomCarrier D tagDec)))
    (hA : RomCarrierEff (chip8RomFamily D tagDec) (leaf8RomCarrier D tagDec) Q A) :
    Negl (gameAdv (romCarrierGame (chip8RomFamily D tagDec) (leaf8RomCarrier D tagDec)) A) :=
  flatSite_binds D.Tag D.tagFintype tagDec D.tagNonempty _ _ _ _
    (leaf8RomCarrier D tagDec) Q hQ A hA

/-- **(TOOTH — the admitted refuter-shape is DEFANGED at the node carrier, not excluded.)** The
`0`-query constant answerer — the exact `IsPolyTime`-refuting shape — is IN the class, WINS at the
constant oracle on distinct child pairs, and is NEGLIGIBLE against the sampled oracle. -/
theorem node8Rom_constAnswer_defanged (D : Chip8Keyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (c : ∀ l, (node8RomCarrier D tagDec).Ctx l)
    (v w : ∀ l, (node8RomCarrier D tagDec).Val l) :
    RomCarrierEff (chip8RomFamily D tagDec) (node8RomCarrier D tagDec) Q
        (romCarrierAdv _ _ (constTripleComp _ _ c v w))
      ∧ Negl (gameAdv (romCarrierGame (chip8RomFamily D tagDec) (node8RomCarrier D tagDec))
        (romCarrierAdv _ _ (constTripleComp _ _ c v w)))
      ∧ ∀ l, v l ≠ w l →
        0 < gameAdv (romCarrierGame (chip8RomFamily D tagDec) (node8RomCarrier D tagDec))
          (romCarrierAdv _ _ (constTripleComp _ _ c v w)) l :=
  ⟨constTriple_in_eff _ _ c v w Q,
    constTriple_binds _ _ c v w Q hQ
      (flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty _ _ _ _),
    fun l hvw => constTriple_gameAdv_pos _ _ c v w l hvw⟩

/-- **(TOOTH — a non-negligible node forger is OUTSIDE the class.)** -/
theorem node8Rom_nonNegl_forger_excluded (D : Chip8Keyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ)
    (hQ : Dregg2.Crypto.ConcreteSecurity.PolyBounded
      (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (chip8RomFamily D tagDec) (node8RomCarrier D tagDec)))
    (hnn : ¬ Negl (gameAdv
      (romCarrierGame (chip8RomFamily D tagDec) (node8RomCarrier D tagDec)) A)) :
    ¬ RomCarrierEff (chip8RomFamily D tagDec) (node8RomCarrier D tagDec) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ
    (flatFamily_card_R D.Tag D.tagFintype tagDec D.tagNonempty _ _ _ _) A hnn

end RomSuccessor

/-- **(TOOTH — the class the chip floor is instantiated at is NOT EMPTY.)** `HashCRHardQuant (chip8Family
D) (IsPolyTime (chip8AnsSize D))` is not the vacuous `Eff := ⊥` floor: the constant finder is in the
class, because the answer it writes has size `0` under the game's own encoding. Together with
`CostAdversary.bruteForce_not_polyTime` (the ⊤-collapse witness is excluded) this pins the instantiated
floor strictly between §1.4's two poles. -/
theorem chip8Floor_isPolyTime_inhabited (D : Chip8Keyed) :
    IsPolyTime (chip8AnsSize D)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [chip8AnsSize]⟩

/-! ### §4.2 — the arity-4 cell commitment. -/

/-- **THE `h4` COLLISION GAME'S ANSWER ENCODING** — the two claimed quads, four felts each. -/
def h4AnsSize (D : H4Keyed) : AnsSize (hashGame (h4Family D)) :=
  fun _ (_ : (ℤ × ℤ × ℤ × ℤ) × (ℤ × ℤ × ℤ × ℤ)) => 8

/-- **(TOOTH — the `h4` floor's class is NOT EMPTY.)** -/
theorem h4Floor_isPolyTime_inhabited (D : H4Keyed) :
    IsPolyTime (h4AnsSize D)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ)),
                     ((0 : ℤ), (0 : ℤ), (0 : ℤ), (0 : ℤ))))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨8, 0, fun _ _ => by simp [h4AnsSize]⟩

/-! ### ⚑ THE DISCHARGED CELL-COMMITMENT HEADLINE, ON THE PROVED KEYED-ROM FLOOR.

The `IsPolyTime` discharge that stood here (`effectVmCommit_binds_all_from_polyTime`) carried
`HashCRHardQuant (h4Family D) (IsPolyTime …)` — a floor class the `Classical.choice`
short-collision answerer refutes at the deployed `hash_4_to_1`
(`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` is the proved shape:
`IsPolyTime` prices answer SIZE, and a `.pure`-leaf answering a fixed short collision of the fixed
compress is in the class and wins with probability `1`), and no `Eff` repairs the fixed-hash game
(`Crypto.RomBindingReduction`'s header). DELETED. The successor lands on a SAMPLED oracle keyed by
the compress's OWN tag space, where `KeyedRomFloor.keyedRom_hard` (the birthday bound) is a
THEOREM.

⚑ THE MODELLING STEP, STATED (not smuggled): the deployed BabyBear digest is idealised as ONE
`λ`-bit sampled value `Fin (2 ^ l)` — there is NO `l` at which that is the deployed ~31-bit felt
(the felt-width wound, said out loud). The message domain is the TRUNCATED deployed absorb
schedule, domain-separated by constructor inside ONE family: an INNER quad (four BabyBear-range
felts — `commit4Find`'s head/body quads `(bl, bh, n, f0)` / `(f1..f4)` / `(f5..f7, cr)` at the
truncated widths) or the OUTER absorb (the three inner digests plus the authority-residue felt —
the fourth outer slot is a PAYLOAD felt, not an inner hash: the deployed
`h4 i1 i2 i3 rd` shape, exactly). The two-level nest is genuinely re-absorbed: the oracle appears
INSIDE the win relation, which is what §2's fixed `commit4Find` trace could not say in the ROM —
WHICH inner `h4` call collides depends on the sampled oracle's answers, so a fixed `mapOut` cannot
pick it. The successor splits into an INNER and an OUTER carrier over one family and takes the
UNION bound (`chained_rom_binds`) — the landed
`EffectVmRowCommitReduction.narrowRow_binds_rom` shape, re-keyed from `SpongeKeyed` to the bare
`H4Keyed` tag space.

⚑ WHAT THE ROM LAYER DOES NOT CARRY: §2's fixed-hash content — the break game over real
`Claim13`s, the tree-trace extractor, the `Eff`-parametric
`effectVmCommit_binds_all_advantage_bound` with `hEff` in the open, and both poles §2.5 prices —
stays untouched beside it. CR of the fixed public `hash_4_to_1` remains a conjecture, not a Lean
theorem. -/

section RomSuccessorCommit4

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomCarrierSites hiding babyBearP
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- A truncated inner quad: four BabyBear-range felts — the deployed `commit4Find` head/body quad
shape at the truncated widths. -/
abbrev Quad4 : Type := Fin 4 → Fin Dregg2.Crypto.RomCarrierSites.babyBearP

/-- **THE ORACLE MESSAGE DOMAIN** — the deployed two-level absorb schedule, domain-separated by
constructor: `inl` an inner quad, `inr` the OUTER absorb (three inner digests + the
authority-residue felt). -/
abbrev Commit4RomMsg (l : ℕ) : Type :=
  Quad4 ⊕ ((Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))
    × Fin Dregg2.Crypto.RomCarrierSites.babyBearP)

/-- The cell-commitment keyed ROM family — keyed by the DEPLOYED compress's own tag space. -/
def commit4RomFamily (D : H4Keyed) (tagDec : DecidableEq D.Tag) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty Commit4RomMsg
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (fun _ => ⟨0, babyBearP_pos⟩)⟩)

theorem commit4RomFamily_card_R (D : H4Keyed) (tagDec : DecidableEq D.Tag) (l : ℕ) :
    letI := (commit4RomFamily D tagDec).rFin l
    Fintype.card ((commit4RomFamily D tagDec).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- The truncated 13-limb payload — the three inner quads and the authority-residue felt
(`Claim13`'s limbs distributed into the deployed quad decomposition, at the truncated widths). -/
abbrev Commit4RomVal : Type :=
  (Quad4 × Quad4 × Quad4) × Fin Dregg2.Crypto.RomCarrierSites.babyBearP

/-- The inner carrier — binds one absorbed quad. The embedding is by constructor, injective on
the nose. -/
def commit4InnerCarrier (D : H4Keyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (commit4RomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => Quad4)
    (fun _ => inferInstance) (fun _ _ v => Sum.inl v)
    (fun _ _ _ _ h => Sum.inl_injective h)

/-- The outer carrier — binds the outer absorb (three inner digests + the residue felt). -/
def commit4OuterCarrier (D : H4Keyed) (tagDec : DecidableEq D.Tag) :
    RomCarrier (commit4RomFamily D tagDec) :=
  taggedCarrier _ (fun _ => Unit)
    (fun l => (Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))
      × Fin Dregg2.Crypto.RomCarrierSites.babyBearP)
    (fun _ => inferInstance) (fun _ _ v => Sum.inr v)
    (fun _ _ _ _ h => Sum.inr_injective h)

/-- **THE DEPLOYED NESTED COMMITMENT AT THE SAMPLED ORACLE** — the ROM restatement of
`effectVmCommit h4 … = h4 (h4 bl bh n f0) (h4 f1 f2 f3 f4) (h4 f5 f6 f7 cr) rd`, with the three
inner digests genuinely re-absorbed by the outer query. -/
def commit4RomCommit (D : H4Keyed) (tagDec : DecidableEq D.Tag) (l : ℕ)
    (H : (commit4RomFamily D tagDec).toRomFamily.D l
      → (commit4RomFamily D tagDec).toRomFamily.R l)
    (t : D.Tag) (v : Commit4RomVal) : (commit4RomFamily D tagDec).toRomFamily.R l :=
  H (t, Sum.inr ((H (t, Sum.inl v.1.1), H (t, Sum.inl v.1.2.1), H (t, Sum.inl v.1.2.2)), v.2))

/-- **THE CELL-COMMITMENT ROM FORGERY** — two DISTINCT truncated 13-limb payloads, one nested
deployed commitment: `commit4BreakGame`'s commitment content at the sampled oracle. -/
def effectVmCommitRomForgery (D : H4Keyed) (tagDec : DecidableEq D.Tag) :
    RomForgery (commit4RomFamily D tagDec) where
  Ans := fun _ => D.Tag × Commit4RomVal × Commit4RomVal
  wins := fun l H a =>
    a.2.1 ≠ a.2.2
      ∧ commit4RomCommit D tagDec l H a.1 a.2.1 = commit4RomCommit D tagDec l H a.1 a.2.2
  winsDec := fun l _ _ => by
    letI := ((commit4RomFamily D tagDec).toRomFamily).rDec l
    exact instDecidableAnd

/-- The inner-leg selection — the first differing quad (pure post-map, no queries added). If all
three agree the payloads differ only at the residue felt, which the OUTER leg then catches (the
felt sits in the outer message). The fallback answer is the (equal) head quads — never a win,
harmlessly. -/
def commit4InnerSelect (D : H4Keyed) (tagDec : DecidableEq D.Tag) (l : ℕ)
    (a : (effectVmCommitRomForgery D tagDec).Ans l) :
    (commit4InnerCarrier D tagDec).Ctx l
      × (commit4InnerCarrier D tagDec).Val l × (commit4InnerCarrier D tagDec).Val l :=
  let v := a.2.1
  let w := a.2.2
  if v.1.1 ≠ w.1.1 then ((a.1, ()), v.1.1, w.1.1)
  else if v.1.2.1 ≠ w.1.2.1 then ((a.1, ()), v.1.2.1, w.1.2.1)
  else ((a.1, ()), v.1.2.2, w.1.2.2)

/-- The outer-leg extraction — run the forger, then RE-QUERY the six inner points and answer with
the two outer messages (`bindComp`, budget `Q + 6`). -/
def commit4OuterComp (D : H4Keyed) (tagDec : DecidableEq D.Tag)
    (M : ∀ l, OracleComp ((commit4RomFamily D tagDec).toRomFamily.D l)
      ((commit4RomFamily D tagDec).toRomFamily.R l)
      ((effectVmCommitRomForgery D tagDec).Ans l)) :
    Dregg2.Crypto.RomBindingReduction.RomCarrierComp (commit4RomFamily D tagDec)
      (commit4OuterCarrier D tagDec) :=
  fun l => OracleComp.bindComp (M l) (fun a =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.1) (fun d₁ =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.2.1) (fun d₂ =>
    OracleComp.query (a.1, Sum.inl a.2.1.1.2.2) (fun d₃ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.1) (fun e₁ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.2.1) (fun e₂ =>
    OracleComp.query (a.1, Sum.inl a.2.2.1.2.2) (fun e₃ =>
    OracleComp.pure ((a.1, ()), ((d₁, d₂, d₃), a.2.1.2), ((e₁, e₂, e₃), a.2.2.2)))))))))

/-- **⚑⚑ THE CELL-COMMITMENT BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the
deleted `effectVmCommit_binds_all_from_polyTime`: a query-bounded forger of the deployed nested
cell commitment has NEGLIGIBLE advantage. Outer messages differ (which covers a
residue-felt-only disagreement, since the felt sits in the outer absorb) → outer-carrier win,
budget `Q + 6`; outer messages agree → the first differing quad is an inner collision, budget
`Q`. Each leg dies by the birthday floor. NO floor hypothesis. -/
theorem effectVmCommit_binds_all_rom (D : H4Keyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmCommitRomForgery D tagDec).game)
    (hA : RomForgeryEff (commit4RomFamily D tagDec) (effectVmCommitRomForgery D tagDec) Q A) :
    Negl (gameAdv (effectVmCommitRomForgery D tagDec).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine chained_rom_binds (effectVmCommitRomForgery D tagDec)
    (commit4InnerCarrier D tagDec) (commit4OuterCarrier D tagDec)
    Q (fun l => Q l + 2 + 2 + 2) hQ
    (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ (polyBounded_sq_add_two _ hQ)))
    (commit4RomFamily_card_R D tagDec) A
    (romCarrierAdv _ _ (fun l => OracleComp.mapOut (commit4InnerSelect D tagDec l) (M l)))
    (romCarrierAdv _ _ (commit4OuterComp D tagDec M))
    ?_
    ⟨fun l => OracleComp.mapOut (commit4InnerSelect D tagDec l) (M l),
      fun l => OracleComp.mapOut_queryBounded _ (hM l), fun _ _ => rfl⟩
    ⟨commit4OuterComp D tagDec M,
      fun l => (OracleComp.bindComp_queryBounded (hM l)
        (fun a => QueryBounded.query 5 _ _ (fun _ => QueryBounded.query 4 _ _
          (fun _ => QueryBounded.query 3 _ _ (fun _ => QueryBounded.query 2 _ _
          (fun _ => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
          (fun _ => QueryBounded.pure 0 _)))))))).mono
        (by show Q l + 6 ≤ Q l + 2 + 2 + 2; omega),
      fun _ _ => rfl⟩
  intro l H hwin
  have hArun : A.run l H = (M l).eval H := hrun l H
  set a := A.run l H with ha
  obtain ⟨hne, heq⟩ := hwin
  have hB₁run : (romCarrierAdv _ _
      (fun l => OracleComp.mapOut (commit4InnerSelect D tagDec l) (M l))).run l H
      = commit4InnerSelect D tagDec l a := by
    show (OracleComp.mapOut (commit4InnerSelect D tagDec l) (M l)).eval H = _
    erw [OracleComp.mapOut_eval, ← hArun]
  have hB₂run : (romCarrierAdv _ _ (commit4OuterComp D tagDec M)).run l H
      = ((a.1, ()),
          ((H (a.1, Sum.inl a.2.1.1.1), H (a.1, Sum.inl a.2.1.1.2.1),
            H (a.1, Sum.inl a.2.1.1.2.2)), a.2.1.2),
          ((H (a.1, Sum.inl a.2.2.1.1), H (a.1, Sum.inl a.2.2.1.2.1),
            H (a.1, Sum.inl a.2.2.1.2.2)), a.2.2.2)) := by
    show (commit4OuterComp D tagDec M l).eval H = _
    unfold commit4OuterComp
    erw [OracleComp.bindComp_eval, ← hArun]
    rfl
  by_cases hT :
      (((H (a.1, Sum.inl a.2.1.1.1), H (a.1, Sum.inl a.2.1.1.2.1),
         H (a.1, Sum.inl a.2.1.1.2.2)), a.2.1.2)
        : (Fin (2 ^ l) × Fin (2 ^ l) × Fin (2 ^ l))
          × Fin Dregg2.Crypto.RomCarrierSites.babyBearP)
      = ((H (a.1, Sum.inl a.2.2.1.1), H (a.1, Sum.inl a.2.2.1.2.1),
          H (a.1, Sum.inl a.2.2.1.2.2)), a.2.2.2)
  · -- the outer messages AGREE: all three inner digests collide and the residue felts are
    -- equal, so some quad differs — an inner-carrier equivocation.
    refine Or.inl ?_
    rw [hB₁run]
    have h1 : H (a.1, Sum.inl a.2.1.1.1) = H (a.1, Sum.inl a.2.2.1.1) :=
      congrArg (fun p => p.1.1) hT
    have h2 : H (a.1, Sum.inl a.2.1.1.2.1) = H (a.1, Sum.inl a.2.2.1.2.1) :=
      congrArg (fun p => p.1.2.1) hT
    have h3 : H (a.1, Sum.inl a.2.1.1.2.2) = H (a.1, Sum.inl a.2.2.1.2.2) :=
      congrArg (fun p => p.1.2.2) hT
    have hd : a.2.1.2 = a.2.2.2 := congrArg (fun p => p.2) hT
    unfold commit4InnerSelect
    by_cases hA1 : a.2.1.1.1 ≠ a.2.2.1.1
    · rw [if_pos hA1]
      exact ⟨hA1, h1⟩
    · rw [if_neg hA1]
      by_cases hB1 : a.2.1.1.2.1 ≠ a.2.2.1.2.1
      · rw [if_pos hB1]
        exact ⟨hB1, h2⟩
      · rw [if_neg hB1]
        push_neg at hA1 hB1
        have hC1 : a.2.1.1.2.2 ≠ a.2.2.1.2.2 := by
          intro hc
          apply hne
          exact Prod.ext (Prod.ext hA1 (Prod.ext hB1 hc)) hd
        exact ⟨hC1, h3⟩
  · -- the outer messages DIFFER — an outer-carrier equivocation, witnessed by the re-queried
    -- inner digests.
    refine Or.inr ?_
    rw [hB₂run]
    exact ⟨hT, heq⟩

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage, and the admitted refuter-shape is
DEFANGED.)** The `0`-query constant answerer on two distinct payloads is in `RomForgeryEff` at
every budget; at the constant oracle both nested commitments collapse, so it WINS there (positive
advantage); and `effectVmCommit_binds_all_rom` applies to it — NEGLIGIBLE advantage. The exact
`IsPolyTime`-refuting shape, admitted and defanged, dying at this layer. -/
theorem commit4Rom_constAnswer_defanged (D : H4Keyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (t₀ : D.Tag) (v w : Commit4RomVal) (hvw : v ≠ w) :
    ∃ A, RomForgeryEff (commit4RomFamily D tagDec) (effectVmCommitRomForgery D tagDec) Q A
      ∧ Negl (gameAdv (effectVmCommitRomForgery D tagDec).game A)
      ∧ ∀ l, 0 < gameAdv (effectVmCommitRomForgery D tagDec).game A l := by
  refine ⟨⟨fun _ _ => (t₀, v, w)⟩,
    ⟨fun _ => OracleComp.pure (t₀, v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩,
    effectVmCommit_binds_all_rom D tagDec Q hQ _
      ⟨fun _ => OracleComp.pure (t₀, v, w), fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩,
    fun l => ?_⟩
  obtain ⟨r₀⟩ := ((commit4RomFamily D tagDec).toRomFamily).rNe l
  refine @winProb_pos_of_witness _
    (((effectVmCommitRomForgery D tagDec).game).instFin l) _ (fun _ => r₀) ?_
  exact (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ l _).mpr ⟨hvw, rfl⟩

/-- **(TOOTH — a non-negligible cell-commitment forger is OUTSIDE the class.)** The refutation
strategy that killed the `IsPolyTime` floor cannot produce a member of this one. -/
theorem commit4Rom_nonNegl_forger_excluded (D : H4Keyed) (tagDec : DecidableEq D.Tag)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (effectVmCommitRomForgery D tagDec).game)
    (hnn : ¬ Negl (gameAdv (effectVmCommitRomForgery D tagDec).game A)) :
    ¬ RomForgeryEff (commit4RomFamily D tagDec) (effectVmCommitRomForgery D tagDec) Q A :=
  fun hA => hnn (effectVmCommit_binds_all_rom D tagDec Q hQ A hA)

end RomSuccessorCommit4

/-! ### §4.3 — the wide chained wire commitment: the chain walk's output is BOUNDED.

The wire extractor is the only one in this file that is not a fixed-width reshape: `wireCommit8Find`
WALKS the two chains. Its output is nevertheless a CONSTANT `≤ 22` felts, because every value the walk
can return is a carrier (width `8`, the deployed squeeze) or a carrier plus one body block (`≤ 3`).
Proved here beside the extractor's own advantage bound. (The `IsPolyTime` discharge these bounds once
served is DELETED — that class is refuted; §4.4's `RomSuccessorWire` is the discharged successor —
but the bounds remain true facts of §3's fixed-hash extractor and of the deployed schedule.) -/

/-- Every `chunk31` block is at most three limbs wide (the deployed body arity is `carrier ‖ 3`). -/
theorem chunk31_len_le : ∀ (xs : List ℤ) (c : List ℤ), c ∈ chunk31 xs → c.length ≤ 3
  | a :: b :: d :: rest, c, hc => by
      simp only [chunk31, List.mem_cons] at hc
      rcases hc with h | h
      · subst h; simp
      · exact chunk31_len_le rest c h
  | [a, b], c, hc => by
      simp only [chunk31, List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with h | h <;> subst h <;> simp
  | [a], c, hc => by
      simp only [chunk31, List.mem_cons, List.not_mem_nil, or_false] at hc
      subst hc; simp
  | [], c, hc => by simp [chunk31] at hc

/-- **THE CHAIN WALK RETURNS BOUNDED LISTS.** Every value `chainCollFind` can return is either a carrier
(width `8`, since `permW` squeezes eight felts) or a carrier concatenated with one body block (`≤ 3`), so
at most `11` felts. This is what makes the wire→collision reduction's OUTPUT SIZE a proved constant
instead of an assumption. -/
theorem chainCollFind_len_le (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW) :
    ∀ (cs cs' : List (List ℤ)) (acc acc' : List ℤ),
      acc.length ≤ 8 → acc'.length ≤ 8 →
      (∀ c ∈ cs, c.length ≤ 3) → (∀ c ∈ cs', c.length ≤ 3) →
      (chainCollFind permW acc cs acc' cs').1.length ≤ 11
        ∧ (chainCollFind permW acc cs acc' cs').2.length ≤ 11 := by
  intro cs
  induction cs with
  | nil =>
      intro cs' acc acc' ha ha' _ _
      have hnil : chainCollFind permW acc [] acc' cs' = (acc, acc') := by cases cs' <;> rfl
      rw [hnil]
      refine ⟨?_, ?_⟩
      · show acc.length ≤ 11; omega
      · show acc'.length ≤ 11; omega
  | cons c ds ih =>
      intro cs' acc acc' ha ha' hcs hcs'
      cases cs' with
      | nil =>
          have hnil : chainCollFind permW acc (c :: ds) acc' [] = (acc, acc') := rfl
          rw [hnil]
          refine ⟨?_, ?_⟩
          · show acc.length ≤ 11; omega
          · show acc'.length ≤ 11; omega
      | cons c' ds' =>
          by_cases hif : permW (acc ++ c) = permW (acc' ++ c') ∧ (acc ++ c) ≠ (acc' ++ c')
          · rw [chainCollFind, if_pos hif]
            have h1 := hcs c (by simp)
            have h2 := hcs' c' (by simp)
            exact ⟨by simp only [List.length_append]; omega,
                   by simp only [List.length_append]; omega⟩
          · rw [chainCollFind, if_neg hif]
            exact ih ds' (permW (acc ++ c)) (permW (acc' ++ c'))
              (le_of_eq (hW _)) (le_of_eq (hW _))
              (fun x hx => hcs x (List.mem_cons_of_mem _ hx))
              (fun x hx => hcs' x (List.mem_cons_of_mem _ hx))

/-- **⚑ THE WIRE→COLLISION EXTRACTOR DOES NOT BLOW UP ITS INPUT** — it returns at most `11 + 11` felts,
a CONSTANT, whichever branch it takes. Proved, not assumed; this is the output-size obligation the cost
model's `reshape`-leaf charge creates, discharged. -/
theorem wireCommit8Find_len_le (permW : List ℤ → List ℤ) (hW : Poseidon2Width8 permW)
    (l : List ℤ) (ir : ℤ) (l' : List ℤ) (ir' : ℤ) :
    (wireCommit8Find permW l ir l' ir').1.length
      + (wireCommit8Find permW l ir l' ir').2.length ≤ 22 := by
  have hchunks : ∀ (xs : List ℤ) (z : ℤ) (c : List ℤ),
      c ∈ chunk31 xs ++ [[z, 0, 0]] → c.length ≤ 3 := by
    intro xs z c hc
    rcases List.mem_append.mp hc with h | h
    · exact chunk31_len_le xs c h
    · simp only [List.mem_singleton] at h; subst h; simp
  by_cases hif : IsCollW permW (chainCollFind permW (permW (l.take 4))
      (chunk31 (l.drop 4) ++ [[ir, 0, 0]]) (permW (l'.take 4)) (chunk31 (l'.drop 4) ++ [[ir', 0, 0]]))
  · rw [wireCommit8Find, if_pos hif]
    have h := chainCollFind_len_le permW hW
      (chunk31 (l.drop 4) ++ [[ir, 0, 0]]) (chunk31 (l'.drop 4) ++ [[ir', 0, 0]])
      (permW (l.take 4)) (permW (l'.take 4))
      (le_of_eq (hW (l.take 4))) (le_of_eq (hW (l'.take 4)))
      (hchunks (l.drop 4) ir) (hchunks (l'.drop 4) ir')
    omega
  · rw [wireCommit8Find, if_neg hif]
    have h1 : (l.take 4).length ≤ 4 := List.length_take_le 4 l
    have h2 : (l'.take 4).length ≤ 4 := List.length_take_le 4 l'
    show (l.take 4).length + (l'.take 4).length ≤ 22
    omega

/-- **THE WIDE COLLISION GAME'S ANSWER ENCODING** — the two claimed preimages of the wide permutation. -/
def wideAnsSize (D : WideKeyed) : AnsSize (hashGame (wideFamily D)) :=
  fun _ (p : List ℤ × List ℤ) => p.1.length + p.2.length

/-- **(TOOTH — the wide floor's class is NOT EMPTY.)** -/
theorem wideFloor_isPolyTime_inhabited (D : WideKeyed) :
    IsPolyTime (wideAnsSize D)
      (idAdv (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ _ => (([] : List ℤ), ([] : List ℤ)))).toAdversary :=
  isPolyTime_inhabited _ _ ⟨0, 0, fun _ _ => by simp [wideAnsSize]⟩

/-! ### §4.4 — ⚑ THE DISCHARGED WIRE-COMMIT HEADLINE, ON THE PROVED KEYED-ROM FLOOR.

The `IsPolyTime` discharge that stood here (`wireCommitR8_binds_from_polyTime`) carried
`HashCRHardQuant (wideFamily D) (IsPolyTime …)` — the floor class
`Market.WideCommitBoundary.stateCommit_floor_polyTime_false_babyBear` PROVES FALSE at this very
family (the `Classical.choice` short-collision answerer is in the class and wins with probability
`1`), and no `Eff` repairs the fixed-hash game. DELETED. The successor is the CHAIN-WALK shape
(`Crypto.RomChainedReduction`): `wireCommitR8` is a chained absorption — the 4-limb head
`permW (l.take 4)`, then the `chunk31` 3-limb blocks each re-absorbing the previous 8-felt digest,
the iroot block `[ir, 0, 0]` last — and the colliding step of a forgery sits at an INTERIOR chain
position that depends on the sampled oracle's answers, so the extractor cannot be a post-map: it
must RE-WALK both chains, two queries per step, and PAY for them (`chainedFinder_in_romEff`,
budget `Q + 2·len + 2`).

⚑ THE MODELLING STEP, STATED (not smuggled): digests AND limbs are idealised at `Fin (2 ^ l)` —
there is NO `l` at which that is the deployed ~31-bit BabyBear felt (the felt-width wound). The
head/step encodings are the deployed fixed-width concatenation `acc ++ c` made type-level, so
their injectivity is a LAYOUT fact, never a hash claim. The chain-as-oracle-program weld to the
REAL `wireCommitR8` is already landed at `Market.WideCommitBoundary` §Q (`wireCommitComp_eval`:
the program's run at the deployed permutation IS `wireCommitR8`, step for step); the carrier below
is that schedule re-keyed to `WideKeyed`'s OWN tag space and generic in the block count `n` (the
break game §3.4 pins only EQUAL limb counts; `wireCommitRomCarrier_len_eq_schedule` welds `n` to
the deployed `chunk31 ++ [iroot]` schedule of any limb list). §3's fixed-hash content — the break
game over real limb lists, the walking extractor `wireCommit8Find`, the `Eff`-parametric
`wireCommitR8_binds_advantage_bound`, both poles §3.6 prices — stays untouched beside it. -/

section RomSuccessorWire

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomCarrierSites hiding babyBearP
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomChainedReduction
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- **THE ORACLE MESSAGE DOMAIN** — the deployed chained absorb schedule, head/step
domain-separated by constructor: `inl` the 4-limb head (`l.take 4`), `inr` a step input — the
previous 8-felt digest re-absorbed with the next 3-limb block (`acc ++ c` at the deployed fixed
widths, made type-level). -/
abbrev WireRomMsg (l : ℕ) : Type :=
  (Fin 4 → Fin (2 ^ l)) ⊕ (Fin (2 ^ l) × (Fin 3 → Fin (2 ^ l)))

/-- The wire keyed ROM family — keyed by the DEPLOYED wide permutation's own tag space. -/
def wireRomFamily (D : WideKeyed) (tagDec : DecidableEq D.Tag) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty WireRomMsg
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun _ => ⟨Sum.inl (fun _ => ⟨0, by positivity⟩)⟩)

theorem wireRomFamily_card_R (D : WideKeyed) (tagDec : DecidableEq D.Tag) (l : ℕ) :
    letI := (wireRomFamily D tagDec).rFin l
    Fintype.card ((wireRomFamily D tagDec).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE CHAINED WIRE CARRIER** — 4-limb head, `n` three-limb blocks, each step re-absorbing the
previous digest; the context is the shared domain-separation tag. Generic in the block count `n`
because §3.4's break game pins only EQUAL limb counts; the weld below pins `n` to the deployed
schedule of any concrete limb list. Same shape as the landed
`Market.WideCommitBoundary.stateCommitRomCarrier` (which fixes `n = 61` at the 184-limb payload). -/
def wireCommitRomCarrier (D : WideKeyed) (tagDec : DecidableEq D.Tag) (n : ℕ) :
    RomChainedCarrier (wireRomFamily D tagDec) where
  Ctx := fun _ => D.Tag
  Hd := fun l => Fin 4 → Fin (2 ^ l)
  Blk := fun l => Fin 3 → Fin (2 ^ l)
  len := fun _ => n
  hdDec := fun _ => inferInstance
  blkDec := fun _ => inferInstance
  encHd := fun _ c h => (c, Sum.inl h)
  encStep := fun _ c r b => (c, Sum.inr (r, b))
  encHd_inj := fun _ _ _ _ h => Sum.inl_injective (congrArg Prod.snd h)
  encStep_inj := fun _ _ r b r' b' h => by
    have h2 := Sum.inr_injective (congrArg Prod.snd h)
    exact ⟨congrArg Prod.fst h2, congrArg Prod.snd h2⟩

/-- **THE SCHEDULE WELD** — at `n = |chunk31 (l.drop 4)| + 1` the carrier's chain length IS the
deployed block count of `wireCommitR8`'s absorption schedule (`chunk31` chunks + the iroot block)
for a limb list of any length. -/
theorem wireCommitRomCarrier_len_eq_schedule (D : WideKeyed) (tagDec : DecidableEq D.Tag)
    (l : ℕ) (xs : List ℤ) (ir : ℤ) :
    (wireCommitRomCarrier D tagDec ((chunk31 (xs.drop 4)).length + 1)).len l
      = (chunk31 (xs.drop 4) ++ [[ir, 0, 0]]).length := by
  show (chunk31 (xs.drop 4)).length + 1 = (chunk31 (xs.drop 4) ++ [[ir, 0, 0]]).length
  simp

/-- **⚑⚑ THE WIRE-COMMIT BINDING, DISCHARGED ON THE PROVED FLOOR** — the successor of the deleted
`wireCommitR8_binds_from_polyTime`: a query-bounded chained forger against the wire schedule has
NEGLIGIBLE advantage — the chained commitment binds the head and EVERY block of its payload except
with negligible probability, over the sampled tag-separated oracle. Budget accounting: the
forger's `Q` plus the extractor's re-walk of both chains (`2·n + 2`). NO floor hypothesis —
`keyedRom_hard` (the birthday bound, a theorem) closes it through `romChained_binds`. -/
theorem wireCommitR8_binds_rom (D : WideKeyed) (tagDec : DecidableEq D.Tag) (n : ℕ)
    (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l =>
      (((Q l + (2 * n + 2) : ℕ) : ℝ) * ((Q l + (2 * n + 2) : ℕ) : ℝ) + 1)))
    (A : Adversary (romChainedGame (wireRomFamily D tagDec) (wireCommitRomCarrier D tagDec n)))
    (hA : RomChainedEff (wireRomFamily D tagDec) (wireCommitRomCarrier D tagDec n) Q A) :
    Negl (gameAdv (romChainedGame (wireRomFamily D tagDec)
      (wireCommitRomCarrier D tagDec n)) A) :=
  romChained_binds (wireRomFamily D tagDec) (wireCommitRomCarrier D tagDec n)
    Q (fun l => Q l + (2 * n + 2))
    (fun l => by show Q l + (2 * n + 2) ≤ Q l + (2 * n + 2); omega)
    hQ (wireRomFamily_card_R D tagDec) A hA

/-- **(TOOTH — the class is INHABITED and the admitted refuter-shape is DEFANGED.)** The
`0`-query fixed-answer forger is in `RomChainedEff` at every budget, and the binding applies to
it: the exact shape that wins with probability `1` against the fixed public permutation wins only
negligibly against the sampled oracle. -/
theorem wireCommitRom_fixedForger_defanged (D : WideKeyed) (tagDec : DecidableEq D.Tag)
    (n : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l =>
      (((Q l + (2 * n + 2) : ℕ) : ℝ) * ((Q l + (2 * n + 2) : ℕ) : ℝ) + 1)))
    (t₀ : ∀ _l : ℕ, D.Tag) (v v' : ∀ l, (wireCommitRomCarrier D tagDec n).Val l) :
    RomChainedEff (wireRomFamily D tagDec) (wireCommitRomCarrier D tagDec n) Q
        (romChainedAdv _ _ (fixedChainedComp _ _ t₀ v v'))
      ∧ Negl (gameAdv (romChainedGame (wireRomFamily D tagDec)
          (wireCommitRomCarrier D tagDec n))
          (romChainedAdv _ _ (fixedChainedComp _ _ t₀ v v'))) :=
  ⟨fixedChainedForger_in_eff _ _ Q t₀ v v',
    fixedChainedForger_negl (wireRomFamily D tagDec) (wireCommitRomCarrier D tagDec n)
      Q (fun l => Q l + (2 * n + 2))
      (fun l => by show Q l + (2 * n + 2) ≤ Q l + (2 * n + 2); omega)
      hQ (wireRomFamily_card_R D tagDec) t₀ v v'⟩

/-- **(TOOTH — the game is genuinely winnable.)** At the constant oracle any two distinct
payloads equivocate (the chain forgets its input once the digests agree), so the negligible
advantage is earned against a live event, not vacuously. -/
theorem wireCommitRom_game_winnable (D : WideKeyed) (tagDec : DecidableEq D.Tag) (n : ℕ)
    (l : ℕ) (hl : 1 ≤ l) :
    ∃ (H : (romChainedGame (wireRomFamily D tagDec)
        (wireCommitRomCarrier D tagDec n)).Inst l)
      (p : (romChainedGame (wireRomFamily D tagDec)
        (wireCommitRomCarrier D tagDec n)).Ans l),
      (romChainedGame (wireRomFamily D tagDec)
        (wireCommitRomCarrier D tagDec n)).wins l H p := by
  obtain ⟨t₀⟩ := D.tagNonempty
  have h2 : 1 < 2 ^ l := Nat.one_lt_two_pow_iff.mpr (by omega)
  have hpos : 0 < 2 ^ l := by positivity
  refine ⟨fun _ => (⟨0, hpos⟩ : Fin (2 ^ l)),
    (t₀,
     ((fun _ => (⟨0, hpos⟩ : Fin (2 ^ l))), fun _ _ => (⟨0, hpos⟩ : Fin (2 ^ l))),
     ((fun _ => (⟨1, h2⟩ : Fin (2 ^ l))), fun _ _ => (⟨0, hpos⟩ : Fin (2 ^ l)))), ?_⟩
  refine romChainedGame_win_at_const _ _ l _ _ _ ?_ _
  intro h
  have h0 : (⟨0, hpos⟩ : Fin (2 ^ l)) = ⟨1, h2⟩ := congrFun (congrArg Prod.fst h) 0
  simp [Fin.ext_iff] at h0

/-- **(TOOTH — a non-negligible wire forger is OUTSIDE the class.)** The `Classical.choice`
collision-answerer that refuted the deleted `IsPolyTime` floor cannot produce a member of this
class: were it inside, the binding would collapse its advantage. -/
theorem wireCommitRom_choiceForger_excluded (D : WideKeyed) (tagDec : DecidableEq D.Tag)
    (n : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l =>
      (((Q l + (2 * n + 2) : ℕ) : ℝ) * ((Q l + (2 * n + 2) : ℕ) : ℝ) + 1)))
    (A : Adversary (romChainedGame (wireRomFamily D tagDec) (wireCommitRomCarrier D tagDec n)))
    (hnn : ¬ Negl (gameAdv (romChainedGame (wireRomFamily D tagDec)
      (wireCommitRomCarrier D tagDec n)) A)) :
    ¬ RomChainedEff (wireRomFamily D tagDec) (wireCommitRomCarrier D tagDec n) Q A :=
  fun hA => hnn (wireCommitR8_binds_rom D tagDec n Q hQ A hA)

end RomSuccessorWire

/-! ## §5 — axiom-hygiene pins. -/

#assert_all_clean [
  pack8_length,
  leafFields_length,
  node8_binds_rom,
  leaf8_binds_rom,
  node8Rom_constAnswer_defanged,
  node8Rom_nonNegl_forger_excluded,
  chip8Floor_isPolyTime_inhabited,
  commit4RomFamily_card_R,
  effectVmCommit_binds_all_rom,
  commit4Rom_constAnswer_defanged,
  commit4Rom_nonNegl_forger_excluded,
  h4Floor_isPolyTime_inhabited,
  chunk31_len_le,
  chainCollFind_len_le,
  wireCommit8Find_len_le,
  wireRomFamily_card_R,
  wireCommitRomCarrier_len_eq_schedule,
  wireCommitR8_binds_rom,
  wireCommitRom_fixedForger_defanged,
  wireCommitRom_game_winnable,
  wireCommitRom_choiceForger_excluded,
  wideFloor_isPolyTime_inhabited
]

#assert_all_clean [
  hashCRHardQuant_top_false_of_compressing,
  hashCRHardQuant_bot_vacuous,
  exists_collision_of_not_injective,
  deployedChip_is_family_instance,
  node8BreakGame_wins_iff,
  node8_wins_imp,
  node8_adv_le,
  node8_injective_advantage_bound,
  leaf8_wins_imp,
  leaf8_adv_le,
  leaf8_injective_advantage_bound,
  the_repaired_node8_bound_fires,
  chip8_floor_top_false_babyBear,
  chip8_floor_bot_vacuous,
  compress4_not_injective_of_finite_range,
  compress4_not_injective_babyBear,
  deployedH4_is_family_instance,
  Claim13.ext',
  commit4BreakGame_wins_iff,
  commit4Find_spec,
  commit4_wins_imp,
  commit4_adv_le,
  effectVmCommit_binds_all_advantage_bound,
  the_repaired_commit4_bound_fires,
  h4_floor_top_false_babyBear,
  h4_floor_bot_vacuous,
  chainCollFind_spec,
  wireCommit8Find_spec,
  deployedPermW_is_family_instance,
  wireCommitBreakGame_wins_iff,
  wire_wins_imp,
  wire_adv_le,
  wireCommitR8_binds_advantage_bound,
  the_repaired_wire_bound_fires,
  wide_floor_top_false_babyBear,
  wide_floor_bot_vacuous
]

end Dregg2.Circuit.InjectiveFloorRegrounded

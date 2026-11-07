/-
# `Dregg2.Crypto.BeaconSlotRegrounded` — the `HonestSlotCR` consumers RE-GROUNDED off the
FALSE-AS-NAMED injective floor onto a REAL collision game carrying an explicit `Eff`.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `HonestSlotCR` site)

`RandomnessBeacon.HonestSlotCR b := ∀ rest c c', b.combine (c ::ₘ rest) = b.combine (c' ::ₘ rest) →
c = c'` is stated as **injectivity** of the honest slot. Fix `rest` and it IS
`Function.Injective (fun c => b.combine (c ::ₘ rest))` — a map `Ct → O` from the contribution type to
the beacon output. For the deployed hash-combine that map is COMPRESSING, so the floor is **FALSE at
deployed parameters by pigeonhole** (§1), and `honest_makes_unbiasable` /
`bias_breaks_honest_slot_cr` are **VACUOUSLY TRUE** there. `#assert_axioms` is blind: the proofs are
clean; the HYPOTHESIS is the flaw.

## ⚑ THE FALSITY HAS A DIFFERENT SHAPE HERE THAN AT ITS SIBLINGS — and being precise about why is
part of the repair.

`KeySetCR`, `Poseidon2SpongeCR` and `CompressionCR` are all refuted by the **counting core**
(`HashFloorHonesty.not_injective_of_finite_range`): their DOMAINS are structurally infinite (`List
Key`, `List ℤ`, `State × List ℤ`) and no assumption about the deployment is needed beyond a bounded
range. `HonestSlotCR` is NOT like that. With `rest` fixed its domain is `Ct` — ONE contribution, a
fixed-width value, not a list — and nothing makes `Ct` infinite. Forcing the infinitude core onto it
would be assuming a deployment nobody runs.

So the honest refutation is by **COMPRESSION**, not by infinitude:
`honestSlotCR_false_of_compressing` uses `Fintype.exists_ne_map_eq_of_card_lt` under
`Fintype.card O < Fintype.card Ct` — the SAME shape as
`HashFloorHonesty.hashCR_false_of_compressing`, and for the same reason: both carriers compress a
fixed-width input into a fixed-width digest, and `|O| < |Ct|` is the DEFINING property of that, not an
extra hypothesis. The infinite-`Ct` variant is stated too (`honestSlotCR_false_of_infinite_ct`), for
the unbounded-contribution deployment, via the counting core — but it is the secondary form here,
where at the siblings it is the primary one.

## ⚑ THE "NOT A BESPOKE CARRIER" DEFENSE DOES NOT RESCUE IT — and that is a real finding.

`RandomnessBeacon`'s header argues at length that `HonestSlotCR` is *"NOT bespoke: it is DISCHARGED by
the imported `HashCR` (`honestSlotCR_of_hashcr`) … so the honest slot bottoms out at the one named
hash carrier, the true floor, with no bespoke beacon carrier."* That is TRUE and it is NOT a defense.
`HashCR` is one of the FOUR floors `HashFloorHonesty` already proved FALSE at deployed parameters
(`hashCR_false_of_compressing`, its TOOTH 3). Bottoming out at a false floor is not grounding; it is
inheriting the emptiness one level down. §1 proves this rather than asserting it:
`honestSlotCR_discharge_hypothesis_is_false` refutes the very `HashCR cr` that
`honestSlotCR_of_hashcr` consumes, at a compressing multiset-hash — so BOTH the carrier and the
carrier it reduces to are unsatisfiable together, and the reduction between them transports nothing.

`sumBeacon_cr` gives FALSE COMFORT of exactly the shape `HashFloorHonesty`'s header predicts: it
satisfies the floor with `combine = Σ` over ALL of `ℤ` — an injective, NON-compressing "hash" (adding
a constant is a bijection). Toy witness satisfiable, real hash-combine false.

## The re-grounding (the `PreRotationKeySetRegrounded` pattern)

  * **§1 — FALSE AS NAMED**, by compression (primary) and by infinitude (secondary), plus the
    `HashCR`-bottoming-out finding, proved.
  * **§2 — the KEYED family.** `BeaconDeployment` bundles the deployed multiset hash-combine
    (`beaconOfHash`'s realization, the one `honestSlotCR_of_hashcr` is about) with its
    domain-separation tag space (the effective key). `multisetHashFamily` lifts it to a
    `HashFloorHonesty.KeyedHashFamily`; `deployed_combine_is_family_instance` pins FAITHFULNESS.
  * **§3 — the BEACON BIAS GAME.** A biasing adversary is a first-class λ-indexed adversary: handed a
    sampled tag, it outputs the adversarial contribution multiset `rest` and two DISTINCT honest
    contributions, and WINS iff the beacon output is the SAME — i.e. it ABSORBED the honest randomness
    and the honest contribution no longer moves the beacon. That IS `bias_breaks_honest_slot_cr`'s
    content, as a game.
  * **§4 — THE REDUCTION.** `biasToCollisionFinder` maps a biasing adversary to a multiset-hash
    collision finder by consing each honest contribution onto its own `rest`; `bias_wins_imp` proves
    win-preservation via `Multiset.cons_inj_left` — the pure cancellation fact
    `honestSlotCR_of_hashcr` already uses, now carrying the reduction instead of a false hypothesis.
    Note the adversary chooses `rest` per tag and the extractor follows it — the reduction is genuinely
    data-dependent, not a rename.
  * **§5 — the RE-GROUNDED CONSUMERS.** `honest_makes_unbiasable_advantage_bound` and
    `bias_breaks_honest_slot_cr_advantage_bound`: the Boolean "distinct honest contributions ALWAYS
    move the beacon" becomes "move it EXCEPT with negligible probability" — which is what a real
    collision-resistant combine can deliver, and what the FALSE injective floor was standing in for.

## ⚑ THE `Eff` PARAMETER IS THE WHOLE HONESTY, AND IT IS UNDISCHARGED

The sweep's load-bearing result (`FloorGames` §2, `hard_top_iff_solvableFrac_negl`): at the
UNRESTRICTED adversary class a game floor IS the existence floor, so it is FALSE wherever collisions
exist — and §1 proves they exist at the deployed combine. §7 instantiates both poles at THIS carrier:
`beaconSlot_floor_top_false_of_finite_out` (`Eff := ⊤` is FALSE at a bounded beacon output) and
`beaconSlot_floor_bot_vacuous` (`Eff := ⊥` is vacuous). So `Eff` is a PARAMETER, in the open, at every
use site: this tree has no cost model (`FloorGames` §8), and inventing a shallow imitation would be
another costume. Hiding the `Eff` dependence is the disease; naming it is the repair.

## Non-fake

The floor is REFUTABLE (`brokenBeacon_floor_top_false`: a combine that ignores the contributions has a
finder winning at every tag, advantage `1`) and the reduction is LOAD-BEARING (§6's canary). The OLD
`HonestSlotCR` consumers are KEPT untouched in `RandomnessBeacon`; siblings ADDED. `#assert_all_clean`;
no `sorry`, no fresh `axiom`.

## Coordination

This is the BEACON honest-slot lane. The sponge compression carrier is re-grounded in
`Crypto.SpongeCompressionRegrounded`; the pre-rotation key-set carrier in
`Apps.PreRotationKeySetRegrounded`. `Crypto.HashRandRefinement` consumes the same
`Multiset.cons_inj_left` shape against an injective `frameOutput` and is the next site for this
treatment.
-/
import Dregg2.Crypto.RandomnessBeacon
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.RomCarrierSites
import Mathlib.Data.Sym.Basic
import Mathlib.Data.Fintype.Vector

namespace Dregg2.Crypto.BeaconSlotRegrounded

open Dregg2.Crypto.RandomnessBeacon
  (Beacon HonestSlotCR bias_breaks_honest_slot_cr beaconOfHash)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.ProbCrypto (winProb winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable
   HashCRHardQuant hashCRHardQuant_top_of_injective)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED: the injective `HonestSlotCR` floor is refuted by a COMPRESSING combine.

⚑ Read the header: this carrier's falsity does NOT have the shape of its siblings'. With `rest` fixed
the honest slot is a map `Ct → O` between two fixed-width types, so the counting core has no infinite
domain to bite on. The honest refutation is `Fintype.exists_ne_map_eq_of_card_lt` under
`|O| < |Ct|` — which is not an extra hypothesis but the definition of a compressing combine. -/

/-- **⚑ TOOTH (the primary form) — `HonestSlotCR` is FALSE for any COMPRESSING combine.** If the
beacon output space is smaller than the contribution space — the defining property of a hash-combine,
and true of every real beacon (a 256-bit digest over contributions carrying more entropy than that, or
a BabyBear felt over anything at all) — then at EVERY fixed adversarial `rest`, two distinct honest
contributions give the same output, by pigeonhole. So the floor is not merely un-proven at the
deployed combine; it is provably FALSE there, and `honest_makes_unbiasable` /
`bias_breaks_honest_slot_cr` are vacuous at real parameters.

This is the SAME shape as `HashFloorHonesty.hashCR_false_of_compressing` (its TOOTH 3), and that is
not a coincidence: §1's last tooth shows the two carriers are false TOGETHER. -/
theorem honestSlotCR_false_of_compressing {Ct O : Type*} [Fintype Ct] [Fintype O]
    (b : Beacon Ct O) (rest : Multiset Ct) (hcard : Fintype.card O < Fintype.card Ct) :
    ¬ HonestSlotCR b := by
  obtain ⟨c, c', hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun c : Ct => b.combine (c ::ₘ rest)) hcard
  exact fun hCR => hne (hCR rest c c' heq)

/-- **THE COLLISION THE FALSITY EXHIBITS.** A compressing combine has, at every adversarial `rest`, a
genuine honest-slot collision — two DISTINCT honest contributions the beacon cannot tell apart. This
is the pigeonhole in the positive form the game floors below consume: it is what makes the `⊤`-class
floor false (§7), and therefore what makes the `Eff` parameter load-bearing rather than decorative. -/
theorem exists_honest_slot_collision_of_compressing {Ct O : Type*} [Fintype Ct] [Fintype O]
    (b : Beacon Ct O) (rest : Multiset Ct) (hcard : Fintype.card O < Fintype.card Ct) :
    ∃ p : Ct × Ct, p.1 ≠ p.2 ∧ b.combine (p.1 ::ₘ rest) = b.combine (p.2 ::ₘ rest) := by
  obtain ⟨c, c', hne, heq⟩ :=
    Fintype.exists_ne_map_eq_of_card_lt (fun c : Ct => b.combine (c ::ₘ rest)) hcard
  exact ⟨(c, c'), hne, heq⟩

/-- **(TOOTH — the SECONDARY form: unbounded contributions.)** If contributions are unbounded (`Ct`
infinite — an aggregated / variable-length contribution rather than a fixed-width one) while the
beacon output stays bounded, the counting core fires directly, exactly as at the siblings. Stated for
completeness: it is the same disease, reached by the argument that IS primary elsewhere. -/
theorem honestSlotCR_false_of_infinite_ct {Ct O : Type*} [Infinite Ct] (b : Beacon Ct O)
    (rest : Multiset Ct) (hfin : (Set.range (fun c : Ct => b.combine (c ::ₘ rest))).Finite) :
    ¬ HonestSlotCR b :=
  fun hCR => not_injective_of_finite_range _ hfin (fun c c' h => hCR rest c c' h)

/-- `Multiset Ct` is infinite whenever a contribution exists (`replicate n c` has card `n`). The fact
the `HashCR`-bottoming-out tooth below needs — and note what it says: the MULTISET domain of the
underlying hash IS infinite, even though the honest SLOT's domain need not be. That asymmetry is
exactly why this carrier and its floor are refuted by different arguments. -/
instance instInfiniteMultiset {Ct : Type*} [Nonempty Ct] : Infinite (Multiset Ct) :=
  Infinite.of_injective (fun n : ℕ => Multiset.replicate n (Classical.arbitrary Ct)) (by
    intro n m h
    have := congrArg Multiset.card h
    simpa using this)

/-- **⚑⚑ TOOTH — THE "IT BOTTOMS OUT AT THE STANDARD `HashCR`" DEFENSE FAILS, PROVED.**

`RandomnessBeacon`'s header rests on `honestSlotCR_of_hashcr`: `HonestSlotCR (beaconOfHash cr)` is
DISCHARGED from `HermineHintMLWE.HashCR cr`, so — the argument goes — the honest slot is not a bespoke
carrier, it bottoms out at the one standard hash floor. The discharge is real. The defense is not:
`HashCR cr` for a multiset-hash into a BOUNDED output is itself FALSE, by the counting core over the
infinite `Multiset Ct`. It is `HashFloorHonesty`'s own TOOTH 3, at the very `cr` this file's beacon is
built from.

So the reduction `honestSlotCR_of_hashcr` transports NOTHING at deployed parameters: it derives a
false conclusion from a false hypothesis, and both are vacuous. Bottoming out at a standard floor is
grounding only if the standard floor is satisfiable, and this one is not. That is the finding; this is
the proof of it. -/
theorem honestSlotCR_discharge_hypothesis_is_false {Ct O : Type*} [Nonempty Ct]
    (cr : CommitReveal Unit (Multiset Ct) O)
    (hfin : (Set.range (cr.H ())).Finite) : ¬ HashCR cr :=
  fun hCR => not_injective_of_finite_range (cr.H ()) hfin (fun w w' h => hCR () w w' h)

/-- **(TOOTH — the deployed form of the same.)** A beacon combine landing in a genuinely bounded
output type (a digest — a `Finite` type: every real one is) refutes the `HashCR` floor that
`honestSlotCR_of_hashcr` consumes. No bound, no modulus, no parameter: `Finite O` is the whole
hypothesis. -/
theorem honestSlotCR_discharge_hypothesis_is_false_of_finite_out {Ct O : Type*} [Nonempty Ct]
    [Finite O] (cr : CommitReveal Unit (Multiset Ct) O) : ¬ HashCR cr :=
  honestSlotCR_discharge_hypothesis_is_false cr (Set.toFinite _)

/-! ## §2 — the KEYED family: domain separation is the key.

The deployed combine is a FIXED unkeyed multiset hash; its effective key is the domain-separation tag
the beacon absorbs ahead of the contribution set (the standard keyed-from-unkeyed treatment). Modelling
that tag as the key is what stops the "hardcode a known collision" degeneracy that collapses an unkeyed
floor. The family is over `Multiset Ct` — the honest realization `beaconOfHash` uses — so the game is
about the very function `honestSlotCR_of_hashcr` reduces to. -/

/-- **The deployed beacon combine.** `hash t` is the tag-keyed multiset hash-combine
`H(t, c₁ ‖ … ‖ cₙ)` — the deployed fixed function at each domain-separation tag; `Tag` is the finite,
inhabited tag space the CR game samples; `deployedTag` is the tag the beacon computes at. -/
structure BeaconDeployment (Ct O : Type) where
  /-- The domain-separation tag space (the effective key the CR game samples). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The tag-keyed multiset hash-combine — the deployed fixed function at each tag. -/
  hash : Tag → Multiset Ct → O
  /-- Decidable equality on contributions (the game checks two honest reveals are distinct). -/
  ctDecEq : DecidableEq Ct
  /-- Contributions exist. -/
  ctNonempty : Nonempty Ct
  /-- Decidable equality on outputs (the game checks the beacon outputs agree). -/
  outDecEq : DecidableEq O
  /-- The specific domain-separation tag the beacon computes. -/
  deployedTag : Tag

/-- **The deployed BEACON at tag `t`** — literally `RandomnessBeacon.beaconOfHash`'s shape: the combine
IS the tag-keyed multiset hash. This is the object the abstract `Beacon`/`HonestSlotCR` is realized
at. -/
def BeaconDeployment.beacon {Ct O : Type} (D : BeaconDeployment Ct O) (t : D.Tag) : Beacon Ct O :=
  ⟨D.hash t⟩

/-- **`multisetHashFamily D`** — the deployed combine lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. This is the object the keyed collision floor `FloorGames.HashCRHardQuant` is
realized at for the real combine, and the game §4's reduction lands in. -/
def multisetHashFamily {Ct O : Type} (D : BeaconDeployment Ct O) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := Multiset Ct
  Out := O
  H := fun _ t cs => D.hash t cs
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := letI := D.ctDecEq; inferInstance
  outDecEq := D.outDecEq

/-- **FAITHFULNESS.** The deployed beacon's FIXED combine IS the keyed family's instance at the
deployed tag — a definitional equality, no idealization. So the CR game below is a game about the very
function the beacon computes. -/
theorem deployed_combine_is_family_instance {Ct O : Type} (D : BeaconDeployment Ct O) (n : ℕ) :
    (D.beacon D.deployedTag).combine = (multisetHashFamily D).H n D.deployedTag := rfl

/-- **THE OLD-FLOOR ⟹ NEW-FLOOR BRIDGE.** If the deployed combine were injective at every tag — the
`HashCR` shape `honestSlotCR_of_hashcr` consumes, the floor `HonestSlotCR` bottoms out at — it would
discharge `HashCRHardQuant (multisetHashFamily D) (fun _ => True)`, the collision floor at the
UNRESTRICTED adversary class (no collisions ⟹ every adversary's advantage `0`). So the OLD floor was
STRICTLY STRONGER than that — and, being FALSE at any bounded output (§1), it was an EMPTY hypothesis.

⚑ **`fun _ => True` is WRITTEN OUT in the conclusion, and it CORRECTS what this docstring used to
claim.** The conclusion was spelled `CollisionResistant (multisetHashFamily D)` by a `def` that hid the
adversary class; that `def` is DELETED, and with the class visible the old closing sentence — "nothing
is lost re-grounding; a false hypothesis is replaced by one a real combine can satisfy" — is FALSE of
THIS statement. §7's `beaconSlot_floor_top_false_of_finite_range` refutes the `⊤` class at a
range-bounded (i.e. real) combine, exactly as §1 refutes `HonestSlotCR`. The hypothesis a real combine
CAN satisfy is the floor at a restricted `Eff`, which is what §5's `_advantage_bound` keystones take;
this bridge only records that the old carrier implied even the `⊤` one. -/
theorem multisetHashFamily_CR_of_injective {Ct O : Type} (D : BeaconDeployment Ct O)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hash t)) :
    HashCRHardQuant (multisetHashFamily D) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (multisetHashFamily D) (fun _ t => hinj t)

/-- **THE OLD CARRIER FROM THE OLD FLOOR (`honestSlotCR_of_hashcr`, at this deployment).** The same
injectivity also gives `HonestSlotCR` at every tag, by `Multiset.cons_inj_left` — this is
`RandomnessBeacon`'s discharge, restated over the deployment so the two bridges sit side by side.
Both hypotheses are the same false object (§1); §4 replaces it with a reduction. -/
theorem honestSlotCR_of_injective {Ct O : Type} (D : BeaconDeployment Ct O)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hash t)) (t : D.Tag) :
    HonestSlotCR (D.beacon t) :=
  fun rest _ _ h => (Multiset.cons_inj_left rest).mp (hinj t h)

/-! ## §3 — the multiset COLLISION GAME and the BEACON BIAS GAME, as first-class objects. -/

/-- **THE MULTISET-COMBINE COLLISION GAME.** Instances are sampled domain-separation tags; the
adversary outputs two contribution multisets and WINS iff they are a GENUINE collision of the deployed
combine at that tag — distinct multisets, equal beacon output. This is the game the floor below
quantifies over, with an explicit adversary class. -/
def multisetCollisionGame {Ct O : Type} (D : BeaconDeployment Ct O) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => Multiset Ct × Multiset Ct
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2
  winsDec := fun _ t p => by
    letI := D.ctDecEq
    letI := D.outDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation unfolds, by `Iff.rfl`, to a genuine
collision of the real deployed combine. Not a docstring: the `Prop` itself. -/
theorem collisionGame_wins_iff {Ct O : Type} (D : BeaconDeployment Ct O) (n : ℕ) (t : D.Tag)
    (p : Multiset Ct × Multiset Ct) :
    (multisetCollisionGame D).wins n t p ↔ (p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2) :=
  Iff.rfl

/-- **⚑ THE BEACON BIAS GAME.** The adversary is handed a sampled domain-separation tag and outputs
its own adversarial contribution multiset `rest` — it committed first, so it chooses — together with
two DISTINCT honest contributions. It WINS iff the beacon output is the SAME on both: the honest
randomness was ABSORBED, the honest contribution no longer moves the beacon, and the adversary that
committed its part first has pinned the output.

That is exactly `bias_breaks_honest_slot_cr`'s content ("biasability is exactly a hash collision on the
honest slot") and the negation of `honest_makes_unbiasable`'s — as a game, with the problem IN the win
predicate rather than in a docstring. Note the adversary CHOOSES `rest` per tag; the floor is not
about one fixed adversarial aggregate. -/
def beaconBiasGame {Ct O : Type} (D : BeaconDeployment Ct O) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => Multiset Ct × Ct × Ct
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p =>
    p.2.1 ≠ p.2.2 ∧
      (D.beacon t).combine (p.2.1 ::ₘ p.1) = (D.beacon t).combine (p.2.2 ::ₘ p.1)
  winsDec := fun _ t p => by
    letI := D.ctDecEq
    letI := D.outDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (2/2)** — a bias win is, by `Iff.rfl`, the real deployed beacon
producing the SAME output on two distinct honest contributions at the adversary's own `rest`. -/
theorem biasGame_wins_iff {Ct O : Type} (D : BeaconDeployment Ct O) (n : ℕ) (t : D.Tag)
    (p : Multiset Ct × Ct × Ct) :
    (beaconBiasGame D).wins n t p ↔
      (p.2.1 ≠ p.2.2 ∧
        (D.beacon t).combine (p.2.1 ::ₘ p.1) = (D.beacon t).combine (p.2.2 ::ₘ p.1)) :=
  Iff.rfl

/-! ## §4 — THE REDUCTION: a beacon biaser IS a combine collision finder. -/

/-- **THE REDUCTION, AS A MAP OF ADVERSARIES.** A biasing adversary becomes a multiset-combine
collision finder by consing each of its two honest contributions onto the adversarial `rest` IT chose.
This is not a rename and not a re-indexing: it is `honestSlotCR_of_hashcr` read as an extractor — the
cons-cancellation that file uses to DERIVE the false slot floor is exactly what makes the extracted
pair distinct here. -/
def biasToCollisionFinder {Ct O : Type} (D : BeaconDeployment Ct O)
    (A : Adversary (beaconBiasGame D)) : Adversary (multisetCollisionGame D) where
  run := fun l t => ((A.run l t).2.1 ::ₘ (A.run l t).1, (A.run l t).2.2 ::ₘ (A.run l t).1)

/-- **⚑ WIN-PRESERVATION — and this IS `bias_breaks_honest_slot_cr`, at the game level.** Wherever the
biaser wins, the extracted pair is a GENUINE collision of the deployed combine: the two committed
multisets are DISTINCT (`Multiset.cons_inj_left` — distinct honest contributions onto the same `rest`
give distinct multisets, the pure cancellation fact) while the beacon output is EQUAL (the bias
itself). The crypto content lives in a proof term, not in a sentence about one. -/
theorem bias_wins_imp {Ct O : Type} (D : BeaconDeployment Ct O)
    (A : Adversary (beaconBiasGame D)) (l : ℕ) (t : D.Tag)
    (hwin : (beaconBiasGame D).wins l t (A.run l t)) :
    (multisetCollisionGame D).wins l t ((biasToCollisionFinder D A).run l t) := by
  obtain ⟨hne, hcol⟩ := hwin
  refine ⟨fun h => hne ((Multiset.cons_inj_left _).mp h), hcol⟩

/-- **THE ADVANTAGE INEQUALITY.** The biaser's advantage is at most the extracted collision finder's,
at every parameter — both play over the SAME sampled tag space, and every tag the biaser wins the
extracted finder wins. A genuine reduction inequality over real game advantages. -/
theorem bias_adv_le {Ct O : Type} (D : BeaconDeployment Ct O) (A : Adversary (beaconBiasGame D))
    (l : ℕ) :
    gameAdv (beaconBiasGame D) A l
      ≤ gameAdv (multisetCollisionGame D) (biasToCollisionFinder D A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact bias_wins_imp D A l t ht

/-! ## §5 — the RE-GROUNDED CONSUMERS.

The Boolean keystones become advantage bounds, derived FROM the collision floor VIA the reduction. The
old statements are kept in `RandomnessBeacon`; these are their honest siblings. -/

/-- **⚑ RE-GROUNDED `RandomnessBeacon.honest_makes_unbiasable`.**

Under the combine-collision floor at the game the reduction actually attacks, a biasing adversary whose
extracted finder is in the floor's adversary class has NEGLIGIBLE advantage: an adversary that commits
its contributions first steers the beacon — makes the output insensitive to a distinct honest
contribution — only with negligible probability. The Boolean "distinct honest values ALWAYS yield
distinct outputs, so the honest contribution ALWAYS moves the beacon" becomes "moves it EXCEPT with
negligible probability" — which is what a real hash-combine can actually deliver, and what the FALSE
injective floor was standing in for.

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about the
bias game, the hypothesis about the collision game, and `bias_adv_le` is the only bridge (§6's canary
compiles that fact).

⚑ **`hEff` IS UNDISCHARGED AND THAT IS THE HONEST STATE** — the standard "the reduction is efficient"
side condition, a PARAMETER because this tree has no cost model (`FloorGames` §8). The floor's honesty
is exactly its `Eff`'s, and §7 prices both poles: `⊤` makes it FALSE at a bounded output, `⊥`
vacuous. The DISCHARGED successor — on the PROVED keyed-ROM floor, biaser an oracle program with
query-counted cost — is §8's `honest_makes_unbiasable_binds_rom`. -/
theorem honest_makes_unbiasable_advantage_bound {Ct O : Type} (D : BeaconDeployment Ct O)
    (Eff : Adversary (multisetCollisionGame D) → Prop) (A : Adversary (beaconBiasGame D))
    (hEff : Eff (biasToCollisionFinder D A))
    (hcol : Hard (multisetCollisionGame D) Eff) :
    Negl (gameAdv (beaconBiasGame D) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (beaconBiasGame D) A l).1) (bias_adv_le D A) (hcol _ hEff)

/-- **⚑ RE-GROUNDED `RandomnessBeacon.bias_breaks_honest_slot_cr`.** "A bias IS a collision" survives
as: an adversary exhibiting a bias IS, by the extractor, a combine collision finder — so under the
collision floor at that finder, bias happens only with negligible probability. The old theorem's
contrapositive shape is exactly this bound; what changes is that the hypothesis is now satisfiable and
the reduction is exhibited.

The `Eff` obligation is the same undischarged side condition as above — named, not hidden. -/
theorem bias_breaks_honest_slot_cr_advantage_bound {Ct O : Type} (D : BeaconDeployment Ct O)
    (Eff : Adversary (multisetCollisionGame D) → Prop) (A : Adversary (beaconBiasGame D))
    (hEff : Eff (biasToCollisionFinder D A))
    (hcol : Hard (multisetCollisionGame D) Eff) :
    Negl (gameAdv (beaconBiasGame D) A) :=
  honest_makes_unbiasable_advantage_bound D Eff A hEff hcol

/-! ## §6 — the CANARY: break the reduction and the keystone goes RED. -/

/-- **(CANARY — the keystone does NOT follow from the floor applied at some OTHER finder.)** Strip the
reduction — try to conclude the biaser's negligibility from the collision floor applied at some OTHER
finder `B`, NOT the one extracted from the biaser — and the proof does not go through: the floor bounds
`B`, and only `bias_adv_le` connects the EXTRACTED finder to the bias game. Under the OLD free
hypothesis (`hcr : HonestSlotCR b` with hypothesis and conclusion sharing the same free `b`) this tooth
was unwritable. It compiles now, and reds if a future edit reconnects the games. -/
example {Ct O : Type} (D : BeaconDeployment Ct O)
    (Eff : Adversary (multisetCollisionGame D) → Prop) (A : Adversary (beaconBiasGame D))
    (B : Adversary (multisetCollisionGame D)) (hB : Eff B)
    (hcol : Hard (multisetCollisionGame D) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (beaconBiasGame D) A) := hcol B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With the collision floor at the EXTRACTED finder the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floor {Ct O : Type} (D : BeaconDeployment Ct O)
    (Eff : Adversary (multisetCollisionGame D) → Prop) (A : Adversary (beaconBiasGame D))
    (hEff : Eff (biasToCollisionFinder D A))
    (hcol : Hard (multisetCollisionGame D) Eff) :
    Negl (gameAdv (beaconBiasGame D) A) :=
  honest_makes_unbiasable_advantage_bound D Eff A hEff hcol

/-! ## §7 — the `Eff` parameter, PRICED: both poles proved at THIS carrier.

The sweep's deep result (`FloorGames` §2) says a game floor at the unrestricted class IS the existence
floor. Here is that theorem instantiated at the deployed combine, so a reader can price any `Eff`
exactly rather than take the residual on faith. -/

/-- **THE COLLISION THE `⊤`-POLE REFUTATION EATS.** At the multiset domain the counting core DOES fire
(the domain is genuinely infinite — `instInfiniteMultiset`), so a bounded-output combine has a genuine
collision at every tag. ⚑ Note the asymmetry with §1: the SLOT floor needed compression, the FAMILY's
floor needs only a bounded output. Both are true of every real beacon; they are different arguments and
saying which is which is the point. -/
theorem exists_combine_collision_of_finite_range {Ct O : Type} (D : BeaconDeployment Ct O)
    (t : D.Tag) (hfin : (Set.range (D.hash t)).Finite) :
    ∃ p : Multiset Ct × Multiset Ct, p.1 ≠ p.2 ∧ D.hash t p.1 = D.hash t p.2 := by
  haveI := D.ctNonempty
  by_contra hno
  push_neg at hno
  refine not_injective_of_finite_range (D.hash t) hfin ?_
  intro a b hab
  by_contra hne
  exact hno (a, b) hne hab

/-- **⚑ (TOOTH — the floor is FALSE at `Eff := ⊤` for a range-bounded combine.)** The real content,
and the reason `Eff` is not decoration: a range-bounded combine HAS a collision at every tag, so the
collision game is always solvable, so the floor at the unrestricted adversary class is FALSE — and
every consumer would be vacuous there. `Classical.choice` is the adversary and no restatement of the
win relation can see it coming. This is the price of `hEff`, stated as a theorem instead of a
promise. -/
theorem beaconSlot_floor_top_false_of_finite_range {Ct O : Type} (D : BeaconDeployment Ct O)
    (hfin : ∀ t : D.Tag, (Set.range (D.hash t)).Finite) :
    ¬ Hard (multisetCollisionGame D) (fun _ => True) := by
  refine not_hard_top_of_always_solvable (multisetCollisionGame D) (fun _ => ⟨(0, 0)⟩) (fun _ t => ?_)
  exact exists_combine_collision_of_finite_range D t (hfin t)

/-- **⚑ (TOOTH — the DEPLOYED form, and it needs NO parameters.)** A real beacon output is a digest: a
`Finite` type. That single instance is the whole hypothesis. So `Eff := ⊤` fails at every real
hash-combine deployment. -/
theorem beaconSlot_floor_top_false_of_finite_out {Ct O : Type} [Finite O]
    (D : BeaconDeployment Ct O) : ¬ Hard (multisetCollisionGame D) (fun _ => True) :=
  beaconSlot_floor_top_false_of_finite_range D (fun _ => Set.toFinite _)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty adversary class the floor holds
for ANY deployment, including a completely broken combine. Recorded HONESTLY: a satisfiability witness
is worth nothing without the refutation beside it, and these two poles together are what make `Eff` a
dial rather than a costume. -/
theorem beaconSlot_floor_bot_vacuous {Ct O : Type} (D : BeaconDeployment Ct O) :
    Hard (multisetCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floor is REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** beacon deployment: the combine IGNORES the contributions entirely — the constant
`0` — so the adversary sets the beacon output outright and every pair of distinct contribution
multisets collides at every tag. This is `RandomnessBeacon.badBeaconOut`'s disease, as a deployment. -/
def brokenBeacon : BeaconDeployment ℕ ℕ where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  hash := fun _ _ => 0
  ctDecEq := inferInstance
  ctNonempty := inferInstance
  outDecEq := inferInstance
  deployedTag := ()

/-- **(TOOTH — the floor is REFUTABLE.)** The broken deployment's collision game is solvable at every
tag (`{0} ≠ {1}`, both combine to `0`), so it has no unrestricted-class floor. So the floor is a
GENUINE constraint — a broken combine refutes it — not vacuously true. -/
theorem brokenBeacon_floor_top_false :
    ¬ Hard (multisetCollisionGame brokenBeacon) (fun _ => True) :=
  not_hard_top_of_always_solvable (multisetCollisionGame brokenBeacon)
    (fun _ => ⟨(0, 0)⟩)
    (fun _ _ => ⟨(({0} : Multiset ℕ), ({1} : Multiset ℕ)), by simp, rfl⟩)

/-- **(TOOTH — the broken deployment also refutes `HonestSlotCR` as named.)** `brokenBeacon`'s beacon
FALSIFIES the injective slot floor outright — the honest contribution never moves the output — so
`HonestSlotCR` is a meaningful named proposition and not a relabelled `True`. Fired through
`RandomnessBeacon.bias_breaks_honest_slot_cr` itself: the OLD theorem is the tooth. -/
theorem brokenBeacon_not_honestSlotCR : ¬ HonestSlotCR (brokenBeacon.beacon ()) :=
  bias_breaks_honest_slot_cr (brokenBeacon.beacon ()) 0 5 6 (by decide) rfl

/-! ### The floor is SATISFIABLE (the connection to the keyed-family treatment). -/

/-- **(TOOTH — the keyed family is SATISFIABLE on an injective deployment.)** A deployment whose
per-tag combine is injective discharges `HashCRHardQuant (multisetHashFamily D) (fun _ => True)` — the
floor is REALIZABLE, unlike the injective `HonestSlotCR`/`HashCR` at deployed parameters. ⚑ Recorded
with its price, which the statement now carries instead of a docstring: the class is `fun _ => True`,
and §7's first tooth proves THAT FALSE at a range-bounded (i.e. real) combine. An injective combine is
exactly the `sumBeacon`/`idMultisetHash` shape — a non-compressing "hash" into all of `ℤ`, or the
identity — and the satisfiability is honest only as a non-emptiness check, never as evidence the
deployed combine satisfies it. (The conclusion used to be spelled `CollisionResistant …`; that `def`
hid precisely the `⊤` this tooth has to be read against, and is deleted.) -/
theorem multisetHashFamily_CR_of_injective_deployment {Ct O : Type} (D : BeaconDeployment Ct O)
    (hinj : ∀ t : D.Tag, Function.Injective (D.hash t)) :
    HashCRHardQuant (multisetHashFamily D) (fun _ => True) :=
  multisetHashFamily_CR_of_injective D hinj

/-! ## §8 — ⚑ THE KEYED-ROM SUCCESSOR: the bias bound DISCHARGED on the PROVED floor.

§5's `_advantage_bound` siblings are the honest fixed-hash statements, and their `hcol : Hard … Eff`
hypothesis is a PARAMETER with no known non-vacuous instantiation (§7: `⊤` FALSE at a bounded output,
`⊥` vacuous, no cost model). The DISCHARGED successor moves the floor where it is a THEOREM: the
keyed random-oracle model (`Crypto.KeyedRomFloor.keyedRom_hard`, the birthday bound), the biaser an
ORACLE PROGRAM with QUERY-COUNTED cost, oracle sampled AFTER the program is fixed
(`Crypto.RomCarrierSites`, the `Exec.SystemRootsBindingReduction` §7 pattern).

⚑ **THE MODELLING STEP, STATED (not smuggled)** — `RomCarrierSites`' header caveat, inherited: the
sampled `H : Tag × Msg → Fin (2 ^ l)` replaces the fixed public multiset combine (a deliberate
labelled idealisation, NOT a derivation); the digest space is `λ`-growing where the deployed output
is a FIXED-width digest. The message domain is the TRUNCATED deployed shape: the honest contribution
beside an adversarial aggregate of EXACTLY `m` contributions (`Ct × Sym Ct m` — the aggregate stays
an UNORDERED multiset, as deployed; `m` is the truncation bound on how much the adversary commits).
The adversarial `rest` is the game CONTEXT — the adversary still chooses it per tag — and the honest
slot is the PAYLOAD the commitment must bind; two distinct honest contributions absorbed at one
chosen `rest` with one digest IS the bias, in the win relation. -/

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction
  (RomCarrier romCarrierGame RomCarrierEff romCarrierAdv romCarrier_choiceForger_excluded)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily flatFamily_card_R taggedCarrier flatSite_binds constTripleComp constTriple_in_eff
   constTriple_gameAdv_pos constTriple_binds)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- **THE BEACON KEYED ROM FAMILY** — keyed by the DEPLOYED tag space `D.Tag` (the anchor to the
deployed object), over one honest contribution beside an adversarial aggregate of exactly `m`
contributions (unordered, as the deployed multiset combine absorbs it), with the ideal `λ`-bit
digest. -/
def beaconRomFamily {Ct O : Type} (D : BeaconDeployment Ct O) (ctFin : Fintype Ct)
    (tagDec : DecidableEq D.Tag) (m : ℕ) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty (fun _ => Ct × Sym Ct m)
    (fun _ => by letI := ctFin; letI := D.ctDecEq; infer_instance)
    (fun _ => by letI := ctFin; letI := D.ctDecEq; infer_instance)
    (fun _ => by
      obtain ⟨c₀⟩ := D.ctNonempty
      exact ⟨(c₀, Sym.replicate m c₀)⟩)

/-- **THE HONEST-SLOT CARRIER** — commitment `H (t, (c, rest))`: the beacon output binds the honest
contribution `c` UNDER the adversary's own chosen aggregate `rest` (the context). The embedding is
injective in the honest slot on the nose (`Prod.fst`). -/
def beaconRomCarrier {Ct O : Type} (D : BeaconDeployment Ct O) (ctFin : Fintype Ct)
    (tagDec : DecidableEq D.Tag) (m : ℕ) : RomCarrier (beaconRomFamily D ctFin tagDec m) :=
  taggedCarrier _ (fun _ => Sym Ct m) (fun _ => Ct) (fun _ => D.ctDecEq)
    (fun _ rest c => (c, rest)) (fun _ _ _ _ h => congrArg Prod.fst h)

/-- The beacon bias game at the sampled oracle: the adversary chooses a tag-and-`rest` context and
exhibits two DISTINCT honest contributions the beacon output cannot tell apart — `romCarrierGame`,
`beaconBiasGame`'s event at the sampled oracle. -/
abbrev beaconBiasRomGame {Ct O : Type} (D : BeaconDeployment Ct O) (ctFin : Fintype Ct)
    (tagDec : DecidableEq D.Tag) (m : ℕ) : Game :=
  romCarrierGame (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m)

/-- **⚑ THE DEPLOYED BIAS IS A WIN OF THE ROM GAME.** Two DISTINCT honest contributions absorbed at
ONE adversarial aggregate with ONE sampled-oracle output ARE a win — `bias_breaks_honest_slot_cr`'s
"biasability is exactly a hash collision on the honest slot", restated at the sampled oracle. -/
theorem beaconBiasRom_bias_is_break {Ct O : Type} (D : BeaconDeployment Ct O) (ctFin : Fintype Ct)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (l : ℕ)
    (H : (beaconBiasRomGame D ctFin tagDec m).Inst l) (t : D.Tag) (rest : Sym Ct m)
    {c c' : Ct} (hne : c ≠ c') (heq : H (t, (c, rest)) = H (t, (c', rest))) :
    (beaconBiasRomGame D ctFin tagDec m).wins l H ((t, rest), c, c') :=
  ⟨hne, heq⟩

/-- **⚑⚑ RE-GROUNDED `RandomnessBeacon.honest_makes_unbiasable`, DISCHARGED ON THE PROVED FLOOR** —
the keyed-ROM successor of §5's `honest_makes_unbiasable_advantage_bound`: every query-bounded
biasing adversary has NEGLIGIBLE advantage — the adversary that commits its contributions first
steers the beacon only with negligible probability, in the keyed ROM model of §8's header. The
hypotheses are a polynomial query budget and class membership — nothing refutable is carried. -/
theorem honest_makes_unbiasable_binds_rom {Ct O : Type} (D : BeaconDeployment Ct O)
    (ctFin : Fintype Ct) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (beaconBiasRomGame D ctFin tagDec m))
    (hA : RomCarrierEff (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m)
      Q A) :
    Negl (gameAdv (beaconBiasRomGame D ctFin tagDec m) A) :=
  flatSite_binds _ _ _ _ _ _ _ _ _ Q hQ A hA

/-- **⚑ RE-GROUNDED `RandomnessBeacon.bias_breaks_honest_slot_cr`, DISCHARGED** — a bias IS a
collision of the sampled oracle on the honest slot (`beaconBiasRom_bias_is_break`), so the same
discharged bound. -/
theorem bias_breaks_honest_slot_cr_binds_rom {Ct O : Type} (D : BeaconDeployment Ct O)
    (ctFin : Fintype Ct) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (beaconBiasRomGame D ctFin tagDec m))
    (hA : RomCarrierEff (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m)
      Q A) :
    Negl (gameAdv (beaconBiasRomGame D ctFin tagDec m) A) :=
  honest_makes_unbiasable_binds_rom D ctFin tagDec m Q hQ A hA

/-- **(TOOTH — the class is INHABITED with POSITIVE advantage.)** The `0`-query constant answerer on
two distinct honest contributions is in the class at every budget and wins with positive probability
at every parameter — the discharged bound bounds something genuinely nonzero. -/
theorem beaconBiasRom_class_inhabited_pos {Ct O : Type} (D : BeaconDeployment Ct O)
    (ctFin : Fintype Ct) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    {c c' : Ct} (hne : c ≠ c') :
    ∃ A, RomCarrierEff (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m) Q A
      ∧ ∀ l, 0 < gameAdv (beaconBiasRomGame D ctFin tagDec m) A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  refine ⟨romCarrierAdv (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m)
      (constTripleComp (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m)
        (fun _ => (t₀, Sym.replicate m c)) (fun _ => c) (fun _ => c')),
    constTriple_in_eff (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m)
      _ _ _ Q,
    fun l => constTriple_gameAdv_pos (beaconRomFamily D ctFin tagDec m)
      (beaconRomCarrier D ctFin tagDec m) _ _ _ l hne⟩

/-- **(TOOTH — the `shortCollAdv` shape is ADMITTED and DEFANGED, at this site.)** -/
theorem beaconBiasRom_constAnswer_defanged {Ct O : Type} (D : BeaconDeployment Ct O)
    (ctFin : Fintype Ct) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (ctx : ∀ _l, D.Tag × Sym Ct m) (v w : ∀ _l, Ct) :
    Negl (gameAdv (beaconBiasRomGame D ctFin tagDec m)
      (romCarrierAdv _ _ (constTripleComp (beaconRomFamily D ctFin tagDec m)
        (beaconRomCarrier D ctFin tagDec m) ctx v w))) :=
  constTriple_binds (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m)
    ctx v w Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _)

/-- **(TOOTH — a non-negligible biaser is OUTSIDE the class.)** -/
theorem beaconBiasRom_nonNegl_forger_excluded {Ct O : Type} (D : BeaconDeployment Ct O)
    (ctFin : Fintype Ct) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (beaconBiasRomGame D ctFin tagDec m))
    (hnn : ¬ Negl (gameAdv (beaconBiasRomGame D ctFin tagDec m) A)) :
    ¬ RomCarrierEff (beaconRomFamily D ctFin tagDec m) (beaconRomCarrier D ctFin tagDec m) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _) A hnn

#assert_all_clean [
  honestSlotCR_false_of_compressing,
  exists_honest_slot_collision_of_compressing,
  honestSlotCR_false_of_infinite_ct,
  honestSlotCR_discharge_hypothesis_is_false,
  honestSlotCR_discharge_hypothesis_is_false_of_finite_out,
  deployed_combine_is_family_instance,
  multisetHashFamily_CR_of_injective,
  honestSlotCR_of_injective,
  collisionGame_wins_iff,
  biasGame_wins_iff,
  bias_wins_imp,
  bias_adv_le,
  honest_makes_unbiasable_advantage_bound,
  bias_breaks_honest_slot_cr_advantage_bound,
  the_repaired_bound_fires_on_the_right_floor,
  exists_combine_collision_of_finite_range,
  beaconSlot_floor_top_false_of_finite_range,
  beaconSlot_floor_top_false_of_finite_out,
  beaconSlot_floor_bot_vacuous,
  brokenBeacon_floor_top_false,
  brokenBeacon_not_honestSlotCR,
  multisetHashFamily_CR_of_injective_deployment,
  beaconBiasRom_bias_is_break,
  honest_makes_unbiasable_binds_rom,
  bias_breaks_honest_slot_cr_binds_rom,
  beaconBiasRom_class_inhabited_pos,
  beaconBiasRom_constAnswer_defanged,
  beaconBiasRom_nonNegl_forger_excluded
]

end Dregg2.Crypto.BeaconSlotRegrounded

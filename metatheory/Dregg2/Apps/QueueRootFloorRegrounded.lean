/-
# `Dregg2.Apps.QueueRootFloorRegrounded` — the `RootCR` / `LeafCR` / `PairCR` / `LenBindCR`
consumers RE-GROUNDED off the FALSE-AS-NAMED injective floors onto REAL collision games carrying
explicit `Eff`s.

## The bug this closes (VACUITY-SWEEP FINDING 2, the `Apps/QueueRoot` cluster — 4 carriers)

All four queue-root carriers are stated as **injectivity**:

  * `RootCR root := ∀ ls₁ ls₂, ZeroFree ls₁ → ZeroFree ls₂ → root ls₁ = root ls₂ → ls₁ = ls₂`
  * `LeafCR leafHash := ∀ a b, leafHash a = leafHash b → a = b`
  * `PairCR combine := ∀ a b a' b', combine a b = combine a' b' → a = a' ∧ b = b'`
  * `LenBindCR bindLen := ∀ n x m y, bindLen n x = bindLen m y → n = m ∧ x = y`

The deployed scheme is `blake3_binary_root` over `hash_entry` (`storage/src/commitment.rs`,
`storage/src/queue.rs`): every one of these maps a domain into a BOUNDED 256-bit digest, so each is
**FALSE at deployed parameters by pigeonhole** (§1). Every consumer conditioned on them —
`dequeue_proof_pins`, `dequeue_forgery_refused`, `stale_proof_refused`, `dequeue_proof_unique`,
`queueDequeueProven_pins_root_transition`, `queueDequeueProven_refuses_forgery`,
`queueDequeueProven_refuses_stale`, `tagged_dequeue_proof_pins` — is therefore **VACUOUSLY TRUE** at
real parameters. `#assert_axioms` is blind: the proofs are clean; the HYPOTHESIS is the flaw.

## ⚑ THE ZERO-FREE RESTRICTION IS RESPECTED, NOT DODGED — this is the delicate part

`RootCR` does NOT claim full injectivity. `QueueRoot` itself proves full injectivity FALSE for the
padded scheme (`refRoot_pad_alias` / `padded_root_not_fully_injective`: `root [1,2,3] = root [1,2,3,0]`
— padding is indistinguishable from a zero leaf), which is exactly WHY the carrier is restricted to
ZERO-FREE lists. A false-proof that merely re-exhibited the padding alias would prove nothing new and
would miss the carrier.

So §1 refutes `RootCR` **on its own restricted domain**: `zfRep n := List.replicate (n+1) 1` is an
INFINITE family of pairwise-distinct ZERO-FREE lists (`zfRep_zeroFree`, `zfRep_injective`), so a
range-bounded root collides on two of THEM (`exists_zeroFree_collision_of_finite_range`). The
restriction buys nothing against counting: the zero-free lists are still infinite, the digest is still
bounded. `rootCR_false_blake3` is the deployed form.

## The re-grounding (the `HermineHashCRRegrounded` concurrent-forgery pattern)

The deployed dequeue path rests on TWO carriers at once, and a forger breaks EITHER — so this is a
genuine **DICHOTOMY with a union bound**, exactly like `HermineHashCRRegrounded`'s concurrent-forgery
keystone, not a single-leaf bound:

  * **§3 `dequeueForgeryGame`** — a first-class λ-indexed game: the adversary is handed a sampled
    instance (the tag, the live pending window `head :: rest`) and WINS iff it produces a proof that
    VERIFIES against the live root yet claims a DIFFERENT entry or remaining list. The forgery is IN
    the win relation, read off the REAL `verifyDequeue` (which mirrors `verify_dequeue_proof`
    verbatim) — nothing here is a docstring.
  * **§4 the two extractors + the dichotomy.** `forgeryToRootFinder` hands over the two committed
    windows; `forgeryToLeafFinder` hands over the two entries. `forgery_wins_imp` proves the real
    dichotomy: wherever the forger wins, EITHER the two windows are DISTINCT zero-free lists with one
    root (a genuine ROOT collision) OR they are equal, forcing `remaining = rest`, so the claim
    differs in the ENTRY while the leaves collide (a genuine LEAF collision). `forgery_adv_le` is the
    UNION BOUND over the shared sampled-instance space.
  * **§5** — `dequeue_proof_pins_advantage_bound` &c: the Boolean "an admitted proof PINS the
    transition" / "a forged claim is REFUSED" become "EXCEPT with negligible probability", from the
    two collision floors VIA the reduction.

## ⚑ THE `Eff` PARAMETERS ARE THE WHOLE HONESTY, AND THEY ARE UNDISCHARGED

The sweep's load-bearing result (`FloorGames` §2, `hard_top_iff_solvableFrac_negl`): at the
UNRESTRICTED adversary class a game floor IS the existence floor, hence FALSE wherever collisions
exist — and §1 proves they exist at the deployed root AND at the deployed leaf hash. §7 prices both
poles at THESE carriers. `Eff` is a PARAMETER, in the open, at every use site: this tree has no cost
model (`FloorGames` §8), and inventing a shallow imitation would be another costume.

## Scope — HONEST

FULLY re-grounded: the DEPLOYED dequeue path (`RootCR` + `LeafCR`), via the dichotomy reduction.
FALSE-PROVED but NOT game-re-grounded: `PairCR` / `LenBindCR` (§8), the carriers of the PROPOSED §7
level-tagged hardening (`taggedRoot_injective`) — which Rust has NOT adopted (a wire-affecting root
format change, per `QueueRoot`'s own ⚠). Their repair path is stated in §8 and is mechanical: the same
`Deployment` + collision-game + extractor shape as §2-§5, at `tRoot`/`bindLen`. Re-grounding a
hardening that is not deployed is lower value than refuting it honestly, which §8 does.

## Non-fake

Both floors are REFUTABLE on broken deployments (§7) and the reduction is LOAD-BEARING (§6's canary:
the keystones do NOT follow from the floors applied at OTHER adversaries). The OLD consumers are KEPT
untouched and doc-marked at the teeth; siblings ADDED. `#assert_all_clean`; no `sorry`, no fresh
`axiom`.

## Coordination

This is the QUEUE-ROOT lane. `KeySetCR` is `Apps.PreRotationKeySetRegrounded`; `RosterCR` is
`Circuit.CouncilRosterRegrounded`; the STARK/FRI/Merkle hash consumers are
`Circuit.FloorRegroundedConsumers` / `Circuit.Poseidon2KeyedBridge`; the commit-reveal side is
`Crypto.HermineHashCRRegrounded` (whose `winProb_le_add_of_imp` union bound this file reuses rather
than duplicating).
-/
import Dregg2.Apps.QueueRoot
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.RomCarrierSites

namespace Dregg2.Apps.QueueRootFloorRegrounded

open Dregg2.Apps.QueueRoot
  (ZeroFree RootCR LeafCR LeafNonzero PairCR LenBindCR DequeueProof verifyDequeue
   verifyDequeue_factors leafImage_zero_free)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv not_injective_of_finite_range)
open Dregg2.Crypto.ProbCrypto (winProb winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero negl_add not_negl_one)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit Hard hard_bot_vacuous not_hard_top_of_always_solvable)
open Dregg2.Crypto.HermineHashCRRegrounded (winProb_le_add_of_imp)

set_option autoImplicit false

/-! ## §1 — FALSE AS NAMED, on the carriers' OWN domains.

The deployed digest is a bounded 256-bit BLAKE3 output, so each carrier's map is compressing and the
counting core fires. The `RootCR` case is the delicate one — it is restricted to ZERO-FREE lists, and
the refutation must live INSIDE that restriction (see the header). -/

/-- A digest function into a BOUNDED integer window has FINITE range (`⊆ Ico 0 q`). The general form
of `HashFloorHonesty.finite_range_of_field_bound` — the domain is arbitrary here because these
carriers' domains are `List Int`, `Entry`, `Int × Int` and `Nat × Int`. -/
theorem finite_range_of_bound {α : Type} (f : α → Int) (q : Int)
    (hb : ∀ x, 0 ≤ f x ∧ f x < q) : (Set.range f).Finite := by
  refine (Set.finite_Ico (0 : Int) q).subset ?_
  rintro _ ⟨x, rfl⟩
  exact ⟨(hb x).1, (hb x).2⟩

/-! ### §1a — `RootCR`, refuted INSIDE its zero-free restriction. -/

/-- An infinite family of pairwise-distinct **ZERO-FREE** leaf lists: the all-ones lists of every
positive length. These live entirely inside `RootCR`'s restricted domain, which is what makes the
refutation below hit the carrier rather than the padding alias `QueueRoot` already knows about. -/
def zfRep (n : ℕ) : List Int := List.replicate (n + 1) 1

/-- Every `zfRep n` is zero-free — its only element is `1`. -/
theorem zfRep_zeroFree (n : ℕ) : ZeroFree (zfRep n) := by
  intro l hl
  rw [List.eq_of_mem_replicate hl]
  decide

/-- The family is injective — the lengths differ. So it is genuinely infinite. -/
theorem zfRep_injective : Function.Injective zfRep := by
  intro n m h
  have hl := congrArg List.length h
  simpa [zfRep] using hl

/-- **⚑ THE ZERO-FREE COLLISION.** A range-bounded root collides on two DISTINCT **ZERO-FREE** lists.
The zero-free restriction buys nothing against counting: the zero-free lists are still infinite (the
all-ones family), while the digest is still bounded. This is the honest content behind "the queue root
is compressing", and it is what makes `RootCR` false rather than merely un-proven. -/
theorem exists_zeroFree_collision_of_finite_range (root : List Int → Int)
    (hfin : (Set.range root).Finite) :
    ∃ p : List Int × List Int, p.1 ≠ p.2 ∧ ZeroFree p.1 ∧ ZeroFree p.2 ∧ root p.1 = root p.2 := by
  have hsub : (Set.range (root ∘ zfRep)).Finite := by
    refine hfin.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨zfRep n, rfl⟩
  have hnotinj : ¬ Function.Injective (root ∘ zfRep) :=
    not_injective_of_finite_range (root ∘ zfRep) hsub
  rw [Function.not_injective_iff] at hnotinj
  obtain ⟨n, m, heq, hne⟩ := hnotinj
  exact ⟨(zfRep n, zfRep m), fun h => hne (zfRep_injective h),
    zfRep_zeroFree n, zfRep_zeroFree m, heq⟩

/-- **TOOTH — `RootCR` is FALSE for any range-bounded pending-window root**, ON ITS OWN restricted
domain. Not the padding alias (`padded_root_not_fully_injective`, which refutes only the UNrestricted
statement the carrier never made) — this refutes the carrier AS STATED. -/
theorem rootCR_false_of_finite_range (root : List Int → Int) (hfin : (Set.range root).Finite) :
    ¬ RootCR root := by
  obtain ⟨p, hne, hz1, hz2, heq⟩ := exists_zeroFree_collision_of_finite_range root hfin
  exact fun hCR => hne (hCR p.1 p.2 hz1 hz2 heq)

/-- **TOOTH (deployed form) — `RootCR` is FALSE at the deployed `blake3_binary_root`.** A root that is
a genuine 256-bit BLAKE3 digest REFUTES the floor. So every `RootCR` consumer is vacuous at real
parameters — the floor is not merely un-proven at the deployed hash; it is provably FALSE there. -/
theorem rootCR_false_blake3 (root : List Int → Int)
    (hb : ∀ ls, 0 ≤ root ls ∧ root ls < (2 : Int) ^ 256) : ¬ RootCR root :=
  rootCR_false_of_finite_range root (finite_range_of_bound root _ hb)

/-! ### §1b — `LeafCR`, refuted by COMPRESSION (a different shape — the entry space is finite).

`LeafCR`'s domain is `Entry`, the canonical 88-byte entry preimage (`content_hash ‖ sender ‖ deposit
‖ enqueued_at ‖ size`) — a FINITE type. So the counting core's `Infinite` hypothesis does NOT apply,
and the honest refutation is pigeonhole on cardinalities, exactly the shape of
`HashFloorHonesty.hashCR_false_of_compressing`. Being precise about which teeth fire on which carrier
is part of the repair. -/

/-- **TOOTH — `LeafCR` is FALSE for a COMPRESSING entry hash.** If the entry space is larger than the
digest window (`B < |Entry|` — for the deployed queue, an 88-byte preimage space against a 256-bit
digest, so `2²⁵⁶ < 2⁷⁰⁴`), then two DISTINCT entries share a leaf commitment by pigeonhole. -/
theorem leafCR_false_of_compressing {Entry : Type} [Fintype Entry] [DecidableEq Entry]
    (leafHash : Entry → Int) (B : ℕ)
    (hb : ∀ e, leafHash e ∈ Finset.Ico (0 : Int) (B : Int))
    (hcard : B < Fintype.card Entry) : ¬ LeafCR leafHash := by
  have hlt : (Finset.Ico (0 : Int) (B : Int)).card < (Finset.univ : Finset Entry).card := by
    simpa using hcard
  obtain ⟨a, -, b, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun e _ => hb e)
  exact fun hCR => hne (hCR a b heq)

/-- **TOOTH — `LeafCR` is FALSE for an INFINITE entry space with a bounded digest** (the variant that
fires if `Entry` is modelled unboundedly rather than as the 88-byte preimage). -/
theorem leafCR_false_of_finite_range {Entry : Type} [Infinite Entry] (leafHash : Entry → Int)
    (hfin : (Set.range leafHash).Finite) : ¬ LeafCR leafHash :=
  fun hCR => not_injective_of_finite_range leafHash hfin (fun a b h => hCR a b h)

/-- **THE LEAF COLLISION, in the positive form §7 consumes.** -/
theorem exists_leaf_collision_of_compressing {Entry : Type} [Fintype Entry] [DecidableEq Entry]
    (leafHash : Entry → Int) (B : ℕ)
    (hb : ∀ e, leafHash e ∈ Finset.Ico (0 : Int) (B : Int))
    (hcard : B < Fintype.card Entry) :
    ∃ p : Entry × Entry, p.1 ≠ p.2 ∧ leafHash p.1 = leafHash p.2 := by
  have hlt : (Finset.Ico (0 : Int) (B : Int)).card < (Finset.univ : Finset Entry).card := by
    simpa using hcard
  obtain ⟨a, -, b, -, hne, heq⟩ :=
    Finset.exists_ne_map_eq_of_card_lt_of_maps_to hlt (fun e _ => hb e)
  exact ⟨(a, b), hne, heq⟩

/-! ## §2 — the DEPLOYED QUEUE DEPLOYMENT: domain separation is the key.

The deployed root and leaf hash are FIXED unkeyed functions; their effective key is the
domain-separation tag (`TAG_QUEUE_ENTRY`, the derive-key prefix the leaf hash already uses) — the
standard keyed-from-unkeyed model (`Poseidon2KeyedBridge` §1-§2), and what stops the "hardcode a known
collision" degeneracy that collapses an unkeyed floor. -/

/-- **The deployed queue-root commitment scheme.** `root` / `leafHash` are the tag-keyed deployed
functions; `head` and `restEntries` are the LIVE pending window at the sampled instance (the head
entry and the entries behind it); `leafNonzero` is the `QueueRoot.LeafNonzero` carrier — BLAKE3
preimage resistance, which is NOT an injectivity floor and is NOT refuted by §1. -/
structure QueueDeployment (Entry : Type) where
  /-- The domain-separation tag space (the effective key the CR games sample). -/
  Tag : Type
  /-- The tag space is finite (the games sample a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- The tag-keyed pending-window root (`blake3_binary_root` at each tag). -/
  root : Tag → List Int → Int
  /-- The tag-keyed entry-leaf commitment (`hash_entry` at each tag). -/
  leafHash : Tag → Entry → Int
  /-- No entry's leaf is the zero padding/sentinel — `QueueRoot.LeafNonzero`, i.e. BLAKE3 preimage
  resistance. This is what keeps honest pending windows zero-free; it is a genuine assumption, not an
  injectivity floor, so §1 does not touch it. -/
  leafNonzero : ∀ (t : Tag) (e : Entry), leafHash t e ≠ 0
  /-- The live head entry of the pending window at the sampled instance. -/
  head : Tag → Entry
  /-- The entries remaining behind the head, FIFO order. -/
  restEntries : Tag → List Entry
  /-- Decidable equality on entries (the games check two entries are distinct). -/
  entryDecEq : DecidableEq Entry
  /-- The specific domain-separation tag the deployment computes. -/
  deployedTag : Tag

/-- The live remaining-leaf window at the sampled instance — an IMAGE of the leaf hash, exactly as
the real pending window is. -/
def QueueDeployment.rest {Entry : Type} (D : QueueDeployment Entry) (t : D.Tag) : List Int :=
  (D.restEntries t).map (D.leafHash t)

/-- The live window is ZERO-FREE — derived, not assumed: it is a leaf image, and leaves are nonzero
(`QueueRoot.leafImage_zero_free`). This is the honest-window half of the zero-free story. -/
theorem QueueDeployment.rest_zeroFree {Entry : Type} (D : QueueDeployment Entry) (t : D.Tag) :
    ZeroFree (D.rest t) :=
  leafImage_zero_free (D.leafNonzero t) _

/-- **`rootFamily D`** — the deployed pending-window root lifted to a `KeyedHashFamily`, keyed by its
domain-separation tag. -/
def rootFamily {Entry : Type} (D : QueueDeployment Entry) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List Int
  Out := Int
  H := fun _ t ls => D.root t ls
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **`leafFamily D`** — the deployed entry-leaf commitment lifted to a `KeyedHashFamily`. -/
def leafFamily {Entry : Type} (D : QueueDeployment Entry) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := Entry
  Out := Int
  H := fun _ t e => D.leafHash t e
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := D.entryDecEq
  outDecEq := inferInstance

/-- **FAITHFULNESS.** The deployed FIXED root IS the keyed family's instance at the deployed tag — a
definitional equality, no idealization. -/
theorem deployed_root_is_family_instance {Entry : Type} (D : QueueDeployment Entry) (n : ℕ) :
    D.root D.deployedTag = (rootFamily D).H n D.deployedTag := rfl

/-- **FAITHFULNESS (leaf).** -/
theorem deployed_leaf_is_family_instance {Entry : Type} (D : QueueDeployment Entry) (n : ℕ) :
    D.leafHash D.deployedTag = (leafFamily D).H n D.deployedTag := rfl

/-! ### ⚑ THERE IS NO OLD-FLOOR ⟹ NEW-FLOOR BRIDGE HERE, AND THAT IS THE POINT.

A theorem `leafFamily_CR_of_leafCR` sat here: `LeafCR` at every tag ⟹ the `⊤`-class collision floor on
`leafFamily D`, argued as "the OLD floor was STRICTLY STRONGER, so re-grounding loses nothing".
**BOTH ENDS ARE REFUTED.** §1b kills the injective `LeafCR` at a compressing entry hash; §7's
`leaf_floor_top_false_of_compressing` kills the `⊤`-class floor at the SAME hash. An implication
between two propositions that are both FALSE at deployed parameters transports nothing, and "loses
nothing" was FALSE as written — the floor it re-grounded ONTO is refuted at a real BLAKE3 too. So the
bridge is DELETED rather than restated at the unrestricted class.

What stands in its place is not another rung-1 bridge but this module's OWN poles at its OWN games,
which is why the bridge could be dropped rather than replaced: §7 prices `EffR` and `EffL` exactly
(`root_floor_top_false_of_compressing` / `leaf_floor_top_false_of_compressing` against
`root_floor_bot_vacuous` / `leaf_floor_bot_vacuous`) and refutes the root floor on a broken deployment
(`brokenQueue_root_floor_top_false`); §7b then lands both layers where the floor is a THEOREM
(`dequeue_proof_pins_binds_rom`, the keyed ROM, dichotomy intact). -/

/-! ## §3 — the COLLISION GAMES and the DEQUEUE-FORGERY GAME, as first-class objects. -/

/-- **THE ROOT COLLISION GAME.** Instances are sampled domain-separation tags; the adversary outputs
two leaf lists and WINS iff they are a GENUINE collision of the deployed root **inside `RootCR`'s
restricted domain** — DISTINCT, both ZERO-FREE, equal roots. ⚑ The zero-free side conditions are IN
the win relation on purpose: without them the game would be won by the padding alias
(`QueueRoot.refRoot_pad_alias`), which is a STRUCTURAL fact about the padded scheme and not a hash
break at all. A game that counted the alias as a win would be measuring the wrong thing. -/
def rootCollisionGame {Entry : Type} (D : QueueDeployment Entry) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List Int × List Int
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p =>
    p.1 ≠ p.2 ∧ ZeroFree p.1 ∧ ZeroFree p.2 ∧ D.root t p.1 = D.root t p.2
  winsDec := fun _ t p => by
    unfold ZeroFree
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — a root-game win unfolds, by `Iff.rfl`, to a genuine
zero-free collision of the real deployed root. -/
theorem rootCollisionGame_wins_iff {Entry : Type} (D : QueueDeployment Entry) (n : ℕ) (t : D.Tag)
    (p : List Int × List Int) :
    (rootCollisionGame D).wins n t p ↔
      (p.1 ≠ p.2 ∧ ZeroFree p.1 ∧ ZeroFree p.2 ∧ D.root t p.1 = D.root t p.2) :=
  Iff.rfl

/-- **THE LEAF COLLISION GAME.** The adversary outputs two entries and WINS iff they are DISTINCT yet
share a leaf commitment — a genuine `hash_entry` collision. -/
def leafCollisionGame {Entry : Type} (D : QueueDeployment Entry) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => Entry × Entry
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => p.1 ≠ p.2 ∧ D.leafHash t p.1 = D.leafHash t p.2
  winsDec := fun _ t p => by
    letI := D.entryDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (leaf)** — by `Iff.rfl`. -/
theorem leafCollisionGame_wins_iff {Entry : Type} (D : QueueDeployment Entry) (n : ℕ) (t : D.Tag)
    (p : Entry × Entry) :
    (leafCollisionGame D).wins n t p ↔ (p.1 ≠ p.2 ∧ D.leafHash t p.1 = D.leafHash t p.2) :=
  Iff.rfl

/-- **THE DEQUEUE-FORGERY GAME.** The adversary is handed a sampled tag and outputs a `DequeueProof`;
it WINS iff the proof (i) VERIFIES under the REAL `verifyDequeue` (which mirrors Rust's
`verify_dequeue_proof` verbatim), (ii) claims a zero-free remaining window — the honest-claim residue
`QueueRoot`'s ⚠ names, CHECKED by `verifyDequeueStrict` — (iii) is aimed at the LIVE pre-root
committing to the real window `leafHash head :: rest`, yet (iv) claims a DIFFERENT entry or a
DIFFERENT remaining list. Winning this game IS the dequeue forgery `dequeue_forgery_refused` rules
out; the verifier and the claim live in the win predicate, not in prose. -/
def dequeueForgeryGame {Entry : Type} (D : QueueDeployment Entry) : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => DequeueProof Entry
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p =>
    verifyDequeue (D.root t) (D.leafHash t) p = true ∧
      ZeroFree p.remaining ∧
      p.oldRoot = D.root t (D.leafHash t (D.head t) :: D.rest t) ∧
      (p.entry ≠ D.head t ∨ p.remaining ≠ D.rest t)
  winsDec := fun _ t p => by
    letI := D.entryDecEq
    unfold ZeroFree
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT (forgery)** — by `Iff.rfl`. -/
theorem dequeueForgeryGame_wins_iff {Entry : Type} (D : QueueDeployment Entry) (n : ℕ) (t : D.Tag)
    (p : DequeueProof Entry) :
    (dequeueForgeryGame D).wins n t p ↔
      (verifyDequeue (D.root t) (D.leafHash t) p = true ∧
        ZeroFree p.remaining ∧
        p.oldRoot = D.root t (D.leafHash t (D.head t) :: D.rest t) ∧
        (p.entry ≠ D.head t ∨ p.remaining ≠ D.rest t)) :=
  Iff.rfl

/-! ## §4 — THE REDUCTION: a dequeue forger breaks the ROOT or the LEAF. -/

/-- **THE ROOT HORN, AS A MAP OF ADVERSARIES.** A dequeue forger becomes a root-collision finder by
handing over the two committed windows: the one its claim commits to, and the real live one. -/
def forgeryToRootFinder {Entry : Type} (D : QueueDeployment Entry)
    (A : Adversary (dequeueForgeryGame D)) : Adversary (rootCollisionGame D) where
  run := fun n t =>
    let p := A.run n t
    (D.leafHash t p.entry :: p.remaining, D.leafHash t (D.head t) :: D.rest t)

/-- **THE LEAF HORN, AS A MAP OF ADVERSARIES.** A dequeue forger becomes a leaf-collision finder by
handing over its claimed entry and the real head entry. -/
def forgeryToLeafFinder {Entry : Type} (D : QueueDeployment Entry)
    (A : Adversary (dequeueForgeryGame D)) : Adversary (leafCollisionGame D) where
  run := fun n t => let p := A.run n t; (p.entry, D.head t)

/-- **⚑ THE DICHOTOMY — and this IS `dequeue_proof_pins`, at the game level.** Wherever the forger
wins: the verifier's first check plus the live-root pin force the two committed windows to share a
root, and BOTH are zero-free (the claim by the win condition, the live one because it is a leaf image
and leaves are nonzero). So EITHER the two windows are DISTINCT — a genuine ROOT collision inside
`RootCR`'s own restricted domain — OR they are EQUAL, whence `remaining = rest` (cons-injectivity), so
the claim must differ in the ENTRY while the two leaves collide — a genuine LEAF collision.

The crypto content lives in proof terms, not in a sentence about them. This is exactly the reasoning
`dequeue_proof_pins` performs with `hRC`/`hLC` as free hypotheses; here it is a win-preserving map
into two real games. -/
theorem forgery_wins_imp {Entry : Type} (D : QueueDeployment Entry)
    (A : Adversary (dequeueForgeryGame D)) (n : ℕ) (t : D.Tag)
    (hwin : (dequeueForgeryGame D).wins n t (A.run n t)) :
    (rootCollisionGame D).wins n t ((forgeryToRootFinder D A).run n t) ∨
      (leafCollisionGame D).wins n t ((forgeryToLeafFinder D A).run n t) := by
  obtain ⟨hv, hzfClaim, hpre, hne⟩ := hwin
  set p := A.run n t with hp
  -- the verifier's first check + the live-root pin: the two windows share a root.
  have h1 := (verifyDequeue_factors hv).1
  have hroots : D.root t (D.leafHash t p.entry :: p.remaining)
      = D.root t (D.leafHash t (D.head t) :: D.rest t) := h1.trans hpre
  -- both windows are zero-free: the claim by hypothesis, the live one because leaves are nonzero.
  have hz1 : ZeroFree (D.leafHash t p.entry :: p.remaining) :=
    ZeroFree.cons (D.leafNonzero t p.entry) hzfClaim
  have hz2 : ZeroFree (D.leafHash t (D.head t) :: D.rest t) :=
    ZeroFree.cons (D.leafNonzero t (D.head t)) (D.rest_zeroFree t)
  by_cases hlists : (D.leafHash t p.entry :: p.remaining) = (D.leafHash t (D.head t) :: D.rest t)
  · -- EQUAL windows: cons-injectivity pins the remaining list, so the claim differs in the ENTRY.
    right
    injection hlists with hl hr
    refine ⟨?_, hl⟩
    rcases hne with h | h
    · exact h
    · exact absurd hr h
  · -- DISTINCT windows with one root: a genuine zero-free ROOT collision.
    exact Or.inl ⟨hlists, hz1, hz2, hroots⟩

/-- **THE UNION BOUND.** The forger's advantage is at most the SUM of the extracted root-finder's and
leaf-finder's advantages, at every parameter — the three play over the SAME sampled tag space, and
every tag the forger wins one of the two derived adversaries wins. A genuine reduction inequality over
real game advantages. (`winProb_le_add_of_imp` is `HermineHashCRRegrounded`'s union bound, reused.) -/
theorem forgery_adv_le {Entry : Type} (D : QueueDeployment Entry)
    (A : Adversary (dequeueForgeryGame D)) (n : ℕ) :
    gameAdv (dequeueForgeryGame D) A n ≤
      gameAdv (rootCollisionGame D) (forgeryToRootFinder D A) n +
        gameAdv (leafCollisionGame D) (forgeryToLeafFinder D A) n := by
  refine @winProb_le_add_of_imp _ (D.tagFintype) _ _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  rcases forgery_wins_imp D A n t ht with hr | hl
  · exact Or.inl ((Adversary.hit_eq_true (forgeryToRootFinder D A) n t).mpr hr)
  · exact Or.inr ((Adversary.hit_eq_true (forgeryToLeafFinder D A) n t).mpr hl)

/-! ## §5 — the RE-GROUNDED CONSUMERS. -/

/-- **⚑ RE-GROUNDED `QueueRoot.dequeue_proof_pins` / `dequeue_forgery_refused` — from ROOT collision
resistance AND LEAF collision resistance, VIA the reduction.**

Under the root-collision floor at the game the reduction attacks AND the leaf-collision floor at the
entry hash, a dequeue forger whose extracted finders are in the floors' adversary classes has
NEGLIGIBLE advantage: an admitted proof PINS the head-dequeue transition EXCEPT with negligible
probability, and a forged claim is REFUSED EXCEPT with negligible probability. The Boolean pins become
the additive negligible advantage — which is what a real BLAKE3 can actually deliver, and what the
FALSE injective floors were standing in for.

Unlike its predecessor this statement is FALSE if you delete the reduction: the conclusion is about
the forgery game, the hypotheses about the two collision games, and `forgery_adv_le` is the only
bridge (§6's canary compiles that fact).

⚑ **THE `hEffR`/`hEffL` OBLIGATIONS ARE UNDISCHARGED AND THAT IS THE HONEST STATE** — the standard
"the reduction is efficient" side conditions, PARAMETERS because this tree has no cost model
(`FloorGames` §8). Both floors are priced exactly by §7: `⊤` makes them FALSE at the deployed BLAKE3,
`⊥` vacuous. The DISCHARGED successor — on the PROVED keyed-ROM floor, forger an oracle program with
query-counted cost, dichotomy intact — is §7b's `dequeue_proof_pins_binds_rom`. -/
theorem dequeue_proof_pins_advantage_bound {Entry : Type} (D : QueueDeployment Entry)
    (EffR : Adversary (rootCollisionGame D) → Prop)
    (EffL : Adversary (leafCollisionGame D) → Prop)
    (A : Adversary (dequeueForgeryGame D))
    (hEffR : EffR (forgeryToRootFinder D A))
    (hEffL : EffL (forgeryToLeafFinder D A))
    (hroot : Hard (rootCollisionGame D) EffR)
    (hleaf : Hard (leafCollisionGame D) EffL) :
    Negl (gameAdv (dequeueForgeryGame D) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (dequeueForgeryGame D) A n).1)
    (forgery_adv_le D A) (negl_add (hroot _ hEffR) (hleaf _ hEffL))

/-- **⚑ RE-GROUNDED `QueueRoot.queueDequeueProven_pins_root_transition` / `_refuses_forgery`.** The
WELD keystone's advantage-bounded sibling: a proven dequeue's committed root pair IS the modeled root
transition EXCEPT with negligible probability. The guarded verb (`queueDequeueProven`) checks exactly
`verifyDequeueAgainst` against the live `message_root`, whose structural leg is the `verifyDequeue` the
forgery game already carries and whose live-root leg is the game's `p.oldRoot = …` conjunct — so a
forger against the WELD is a forger against `dequeueForgeryGame`, and this bound is that one. -/
theorem queueDequeueProven_pins_root_transition_advantage_bound {Entry : Type}
    (D : QueueDeployment Entry)
    (EffR : Adversary (rootCollisionGame D) → Prop)
    (EffL : Adversary (leafCollisionGame D) → Prop)
    (A : Adversary (dequeueForgeryGame D))
    (hEffR : EffR (forgeryToRootFinder D A))
    (hEffL : EffL (forgeryToLeafFinder D A))
    (hroot : Hard (rootCollisionGame D) EffR)
    (hleaf : Hard (leafCollisionGame D) EffL) :
    Negl (gameAdv (dequeueForgeryGame D) A) :=
  dequeue_proof_pins_advantage_bound D EffR EffL A hEffR hEffL hroot hleaf

/-- **⚑ RE-GROUNDED `QueueRoot.dequeue_proof_unique` / `stale_proof_refused`.** Two admitted proofs
against one pre-root pin the same transition, and a stale proof is refused, EXCEPT with negligible
probability — both are the same forger under the same two floors, so both are this bound. -/
theorem dequeue_proof_unique_advantage_bound {Entry : Type} (D : QueueDeployment Entry)
    (EffR : Adversary (rootCollisionGame D) → Prop)
    (EffL : Adversary (leafCollisionGame D) → Prop)
    (A : Adversary (dequeueForgeryGame D))
    (hEffR : EffR (forgeryToRootFinder D A))
    (hEffL : EffL (forgeryToLeafFinder D A))
    (hroot : Hard (rootCollisionGame D) EffR)
    (hleaf : Hard (leafCollisionGame D) EffL) :
    Negl (gameAdv (dequeueForgeryGame D) A) :=
  dequeue_proof_pins_advantage_bound D EffR EffL A hEffR hEffL hroot hleaf

/-! ## §6 — the CANARY: break the reduction and the keystones go RED. -/

/-- **(CANARY — the keystone does NOT follow from the floors applied at OTHER adversaries.)** Strip
the reduction — try to conclude the forger's negligibility from the two floors applied at some OTHER
root finder `B` and leaf finder `E`, NOT the ones extracted from the forger — and the proof does not
go through: the floors bound `B` and `E`, and only `forgery_adv_le` connects the EXTRACTED pair to the
forgery game. Under the OLD free hypotheses (`hRC : RootCR root`, `hLC : LeafCR leafHash`, with
hypothesis and conclusion sharing the same free `root`/`leafHash`) this tooth was unwritable. It
compiles now, and reds if a future edit reconnects the games. -/
example {Entry : Type} (D : QueueDeployment Entry)
    (EffR : Adversary (rootCollisionGame D) → Prop)
    (EffL : Adversary (leafCollisionGame D) → Prop)
    (A : Adversary (dequeueForgeryGame D))
    (B : Adversary (rootCollisionGame D)) (hB : EffR B)
    (E : Adversary (leafCollisionGame D)) (hE : EffL E)
    (hroot : Hard (rootCollisionGame D) EffR)
    (hleaf : Hard (leafCollisionGame D) EffL) : True := by
  fail_if_success
    (have : Negl (gameAdv (dequeueForgeryGame D) A) := negl_add (hroot B hB) (hleaf E hE))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floors DO discharge it.** A gate that refuses everything is a
broken keystone, not a fixed one. With both floors at the EXTRACTED adversaries the keystone fires.
Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floors {Entry : Type} (D : QueueDeployment Entry)
    (EffR : Adversary (rootCollisionGame D) → Prop)
    (EffL : Adversary (leafCollisionGame D) → Prop)
    (A : Adversary (dequeueForgeryGame D))
    (hEffR : EffR (forgeryToRootFinder D A))
    (hEffL : EffL (forgeryToLeafFinder D A))
    (hroot : Hard (rootCollisionGame D) EffR)
    (hleaf : Hard (leafCollisionGame D) EffL) :
    Negl (gameAdv (dequeueForgeryGame D) A) :=
  dequeue_proof_pins_advantage_bound D EffR EffL A hEffR hEffL hroot hleaf

/-! ## §7 — the `Eff` parameters, PRICED: both poles proved at THESE carriers. -/

/-- **⚑ (TOOTH — the ROOT floor is FALSE at `Eff := ⊤` for the DEPLOYED root.)** The real content, and
the reason `Eff` is not decoration: a range-bounded root HAS a ZERO-FREE collision at every tag (§1a's
counting core, inside the carrier's own restricted domain), so the root-collision game is always
solvable and the floor at the unrestricted class is FALSE — every consumer would be vacuous there.
`Classical.choice` is the adversary and no restatement of the win relation can see it coming. This is
the price of `hEffR`, stated as a theorem instead of a promise. -/
theorem root_floor_top_false_of_compressing {Entry : Type} (D : QueueDeployment Entry)
    (hfin : ∀ t : D.Tag, (Set.range (D.root t)).Finite) :
    ¬ Hard (rootCollisionGame D) (fun _ => True) :=
  not_hard_top_of_always_solvable (rootCollisionGame D)
    (fun _ => ⟨([], [])⟩)
    (fun _ t => exists_zeroFree_collision_of_finite_range (D.root t) (hfin t))

/-- **(TOOTH — the deployed BLAKE3 form.)** A genuine 256-bit `blake3_binary_root` refutes the
unrestricted-class root floor. The deployment `QueueRoot`'s header names is exactly where `Eff := ⊤`
fails. -/
theorem root_floor_top_false_blake3 {Entry : Type} (D : QueueDeployment Entry)
    (hb : ∀ (t : D.Tag) (ls : List Int), 0 ≤ D.root t ls ∧ D.root t ls < (2 : Int) ^ 256) :
    ¬ Hard (rootCollisionGame D) (fun _ => True) :=
  root_floor_top_false_of_compressing D
    (fun t => finite_range_of_bound (D.root t) _ (fun ls => hb t ls))

/-- **⚑ (TOOTH — the LEAF floor is FALSE at `Eff := ⊤` for a COMPRESSING entry hash.)** The deployed
88-byte entry preimage space dwarfs the 256-bit digest, so a collision exists at every tag and the
unrestricted-class leaf floor is FALSE. The price of `hEffL`. -/
theorem leaf_floor_top_false_of_compressing {Entry : Type} [Fintype Entry] [DecidableEq Entry]
    [Nonempty Entry] (D : QueueDeployment Entry) (B : ℕ)
    (hb : ∀ (t : D.Tag) (e : Entry), D.leafHash t e ∈ Finset.Ico (0 : Int) (B : Int))
    (hcard : B < Fintype.card Entry) :
    ¬ Hard (leafCollisionGame D) (fun _ => True) :=
  not_hard_top_of_always_solvable (leafCollisionGame D)
    (fun _ => ⟨(Classical.arbitrary Entry, Classical.arbitrary Entry)⟩)
    (fun _ t => exists_leaf_collision_of_compressing (D.leafHash t) B (fun e => hb t e) hcard)

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous, root.)** At the empty adversary class the floor
holds for ANY deployment, including a completely broken root. Recorded HONESTLY: a satisfiability
witness is worth nothing without the refutation beside it, and the two poles together are what make
`Eff` a dial rather than a costume. -/
theorem root_floor_bot_vacuous {Entry : Type} (D : QueueDeployment Entry) :
    Hard (rootCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous, leaf.)** -/
theorem leaf_floor_bot_vacuous {Entry : Type} (D : QueueDeployment Entry) :
    Hard (leafCollisionGame D) (fun _ => False) :=
  hard_bot_vacuous _

/-! ### The floors are REFUTABLE on a broken deployment (load-bearing, not `True`-shaped). -/

/-- A **broken** queue deployment: the root IGNORES the leaf list, so every pair of distinct zero-free
windows collides. (The leaf hash is kept injective and nonzero so the refutation isolates the ROOT.) -/
def brokenQueue : QueueDeployment Int where
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  root := fun _ _ => 0
  leafHash := fun _ e => 2 * e + 1
  leafNonzero := fun _ e => by omega
  head := fun _ => 0
  restEntries := fun _ => []
  entryDecEq := inferInstance
  deployedTag := ()

/-- **(TOOTH — the ROOT floor is REFUTABLE.)** The broken deployment's root-collision game is solvable
at every tag (`[1] ≠ [1,1]`, both zero-free, both rooting to `0`), so it has no unrestricted-class
floor. So the floor is a GENUINE constraint — a broken root refutes it — not vacuously true. -/
theorem brokenQueue_root_floor_top_false :
    ¬ Hard (rootCollisionGame brokenQueue) (fun _ => True) :=
  not_hard_top_of_always_solvable (rootCollisionGame brokenQueue)
    (fun _ => ⟨([], [])⟩)
    (fun _ _ => ⟨([1], [1, 1]), by decide, by decide, by decide, rfl⟩)

/-! ## §7b — ⚑ THE KEYED-ROM SUCCESSOR: the dequeue dichotomy DISCHARGED on the PROVED floor.

§5's `_advantage_bound` keystones are the honest fixed-hash statements; their `hroot`/`hleaf`
`Hard … Eff` hypotheses are PARAMETERS with no known non-vacuous instantiation (§7: `⊤` FALSE at the
deployed BLAKE3 root and leaf, `⊥` vacuous, no cost model). The DISCHARGED successor moves the floor
where it is a THEOREM: the keyed random-oracle model (`Crypto.KeyedRomFloor.keyedRom_hard`, the
birthday bound), the forger an ORACLE PROGRAM with QUERY-COUNTED cost, the oracle sampled AFTER the
program is fixed. The dichotomy survives INTACT: the composed dequeue forgery is a `RomForgery` whose
win relation NESTS the oracle (the window absorbs the entry's leaf digest, which is itself an oracle
answer), and the union bound runs over the ONE sampled oracle both layer carriers share
(`RomCarrierSites.chained_rom_binds` — the `Exec.SystemRootsBindingReduction.cellRoots_binds_rom`
pattern; the root-layer extractor RE-QUERIES the two leaf digests, paying `+2` queries).

⚑ **THE MODELLING STEP, STATED (not smuggled)** — `RomCarrierSites`' header caveat, inherited: the
sampled `H` replaces the fixed public `blake3_binary_root`/`hash_entry` (a deliberate labelled
idealisation, NOT a derivation); the digest space is `λ`-growing where the deployed digest is a FIXED
256-bit value; the message domain is the TRUNCATED deployed shape — a pending window of at most `m`
remaining leaves beside the head leaf limb (`Fin (2 ^ l) × BVec (Fin (2 ^ l)) m`, the deployed
`leafHash head :: rest` nesting with the leaf limbs oracle answers), domain-separated by constructor
from the entry-leaf shape inside ONE family. ⚑ The interior binary-tree structure of
`blake3_binary_root` is deployed-side: the model commits the window in ONE query (the digest-layer
coarse-graining, exactly `SystemRootsBindingReduction`'s `rootsRomCarrier` move). The zero-free side
condition of `rootCollisionGame` has no ROM counterpart because the padding alias it guards against
is a property of the FIXED padded scheme, not of the sampled oracle — the truncated window shape
carries its length tag instead, which is the honest version of the same discrimination. -/

open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomBindingReduction
  (RomCarrier RomCarrierComp romCarrierGame RomCarrierEff romCarrierAdv romCarrier_binds
   romCarrier_choiceForger_excluded)
open Dregg2.Crypto.RomBindingReduction.OracleComp (mapOut mapOut_eval mapOut_queryBounded)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily flatFamily_card_R taggedCarrier BVec flatSite_binds constTripleComp constTriple_in_eff
   constTriple_gameAdv_pos constTriple_binds RomForgery RomForgeryEff chained_rom_binds
   polyBounded_sq_add_two winProb_pos_of_witness)
open Dregg2.Crypto.RomCarrierSites.OracleComp (bindComp bindComp_eval bindComp_queryBounded)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)

/-- **THE QUEUE KEYED ROM FAMILY** — keyed by the DEPLOYED tag space `D.Tag`, over the two absorbed
shapes domain-separated by constructor: `inl` a truncated pending window (head-leaf limb + at most
`m` remaining leaf limbs, each limb an oracle answer — the deployed `leafHash head :: rest` nesting),
`inr` an entry (the leaf layer). One family, one sampled oracle — what makes the union bound a
`winProb` fact. -/
def queueRomFamily {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ) : KeyedRomFamily :=
  flatFamily D.Tag D.tagFintype tagDec D.tagNonempty
    (fun l => (Fin (2 ^ l) × BVec (Fin (2 ^ l)) m) ⊕ Entry)
    (fun l => by letI := entryFin; letI := D.entryDecEq; infer_instance)
    (fun l => by letI := entryFin; letI := D.entryDecEq; infer_instance)
    (fun l => ⟨Sum.inr entryNe.some⟩)

/-- **THE ROOT-LAYER CARRIER** — commitment `H (t, inl window)`: the pending-window root binds the
head-leaf limb AND the whole remaining window. `Sum.inl` is injective on the nose. -/
def queueRootRomCarrier {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomCarrier (queueRomFamily D entryFin entryNe tagDec m) :=
  taggedCarrier _ (fun _ => Unit) (fun l => Fin (2 ^ l) × BVec (Fin (2 ^ l)) m)
    (fun _ => inferInstance) (fun _ _ v => Sum.inl v) (fun _ _ _ _ h => Sum.inl.inj h)

/-- **THE LEAF-LAYER CARRIER** — commitment `H (t, inr entry)`: the entry-leaf commitment binds the
whole entry. -/
def queueLeafRomCarrier {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomCarrier (queueRomFamily D entryFin entryNe tagDec m) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => Entry) (fun _ => D.entryDecEq)
    (fun _ _ e => Sum.inr e) (fun _ _ _ _ h => Sum.inr.inj h)

/-- **⚑ RE-GROUNDED ROOT LAYER, DISCHARGED** — every query-bounded window equivocator has NEGLIGIBLE
advantage: the honest successor of the `RootCR` consumer's root horn. -/
theorem queueRoot_binds_rom {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (queueRomFamily D entryFin entryNe tagDec m)
      (queueRootRomCarrier D entryFin entryNe tagDec m)))
    (hA : RomCarrierEff (queueRomFamily D entryFin entryNe tagDec m)
      (queueRootRomCarrier D entryFin entryNe tagDec m) Q A) :
    Negl (gameAdv (romCarrierGame (queueRomFamily D entryFin entryNe tagDec m)
      (queueRootRomCarrier D entryFin entryNe tagDec m)) A) :=
  romCarrier_binds _ _ Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _) A hA

/-- **⚑ RE-GROUNDED LEAF LAYER, DISCHARGED** — the honest successor of the `LeafCR` consumer's leaf
horn. -/
theorem queueLeaf_binds_rom {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (queueRomFamily D entryFin entryNe tagDec m)
      (queueLeafRomCarrier D entryFin entryNe tagDec m)))
    (hA : RomCarrierEff (queueRomFamily D entryFin entryNe tagDec m)
      (queueLeafRomCarrier D entryFin entryNe tagDec m) Q A) :
    Negl (gameAdv (romCarrierGame (queueRomFamily D entryFin entryNe tagDec m)
      (queueLeafRomCarrier D entryFin entryNe tagDec m)) A) :=
  romCarrier_binds _ _ Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _) A hA

/-- **THE COMPOSED DEQUEUE FORGERY** — the dichotomy's endpoint as ONE break over the shared sampled
oracle: two claimed `(entry, remaining-window)` pairs, DISTINCT, whose NESTED deployed commitments
agree — `H (t, inl (H (t, inr e), w))` on both sides. The entry's leaf digest is genuinely
re-absorbed by the window commitment: the oracle appears INSIDE the win relation, which is exactly
what neither single carrier can say and what `verifyDequeue`'s recompute does. -/
def dequeueRomForgery {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ) :
    RomForgery (queueRomFamily D entryFin entryNe tagDec m) where
  Ans := fun l => D.Tag × (Entry × BVec (Fin (2 ^ l)) m) × (Entry × BVec (Fin (2 ^ l)) m)
  wins := fun l H a =>
    a.2.1 ≠ a.2.2 ∧
      H (a.1, Sum.inl (H (a.1, Sum.inr a.2.1.1), a.2.1.2))
        = H (a.1, Sum.inl (H (a.1, Sum.inr a.2.2.1), a.2.2.2))
  winsDec := fun l H a => by
    letI := D.entryDecEq
    letI := ((queueRomFamily D entryFin entryNe tagDec m).toRomFamily).rDec l
    infer_instance

/-- **THE ROOT-LAYER EXTRACTION** — run the composed forger, then RE-QUERY the two claimed entries'
leaf digests and answer with the two full windows: `bindComp` with a two-query continuation, so the
budget grows by exactly `2` (the priced re-walk). -/
def dequeueRomComp₁ {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (M : ∀ l, OracleComp ((queueRomFamily D entryFin entryNe tagDec m).toRomFamily.D l)
      ((queueRomFamily D entryFin entryNe tagDec m).toRomFamily.R l)
      ((dequeueRomForgery D entryFin entryNe tagDec m).Ans l)) :
    RomCarrierComp (queueRomFamily D entryFin entryNe tagDec m)
      (queueRootRomCarrier D entryFin entryNe tagDec m) :=
  fun l => bindComp (M l) (fun a =>
    OracleComp.query (a.1, Sum.inr a.2.1.1) (fun d =>
      OracleComp.query (a.1, Sum.inr a.2.2.1) (fun d' =>
        OracleComp.pure ((a.1, ()), (d, a.2.1.2), (d', a.2.2.2)))))

/-- **THE LEAF-LAYER EXTRACTION** — a pure post-map: answer with the two claimed entries.
`mapOut`, budget preserved. -/
def dequeueRomComp₂ {Entry : Type} (D : QueueDeployment Entry) (entryFin : Fintype Entry)
    (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (M : ∀ l, OracleComp ((queueRomFamily D entryFin entryNe tagDec m).toRomFamily.D l)
      ((queueRomFamily D entryFin entryNe tagDec m).toRomFamily.R l)
      ((dequeueRomForgery D entryFin entryNe tagDec m).Ans l)) :
    RomCarrierComp (queueRomFamily D entryFin entryNe tagDec m)
      (queueLeafRomCarrier D entryFin entryNe tagDec m) :=
  fun l => mapOut (fun a => ((a.1, ()), a.2.1.1, a.2.2.1)) (M l)

/-- **⚑⚑ RE-GROUNDED `dequeue_proof_pins` / `dequeue_forgery_refused`, DISCHARGED ON THE PROVED
FLOOR** — the keyed-ROM successor of §5's `dequeue_proof_pins_advantage_bound`, dichotomy intact:
every query-bounded composed dequeue forger has NEGLIGIBLE advantage. The chain peel is the §4 case
split at the sampled oracle (windows-with-digests equal → the claim differs in the ENTRY while the
leaves collide, the LEAF horn; distinct → the ROOT horn); the two extracted programs are `bindComp`
(budget `Q + 2`) and `mapOut` (budget `Q`); the union bound runs over the ONE sampled oracle; each
horn dies by the birthday floor. NO `Hard` hypothesis — nothing refutable is carried. -/
theorem dequeue_proof_pins_binds_rom {Entry : Type} (D : QueueDeployment Entry)
    (entryFin : Fintype Entry) (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (dequeueRomForgery D entryFin entryNe tagDec m).game)
    (hA : RomForgeryEff (queueRomFamily D entryFin entryNe tagDec m)
      (dequeueRomForgery D entryFin entryNe tagDec m) Q A) :
    Negl (gameAdv (dequeueRomForgery D entryFin entryNe tagDec m).game A) := by
  obtain ⟨M, hM, hrun⟩ := hA
  refine chained_rom_binds (dequeueRomForgery D entryFin entryNe tagDec m)
    (queueRootRomCarrier D entryFin entryNe tagDec m)
    (queueLeafRomCarrier D entryFin entryNe tagDec m)
    (fun l => Q l + 2) Q (polyBounded_sq_add_two Q hQ) hQ
    (flatFamily_card_R _ _ _ _ _ _ _ _) A
    (romCarrierAdv _ _ (dequeueRomComp₁ D entryFin entryNe tagDec m M))
    (romCarrierAdv _ _ (dequeueRomComp₂ D entryFin entryNe tagDec m M))
    ?_
    ⟨dequeueRomComp₁ D entryFin entryNe tagDec m M,
      fun l => bindComp_queryBounded (hM l)
        (fun a => QueryBounded.query 1 _ _ (fun _ => QueryBounded.query 0 _ _
          (fun _ => QueryBounded.pure 0 _))), fun _ _ => rfl⟩
    ⟨dequeueRomComp₂ D entryFin entryNe tagDec m M,
      fun l => mapOut_queryBounded _ (hM l), fun _ _ => rfl⟩
  intro l H hwin
  have hB₁run : (romCarrierAdv _ _ (dequeueRomComp₁ D entryFin entryNe tagDec m M)).run l H
      = (((A.run l H).1, ()),
          (H ((A.run l H).1, Sum.inr (A.run l H).2.1.1), (A.run l H).2.1.2),
          (H ((A.run l H).1, Sum.inr (A.run l H).2.2.1), (A.run l H).2.2.2)) := by
    show (dequeueRomComp₁ D entryFin entryNe tagDec m M l).eval H = _
    unfold dequeueRomComp₁
    erw [bindComp_eval, ← hrun l H]
    rfl
  have hB₂run : (romCarrierAdv _ _ (dequeueRomComp₂ D entryFin entryNe tagDec m M)).run l H
      = (((A.run l H).1, ()), (A.run l H).2.1.1, (A.run l H).2.2.1) := by
    show (dequeueRomComp₂ D entryFin entryNe tagDec m M l).eval H = _
    unfold dequeueRomComp₂
    erw [mapOut_eval, ← hrun l H]
    rfl
  obtain ⟨hne, heq⟩ := hwin
  by_cases hwin' : (H ((A.run l H).1, Sum.inr (A.run l H).2.1.1), (A.run l H).2.1.2)
      = (H ((A.run l H).1, Sum.inr (A.run l H).2.2.1), (A.run l H).2.2.2)
  · -- EQUAL full windows: the leaf digests agree and the remaining windows agree, so the claim
    -- differs in the ENTRY while the leaves collide — the LEAF horn.
    refine Or.inr ?_
    rw [hB₂run]
    have hd := congrArg Prod.fst hwin'
    have hw := congrArg Prod.snd hwin'
    simp only at hd hw
    refine ⟨fun hc => hne (Prod.ext hc hw), hd⟩
  · -- DISTINCT full windows with one root: the ROOT horn.
    refine Or.inl ?_
    rw [hB₁run]
    exact ⟨hwin', heq⟩

/-- **⚑ RE-GROUNDED `queueDequeueProven_pins_root_transition` / `_refuses_forgery`, DISCHARGED** —
the WELD keystone's forger is a forger against the composed break, so the same discharged bound. -/
theorem queueDequeueProven_pins_root_transition_binds_rom {Entry : Type}
    (D : QueueDeployment Entry) (entryFin : Fintype Entry) (entryNe : Nonempty Entry)
    (tagDec : DecidableEq D.Tag) (m : ℕ) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (dequeueRomForgery D entryFin entryNe tagDec m).game)
    (hA : RomForgeryEff (queueRomFamily D entryFin entryNe tagDec m)
      (dequeueRomForgery D entryFin entryNe tagDec m) Q A) :
    Negl (gameAdv (dequeueRomForgery D entryFin entryNe tagDec m).game A) :=
  dequeue_proof_pins_binds_rom D entryFin entryNe tagDec m Q hQ A hA

/-- **⚑ RE-GROUNDED `dequeue_proof_unique` / `stale_proof_refused`, DISCHARGED** — same forger, same
floor, same discharged bound. -/
theorem dequeue_proof_unique_binds_rom {Entry : Type} (D : QueueDeployment Entry)
    (entryFin : Fintype Entry) (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (dequeueRomForgery D entryFin entryNe tagDec m).game)
    (hA : RomForgeryEff (queueRomFamily D entryFin entryNe tagDec m)
      (dequeueRomForgery D entryFin entryNe tagDec m) Q A) :
    Negl (gameAdv (dequeueRomForgery D entryFin entryNe tagDec m).game A) :=
  dequeue_proof_pins_binds_rom D entryFin entryNe tagDec m Q hQ A hA

/-- **(TOOTH — the composed class is INHABITED with POSITIVE advantage.)** The `0`-query constant
answerer on two claims that differ in the remaining window is in `RomForgeryEff` at every budget, and
the composed game is winnable at every parameter (the constant oracle collapses both nested
commitments) — the discharged bound bounds something genuinely nonzero. -/
theorem dequeueRom_class_inhabited_pos {Entry : Type} (D : QueueDeployment Entry)
    (entryFin : Fintype Entry) (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag)
    (m : ℕ) (hm : 0 < m) (Q : ℕ → ℕ) :
    ∃ A, RomForgeryEff (queueRomFamily D entryFin entryNe tagDec m)
        (dequeueRomForgery D entryFin entryNe tagDec m) Q A
      ∧ ∀ l, 0 < gameAdv (dequeueRomForgery D entryFin entryNe tagDec m).game A l := by
  obtain ⟨t₀⟩ := D.tagNonempty
  have e₀ := entryNe.some
  refine ⟨⟨fun l _ => (t₀, (e₀, (⟨0, Nat.succ_pos m⟩, fun _ => none)),
      (e₀, (⟨1, by omega⟩, fun _ => none)))⟩,
    ⟨fun l => OracleComp.pure (t₀, (e₀, (⟨0, Nat.succ_pos m⟩, fun _ => none)),
      (e₀, (⟨1, by omega⟩, fun _ => none))),
      fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩, ?_⟩
  intro l
  refine @winProb_pos_of_witness _
    ((dequeueRomForgery D entryFin entryNe tagDec m).game.instFin l) _
    (fun _ => ⟨0, by positivity⟩) ?_
  refine (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ l _).mpr ⟨?_, rfl⟩
  intro hc
  have : (0 : ℕ) = 1 := congrArg (fun p : Entry × BVec (Fin (2 ^ l)) m => p.2.1.val) hc
  omega

/-- **(TOOTH — a non-negligible ROOT-layer forger is OUTSIDE the class.)** -/
theorem queueRootRom_nonNegl_forger_excluded {Entry : Type} (D : QueueDeployment Entry)
    (entryFin : Fintype Entry) (entryNe : Nonempty Entry) (tagDec : DecidableEq D.Tag) (m : ℕ)
    (Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (queueRomFamily D entryFin entryNe tagDec m)
      (queueRootRomCarrier D entryFin entryNe tagDec m)))
    (hnn : ¬ Negl (gameAdv (romCarrierGame (queueRomFamily D entryFin entryNe tagDec m)
      (queueRootRomCarrier D entryFin entryNe tagDec m)) A)) :
    ¬ RomCarrierEff (queueRomFamily D entryFin entryNe tagDec m)
      (queueRootRomCarrier D entryFin entryNe tagDec m) Q A :=
  romCarrier_choiceForger_excluded _ _ Q hQ (flatFamily_card_R _ _ _ _ _ _ _ _) A hnn

/-! ## §8 — `PairCR` / `LenBindCR`: FALSE-PROVED (the §7 hardening's carriers).

These two carry the PROPOSED level-tagged hardening (`QueueRoot` §7, `taggedRoot_injective`), which
Rust has NOT adopted — switching `blake3_binary_root` to the tagged scheme changes every queue
`message_root` on the wire, so it needs a coordinated root-format migration (`QueueRoot`'s own ⚠).
They are refuted here as named; game-re-grounding a hardening that is not deployed is lower value than
refuting it honestly, and the repair path is mechanical: the same `Deployment`/collision-game/extractor
shape as §2-§5, instantiated at `tRoot`/`bindLen`, with `taggedRoot_injective`'s length-then-shape peel
as the win-preserving map. -/

/-- **TOOTH — `PairCR` is FALSE for a range-bounded node hash.** The 2-to-1 node combine
`blake3(0x01 ‖ l ‖ r)` compresses the INFINITE `Int × Int` into a bounded digest, so it cannot be
pairwise injective. Mirrors `HashFloorHonesty.compressInjective_false_of_finite_range`. -/
theorem pairCR_false_of_finite_range (combine : Int → Int → Int)
    (hfin : (Set.range (fun p : Int × Int => combine p.1 p.2)).Finite) : ¬ PairCR combine := by
  intro hC
  refine not_injective_of_finite_range (fun p : Int × Int => combine p.1 p.2) hfin ?_
  rintro ⟨a, b⟩ ⟨c, d⟩ heq
  obtain ⟨h1, h2⟩ := hC a b c d heq
  simp [h1, h2]

/-- **TOOTH (deployed form) — `PairCR` is FALSE at a 256-bit node hash.** -/
theorem pairCR_false_blake3 (combine : Int → Int → Int)
    (hb : ∀ a b, 0 ≤ combine a b ∧ combine a b < (2 : Int) ^ 256) : ¬ PairCR combine :=
  pairCR_false_of_finite_range combine
    (finite_range_of_bound (fun p : Int × Int => combine p.1 p.2) _ (fun p => hb p.1 p.2))

/-- **TOOTH — `LenBindCR` is FALSE for a range-bounded length wrap.** The root wrap
`blake3(0x02 ‖ len ‖ root)` compresses the INFINITE `Nat × Int` into a bounded digest, so it cannot be
jointly injective in the length and the root. -/
theorem lenBindCR_false_of_finite_range (bindLen : Nat → Int → Int)
    (hfin : (Set.range (fun p : Nat × Int => bindLen p.1 p.2)).Finite) : ¬ LenBindCR bindLen := by
  intro hB
  refine not_injective_of_finite_range (fun p : Nat × Int => bindLen p.1 p.2) hfin ?_
  rintro ⟨n, x⟩ ⟨m, y⟩ heq
  obtain ⟨h1, h2⟩ := hB n x m y heq
  simp [h1, h2]

/-- **TOOTH (deployed form) — `LenBindCR` is FALSE at a 256-bit length wrap.** -/
theorem lenBindCR_false_blake3 (bindLen : Nat → Int → Int)
    (hb : ∀ n x, 0 ≤ bindLen n x ∧ bindLen n x < (2 : Int) ^ 256) : ¬ LenBindCR bindLen :=
  lenBindCR_false_of_finite_range bindLen
    (finite_range_of_bound (fun p : Nat × Int => bindLen p.1 p.2) _ (fun p => hb p.1 p.2))

/-- **⚑ THE HARDENING DOES NOT ESCAPE THE FINDING.** `QueueRoot.taggedRoot_RootCR` discharges `RootCR`
from `Function.Injective tagLeaf` + `PairCR` + `LenBindCR` — so if the hardened scheme's carriers held,
`RootCR` would hold. But §1a proves `RootCR` FALSE for any range-bounded root, and the tagged root IS
range-bounded at a real BLAKE3. Contrapositive: at the deployed digest the hardening's carrier
conjunction is itself FALSE. The upgrade fixes the PADDING ALIAS (a structural bug, and it really does
fix it — `tagged_kills_pad_alias`); it does NOT and cannot fix the counting bug. Only the `Eff`
parameter does. -/
theorem tagged_carriers_false_at_bounded_root {tagLeaf : Int → Int} {combine : Int → Int → Int}
    {bindLen : Nat → Int → Int}
    (hb : ∀ ls, 0 ≤ Dregg2.Apps.QueueRoot.taggedRoot tagLeaf combine bindLen ls ∧
      Dregg2.Apps.QueueRoot.taggedRoot tagLeaf combine bindLen ls < (2 : Int) ^ 256) :
    ¬ (Function.Injective tagLeaf ∧ PairCR combine ∧ LenBindCR bindLen) := by
  rintro ⟨hT, hC, hB⟩
  exact rootCR_false_blake3 _ hb (Dregg2.Apps.QueueRoot.taggedRoot_RootCR hT hC hB)

#assert_all_clean [
  finite_range_of_bound,
  zfRep_zeroFree,
  zfRep_injective,
  exists_zeroFree_collision_of_finite_range,
  rootCR_false_of_finite_range,
  rootCR_false_blake3,
  leafCR_false_of_compressing,
  leafCR_false_of_finite_range,
  exists_leaf_collision_of_compressing,
  deployed_root_is_family_instance,
  deployed_leaf_is_family_instance,
  rootCollisionGame_wins_iff,
  leafCollisionGame_wins_iff,
  dequeueForgeryGame_wins_iff,
  forgery_wins_imp,
  forgery_adv_le,
  dequeue_proof_pins_advantage_bound,
  queueDequeueProven_pins_root_transition_advantage_bound,
  dequeue_proof_unique_advantage_bound,
  the_repaired_bound_fires_on_the_right_floors,
  root_floor_top_false_of_compressing,
  root_floor_top_false_blake3,
  leaf_floor_top_false_of_compressing,
  root_floor_bot_vacuous,
  leaf_floor_bot_vacuous,
  brokenQueue_root_floor_top_false,
  pairCR_false_of_finite_range,
  pairCR_false_blake3,
  lenBindCR_false_of_finite_range,
  lenBindCR_false_blake3,
  tagged_carriers_false_at_bounded_root,
  queueRoot_binds_rom,
  queueLeaf_binds_rom,
  dequeue_proof_pins_binds_rom,
  queueDequeueProven_pins_root_transition_binds_rom,
  dequeue_proof_unique_binds_rom,
  dequeueRom_class_inhabited_pos,
  queueRootRom_nonNegl_forger_excluded
]

end Dregg2.Apps.QueueRootFloorRegrounded

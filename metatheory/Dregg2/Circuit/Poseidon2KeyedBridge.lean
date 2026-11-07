/-
# `Dregg2.Circuit.Poseidon2KeyedBridge` — bridging the DEPLOYED UNKEYED Poseidon2 sponge to the
KEYED collision game (the honest keyed-from-unkeyed-via-domain-separation model).

## The obligation this closes

`HashFloorHonesty.lean` replaced the VACUOUS injective hash floor (`Poseidon2Binding.Poseidon2SpongeCR`,
false at real BabyBear params by pigeonhole) with what it called a PROPER computational floor —
`CollisionResistant F` over a **KEYED** hash family `F` — and `FloorRegroundedConsumers.lean` re-seated
every STARK/FRI/binding
consumer (`OodCommitmentBinding`, `FriSoundness.oracle_binding`, `AirSoundness.committed_trace_pinned`,
`FinBindsKernel`) onto that keyed floor as advantage bounds.

Keying is LOAD-BEARING: an UNKEYED fixed hash lets an adversary hardcode a known collision (advantage
`1`), collapsing the floor. BUT the DEPLOYED Poseidon2 (`p3-poseidon2-circuit-air` BabyBear width-16,
`Poseidon2Binding.babyBearD4W16`) is a FIXED, UNKEYED sponge `List ℤ → ℤ`. So there is a genuine
"bridge to the real object" gap: the consumers rested on a collision floor for an ABSTRACT keyed
family `F`, while the prover computes a fixed unkeyed function. This file connects the two.

⚑ **AND THE FLOOR IT BRIDGED TO IS ITSELF DELETED (2026-07-28).** `HashFloorHonesty.CollisionResistant`
was `FloorGames.HashCRHardQuant F (fun _ => True)` under a name that hid the adversary class, and that
class is exactly what makes it FALSE for a compressing hash. The BRIDGE below is untouched and still
correct — the keyed family, the domain-separation model and the faithfulness lemmas were never the
problem. What changed is that `DomainSeparatedCR`'s body now spells out the `⊤`, so the ⚠⚠ warning at
§3 no longer needs a lemma to be visible. The honest successor with a real class is
`Circuit.DomainSeparatedCREffRegrounded.DomainSeparatedCREff D Eff`.

## The standard bridge: domain separation IS the key

The deployed sponge's effective "key" is its **domain-separation tag** — the per-use prefix
(`PaddingFreeSponge` over the round-constant/rate-capacity regime, absorbed ahead of the message) that
the deployment uses to separate the Merkle-node hash from the leaf hash from the log hash from the OOD
commitment. Modelling that tag as the key of a keyed family is the standard way a real FIXED hash
receives a keyed collision-resistance treatment (the keyed-from-unkeyed / domain-separation model). The
keyed CR game then FAITHFULLY MODELS the deployed hash: its win event at the deployed tag is
DEFINITIONALLY a collision of the deployed unkeyed function `xs ↦ sponge (tag ++ xs)`.

  * **§1** — `DomainSeparatedSponge`: the deployed unkeyed sponge + its finite domain-separation tag
    space + the tag-absorption encoding + the specific deployed tag the prover uses.
  * **§2** — `poseidon2KeyedFamily`: that bundle lifted to a `HashFloorHonesty.KeyedHashFamily`, keyed
    by the domain-separation tag. FAITHFULNESS (`deployed_hash_is_family_instance`,
    `wins_iff_deployed_collision`): the deployed fixed hash IS the family instance at the deployed tag,
    and a keyed-game win at any tag is exactly a deployed-hash collision — the game models the real
    object, no idealization.
  * **§3** — the NAMED domain-separation floor `DomainSeparatedCR D := HashCRHardQuant
    (poseidon2KeyedFamily D) ⊤`. Read the ⚠⚠ at §3 BEFORE reading the rest of this bullet, which is
    the 07-22 claim and is WRONG at the `⊤` this floor is fixed at: SATISFIABLE (a
    domain-separated family over an injective sponge is CR — `domainSeparatedCR_of_injective_sponge`,
    witnessed concretely by `Reference.refSponge` at the REAL `babyBearD4W16` params) and REFUTABLE (a
    broken domain separation — the tag-ignoring constant sponge — has advantage `1`,
    `brokenDomainSep_not_CR`). NOT an injectivity/existence-refutation: the win event is *finding* a
    collision over a random tag, not the mere *existence* of one.
  * **§4** — the connection: under `DomainSeparatedCR D`, the `FloorRegroundedConsumers` advantage
    bounds fire at `F := poseidon2KeyedFamily D`, so the deployed circuit's keyed-CR floor is BRIDGED to
    the real deployed hash — `FinBindsKernel`'s root binder, the OOD/Merkle/trace binders, and the apex
    two-hash forgery advantage all rest on the deployed sponge's domain-separation CR.

## Axiom hygiene

`#assert_axioms` ⊆ {propext, Classical.choice, Quot.sound}; NO `sorryAx`/`sorry`, NO fresh `axiom`. The
named floor `DomainSeparatedCR` is a HYPOTHESIS (never an `axiom`) and is refutable — but it is NOT
satisfiable at the deployed sponge (§3's ⚠⚠), so the bridge theorems below are genuine implications
with a FALSE antecedent, which is what `DomainSeparatedCREffRegrounded` exists to repair. The keyed
family reuses `HashFloorHonesty.KeyedHashFamily` and the deployed sponge is the `Poseidon2Binding`
`List ℤ → ℤ` object.
-/
import Dregg2.Circuit.HashFloorHonesty
import Dregg2.Circuit.FloorRegroundedConsumers
import Dregg2.Circuit.Poseidon2Binding
import Dregg2.Crypto.SpongeCarrierReduction

namespace Dregg2.Circuit.Poseidon2KeyedBridge

open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_bot)
open Dregg2.Crypto.ConcreteSecurity (Ensemble Negl PolyBounded negl_zero not_negl_one)
open Dregg2.Crypto

set_option autoImplicit false

/-! ## §1 — the deployed unkeyed sponge with its domain-separation structure.

The deployed Poseidon2 (`Poseidon2Binding.babyBearD4W16`) is a fixed sponge `sponge : List ℤ → ℤ`. Its
effective KEY is the domain-separation tag: a finite set of per-use prefixes the deployment absorbs
ahead of the message. `deployedTag` is the specific tag the prover computes at a given use-site (so the
deployed FIXED function is `xs ↦ sponge (tagCode deployedTag ++ xs)`). -/

/-- The deployed unkeyed Poseidon2 sponge together with its domain-separation structure. `sponge` is the
`Poseidon2Binding` `List ℤ → ℤ` object (the real `babyBearD4W16` PaddingFreeSponge); `Tag` is the
finite, inhabited domain-separation tag space; `tagCode` is how a tag is absorbed as a prefix;
`deployedTag` is the specific tag the deployment uses. -/
structure DomainSeparatedSponge where
  /-- The deployed unkeyed Poseidon2 sponge (`Poseidon2Binding`'s `List ℤ → ℤ`). -/
  sponge : List ℤ → ℤ
  /-- The domain-separation tag space (the effective key). -/
  Tag : Type
  /-- The tag space is finite (the CR game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- How a domain-separation tag is absorbed: as a field-element prefix ahead of the message. -/
  tagCode : Tag → List ℤ
  /-- The specific domain-separation tag the deployment computes at this use-site. -/
  deployedTag : Tag

/-- The deployed sponge domain-separated by a SPECIFIC tag: `xs ↦ sponge (tagCode t ++ xs)` — a fixed
unkeyed function per tag. -/
def DomainSeparatedSponge.hashAt (D : DomainSeparatedSponge) (t : D.Tag) (xs : List ℤ) : ℤ :=
  D.sponge (D.tagCode t ++ xs)

/-- The DEPLOYED fixed unkeyed function the prover actually computes: the sponge over the deployed tag's
prefix concatenated with the message. This is the real object the bridge points at. -/
def DomainSeparatedSponge.deployedHash (D : DomainSeparatedSponge) (xs : List ℤ) : ℤ :=
  D.hashAt D.deployedTag xs

/-! ## §2 — the deployed sponge lifted to a KEYED family (domain separation = the key). -/

/-- **`poseidon2KeyedFamily D`** — the deployed unkeyed Poseidon2 sponge lifted to a
`HashFloorHonesty.KeyedHashFamily`, keyed by its domain-separation tag: `H n t xs = sponge (tagCode t ++
xs)`. Input domain `List ℤ` (the sponge domain), output `ℤ` (the BabyBear field element). This is the
object `FloorRegroundedConsumers`'s keyed collision floor is realized at for the real hash. -/
@[reducible] def poseidon2KeyedFamily (D : DomainSeparatedSponge) : KeyedHashFamily where
  Key := fun _ => D.Tag
  Input := List ℤ
  Out := ℤ
  H := fun _ t xs => D.sponge (D.tagCode t ++ xs)
  keyFintype := fun _ => D.tagFintype
  keyNonempty := fun _ => D.tagNonempty
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **FAITHFULNESS (1/2).** The deployed FIXED unkeyed hash IS the keyed family's instance at the
deployed tag — no idealization, a definitional equality. So the keyed CR game (over the family) is a
game about the very function the prover computes. -/
theorem deployed_hash_is_family_instance (D : DomainSeparatedSponge) (n : ℕ) :
    D.deployedHash = (poseidon2KeyedFamily D).H n D.deployedTag := rfl

/-- **FAITHFULNESS (2/2).** A keyed-game WIN at tag `t` is DEFINITIONALLY a collision of the deployed
unkeyed function `xs ↦ sponge (tagCode t ++ xs)`: the finder outputs two DISTINCT inputs that the
domain-separated sponge maps to the same field element. The game measures *finding* a real collision,
not the *existence* of one — this is what makes modelling the fixed hash by the keyed game honest. -/
theorem wins_iff_deployed_collision (D : DomainSeparatedSponge) (A : CollisionFinder (poseidon2KeyedFamily D))
    (n : ℕ) (t : D.Tag) :
    A.wins n t = true ↔
      (A.find n t).1 ≠ (A.find n t).2 ∧
        D.hashAt t (A.find n t).1 = D.hashAt t (A.find n t).2 := by
  simp only [CollisionFinder.wins, Bool.and_eq_true, decide_eq_true_eq, poseidon2KeyedFamily,
    DomainSeparatedSponge.hashAt]

/-! ## §3 — the NAMED domain-separation floor: SATISFIABLE + REFUTABLE (a genuine floor). -/

/-- **`DomainSeparatedCR D`** — the deployed Poseidon2's domain-separation collision-resistance: the
keyed family (keyed by the domain-separation tag) has the collision floor AT THE UNRESTRICTED
ADVERSARY CLASS. This was presented as the honest deployed-hash assumption — the
keyed-from-unkeyed-via-domain-separation model. It is a HYPOTHESIS (never an `axiom`), and it is
refutable (§ `brokenDomainSep_not_CR`) and satisfiable only by a non-compressing sponge
(§ `domainSeparatedCR_of_injective_sponge`), which is the whole trouble — read the ⚠⚠ next.

⚠⚠ **BROKEN AS NAMED — THIS FLOOR IS FALSE AT THE DEPLOYED SPONGE, so every §4 consumer below
(including the APEX `deployed_lightclientUnfoolable_advantage_bound`) is VACUOUSLY TRUE at deployed
parameters.** `Circuit.DomainSeparatedCREffRegrounded.domainSeparatedCR_false_babyBear` proves it;
`docs/deos/VACUITY-SWEEP.md` FINDING 2. The paragraph above claiming this is "a GENUINE floor …
SATISFIABLE and REFUTABLE … NOT an injectivity/existence-refutation" is WRONG, and `FloorGames` (07-16)
is why: this floor IS `HashCRHardQuant F ⊤` (as of 2026-07-28 its body says so literally) and
`Hard G ⊤ ↔ Negl (solvableFrac G)`, so it IS the existence floor, hence FALSE
wherever collisions merely EXIST — which at a BabyBear-bounded sponge is every tag. Same pigeonhole
that killed `Poseidon2SpongeCR`, one `Classical.choice` later. Domain separation does not help: the
prefix is injective, but the prefixed map still lands in one bounded field.

⚠ **AND `refDomainSep_CR` BELOW IS THE TELL, NOT THE REASSURANCE.**
`domainSeparatedCR_forces_unbounded_sponge` proves anything discharging this floor has an
INFINITE-RANGE sponge — i.e. is not a field hash at all. That is exactly why `Reference.refSponge` (an
injective `Encodable`-style map into ALL of `ℤ`) satisfies it and the deployed BabyBear sponge cannot.
Toy witness satisfiable, real hash false — `HashFloorHonesty`'s own diagnosis of its own predecessor,
recurring here, in the file written to cure it.

⚑ **HONEST SCOPE — nothing here is WRONG and nothing deployed is unsafe today.** The consumers are
true; they are true VACUOUSLY, so they transport no security. This file's REAL contributions STAND and
are untouched: the keyed family, the domain-separation model, and the faithfulness lemmas
(`deployed_hash_is_family_instance`, `wins_iff_deployed_collision`) — the game genuinely IS about the
deployed function. The game was never the problem. The adversary CLASS was.

**The honest replacement is `Circuit.DomainSeparatedCREffRegrounded`** —
`DomainSeparatedCREff D Eff := HashCRHardQuant (poseidon2KeyedFamily D) Eff`: the SAME game over the
SAME family (so every faithfulness lemma applies verbatim) at an EXPLICIT class, with every §4 consumer
re-grounded and `domainSeparatedCREff_top_iff_old` proving this def IS that one at `⊤`. This def is
KEPT so the record and the teeth keep compiling.

⚑ **2026-07-28 — THE BODY NOW SAYS `⊤` OUT LOUD.** It used to read
`CollisionResistant (poseidon2KeyedFamily D)`, and that `def` is DELETED: it WAS
`HashCRHardQuant F (fun _ => True)` wearing a name that hid the adversary class. So this floor's body
is now written the way it always meant, which changes nothing about what it says and everything about
what a reader sees — the field that makes it refuted is on the page instead of one lemma away. It
cannot be defined as `DomainSeparatedCREff D ⊤` because THAT module imports THIS one; the agreement
is `domainSeparatedCREff_top_iff_old`, now true by `Iff.rfl`. -/
def DomainSeparatedCR (D : DomainSeparatedSponge) : Prop :=
  FloorGames.HashCRHardQuant (poseidon2KeyedFamily D) (fun _ => True)

/-- Each keyed instance `xs ↦ sponge (tagCode t ++ xs)` is injective when the underlying sponge is
(domain-separation prefixing is injective — `List.append_right_injective`). -/
theorem family_H_injective_of_injective_sponge {D : DomainSeparatedSponge}
    (hs : Function.Injective D.sponge) (n : ℕ) (t : D.Tag) :
    Function.Injective ((poseidon2KeyedFamily D).H n t) :=
  hs.comp (List.append_right_injective (D.tagCode t))

/-- **(SATISFIABILITY.)** A domain-separated family over an INJECTIVE deployed sponge is
collision-resistant: no finder ever wins, advantage `0`. So the floor is REALIZABLE — a domain-separated
hash satisfies it under the standard model, exactly as a Poseidon2 with proper domain separation is
assumed to. (`Function.Injective sponge` is the idealized-hash shape; it is unsatisfiable at real
BabyBear params — `HashFloorHonesty.poseidon2SpongeCR_false_babyBear` — which is why the DEPLOYED floor
must be the computational `DomainSeparatedCR`, satisfied here by a stand-in to prove non-vacuity.) -/
theorem domainSeparatedCR_of_injective_sponge {D : DomainSeparatedSponge}
    (hs : Function.Injective D.sponge) : DomainSeparatedCR D :=
  FloorGames.hashCRHardQuant_top_of_injective (poseidon2KeyedFamily D)
    (family_H_injective_of_injective_sponge hs)

/-- **The link to the `Poseidon2Binding.Poseidon2SpongeCR` object.** The old (idealized, false-at-real-
params) injective floor `Poseidon2SpongeCR sponge` on the deployed sponge DISCHARGES the honest
`DomainSeparatedCR` floor — the honest keyed floor is strictly WEAKER than (implied by) the old broken
one, and unlike it is satisfiable at real params. So nothing is lost re-grounding onto `DomainSeparatedCR`. -/
theorem domainSeparatedCR_of_poseidon2SpongeCR {D : DomainSeparatedSponge}
    (hCR : Poseidon2Binding.Poseidon2SpongeCR D.sponge) : DomainSeparatedCR D :=
  domainSeparatedCR_of_injective_sponge (fun _ _ h => hCR _ _ h)

/-! ### The refutation: a BROKEN domain separation. -/

/-- A **broken** domain separation: the sponge IGNORES its input entirely (constant `0`), so the
domain-separation tag separates nothing — every pair of distinct inputs collides at every tag. -/
def brokenDomainSep : DomainSeparatedSponge where
  sponge := fun _ => 0
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  tagCode := fun _ => []
  deployedTag := ()

/-- A finder that outputs the distinct pair `([0], [1])` — a genuine collision under the broken sponge. -/
def brokenFinder : CollisionFinder (poseidon2KeyedFamily brokenDomainSep) where
  find := fun _ _ => (([0], [1]) : List ℤ × List ℤ)

theorem brokenFinder_wins (n : ℕ) (k : (poseidon2KeyedFamily brokenDomainSep).Key n) :
    brokenFinder.wins n k = true := by
  simp [CollisionFinder.wins, brokenFinder, poseidon2KeyedFamily, brokenDomainSep]

/-- **(REFUTABILITY.)** The broken domain separation is NOT collision-resistant: the constant finder
wins on every tag, so its advantage is the constant `1`, not negligible. So `DomainSeparatedCR` is
LOAD-BEARING — a broken domain separation refutes it — not vacuously true. -/
theorem brokenDomainSep_not_CR : ¬ DomainSeparatedCR brokenDomainSep := by
  refine FloorGames.hashCRHardQuant_top_false_of_compressing _ ⟨([] : List ℤ)⟩
    (fun _ _ => ⟨[0], [1], ?_, ?_⟩)
  · show ([0] : List ℤ) ≠ [1]
    decide
  · simp [poseidon2KeyedFamily, brokenDomainSep]

/-! ### A SATISFYING witness at the REAL params (non-vacuity of the whole bridge). -/

/-- A concrete domain-separated deployment over `Poseidon2Binding.Reference.refSponge` (the provably-
injective stand-in Poseidon2, tagged with the REAL `babyBearD4W16` params) — a genuine domain-separation
prefix `[7]` ahead of the message. This inhabits `DomainSeparatedSponge` and satisfies `DomainSeparatedCR`,
so the bridge and every consumer connection below FIRE on a concrete instance. -/
def refDomainSep : DomainSeparatedSponge where
  sponge := Poseidon2Binding.Reference.refSponge
  Tag := Unit
  tagFintype := inferInstance
  tagNonempty := inferInstance
  tagCode := fun _ => [7]
  deployedTag := ()

theorem refDomainSep_CR : DomainSeparatedCR refDomainSep :=
  domainSeparatedCR_of_poseidon2SpongeCR Poseidon2Binding.Reference.refSponge_CR

/-! ## §4 — the connection, REBUILT (2026-07-22): the deployed consumers as SECURITY REDUCTIONS.

⚑ **WHAT WAS HERE BEFORE, AND WHY IT WENT.** This section used to export six `deployed_*_advantage_bound`
theorems of the shape

    theorem deployed_oodCommitmentOpening_advantage_bound (D) (hD : DomainSeparatedCR D)
        (opener : CollisionFinder (poseidon2KeyedFamily D))
        : Negl (collisionAdv (poseidon2KeyedFamily D) opener) :=
      FloorRegroundedConsumers.oodCommitmentOpening_advantage_bound hD opener

carrying a DOUBLE defect, both halves fatal on their own:

  1. the consumed `FloorRegroundedConsumers` bound was `P → P` — the hypothesis handed back, with the
     OOD opening named in the theorem's NAME and absent from its STATEMENT (see that file's §0); and
  2. the floor `DomainSeparatedCR D` is PROVED FALSE at deployed BabyBear parameters
     (`DomainSeparatedCREffRegrounded.domainSeparatedCR_false_babyBear`; the ⚠⚠ warning on
     `DomainSeparatedCR` above says so at length). So the whole section was vacuously true at the
     deployed hash — it transported no security to the thing it was written to be about.

The four rebuilt bounds below (2026-07-24, second rebuild) are the KEYED-ROM successors: the same
forgery — one committed root, one shared path, two distinct opened leaves — transposed to the SAMPLED
oracle keyed by the DEPLOYED sponge's own tag space (`FloorRegroundedConsumers` §2's
`merkleOpenRomBreakGame` at `toSpongeKeyed D`). The `IsPolyTime`-discharged forms that briefly stood
here carried `DeployedOpenFloor D` = `HashCRHardQuant (poseidon2KeyedFamily D) (IsPolyTime …)`, which
`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear` REFUTES at the deployed
sponge — they are DELETED with their floor abbrev. The successors carry NO floor hypothesis at all:
the floor is `KeyedRomFloor.keyedRom_hard`, the birthday bound, PROVED. The ROM idealisation is the
labelled modelling step of `RomCarrierSites`' header (ideal `Fin (2 ^ l)` digest vs the deployed
~31-bit felt — the felt-width wound, said out loud, not smuggled).

⚑ **TWO OF THE SIX ARE GONE, NOT MOVED.** `deployed_recStateCommit_advantage_bound` and
`deployed_committedTrace_pinned_advantage_bound` are DELETED, because the `FloorRegroundedConsumers`
bounds they consumed are themselves BLOCKED (that file's §7 (a) and (b): the AIR trace binder is stated
over an abstract `CommitReveal` with no `ℤ`-valued deployed function, and the faithful state root's
extractor chain ends at `FaithfulBreak`, a disjunction of EXISTENTIALS with no total-function extractor).
Exporting a deployed bound for either would be asserting a reduction that does not exist.

⚑ **A MIRROR IS NAMED HERE, NOT SILENTLY FORKED.** `DomainSeparatedSponge` (§1) and
`SpongeCarrierReduction.SpongeKeyed` are FIELD-FOR-FIELD THE SAME STRUCTURE, and `poseidon2KeyedFamily`
is `spongeFamily`. `toSpongeKeyed` below converts, and `spongeFamily_toSpongeKeyed` proves the two
families are one `KeyedHashFamily` by `rfl` — so no drift is possible. But the right repair is to DELETE
one of the two structures, not to bridge them; that is a single-owner edit across the eight files now
using `poseidon2KeyedFamily`/`hashAt`, and is on the work-list rather than done here while those files
are being actively written by other lanes. `Dregg2.Crypto.SpongeCarrierBridge` proves the same
identification from above. -/

/-- The deployed bundle, converted to the reduction spine's bundle. Field-for-field; the theorem below
proves there is nothing to get wrong. -/
def toSpongeKeyed (D : DomainSeparatedSponge) : SpongeCarrierReduction.SpongeKeyed where
  sponge := D.sponge
  Tag := D.Tag
  tagFintype := D.tagFintype
  tagNonempty := D.tagNonempty
  tagCode := D.tagCode
  deployedTag := D.deployedTag

/-- **⚑ THE SAME KEYED FAMILY.** The spine's family at the converted bundle IS this file's
`poseidon2KeyedFamily` — by `rfl`, so `deployed_hash_is_family_instance` and
`wins_iff_deployed_collision` (the faithfulness lemmas, this file's real contribution) apply verbatim to
every reduction landed below. The reductions are about the deployed function. -/
theorem spongeFamily_toSpongeKeyed (D : DomainSeparatedSponge) :
    SpongeCarrierReduction.spongeFamily (toSpongeKeyed D) = poseidon2KeyedFamily D := rfl

/-- The deployed fixed function is the same one on both sides of the conversion. -/
theorem deployedHash_toSpongeKeyed (D : DomainSeparatedSponge) :
    (toSpongeKeyed D).deployedHash = D.deployedHash := rfl

/-- **THE DEPLOYED MERKLE-OPENING FORGERY GAME.** The adversary is handed a uniformly sampled
domain-separation tag of the DEPLOYED sponge and WINS iff it opens one committed Merkle root at one query
index to TWO DISTINCT values. By `spongeFamily_toSpongeKeyed` this is a game about the real
`poseidon2KeyedFamily D`, not an abstract `F`. -/
abbrev deployedOpenBreakGame (D : DomainSeparatedSponge) : FloorGames.Game :=
  FloorRegroundedConsumers.merkleOpenBreakGame (toSpongeKeyed D)

/-- **THE DEPLOYED MERKLE-OPENING FORGERY GAME AT THE SAMPLED ORACLE** — the same win relation,
keyed by the DEPLOYED sponge's own tag space, depth pinned per parameter (a committed tree has a
fixed height). The ROM transposition of `deployedOpenBreakGame`, per the §4 header's labelled
modelling step. -/
abbrev deployedOpenRomBreakGame (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag)
    (d : ℕ → ℕ) : FloorGames.Game :=
  FloorRegroundedConsumers.merkleOpenRomBreakGame (toSpongeKeyed D) tagDec d

/-- **THE QUERY-BOUNDED DEPLOYED-OPENING-FORGER CLASS** — the fixed `Eff` the bridged successors
close at: the forger factors through a `Q`-query oracle tree fixed BEFORE the oracle is sampled. The
honest successor of the deleted `IsPolyTime` discharge. -/
abbrev DeployedOpenRomEff (D : DomainSeparatedSponge) (tagDec : DecidableEq D.Tag)
    (d Q : ℕ → ℕ) : FloorGames.Adversary (deployedOpenRomBreakGame D tagDec d) → Prop :=
  FloorRegroundedConsumers.MerkleOpenRomEff (toSpongeKeyed D) tagDec d Q

/-- **⚑⚑ OOD / Merkle-opening binder, bridged — DISCHARGED ON THE PROVED FLOOR.** A query-bounded
forger that opens one committed OOD/Merkle root of the deployed tag space's sampled oracle at one
query to two DISTINCT leaves has NEGLIGIBLE advantage. NO floor hypothesis: the successor of the
deleted `deployed_oodCommitmentOpening_advantage_bound`, whose `DeployedOpenFloor` was refuted. -/
theorem deployed_oodCommitmentOpening_binds_rom (D : DomainSeparatedSponge)
    (tagDec : DecidableEq D.Tag) (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : FloorGames.Adversary (deployedOpenRomBreakGame D tagDec d))
    (hA : DeployedOpenRomEff D tagDec d Q A) :
    Negl (FloorGames.gameAdv (deployedOpenRomBreakGame D tagDec d) A) :=
  FloorRegroundedConsumers.oodCommitmentOpening_binds_rom (toSpongeKeyed D) tagDec d Q Q'
    hle hQ' A hA

/-- **⚑ FRI per-query layer-opening binder, bridged — DISCHARGED.** See `FloorRegroundedConsumers`
§3 for exactly which step is proved and which is a stated modelling identification (the abstract
`OracleCR` ⟶ the concrete per-query Merkle recompute) — that identification is unchanged by the
floor move. Successor of the deleted `deployed_friOracle_binding_advantage_bound`. -/
theorem deployed_friOracle_binding_binds_rom (D : DomainSeparatedSponge)
    (tagDec : DecidableEq D.Tag) (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (oracleEquivocator : FloorGames.Adversary (deployedOpenRomBreakGame D tagDec d))
    (hA : DeployedOpenRomEff D tagDec d Q oracleEquivocator) :
    Negl (FloorGames.gameAdv (deployedOpenRomBreakGame D tagDec d) oracleEquivocator) :=
  FloorRegroundedConsumers.friOracle_binding_binds_rom (toSpongeKeyed D) tagDec d Q Q'
    hle hQ' oracleEquivocator hA

/-- **⚑ Multi-round FRI/STARK fold, bridged — DISCHARGED.** The total binding-failure advantage
across the `rounds` Merkle checks is a finite sum of PER-ROUND DEPLOYED-GAME advantages (not a sum
of a hypothesis), negligible by the union bound over the ONE sampled oracle. Successor of the
deleted `deployed_friStark_fold_advantage_bound`. -/
theorem deployed_friStark_fold_binds_rom (D : DomainSeparatedSponge)
    (tagDec : DecidableEq D.Tag) (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (rounds : Finset ℕ)
    (roundEquivocator : ℕ → FloorGames.Adversary (deployedOpenRomBreakGame D tagDec d))
    (hA : ∀ r ∈ rounds, DeployedOpenRomEff D tagDec d Q (roundEquivocator r)) :
    Negl (fun n => ∑ r ∈ rounds,
      FloorGames.gameAdv (deployedOpenRomBreakGame D tagDec d) (roundEquivocator r) n) :=
  FloorRegroundedConsumers.friStark_fold_binds_rom (toSpongeKeyed D) tagDec d Q Q' hle hQ'
    rounds roundEquivocator hA

/-- **⚑ APEX two-hash forgery advantage, bridged — DISCHARGED.** The light-client forgery advantage
— trace-commitment opening equivocation PLUS OOD-commitment opening equivocation — is negligible in
the keyed ROM model at the deployed tag space, both legs' query-class membership carried, NO floor
hypothesis. Successor of the deleted `deployed_lightclientUnfoolable_advantage_bound`.

⚑ HONEST SCOPE: this is the HASH-BINDING leg of light-client soundness, not the whole of it. The FRI
proximity leg is a separate named residual, and the deployed digest is ONE BabyBear felt (~31 bits) —
there is NO `l` at which the ideal `Fin (2 ^ l)` digest is that felt, and at the deployed width the
honest reading stays "binds exactly as well as ~31 bits allow" (birthday ≈ `2^15.5`, the felt-width
wound). What the move buys is that the leg now rests on a floor that is PROVED, instead of one the
deployed sponge refutes. -/
theorem deployed_lightclientUnfoolable_binds_rom (D : DomainSeparatedSponge)
    (tagDec : DecidableEq D.Tag) (d Q Q' : ℕ → ℕ) (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (traceEquivocator oodEquivocator : FloorGames.Adversary (deployedOpenRomBreakGame D tagDec d))
    (hT : DeployedOpenRomEff D tagDec d Q traceEquivocator)
    (hO : DeployedOpenRomEff D tagDec d Q oodEquivocator) :
    Negl (fun n => FloorGames.gameAdv (deployedOpenRomBreakGame D tagDec d) traceEquivocator n
        + FloorGames.gameAdv (deployedOpenRomBreakGame D tagDec d) oodEquivocator n) :=
  FloorRegroundedConsumers.lightclientUnfoolable_binds_rom (toSpongeKeyed D) tagDec d Q Q'
    hle hQ' traceEquivocator oodEquivocator hT hO

/-! ### The deployed floor, PRICED at both poles (so the rebuild cannot be read as stronger). -/

/-- **(TOOTH — the deployed floor is FALSE at the UNRESTRICTED class, at REAL BabyBear parameters.)** The
honest price of every `hEff` discharge above, at the deployed family. This is why the rebuilt bounds are
stated at `IsPolyTime` and not at `⊤`: at `⊤` the floor is the EXISTENCE floor, and collisions exist. -/
theorem deployedFloor_top_false_babyBear (D : DomainSeparatedSponge)
    (hb : ∀ xs, 0 ≤ D.sponge xs ∧ D.sponge xs < (2013265921 : ℤ)) :
    ¬ FloorGames.HashCRHardQuant (poseidon2KeyedFamily D) (fun _ => True) :=
  FloorRegroundedConsumers.merkleFloor_top_false_babyBear (toSpongeKeyed D) hb

/-- **(TOOTH — the other pole is vacuous.)** Recorded beside the refutation. -/
theorem deployedFloor_bot_vacuous (D : DomainSeparatedSponge) :
    FloorGames.HashCRHardQuant (poseidon2KeyedFamily D) (fun _ => False) :=
  FloorRegroundedConsumers.merkleFloor_bot_vacuous (toSpongeKeyed D)

/-- **(CANARY — the deployed apex does NOT follow from the floor applied at an unrelated finder.)** Only
the extractor connects the deployed forgery game to the collision game. If this stops failing, the
`P → P` shape has come back. -/
example (D : DomainSeparatedSponge)
    (Eff : FloorGames.Adversary (FloorGames.hashGame (poseidon2KeyedFamily D)) → Prop)
    (A : FloorGames.Adversary (deployedOpenBreakGame D))
    (B : FloorGames.Adversary (FloorGames.hashGame (poseidon2KeyedFamily D))) (hB : Eff B)
    (hD : FloorGames.HashCRHardQuant (poseidon2KeyedFamily D) Eff) : True := by
  fail_if_success
    (have : Negl (FloorGames.gameAdv (deployedOpenBreakGame D) A) := hD B hB)
  trivial

/-! ## §5 — axiom-hygiene tripwires. -/

#assert_axioms deployed_hash_is_family_instance
#assert_axioms wins_iff_deployed_collision
#assert_axioms domainSeparatedCR_of_injective_sponge
#assert_axioms domainSeparatedCR_of_poseidon2SpongeCR
#assert_axioms brokenDomainSep_not_CR
#assert_axioms refDomainSep_CR
#assert_axioms spongeFamily_toSpongeKeyed
#assert_axioms deployedHash_toSpongeKeyed
#assert_axioms deployed_oodCommitmentOpening_binds_rom
#assert_axioms deployed_friOracle_binding_binds_rom
#assert_axioms deployed_lightclientUnfoolable_binds_rom
#assert_axioms deployed_friStark_fold_binds_rom
#assert_axioms deployedFloor_top_false_babyBear
#assert_axioms deployedFloor_bot_vacuous

end Dregg2.Circuit.Poseidon2KeyedBridge

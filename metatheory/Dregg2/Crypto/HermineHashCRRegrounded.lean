/-
# `Dregg2.Crypto.HermineHashCRRegrounded` — the Hermine commit-reveal `HashCR` consumers RE-GROUNDED
off the VACUOUS injective floor onto the keyed collision floor `HashCRHardQuant`, whose ADVERSARY CLASS
is written out at every use.

## The bug this closes (the commit-reveal half of the 07-13 floor sweep)

`HermineHintMLWE.HashCR cr := ∀ i w w', cr.H i w = cr.H i w' → w = w'` is stated as **injectivity** of
the commit map, and `HashFloorHonesty.hashCR_false_of_compressing` PROVES it FALSE for any COMPRESSING
commit-reveal (`|C| < |W|` — pigeonhole forces two reveals to one commitment). So every Hermine
binding consumer conditioned on it — `commitment_binding`, `equivocation_breaks_hashcr`,
`concurrent_forgery_breaks_hashcr_or_msis`, `concurrent_unforgeable_reduces`, and the DEPLOYED-reachable
`RevocationSoundness` / `IdentityCommitment` reuses of the SAME `CommitReveal`/`HashCR` — is VACUOUSLY
TRUE at real parameters. `HashFloorHonesty` landed the honest keyed collision GAME and the advantage
template; `FloorRegroundedConsumers` moved the STARK/FRI side. This file moves the Hermine COMMIT-REVEAL
side.

⚑ **THE FLOOR IS `FloorGames.HashCRHardQuant F Eff`, AND `Eff` IS SPELLED AT EVERY USE SITE.** The
sweep's first repair shipped a `def CollisionResistant F` that was this floor at the unrestricted class
under a name that HID the class; it is DELETED (2026-07-28), so every `⊤` below is written out as
`fun _ => True` in the statement. That matters rather than being cosmetic:
`FloorGames.hashCRHardQuant_top_false_of_compressing` refutes that class at every compressing — i.e.
real — commit hash, so a statement carrying it is priced the moment it is read.

## The re-grounding

* **`commitRevealFamily`** — the concrete bridge: a Hermine `CommitReveal Idx W C` at a fixed index `i`
  becomes a `KeyedHashFamily` (`Input = W`, `Out = C`, `H _ _ w = cr.H i w`). This is the keyed hash the
  honest collision game lives over.
* **`commitRevealFamily_CR_of_hashcr`** — the OLD-floor ⟹ NEW-floor bridge: if the injective `HashCR cr`
  held it would discharge `HashCRHardQuant (commitRevealFamily cr i) (fun _ => True)` (via
  `hashCRHardQuant_top_of_injective`), so the old floor was STRICTLY STRONGER than even that. It does NOT
  follow that re-grounding onto the `⊤` class loses nothing: that class is refuted at a compressing
  commitment too. The load-bearing statements are the `_advantage_bound` forms at an explicit `Eff`.
* **`commitOpenGame` / `openToFinder` / `hermine_commitment_binding_advantage_bound`** — the
  commitment-opening break, as a SECURITY REDUCTION. ⚑ THIS REPLACES two earlier exports that are now
  DELETED, not kept beside it: the bare-CR form took the floor at the UNRESTRICTED class — then spelled
  `CollisionResistant F`, a `def` since deleted for hiding its `⊤` — which
  `hashCRHardQuant_top_false_of_compressing` proves FALSE for every compressing (i.e. real) commit hash —
  a refuted hypothesis, exactly the disease the sweep exists to name; and its `_eff` sibling took a
  `CollisionFinder` and applied the floor TO IT, so hypothesis and conclusion were the same object and the
  OPENING never appeared in a `Prop`. The replacement makes the opening a `Game` (an adversary that
  publishes a commitment and two reveals that both open it), extracts a collision finder by DISCARDING the
  commitment, and proves the advantage inequality unconditionally.
* ⚑ **The `IsPolyTime` discharges are DELETED (07-24).** `hermine_commitment_binding_from_polyTime`
  and `hermine_concurrent_forgery_from_polyTime` discharged `hEff` at `Eff := IsPolyTime`, whose floor
  `HashCRHardQuant … (IsPolyTime …)` is REFUTED at deployed parameters
  (`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`: `IsPolyTime` prices
  answer SIZE, so a `.pure` answerer with a hardcoded short collision is in the class and wins with
  probability `1`). Their DISCHARGED successors live on the PROVED keyed-ROM floor: the generic
  opening binding is `Crypto.RomCarrierSites.rom_open_binds` (the `commitOpenGame` shape at the
  sampled oracle, floor = `KeyedRomFloor.keyedRom_hard`), instantiated per site by
  `IdentityCommitmentRegrounded` / `WireAkeRegrounded` / `RandomnessBeaconRegrounded` /
  `XmVrfRefinementRegrounded`; the concurrent-forgery composition's equivocation horn is discharged
  there by `Crypto.HermineRomBinding.hermine_concurrent_forgery_rom` (`cfEquivRom_hard`). The
  `_advantage_bound` forms below stay the honest fixed-hash statements with `hEff` in the open.

## ⚑ The concurrent-forgery keystone, ROUTED THROUGH THE REAL DICHOTOMY (the 2026-07-17 repair)

`hermine_concurrent_forgery_advantage_bound` is the advantage-bounded sibling of
`concurrent_forgery_breaks_hashcr_or_msis` / `concurrent_unforgeable_reduces`. Until 07-17 it carried a
FREE ensemble unconnected to any forger:

    (adv : S → Ensemble) (s : S) (hmsis : MSISHardQuantShape adv) : Negl (… + adv s n)

whose MSIS leg was `hmsis s` — a `P → P` instantiation of the content-free `MSISHardQuantShape`
(`ProbCrypto`; `HardQuantVacuity` FINDING-1 / `VACUITY-SWEEP.md` documented this exact site). It assumed
the MSIS hardness it should DERIVE from the forger. The HashCR leg was already sound; only the MSIS leg
was rotten.

Now the reduction is a chain of proof terms, MIRRORING the VRF repair (`VrfRegrounded`):

  * **`concurrentForgeryGame`** — a first-class λ-indexed game: the adversary is handed a sampled
    instance (`A`, key `t`, commit map, target commitment `cm`) and WINS iff it opens `cm` with two
    reveals `w`, `w'` and outputs two accepting SelfTargetMSIS solutions with `c ≠ c'`. The forgery is IN
    the win relation; nothing here is a docstring.
  * **`forgeryToMsisSolver`** — the extractor as a map of adversaries: the difference `(z − z', −(c − c'))`
    of `selftarget_extract_nonzero`, written as a function into `msisGame (cfMsisFamily F)`.
  * **`forgeryToEquivFinder`** — the equivocation adversary as a map: the two reveals `(w, w')` into the
    commit-collision game `cfEquivGame F`.
  * **`forgery_wins_imp`** — the dichotomy `concurrent_forgery_breaks_hashcr_or_msis` at the game level:
    every instance the forger wins, EITHER the extracted vector is an `IsMSISSolution` (bound: `w = w'`)
    OR the two reveals are a genuine commit collision (equivocated: `w ≠ w'`).
  * **`forgery_adv_le`** — the UNION BOUND: `gameAdv forgery ≤ gameAdv msis (extracted) + gameAdv equiv
    (extracted)`, over the SHARED sampled-instance space, by `winProb_le_add_of_imp`.
  * **`hermine_concurrent_forgery_advantage_bound`** — the floors bite on the EXTRACTED solver and
    finder, at the games the reduction actually attacks. The Boolean dichotomy `¬HashCR ∨ MSIS-solution`
    becomes the additive negligible advantage — and, unlike its predecessor, this statement is FALSE if
    you delete the reduction: §5's canary compiles that fact.

⚑ **The `hEff`/`hEffH` obligations are UNDISCHARGED and that is the honest state** — the standard "the
reduction is efficient" side conditions, a PARAMETER because this tree has no cost model (`FloorGames`
§8). Both floors' honesty is exactly their `Eff`'s: `⊤` makes them FALSE at compressing parameters,
`⊥` vacuous. §6.

## Non-fake

The `⊤`-class floor is SATISFIABLE (`commitRevealFamily_CR_of_hashcr` on the binding
`HermineHintMLWE.exCR` discharges it) and REFUTABLE (`badCR_family_not_CR`: the COLLIDING commit-reveal
`HermineHintMLWE.badCR` collides at every key — `7 ≠ 8`, both commit to `0` — so its `⊤` floor is FALSE
and the siblings cannot be discharged there). ⚑ Both poles are stated with the class written out, and
read together they say what the `⊤` floor IS: it holds for injective families and fails for compressing
ones, nothing between — so the satisfiability witness is a statement that `exCR` is not a hash, never
evidence about a deployed commitment. The concrete `crEquivocator` is a genuine collision finder, not a
relabel, and is the finder four downstream lanes instantiate. Old injective-floor consumers KEPT
untouched; siblings ADDED. `#assert_all_clean` (⊆ {propext, Classical.choice, Quot.sound}); no `sorry`,
no fresh `axiom`.

## Coordination

This is the COMMIT-REVEAL binding lane. The STARK/FRI/Merkle hash consumers are
`Circuit.FloorRegroundedConsumers` (sibling lane); the decisional/lossy-MLWE and `MSISHard`-Boolean crypto
floors are `FloorBridge`/`CryptoFloorTeeth` (another sibling). It stays in the Hermine `CommitReveal`
subtree — no consumer moved here lives elsewhere.
-/
import Dregg2.Tactics.ThreadAdvantageBound
import Dregg2.Crypto.HermineHintMLWE
import Dregg2.Crypto.FloorGames
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics

namespace Dregg2.Crypto.HermineHashCRRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero negl_add not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top negl_of_le)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR badCR exCR exCR_hashcr)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit msisGame MSISFamily MSISHardQuant Hard
   hard_bot_vacuous msisHardQuant_top_false_of_compressing
   hashGame finderToAdv HashCRHardQuant collisionAdv_eq_gameAdv
   hashCRHardQuant_top_of_injective hashCRHardQuant_top_false_of_compressing)
open Dregg2.Crypto.HermineSelfTargetMSIS
  (IsSelfTargetMSISSolution augmented augmented_apply selftarget_extract_nonzero instShortNormProd)
open scoped Dregg2.Crypto.HermineSelfTargetMSIS
open Dregg2.Crypto.Lattice
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime isPolyTime_inhabited idAdv)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp)

set_option autoImplicit false

/-! ## §1 — the concrete bridge: a Hermine commit-reveal becomes a keyed hash family. -/

/-- **THE COMMIT-REVEAL KEYED FAMILY.** A Hermine `CommitReveal Idx W C` at a fixed index `i` as a
`KeyedHashFamily`: reveals `W` are the inputs, commitments `C` the outputs, and the keyed hash is
`H _ _ w = cr.H i w` (a trivial `Unit` key — the deployed effective key is the domain-separation
index/tag). This is the keyed hash the proper collision game runs over. -/
def commitRevealFamily {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) : KeyedHashFamily where
  Key := fun _ => Unit
  Input := W
  Out := C
  H := fun _ _ w => cr.H i w
  keyFintype := fun _ => inferInstance
  keyNonempty := fun _ => inferInstance
  inputDecEq := inferInstance
  outDecEq := inferInstance

/-- **THE OLD-FLOOR ⟹ NEW-FLOOR BRIDGE.** If the injective `HashCR cr` held (per-index injectivity of the
commit map), it would discharge the collision floor at the UNRESTRICTED class,
`HashCRHardQuant (commitRevealFamily cr i) (fun _ => True)` (no collisions ⟹ every adversary's advantage
`0`, via `hashCRHardQuant_top_of_injective`). So the OLD injective floor is STRICTLY STRONGER than that —
and, being FALSE for a compressing commitment (`HashFloorHonesty.hashCR_false_of_compressing`), it was an
empty hypothesis.

⚑ **The `⊤` is now WRITTEN OUT in the conclusion rather than hidden behind a name.** It used to read
`CollisionResistant (commitRevealFamily cr i)`; that `def` was a SPELLING of this exact statement and is
DELETED, because a reader has to see the adversary class to price the assumption. Seeing it prices this
bridge honestly: `hashCRHardQuant_top_false_of_compressing` refutes the `⊤` floor at every compressing
commit hash too, so the conclusion here is NOT a floor a real commitment satisfies — it is the honest
record that the old hypothesis implied even this, and the load-bearing statements are §2's
`_advantage_bound` forms at an explicit `Eff`. -/
theorem commitRevealFamily_CR_of_hashcr {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (hcr : HashCR cr) :
    HashCRHardQuant (commitRevealFamily cr i) (fun _ => True) :=
  hashCRHardQuant_top_of_injective (commitRevealFamily cr i) (fun _ _ w w' h => hcr i w w' h)

/-! ## §2 — the commitment OPENING, as a SECURITY REDUCTION.

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** Two theorems stood here:

  * `hermine_commitment_binding_advantage_bound (hCR : CollisionResistant F) (equivocator :
    CollisionFinder F)`. That hypothesis was the collision floor at the UNRESTRICTED adversary class —
    `HashCRHardQuant F (fun _ => True)` — behind a `def` that hid the class (itself since DELETED for
    that reason), and `FloorGames.hashCRHardQuant_top_false_of_compressing` proves that class false for
    any compressing family — every real commit hash. So the hypothesis was REFUTED at deployed
    parameters and the theorem transported no security, which is the same defect it was written to
    repair, one costume along.
  * its `_eff` sibling, which took a `CollisionFinder F` and applied the floor to it. Hypothesis and
    conclusion were the SAME object: there was no game about the OPENING at all, so the deployed break —
    "two reveals both open the published commitment" — never appeared in a `Prop`.

Both are DELETED. What stands here instead is the shape the rest of the sweep uses: the break is a
first-class `Game` whose win relation mentions the PUBLISHED commitment, the reduction is a map of
adversaries, the advantage inequality is unconditional (no adversary class appears in it), and the
security conclusion is taken under a NAMED floor at an arbitrary class — the DISCHARGED instantiation
lives on the keyed-ROM floor (`RomCarrierSites.rom_open_binds` and the per-site `*_rom` successors;
the `IsPolyTime` discharge that stood in §2b is DELETED, its floor refuted).

The four downstream instantiations (`IdentityCommitmentRegrounded`, `WireAkeRegrounded`,
`XmVrfRefinementRegrounded`, `RandomnessBeaconRegrounded`) are rewired onto this object. -/

/-- **THE COMMITMENT-OPENING BREAK GAME.** The adversary is handed a sampled key and WINS iff it
publishes a commitment together with TWO DISTINCT reveals that BOTH open it under the deployed commit
hash. Winning is exactly the equivocated opening `HermineHintMLWE.commitment_binding` denies — and the
published commitment is IN the win relation, so this is a game about the deployed opening predicate
rather than the collision relation wearing a different name. -/
def commitOpenGame (F : KeyedHashFamily) : Game where
  Inst := F.Key
  Ans := fun _ => F.Out × F.Input × F.Input
  instFin := F.keyFintype
  instNe := F.keyNonempty
  wins := fun l k p => p.2.1 ≠ p.2.2 ∧ F.H l k p.2.1 = p.1 ∧ F.H l k p.2.2 = p.1
  winsDec := fun l k p => by
    letI := F.inputDecEq; letI := F.outDecEq
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — a win unfolds, by `Iff.rfl`, to two distinct reveals opening
one published commitment. Not a docstring: the `Prop` itself. -/
theorem commitOpenGame_wins_iff (F : KeyedHashFamily) (l : ℕ) (k : F.Key l)
    (p : F.Out × F.Input × F.Input) :
    (commitOpenGame F).wins l k p ↔
      (p.2.1 ≠ p.2.2 ∧ F.H l k p.2.1 = p.1 ∧ F.H l k p.2.2 = p.1) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** An equivocating opener becomes a collision finder by
DISCARDING the published commitment and keeping the two reveals. The commitment is where the opener's
leverage lives — the finder never sees it — so the collision must be RE-DERIVED on the other side
(`open_wins_imp`); the map throws structure away rather than renaming it. -/
def openToFinder (F : KeyedHashFamily) (A : Adversary (commitOpenGame F)) :
    Adversary (hashGame F) where
  run := fun l k => let p := A.run l k; (p.2.1, p.2.2)

/-- **⚑ WIN-PRESERVATION — and this IS `HermineHintMLWE.equivocation_breaks_hashcr`, at the game level.**
Wherever the opener wins, its two reveals are a GENUINE collision: they are distinct (the win's own side
condition) and both hash to the SAME published commitment, so they hash to each other. -/
theorem open_wins_imp (F : KeyedHashFamily) (A : Adversary (commitOpenGame F)) (l : ℕ) (k : F.Key l)
    (hwin : (commitOpenGame F).wins l k (A.run l k)) :
    (hashGame F).wins l k ((openToFinder F A).run l k) := by
  obtain ⟨hne, h1, h2⟩ := hwin
  exact ⟨hne, h1.trans h2.symm⟩

/-- **THE ADVANTAGE INEQUALITY.** The opener's advantage is at most the extracted finder's, at every
parameter — both play over the SAME sampled key space. Unconditional: no adversary class appears. -/
theorem open_adv_le (F : KeyedHashFamily) (A : Adversary (commitOpenGame F)) (l : ℕ) :
    gameAdv (commitOpenGame F) A l ≤ gameAdv (hashGame F) (openToFinder F A) l := by
  refine @winProb_le_of_imp _ (F.keyFintype l) _ _ (fun k hk => ?_)
  replace hk := (Adversary.hit_eq_true _ _ _).mp hk
  exact (Adversary.hit_eq_true _ _ _).mpr (open_wins_imp F A l k hk)

/-- **⚑ RE-GROUNDED `HermineHintMLWE.commitment_binding` — from the commit hash's collision floor, VIA
the reduction.** Under the collision floor at the class `Eff`, an equivocating opener whose extracted
finder is in that class has NEGLIGIBLE advantage: a published commitment opens to ONE reveal except with
negligible probability. The Boolean "two openings ⟹ equal", which needed the FALSE injective `HashCR`,
becomes an honest advantage bound on a hypothesis a real commit hash can satisfy.

`hEff` is a parameter here because this is the statement at an ARBITRARY class; the DISCHARGED
instantiation is the keyed-ROM successor (`RomCarrierSites.rom_open_binds`; the `IsPolyTime` discharge
that stood here is deleted — its floor is refuted). -/
theorem hermine_commitment_binding_advantage_bound (F : KeyedHashFamily)
    (Eff : Adversary (hashGame F) → Prop) (A : Adversary (commitOpenGame F))
    (hEff : Eff (openToFinder F A)) (hD : HashCRHardQuant F Eff) :
    Negl (gameAdv (commitOpenGame F) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (commitOpenGame F) A l).1)
    (open_adv_le F A) (hD _ hEff)

/-- **(TOOTH — `Eff := ⊤` is FALSE at a compressing family.)** The floor at the unrestricted class is
FALSE for any compressing commit hash (`hashCRHardQuant_top_false_of_compressing`: the `Classical.choice`
adversary that outputs a collision at every key is in the class and wins with probability `1`). This is
the price of restricting the class, stated as a theorem — and it is precisely why the DELETED bare-CR
export bought nothing. ⚑ The class is `fun _ => True` in the statement now; it used to hide inside the
name `CollisionResistant F`, which is why that `def` is gone. -/
theorem hermine_binding_eff_top_false_of_compressing {F : KeyedHashFamily} (hin : Nonempty F.Input)
    (hcol : ∀ l (k : F.Key l), ∃ x y : F.Input, x ≠ y ∧ F.H l k x = F.H l k y) :
    ¬ HashCRHardQuant F (fun _ => True) :=
  hashCRHardQuant_top_false_of_compressing F hin hcol

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY family,
including a broken one. Recorded HONESTLY: a satisfiability witness is worth nothing without the refutation
beside it, and the two poles together are what make `Eff` a dial, not a costume. -/
theorem hermine_binding_eff_bot_vacuous {F : KeyedHashFamily} :
    HashCRHardQuant F (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the keystone does NOT follow from the floor applied at another adversary.)** Strip the
reduction — try to conclude the opener's negligibility from the floor applied at some OTHER adversary
`B`, NOT the one extracted from it — and the proof does not go through: `hD B hB` bounds the game
advantage of `B`, a DIFFERENT ensemble, and only `open_adv_le` connects the extracted finder to the
opening game. ⚑ Against the DELETED `_eff` export this tooth was unwritable, because hypothesis and
conclusion were the same object. -/
example {F : KeyedHashFamily} (Eff : Adversary (hashGame F) → Prop)
    (A : Adversary (commitOpenGame F)) (B : Adversary (hashGame F)) (hB : Eff B)
    (hD : HashCRHardQuant F Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (commitOpenGame F) A) := hD B hB)
  trivial

/-- **THE POSITIVE POLE — the RIGHT floor DOES discharge it.** With the floor at the EXTRACTED finder the
keystone fires. A gate that refuses everything is a broken keystone, not a fixed one. -/
theorem hermine_binding_eff_fires {F : KeyedHashFamily} (Eff : Adversary (hashGame F) → Prop)
    (A : Adversary (commitOpenGame F)) (hEff : Eff (openToFinder F A))
    (hD : HashCRHardQuant F Eff) :
    Negl (gameAdv (commitOpenGame F) A) :=
  hermine_commitment_binding_advantage_bound F Eff A hEff hD

/-! ## §3 — the concurrent forger, as a first-class λ-indexed game.

A concurrent rushing forger is a validator that opens a common commitment `cm` and hands back two
accepting SelfTargetMSIS solutions with `c ≠ c'`. This section makes that adversary a `Game`, played over
a SAMPLED instance, exactly as `VrfRegrounded.vrfUniqGame` makes a uniqueness-breaker one. The two games
the reduction attacks — the MSIS game of the augmented map, and the commit-collision game — are derived
from the SAME family, so all three share an instance space and the union bound below is over one `Ω`. -/

/-- **THE CONCURRENT-FORGERY FAMILY.** At each security parameter `l`: the ring `R_q`, the response module
`M`, the commitment module `N`, the commitment-hash codomain `C`, their algebraic structure and shortness
seminorms, a FINITE space of sampled instances, and per instance the public map `A`, public key `t`, the
commit map `commit : N → C` (`= cr.H i`, the commit-reveal at its fixed index), and the target commitment
`cmt = cm` that both reveals must open. `β` is the shortness bound. This carries the deployed data of the
straight-line rushing composition and nothing else. -/
structure ConcurrentForgeryFamily where
  /-- The ring `R_q` at parameter `l` (challenges live here). -/
  Rq : ℕ → Type
  /-- The response module at parameter `l`. -/
  M : ℕ → Type
  /-- The commitment module at parameter `l` (the reveals `w`). -/
  N : ℕ → Type
  /-- The commit-hash codomain at parameter `l` (commitments `cm`). -/
  C : ℕ → Type
  /-- `Rq l` is a commutative ring. -/
  rqRing : ∀ l, CommRing (Rq l)
  /-- The shortness seminorm on challenges. -/
  rqNrm : ∀ l, letI := rqRing l; ShortNorm (Rq l)
  /-- Decidable equality on challenges (the game checks `c ≠ c'`). -/
  rqDec : ∀ l, DecidableEq (Rq l)
  /-- `M l` is an abelian group. -/
  mGrp : ∀ l, AddCommGroup (M l)
  /-- `M l` is an `Rq l`-module. -/
  mMod : ∀ l, letI := rqRing l; letI := mGrp l; Module (Rq l) (M l)
  /-- The shortness seminorm on responses. -/
  mNrm : ∀ l, letI := mGrp l; ShortNorm (M l)
  /-- Decidable equality on responses. -/
  mDec : ∀ l, DecidableEq (M l)
  /-- `N l` is an abelian group. -/
  nGrp : ∀ l, AddCommGroup (N l)
  /-- `N l` is an `Rq l`-module. -/
  nMod : ∀ l, letI := rqRing l; letI := nGrp l; Module (Rq l) (N l)
  /-- The shortness seminorm on commitments (SelfTargetMSIS bounds `‖w‖`). -/
  nNrm : ∀ l, letI := nGrp l; ShortNorm (N l)
  /-- Decidable equality on commitments (the verify equation and the openings check equality in `N`). -/
  nDec : ∀ l, DecidableEq (N l)
  /-- Decidable equality on commitment hashes (the openings check equality in `C`). -/
  cDec : ∀ l, DecidableEq (C l)
  /-- The instance space (key/commitment sampling randomness). -/
  Inst : ℕ → Type
  /-- The instance space is finite. -/
  instFin : ∀ l, Fintype (Inst l)
  /-- The instance space is inhabited. -/
  instNe : ∀ l, Nonempty (Inst l)
  /-- The public map `A` at parameter `l` on instance `i`. -/
  A : ∀ l, Inst l →
    (letI := rqRing l; letI := mGrp l; letI := mMod l; letI := nGrp l; letI := nMod l;
     M l →ₗ[Rq l] N l)
  /-- The public key `t` at parameter `l` on instance `i`. -/
  t : ∀ l, Inst l → N l
  /-- The commit map `commit w = cr.H i w` at the fixed index of instance `i`. -/
  commit : ∀ l, Inst l → N l → C l
  /-- The target commitment `cm` both reveals must open. -/
  cmt : ∀ l, Inst l → C l
  /-- The shortness bound. -/
  β : ℕ → ℕ

/-- The forger's claim: two reveals, two challenges, two responses. -/
abbrev ConcurrentForgeryFamily.Claim (F : ConcurrentForgeryFamily) (l : ℕ) : Type :=
  (F.N l × F.N l) × (F.Rq l × F.Rq l) × (F.M l × F.M l)

/-- **THE CONCURRENT-FORGERY GAME.** The adversary is given a sampled instance and WINS iff it opens the
target commitment `cm` with two reveals `w`, `w'` and outputs two accepting SelfTargetMSIS solutions with
DISTINCT challenges `c ≠ c'`. Winning this game is a rushing validator double-claiming under commit-reveal;
the SelfTargetMSIS relation and the two openings are IN the win predicate, read directly off the family. -/
def concurrentForgeryGame (F : ConcurrentForgeryFamily) : Game where
  Inst := F.Inst
  Ans := fun l => (F.N l × F.N l) × (F.Rq l × F.Rq l) × (F.M l × F.M l)
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i c =>
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l; letI := F.nNrm l
    F.commit l i c.1.1 = F.cmt l i ∧ F.commit l i c.1.2 = F.cmt l i ∧
      c.2.1.1 ≠ c.2.1.2 ∧
      IsSelfTargetMSISSolution (F.A l i) (F.t l i) (F.β l) c.2.2.1 c.2.1.1 c.1.1 ∧
      IsSelfTargetMSISSolution (F.A l i) (F.t l i) (F.β l) c.2.2.2 c.2.1.2 c.1.2
  winsDec := fun l i c => by
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.rqDec l
    letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l; letI := F.mDec l
    letI := F.nGrp l; letI := F.nMod l; letI := F.nNrm l; letI := F.nDec l
    letI := F.cDec l
    unfold IsSelfTargetMSISSolution Dregg2.Crypto.HermineThreshold.verify
    infer_instance

/-- **THE MSIS INSTANCE THE REDUCTION ATTACKS.** The augmented map `[A | t]` over the augmented solution
space `M × R_q`, at the extracted bound `(β + β) + (β + β)` — exactly the map, space and bound
`selftarget_extract_nonzero` produces a solution for. The MSIS floor bites at THIS family, not at an
abstract index set. -/
def cfMsisFamily (F : ConcurrentForgeryFamily) : MSISFamily where
  Rq := F.Rq
  M := fun l => F.M l × F.Rq l
  N := F.N
  rqRing := F.rqRing
  mGrp := fun l => letI := F.rqRing l; letI := F.mGrp l; inferInstance
  mMod := fun l => letI := F.rqRing l; letI := F.mGrp l; letI := F.mMod l; inferInstance
  mNrm := fun l => letI := F.mGrp l; letI := F.mNrm l; letI := F.rqRing l; letI := F.rqNrm l;
    instShortNormProd
  nGrp := F.nGrp
  nMod := F.nMod
  mDec := fun l => letI := F.mDec l; letI := F.rqDec l; inferInstance
  nDec := F.nDec
  Inst := F.Inst
  instFin := F.instFin
  instNe := F.instNe
  A := fun l i =>
    letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
    letI := F.nGrp l; letI := F.nMod l
    augmented (F.A l i) (F.t l i)
  β := fun l => (F.β l + F.β l) + (F.β l + F.β l)

/-- **THE COMMIT-COLLISION GAME THE OTHER HORN ATTACKS.** Instances are the SAME sampled instances as the
forgery game; the adversary outputs two reveals and WINS iff they are a genuine collision of the commit
map — distinct reveals, equal commitments. This is the λ-indexed collision game of `F.commit` at each
sampled index; the equivocation horn of the dichotomy lands here. -/
def cfEquivGame (F : ConcurrentForgeryFamily) : Game where
  Inst := F.Inst
  Ans := fun l => F.N l × F.N l
  instFin := F.instFin
  instNe := F.instNe
  wins := fun l i p => p.1 ≠ p.2 ∧ F.commit l i p.1 = F.commit l i p.2
  winsDec := fun l i p => by
    letI := F.nDec l; letI := F.cDec l
    infer_instance

/-- **THE PROBLEM IS IN THE STATEMENT** — the commit-collision game's win relation is a genuine collision
of the real commit map. -/
theorem cfEquivGame_wins_iff (F : ConcurrentForgeryFamily) (l : ℕ) (i : F.Inst l) (p : F.N l × F.N l) :
    (cfEquivGame F).wins l i p ↔ (p.1 ≠ p.2 ∧ F.commit l i p.1 = F.commit l i p.2) :=
  Iff.rfl

/-- **THE MSIS HORN, AS A MAP OF ADVERSARIES.** A concurrent forger becomes an MSIS solver by SUBTRACTING
its two claims: `(z − z', −(c − c'))`. This is not a re-indexing and not a rename — it is the extractor of
`selftarget_extract_nonzero`, written as a function into the augmented MSIS game. -/
def forgeryToMsisSolver (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F)) :
    Adversary (msisGame (cfMsisFamily F)) where
  run := fun l i =>
    letI := F.rqRing l; letI := F.mGrp l
    let c : F.Claim l := A.run l i
    (c.2.2.1 - c.2.2.2, -(c.2.1.1 - c.2.1.2))

/-- **THE EQUIVOCATION HORN, AS A MAP OF ADVERSARIES.** A concurrent forger becomes a commit-collision
finder by handing back its two reveals `(w, w')` — the equivocating opening of the dichotomy. -/
def forgeryToEquivFinder (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F)) :
    Adversary (cfEquivGame F) where
  run := fun l i => let c : F.Claim l := A.run l i; (c.1.1, c.1.2)

/-! ## §4 — the dichotomy, at the probabilistic level.

`HermineHintMLWE.concurrent_forgery_breaks_hashcr_or_msis` is a Boolean disjunction; here it becomes an
implication of Bool win-events, and then — via a union bound over the shared sampled-instance space — the
additive advantage inequality the floors bite through. -/

/-- **THE UNION BOUND.** If every winning outcome of `f` wins `g` OR wins `h`, then `winProb f ≤ winProb g
+ winProb h` — the favorable set of `f` injects into the union of the other two, `card_union_le` closes
it. The probability-level lift of a two-horned dichotomy (`winProb_le_of_imp` is its one-horned sibling). -/
theorem winProb_le_add_of_imp {Ω : Type*} [Fintype Ω] {f g h : Ω → Bool}
    (himp : ∀ o, f o = true → g o = true ∨ h o = true) :
    winProb f ≤ winProb g + winProb h := by
  classical
  rw [winProb, winProb, winProb, ← add_div]
  rcases Nat.eq_zero_or_pos (Fintype.card Ω) with h0 | h0
  · simp [h0]
  · gcongr
    have hsub : (Finset.univ.filter (fun o : Ω => f o = true))
        ⊆ (Finset.univ.filter (fun o : Ω => g o = true))
          ∪ (Finset.univ.filter (fun o : Ω => h o = true)) := by
      intro o ho
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ho
      rw [Finset.mem_union]
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      exact himp o ho
    calc ((Finset.univ.filter (fun o : Ω => f o = true)).card : ℝ)
        ≤ (((Finset.univ.filter (fun o : Ω => g o = true))
            ∪ (Finset.univ.filter (fun o : Ω => h o = true))).card : ℝ) := by
          exact_mod_cast Finset.card_le_card hsub
      _ ≤ ((Finset.univ.filter (fun o : Ω => g o = true)).card : ℝ)
            + ((Finset.univ.filter (fun o : Ω => h o = true)).card : ℝ) := by
          exact_mod_cast Finset.card_union_le _ _

/-- **⚑ THE DICHOTOMY IS WIN-PRESERVING — and this is `concurrent_forgery_breaks_hashcr_or_msis`, on a
claim.** Stated over an explicit claim `c : F.Claim l` (so the projections are on a concrete product):
wherever the forger wins: EITHER `w = w'` (bound), and the extracted vector `(z − z', −(c − c'))` IS an
`IsMSISSolution` of the augmented map (`selftarget_extract_nonzero`); OR `w ≠ w'` (equivocated), and the
two reveals ARE a collision of the commit map (both open `cm`). The lattice/hash content lives in proof
terms, not in a sentence about them. -/
theorem claim_wins_imp (F : ConcurrentForgeryFamily) (l : ℕ) (i : F.Inst l) (c : F.Claim l)
    (hwin : (concurrentForgeryGame F).wins l i c) :
    (letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
     letI := F.nGrp l; letI := F.nMod l;
     IsMSISSolution (augmented (F.A l i) (F.t l i)) ((F.β l + F.β l) + (F.β l + F.β l))
       (c.2.2.1 - c.2.2.2, -(c.2.1.1 - c.2.1.2)))
      ∨ (c.1.1 ≠ c.1.2 ∧ F.commit l i c.1.1 = F.commit l i c.1.2) := by
  letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l; letI := F.mNrm l
  letI := F.nGrp l; letI := F.nMod l; letI := F.nNrm l
  obtain ⟨ho, ho', hne, hf, hf'⟩ := hwin
  by_cases hww : c.1.1 = c.1.2
  · -- BOUND to one commitment: the shared reveal feeds SelfTargetMSIS → a real MSIS solution.
    refine Or.inl ?_
    obtain ⟨hz, hc1, _hw, hv⟩ := hf
    obtain ⟨hz', hc1', _hw', hv'⟩ := hf'
    rw [← hww] at hv'
    exact selftarget_extract_nonzero (F.A l i) (F.t l i) c.1.1
      c.2.1.1 c.2.1.2 c.2.2.1 c.2.2.2 (F.β l) (F.β l) hz hz' hc1 hc1' hne hv hv'
  · -- EQUIVOCATED: two distinct reveals of one commitment — a commit collision.
    exact Or.inr ⟨hww, ho.trans ho'.symm⟩

/-- **⚑ THE DICHOTOMY AT THE GAME LEVEL.** `claim_wins_imp` applied at the forger's actual output: every
instance the forger wins, EITHER the extracted MSIS solver wins the augmented MSIS game OR the extracted
commit-collision finder wins the equivocation game. The two derived runs are DEFINITIONALLY the extractor
and the reveal-pair, so this is `claim_wins_imp` transported by `rfl`. -/
theorem forgery_wins_imp (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F))
    (l : ℕ) (i : F.Inst l) (hwin : (concurrentForgeryGame F).wins l i (A.run l i)) :
    (msisGame (cfMsisFamily F)).wins l i ((forgeryToMsisSolver F A).run l i) ∨
      (cfEquivGame F).wins l i ((forgeryToEquivFinder F A).run l i) :=
  claim_wins_imp F l i (A.run l i) hwin

/-- **THE ADVANTAGE INEQUALITY.** The forger's advantage is at most the SUM of the extracted MSIS solver's
and the extracted collision finder's advantages, at every parameter — the three play over the SAME sampled
instance space, and every instance the forger wins one of the two derived adversaries wins. A genuine
union-bound reduction inequality over real game advantages. -/
theorem forgery_adv_le (F : ConcurrentForgeryFamily) (A : Adversary (concurrentForgeryGame F)) (l : ℕ) :
    gameAdv (concurrentForgeryGame F) A l ≤
      gameAdv (msisGame (cfMsisFamily F)) (forgeryToMsisSolver F A) l +
        gameAdv (cfEquivGame F) (forgeryToEquivFinder F A) l := by
  refine @winProb_le_add_of_imp _ (F.instFin l) _ _ _ (fun i hi => ?_)
  replace hi := (Adversary.hit_eq_true _ _ _).mp hi
  rcases forgery_wins_imp F A l i hi with hm | he
  · exact Or.inl ((Adversary.hit_eq_true (forgeryToMsisSolver F A) l i).mpr hm)
  · exact Or.inr ((Adversary.hit_eq_true (forgeryToEquivFinder F A) l i).mpr he)

/-- **⚑ RE-GROUNDED HERMINE CONCURRENT-FORGERY BOUND — from MSIS hardness AND commit-collision resistance,
VIA the reduction.**

Under the MSIS floor at the augmented family the reduction attacks AND the collision floor at the commit
map, a concurrent forger whose extracted solver and finder are in the floors' adversary classes has
NEGLIGIBLE advantage: a rushing validator double-claims only with negligible probability. The Boolean
dichotomy `¬HashCR ∨ MSIS-solution` becomes the additive negligible advantage — and, unlike its
predecessor, this statement is FALSE if you delete the reduction: the conclusion is about the forgery
game, the hypotheses about the MSIS and collision games, and `forgery_adv_le` is the only bridge.

⚑ **THE `hEff`/`hEffH` OBLIGATIONS ARE UNDISCHARGED AND THAT IS THE HONEST STATE.** They say the extracted
solver/finder are in the classes the floors quantify over — the standard "the reduction is efficient".
They are PARAMETERS here, in the open, at the use site, because this tree has no cost model
(`FloorGames` §8). Both floors are priced exactly by §6: `⊤` makes them FALSE at compressing parameters,
`⊥` vacuous. -/
theorem hermine_concurrent_forgery_advantage_bound (F : ConcurrentForgeryFamily)
    (Eff : Adversary (msisGame (cfMsisFamily F)) → Prop)
    (EffH : Adversary (cfEquivGame F) → Prop)
    (A : Adversary (concurrentForgeryGame F))
    (hEff : Eff (forgeryToMsisSolver F A))
    (hEffH : EffH (forgeryToEquivFinder F A))
    (hmsis : MSISHardQuant (cfMsisFamily F) Eff)
    (hcol : Hard (cfEquivGame F) EffH) :
    Negl (gameAdv (concurrentForgeryGame F) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (concurrentForgeryGame F) A l).1)
    (forgery_adv_le F A) (negl_add (hmsis _ hEff) (hcol _ hEffH))

/-! ## §5 — the CANARY: break the reduction and the keystone goes RED.

The sweep's lesson is that a floor consumer must be checked by asking whether it survives the WRONG
hypothesis. Under the OLD statement — `(adv) (s) (hmsis : MSISHardQuantShape adv) : Negl (… + adv s n)` —
the MSIS leg was `hmsis s`, so a canary that conclude negligibility from a floor applied at some OTHER
solver was unwritable: hypothesis and conclusion mentioned the same free `adv s`. Here they cannot. -/

/-- **(CANARY — the keystone does NOT follow from the floors applied at OTHER adversaries.)** Strip the
reduction — try to conclude the forger's negligibility from the MSIS and collision floors applied at some
OTHER solver `B` and finder `E`, NOT the ones extracted from the forger — and the proof does not go
through: the floors bound `B` and `E`, and only `forgery_adv_le` connects the EXTRACTED pair to the
forgery game. `negl_add (hmsis B hB) (hcol E hE)` proves `Negl` of the WRONG advantage sum, so it cannot
close `Negl (gameAdv (concurrentForgeryGame F) A)`. This tooth was impossible to write under the old free
hypothesis; it compiles now, and reds if a future edit reconnects the games. -/
example (F : ConcurrentForgeryFamily) (Eff : Adversary (msisGame (cfMsisFamily F)) → Prop)
    (EffH : Adversary (cfEquivGame F) → Prop) (A : Adversary (concurrentForgeryGame F))
    (B : Adversary (msisGame (cfMsisFamily F))) (hB : Eff B)
    (E : Adversary (cfEquivGame F)) (hE : EffH E)
    (hmsis : MSISHardQuant (cfMsisFamily F) Eff) (hcol : Hard (cfEquivGame F) EffH) : True := by
  fail_if_success
    (have : Negl (gameAdv (concurrentForgeryGame F) A) := negl_add (hmsis B hB) (hcol E hE))
  trivial

/-- **THE POSITIVE POLE — the RIGHT floors DO discharge it.** A gate that refuses everything is a broken
keystone, not a fixed one. With the MSIS floor at the augmented game and the collision floor at the commit
map — both at the EXTRACTED adversaries — the keystone fires and concludes negligibility of the forger's
advantage. Refusal is discrimination only if acceptance still happens. -/
theorem the_repaired_bound_fires_on_the_right_floors (F : ConcurrentForgeryFamily)
    (Eff : Adversary (msisGame (cfMsisFamily F)) → Prop)
    (EffH : Adversary (cfEquivGame F) → Prop) (A : Adversary (concurrentForgeryGame F))
    (hEff : Eff (forgeryToMsisSolver F A)) (hEffH : EffH (forgeryToEquivFinder F A))
    (hmsis : MSISHardQuant (cfMsisFamily F) Eff) (hcol : Hard (cfEquivGame F) EffH) :
    Negl (gameAdv (concurrentForgeryGame F) A) :=
  hermine_concurrent_forgery_advantage_bound F Eff EffH A hEff hEffH hmsis hcol

/-! ## §6 — non-vacuity of the derived floors (genuine constraints, priced honestly). -/

/-- **(TOOTH — the MSIS floor is SATISFIABLE.)** At the empty adversary class the floor holds for any
family. Recorded HONESTLY, and it is not evidence of anything: `hard_bot_vacuous` is exactly the statement
that this satisfiability is vacuous — the value of a satisfiability witness is nothing without the
refutation beside it. -/
theorem cf_msis_floor_satisfiable_vacuously (F : ConcurrentForgeryFamily) :
    MSISHardQuant (cfMsisFamily F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the commit-collision floor is SATISFIABLE, vacuously.)** Likewise for the equivocation
horn's game — the empty class holds for any commit map, including a completely broken one. -/
theorem cf_equiv_floor_satisfiable_vacuously (F : ConcurrentForgeryFamily) :
    Hard (cfEquivGame F) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(TOOTH — the MSIS floor is FALSE at the unrestricted class, when the augmented map is compressing.)**
The real content: if a short nonzero kernel vector of `[A | t]` exists at every sampled instance — which
pigeonhole forces at deployed parameters, and which is WHY MSIS is a hard search problem — then the floor
at `Eff := ⊤` is FALSE, and the keystone is vacuous there. This is the price of `hEff`, stated as a
theorem instead of a promise. -/
theorem cf_msis_floor_top_false_of_compressing (F : ConcurrentForgeryFamily)
    (hsolv : ∀ l (i : F.Inst l),
      ∃ z, (letI := F.rqRing l; letI := F.rqNrm l; letI := F.mGrp l; letI := F.mMod l
            letI := F.mNrm l; letI := F.nGrp l; letI := F.nMod l
            IsMSISSolution (augmented (F.A l i) (F.t l i)) ((F.β l + F.β l) + (F.β l + F.β l)) z)) :
    ¬ MSISHardQuant (cfMsisFamily F) (fun _ => True) :=
  msisHardQuant_top_false_of_compressing (cfMsisFamily F) hsolv

/-! ## §7 — non-vacuity: the keyed collision floor is satisfiable AND load-bearing on Hermine
commit-reveals (the HashCR-leg siblings, untouched by the repair). -/

/-- A concrete commit-reveal equivocator: on every key it opens the two reveals `w`, `w'`. It is a genuine
collision finder — it wins exactly when `w ≠ w'` yet `cr.H i w = cr.H i w'`. -/
def crEquivocator {Idx W C : Type} [DecidableEq W] [DecidableEq C]
    (cr : CommitReveal Idx W C) (i : Idx) (w w' : W) :
    CollisionFinder (commitRevealFamily cr i) where
  find := fun _ _ => (w, w')

/-- **(TOOTH — the `⊤`-class floor is SATISFIABLE on a Hermine commit-reveal.)** The binding instance
`HermineHintMLWE.exCR` (`H i w = (i, w)`, injective) satisfies the keyed collision floor at the
UNRESTRICTED class — the sibling hypotheses are inhabited, unlike the vacuous injective floor.

⚑ **Priced, now that the `⊤` is written out instead of spelled `CollisionResistant`.** By
`hashCRHardQuant_top_false_of_compressing` the `⊤` floor holds for injective families and FAILS for
compressing ones with nothing in between, so this satisfiability witness says exactly that `exCR` is
NOT A HASH — it pairs the family into `ℕ × ℤ` and compresses nothing. It is a non-emptiness check and
never evidence about a deployed commitment. -/
theorem exCR_family_CR : HashCRHardQuant (commitRevealFamily exCR 3) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr exCR 3 exCR_hashcr

/-- **(TOOTH — the floor is LOAD-BEARING on a Hermine commit-reveal.)** The COLLIDING commit-reveal
`HermineHintMLWE.badCR` (`H _ _ = 0`, every reveal opens every commitment) collides at EVERY key —
`7 ≠ 8` yet both commit to `0`, the very pair `crEquivocator badCR 5 7 8` hands back — so the
`⊤`-class floor is FALSE there and the siblings cannot be discharged on a broken commit-reveal. The
floor is a genuine constraint, and the re-grounded binding is non-vacuous.

⚑ The `⊤` is in the statement now (it used to read `¬ CollisionResistant (commitRevealFamily badCR 5)`),
so this tooth reads as what it is: a refutation of the UNRESTRICTED-class floor, which
`hashCRHardQuant_top_false_of_compressing` refutes at every compressing commit hash — deployed ones
included, not just this deliberately broken one. -/
theorem badCR_family_not_CR : ¬ HashCRHardQuant (commitRevealFamily badCR 5) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨(0 : ℤ)⟩
    (fun _ _ => ⟨(7 : ℤ), (8 : ℤ), ?_, ?_⟩)
  · show (7 : ℤ) ≠ (8 : ℤ)
    norm_num
  · rfl

#assert_all_clean [
  commitRevealFamily_CR_of_hashcr,
  commitOpenGame_wins_iff,
  open_wins_imp,
  open_adv_le,
  hermine_commitment_binding_advantage_bound,
  hermine_binding_eff_top_false_of_compressing,
  hermine_binding_eff_bot_vacuous,
  hermine_binding_eff_fires,
  cfEquivGame_wins_iff,
  winProb_le_add_of_imp,
  claim_wins_imp,
  forgery_wins_imp,
  forgery_adv_le,
  hermine_concurrent_forgery_advantage_bound,
  the_repaired_bound_fires_on_the_right_floors,
  cf_msis_floor_satisfiable_vacuously,
  cf_equiv_floor_satisfiable_vacuously,
  cf_msis_floor_top_false_of_compressing,
  exCR_family_CR,
  badCR_family_not_CR
]

end Dregg2.Crypto.HermineHashCRRegrounded

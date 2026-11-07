/-
# `Dregg2.Crypto.IdentityCommitmentRegrounded` — the DEPLOYED hybrid-identity-commitment binding
RE-GROUNDED off the VACUOUS injective `HashCR` floor onto the KEYED COLLISION GAME
(`FloorGames.HashCRHardQuant F Eff`, with the adversary class IN THE STATEMENT).

⚑ The intermediate spelling `HashFloorHonesty.CollisionResistant` is DELETED (2026-07-28): it WAS
`HashCRHardQuant F (fun _ => True)` with the `⊤` folded into a name, and that `⊤` floor is itself
FALSE for every compressing hash (`FloorGames.hashCRHardQuant_top_false_of_compressing`). So this
file's `⊤`-class results are stated with the `⊤` written out, and the DISCHARGED binding is §2R's
keyed-ROM successor, not anything at `⊤`.

## The gap this closes (the id-re-basing leg of the 07-13 floor sweep)

`IdentityCommitment.id_commitment_binds` is the soundness floor UNDER THE DEPLOYED id re-basing
(`types/src/lib.rs::hybrid_id_commitment`; the `cell-crypto` / `captp` / `wire` `verify_committed_ml_dsa`
gate). It concludes "one id determines its `(ed25519, ml_dsa)` pair uniquely", conditioned on
`HermineHintMLWE.HashCR cr` — the SAME injective floor `HashFloorHonesty.hashCR_false_of_compressing`
PROVES FALSE for any compressing commitment. `hybrid_id_commitment = BLAKE3_derive_key(tag, ed ‖ len(ml) ‖ ml)`
maps a long framed preimage to a fixed-width id, so it IS compressing — the deployed gate's binding lemma
is VACUOUSLY TRUE at real parameters.

`HermineHashCRRegrounded` landed the generic commit-reveal regrounding (`commitRevealFamily`,
`hermine_commitment_binding_advantage_bound`) and its prose names IdentityCommitment as a "DEPLOYED-reachable
reuse" — but no theorem instantiates it for the id-commitment gate's own `cr`. This file wires that: it moves
the deployed gate onto the proper floor, so the id re-basing no longer rides an empty hypothesis.

## The re-grounding

* **`idCommitFamily cr`** — the deployed id-commit hash `H(())` over framed preimages, as the keyed hash
  family `commitRevealFamily cr ()` the honest collision game runs over.
* **`id_commitment_binds_advantage_bound`** — the advantage-bounded sibling of `id_commitment_binds`: an
  enrollment-equivocation adversary (two DISTINCT key pairs — hence two distinct length-framed preimages,
  by `IdentityCommitment.commit_collision_is_hash_collision` — colliding to one id) IS a `CollisionFinder`,
  so under the collision floor `HashCRHardQuant (idCommitFamily cr) Eff` its advantage is `Negl`. "one id ⟹
  one key pair" becomes "one id ⟹ one key pair EXCEPT with negligible probability" — a self-carried PQ key
  cannot impersonate the enrolled one except with negligible advantage. `Eff` stays a PARAMETER: the
  discharge is §2R's keyed-ROM floor, because the `⊤` class is refuted at the deployed hash.

## Non-fake

The `⊤`-class floor is SATISFIABLE (`idCommit_exCR_CR`: the injective `IdentityCommitment.exCR` discharges
it) and REFUTABLE (`idCommit_badCR_not_CR`: the COLLIDING `IdentityCommitment.badCR` has a collision at
every key, so `hashCRHardQuant_top_false_of_compressing` refutes the floor on it — mirrors
`IdentityCommitment.binding_needs_hashcr`).

⚑ Read those two together and the `⊤` pole prices itself: it holds exactly for the injective families and
fails exactly for the compressing ones, so `idCommit_exCR_CR` says `exCR` is NOT a hash, and the deployed
compressing `BLAKE3(tag, ed ‖ len(ml) ‖ ml)` sits on the refuted side with `badCR`. The re-grounding does
NOT buy a satisfiable floor at deployed parameters; §2R's keyed-ROM successor is what does.

The old injective-floor consumers are KEPT untouched; this file only ADDS the sibling. `#assert_all_clean`
(⊆ {propext, Classical.choice, Quot.sound}); no `sorry`, no fresh `axiom`.

## Coordination

This is the id-re-basing commit-reveal leg. The generic template + the concurrent-forgery composition are
`HermineHashCRRegrounded`; the STARK/FRI/Merkle hash consumers are `Circuit.FloorRegroundedConsumers`; the
`MSISHard`/DL Boolean crypto floors are `FloorBridge`/`CryptoFloorTeeth`. It stays in the
`IdentityCommitment` subtree — no consumer moved here lives elsewhere.
-/
import Dregg2.Crypto.HermineHashCRRegrounded
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Crypto.IdentityCommitment

namespace Dregg2.Crypto.IdentityCommitmentRegrounded

open Dregg2.Crypto.ConcreteSecurity (Negl Ensemble negl_zero not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top)
open Dregg2.Circuit.HashFloorHonesty
  (KeyedHashFamily CollisionFinder collisionAdv idFamily)
open Dregg2.Crypto.HermineHintMLWE (CommitReveal HashCR)
open Dregg2.Crypto.HermineHashCRRegrounded
  (commitRevealFamily commitRevealFamily_CR_of_hashcr commitOpenGame openToFinder
   hermine_commitment_binding_advantage_bound crEquivocator)
open Dregg2.Crypto.ConcreteSecurity (PolyBounded)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily)
open Dregg2.Crypto.RomBindingReduction (RomCarrier)
open Dregg2.Crypto.RomCarrierSites
  (flatFamily taggedCarrier romOpenGame RomOpenEff rom_open_binds romOpen_forger_excluded
   romOpenAdv constOpenComp constOpen_in_eff constOpen_gameAdv_pos constOpen_binds)
open Dregg2.Crypto.FloorGames
  (Game Adversary gameAdv gameAdv_mem_unit hashGame finderToAdv HashCRHardQuant
   hashCRHardQuant_top_false_of_compressing idFamily_hashCRHardQuant_top hard_bot_vacuous)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.CostAdversary (AnsSize IsPolyTime)
open Dregg2.Crypto.IdentityCommitment (commit verify_committed)

set_option autoImplicit false

/-! ## §1 — the deployed id-commit hash as a keyed family. -/

/-- **THE ID-COMMITMENT KEYED FAMILY.** The deployed hybrid-identity commit hash `cr.H ()` over the
length-framed preimages, as a `KeyedHashFamily` (`commitRevealFamily cr ()`). This is the keyed hash the
proper collision game runs over — the honest floor object the id re-basing actually needs. -/
def idCommitFamily {Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) : KeyedHashFamily :=
  commitRevealFamily cr ()

/-! ## §2 — the ENROLLMENT EQUIVOCATION, as a SECURITY REDUCTION on the DEPLOYED gate.

⚑ **WHAT THIS SECTION USED TO EXPORT, AND WHY IT IS GONE.** `id_commitment_binds_advantage_bound` took
the collision floor at the UNRESTRICTED class — `HashCRHardQuant (idCommitFamily cr) (fun _ => True)`,
then written `CollisionResistant (idCommitFamily cr)`, a spelling since DELETED — and
`FloorGames.hashCRHardQuant_top_false_of_compressing` proves THAT false for any compressing hash,
including the deployed `BLAKE3(tag, ed ‖ len(ml) ‖ ml)`. So the exported binding rested on a hypothesis
REFUTED at deployed parameters. Its `_eff` sibling took a `CollisionFinder` and applied the floor TO IT,
so the ENROLLMENT never appeared in a `Prop` at all. BOTH ARE DELETED.

What stands here is stronger than a generic instantiation: the break game is stated on the DEPLOYED
enrollment gate `IdentityCommitment.verify_committed` — the Rust `==` check — so the adversary's win is
literally "two DISTINCT `(ed25519, ml_dsa)` pairs both pass the gate against one enrolled id". The
extractor is the LENGTH FRAMING, and `hframe`'s contrapositive is what makes the two framed pre-images
distinct: that is the step `IdentityCommitment.id_commitment_binds` spends its (false) `HashCR` on. -/

/-- **THE ENROLLMENT-EQUIVOCATION GAME.** The adversary is handed a sampled key and WINS iff it publishes
an identity together with TWO key pairs that BOTH pass the deployed enrollment gate
(`verify_committed`, i.e. `commit cr frame ed ml = id`) while DIFFERING. A win is exactly the
impersonation `IdentityCommitment.attacker_key_not_committed` denies: a self-carried PQ key that the
enrolled id accepts. The deployed gate is IN the win relation. -/
noncomputable def enrollGame {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre) : Game where
  Inst := fun _ => Unit
  Ans := fun _ => Id × (Ed × MlDsa) × (Ed × MlDsa)
  instFin := fun _ => inferInstance
  instNe := fun _ => inferInstance
  wins := fun _ _ p =>
    p.2.1 ≠ p.2.2 ∧
      verify_committed cr frame p.1 p.2.1.1 p.2.1.2 ∧ verify_committed cr frame p.1 p.2.2.1 p.2.2.2
  winsDec := fun _ _ _ => Classical.propDecidable _

/-- **THE PROBLEM IS IN THE STATEMENT** — a win unfolds, by `Iff.rfl`, to two distinct key pairs passing
the deployed enrollment gate against one id. -/
theorem enrollGame_wins_iff {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre) (n : ℕ) (k : Unit)
    (p : Id × (Ed × MlDsa) × (Ed × MlDsa)) :
    (enrollGame cr frame).wins n k p ↔
      (p.2.1 ≠ p.2.2 ∧
        verify_committed cr frame p.1 p.2.1.1 p.2.1.2 ∧
          verify_committed cr frame p.1 p.2.2.1 p.2.2.2) :=
  Iff.rfl

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** An enrollment equivocator becomes a hash-collision finder
by FRAMING its two key pairs — `frame ed ml = ed ‖ len(ml) ‖ ml`, the deployed length framing. The
published id is discarded; the collision must be re-derived on the other side. -/
def enrollToFinder {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (A : Adversary (enrollGame cr frame)) : Adversary (hashGame (idCommitFamily cr)) where
  run := fun n k =>
    let p := A.run n k
    (frame p.2.1.1 p.2.1.2, frame p.2.2.1 p.2.2.2)

/-- **⚑ WIN-PRESERVATION — and this IS `IdentityCommitment.commit_collision_is_hash_collision`, as a map
rather than an `∃`.** Wherever the equivocator wins, the two framed pre-images are a GENUINE collision:
they are DISTINCT because `hframe` is injective in both arguments and the pairs differ, and their hashes
are EQUAL because both equal the published id. The `∃`-form of this fact is unconditionally TRUE at
deployed parameters by pigeonhole and so binds nothing; a MAP OF ADVERSARIES lands in a game advantage,
which a floor can bind. -/
theorem enroll_wins_imp {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame) (A : Adversary (enrollGame cr frame)) (n : ℕ) (k : Unit)
    (hwin : (enrollGame cr frame).wins n k (A.run n k)) :
    (hashGame (idCommitFamily cr)).wins n k ((enrollToFinder cr frame A).run n k) := by
  obtain ⟨hne, h1, h2⟩ := hwin
  refine ⟨fun hf => hne ?_, ?_⟩
  · obtain ⟨he, hm⟩ := hframe hf
    exact Prod.ext he hm
  · show cr.H () (frame (A.run n k).2.1.1 (A.run n k).2.1.2)
      = cr.H () (frame (A.run n k).2.2.1 (A.run n k).2.2.2)
    exact h1.trans h2.symm

/-- **THE ADVANTAGE INEQUALITY.** The enrollment equivocator's advantage is at most the extracted
finder's, at every parameter. Unconditional: no adversary class appears. -/
theorem enroll_adv_le {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame) (A : Adversary (enrollGame cr frame)) (n : ℕ) :
    gameAdv (enrollGame cr frame) A n
      ≤ gameAdv (hashGame (idCommitFamily cr)) (enrollToFinder cr frame A) n := by
  refine @winProb_le_of_imp _ ((enrollGame cr frame).instFin n) _ _ (fun k hk => ?_)
  replace hk := (Adversary.hit_eq_true _ _ _).mp hk
  refine (Adversary.hit_eq_true _ _ _).mpr ?_
  exact enroll_wins_imp cr frame hframe A n k hk

/-- **⚑ RE-GROUNDED `IdentityCommitment.id_commitment_binds` — from the id-commit hash's collision floor,
VIA the reduction.** Under the collision floor at the class `Eff`, an enrollment equivocator whose
extracted finder is in that class has NEGLIGIBLE advantage: an id determines its `(ed25519, ml_dsa)` pair
EXCEPT with negligible probability, so a self-carried PQ key cannot impersonate the enrolled one except
with that advantage. The Boolean "one id ⟹ one key pair", which needed the FALSE injective `HashCR`,
becomes an honest advantage bound.

`Eff` is a parameter here because this is the statement at an ARBITRARY class; the DISCHARGED
instantiation is §2R's keyed-ROM binding (the `IsPolyTime` discharge that stood here is DELETED —
its floor is refuted at deployed parameters, see §2R's header). -/
theorem id_commitment_binds_advantage_bound {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) (frame : Ed → MlDsa → Pre)
    (hframe : Function.Injective2 frame)
    (Eff : Adversary (hashGame (idCommitFamily cr)) → Prop)
    (A : Adversary (enrollGame cr frame))
    (hEff : Eff (enrollToFinder cr frame A))
    (hD : HashCRHardQuant (idCommitFamily cr) Eff) :
    Negl (gameAdv (enrollGame cr frame) A) :=
  negl_of_le (fun n => (gameAdv_mem_unit (enrollGame cr frame) A n).1)
    (enroll_adv_le cr frame hframe A) (hD _ hEff)

/-! ## §2R — ⚑⚑ THE DISCHARGED SUCCESSOR: the enrollment binding on the PROVED keyed-ROM floor.

⚑ **WHAT WAS DELETED HERE, AND WHY.** `id_commitment_binds_from_polyTime` discharged `Eff` at
`CostAdversary.IsPolyTime`, whose floor `HashCRHardQuant … (IsPolyTime …)` is REFUTED at deployed
parameters (`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`: `IsPolyTime`
prices answer SIZE, so a `.pure` answerer with a hardcoded short collision is in the class and wins
with probability `1`). DELETED, and replaced by the keyed-ROM successor below.

⚑ **THE MODELLING STEP, STATED (not smuggled).** The deployed id-commit hash
`BLAKE3_derive_key(tag, ed ‖ len(ml) ‖ ml)` is idealised as ONE SAMPLED oracle
`H : Unit × Pre → Fin (2 ^ l)` over the (finite, truncated-deployed-shape) framed pre-image space —
the standard ROM idealisation at an ASYMPTOTIC id width, a deliberate labelled modelling step, NOT a
derivation about the fixed public function. What it buys: the floor under the binding is
`KeyedRomFloor.keyedRom_hard` (the birthday bound, PROVED). The break keeps §2's shape: the PUBLISHED
id is in the win relation, the LENGTH FRAMING is the carrier's encoding, and `hframe` — the structural
injectivity the deployed framing genuinely satisfies — is the ONLY per-site obligation. -/

section RomSuccessor

variable {Ed MlDsa : Type} (Pre : Type) [Fintype Pre] [DecidableEq Pre] [Nonempty Pre]

/-- **THE ID-COMMITMENT KEYED-ROM FAMILY** — the deployed id-commit hash as a sampled oracle over the
framed pre-image space, ideal `λ`-bit ids. -/
def idCommitRomFamily : KeyedRomFamily :=
  flatFamily Unit inferInstance inferInstance inferInstance (fun _ => Pre)
    (fun _ => inferInstance) (fun _ => inferInstance) (fun _ => inferInstance)

/-- The family's width obligation, closed by construction. -/
theorem idCommitRomFamily_card_R (l : ℕ) :
    letI := (idCommitRomFamily Pre).rFin l
    Fintype.card ((idCommitRomFamily Pre).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-- **THE ENROLLMENT CARRIER** — payloads are `(ed25519, ml_dsa)` key pairs, the encoding is the
deployed LENGTH FRAMING, and `encode_inj` is exactly the `hframe : Function.Injective2 frame` the old
proof carried BESIDE the refuted `HashCR` — the structural fact survives, the false floor does not. -/
def enrollRomCarrier [DecidableEq Ed] [DecidableEq MlDsa]
    (frame : Ed → MlDsa → Pre) (hframe : Function.Injective2 frame) :
    RomCarrier (idCommitRomFamily Pre) :=
  taggedCarrier _ (fun _ => Unit) (fun _ => Ed × MlDsa) (fun _ => inferInstance)
    (fun _ _ p => frame p.1 p.2)
    (fun _ _ a b h => by
      obtain ⟨he, hm⟩ := hframe h
      exact Prod.ext he hm)

/-- **THE ENROLLMENT BREAK AT THE SAMPLED ORACLE** — §2's shape verbatim: the adversary PUBLISHES an
id and exhibits two DISTINCT key pairs whose framed pre-images BOTH commit to it. -/
abbrev enrollRomGame [DecidableEq Ed] [DecidableEq MlDsa]
    (frame : Ed → MlDsa → Pre) (hframe : Function.Injective2 frame) : Game :=
  romOpenGame (idCommitRomFamily Pre) (enrollRomCarrier Pre frame hframe)

/-- **THE DEPLOYED IMPERSONATION IS A WIN** — two distinct `(ed, ml)` pairs whose framed pre-images the
sampled oracle maps to ONE published id are a win of the game (`enroll_wins_imp`'s content, restated at
the sampled oracle). -/
theorem enrollRom_forgery_is_break [DecidableEq Ed] [DecidableEq MlDsa]
    (frame : Ed → MlDsa → Pre) (hframe : Function.Injective2 frame)
    (l : ℕ) (H : (enrollRomGame Pre frame hframe).Inst l) (idv : Fin (2 ^ l))
    {p p' : Ed × MlDsa} (hne : p ≠ p')
    (h1 : H ((), frame p.1 p.2) = idv) (h2 : H ((), frame p'.1 p'.2) = idv) :
    (enrollRomGame Pre frame hframe).wins l H (idv, ((), ()), p, p') :=
  ⟨hne, h1, h2⟩

/-- **⚑⚑ THE RE-GROUNDED ID-COMMITMENT BINDING — floor PROVED, nothing refutable carried.** Every
query-bounded enrollment equivocator has NEGLIGIBLE advantage: an id determines its
`(ed25519, ml_dsa)` pair except with negligible probability, in the keyed ROM model of the header —
so a self-carried PQ key cannot impersonate the enrolled one except with that advantage. This is what
`id_commitment_binds_from_polyTime` (DELETED — floor refuted) claimed and could not have. -/
theorem id_commitment_binds_rom [DecidableEq Ed] [DecidableEq MlDsa]
    (frame : Ed → MlDsa → Pre) (hframe : Function.Injective2 frame) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (enrollRomGame Pre frame hframe))
    (hA : RomOpenEff (idCommitRomFamily Pre) (enrollRomCarrier Pre frame hframe) Q A) :
    Negl (gameAdv (enrollRomGame Pre frame hframe) A) :=
  rom_open_binds _ _ Q hQ (idCommitRomFamily_card_R Pre) A hA

/-- **(TOOTH — the counterexample DIES.)** An enrollment equivocator with non-negligible advantage is
OUTSIDE the query class. -/
theorem enrollRom_nonNegl_forger_excluded [DecidableEq Ed] [DecidableEq MlDsa]
    (frame : Ed → MlDsa → Pre) (hframe : Function.Injective2 frame) (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (enrollRomGame Pre frame hframe))
    (hnn : ¬ Negl (gameAdv (enrollRomGame Pre frame hframe) A)) :
    ¬ RomOpenEff (idCommitRomFamily Pre) (enrollRomCarrier Pre frame hframe) Q A :=
  romOpen_forger_excluded _ _ Q hQ (idCommitRomFamily_card_R Pre) A hnn

/-- **(TOOTH — admitted, winnable, DEFANGED, at a CLOSED instance.)** At `Ed = MlDsa = Fin 2`,
`Pre = Fin 2 × Fin 2`, `frame = Prod.mk`, `Q = 2`: the `0`-query hardcoded opener — the exact shape
that refutes the `IsPolyTime` floor with probability `1` — is IN the class, wins with POSITIVE
probability at every parameter, and its advantage is NEGLIGIBLE. The successor spine elaborates
end-to-end at a closed instance. -/
theorem prodMk_inj2 {α β : Type} : Function.Injective2 (Prod.mk : α → β → α × β) :=
  fun _ _ _ _ h => ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem enrollRom_fires :
    (RomOpenEff (idCommitRomFamily (Fin 2 × Fin 2))
        (enrollRomCarrier (Fin 2 × Fin 2) Prod.mk prodMk_inj2) (fun _ => 2)
        (romOpenAdv _ _ (constOpenComp _ _ (fun l => (0 : Fin (2 ^ l))) (fun _ => ((), ()))
          (fun _ => ((0 : Fin 2), (0 : Fin 2))) (fun _ => ((1 : Fin 2), (0 : Fin 2))))))
    ∧ (∀ l, 0 < gameAdv (enrollRomGame (Fin 2 × Fin 2) Prod.mk prodMk_inj2)
        (romOpenAdv _ _ (constOpenComp _ _ (fun l => (0 : Fin (2 ^ l))) (fun _ => ((), ()))
          (fun _ => ((0 : Fin 2), (0 : Fin 2))) (fun _ => ((1 : Fin 2), (0 : Fin 2))))) l)
    ∧ Negl (gameAdv (enrollRomGame (Fin 2 × Fin 2) Prod.mk prodMk_inj2)
        (romOpenAdv _ _ (constOpenComp _ _ (fun l => (0 : Fin (2 ^ l))) (fun _ => ((), ()))
          (fun _ => ((0 : Fin 2), (0 : Fin 2))) (fun _ => ((1 : Fin 2), (0 : Fin 2)))))) := by
  refine ⟨constOpen_in_eff _ _ _ _ _ _ _,
    fun l => constOpen_gameAdv_pos _ _ _ _ _ _ l
      (by show ((0 : Fin 2), (0 : Fin 2)) ≠ ((1 : Fin 2), (0 : Fin 2)); decide),
    constOpen_binds _ _ _ _ _ _ (fun _ => 2) ⟨1, 5, ?_⟩
      (idCommitRomFamily_card_R (Fin 2 × Fin 2))⟩
  filter_upwards [Filter.eventually_ge_atTop 5] with n hn
  have hn' : (5 : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  rw [abs_of_nonneg (by positivity)]
  push_cast
  nlinarith

end RomSuccessor

/-! ## §3 — non-vacuity: the floor is satisfiable AND load-bearing on the id-commitment. -/

/-- **(TOOTH — the `⊤`-class floor is SATISFIABLE on the id-commitment.)** The binding instance
`IdentityCommitment.exCR` (`H () p = p`, injective) satisfies the keyed collision floor at the
UNRESTRICTED class — the sibling hypothesis is inhabited, unlike the vacuous injective floor.

⚑ And injectivity is the ONLY way to satisfy it: read against `idCommit_badCR_not_CR` below, a `⊤`
witness is a statement that the family is not compressing, i.e. NOT a hash. The deployed
`BLAKE3(tag, ed ‖ len(ml) ‖ ml)` is compressing and so cannot be on this side. -/
theorem idCommit_exCR_CR :
    HashCRHardQuant (idCommitFamily Dregg2.Crypto.IdentityCommitment.exCR) (fun _ => True) :=
  commitRevealFamily_CR_of_hashcr Dregg2.Crypto.IdentityCommitment.exCR ()
    Dregg2.Crypto.IdentityCommitment.exCR_hashcr

/-- **(TOOTH — the `⊤`-class floor is REFUTABLE on the id-commitment.)** The COLLIDING commit
`IdentityCommitment.badCR` (`H () _ = []`, every framed preimage opens every id) has a collision at EVERY
key (`[1] ≠ [2]` yet both hash to `[]`), so `hashCRHardQuant_top_false_of_compressing` refutes the floor at
the UNRESTRICTED class outright. The sibling cannot be discharged on a broken commit, exactly as
`IdentityCommitment.binding_needs_hashcr` shows the id stops binding once collision-resistance fails —
and the same argument runs at ANY compressing hash, the deployed one included. -/
theorem idCommit_badCR_not_CR :
    ¬ HashCRHardQuant (idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR) (fun _ => True) := by
  refine hashCRHardQuant_top_false_of_compressing _ ⟨([] : List ℕ)⟩
    (fun _ _ => ⟨([1] : List ℕ), ([2] : List ℕ), ?_, rfl⟩)
  show ([1] : List ℕ) ≠ [2]
  decide

/-- **THE RE-GROUNDED GATE FIRES AT A REAL FLOOR WITNESS.** On the injective identity family
(`FloorGames.idFamily_hashCRHardQuant_top`), the enrollment-equivocation advantage is negligible — the
deployed id-re-basing binding runs end-to-end to a genuine `Negl` conclusion at an inhabited floor
hypothesis. (Inhabited BECAUSE the family is injective; no compressing family reaches this witness.) -/
theorem id_commitment_binds_fires (A : Adversary (commitOpenGame idFamily)) :
    Negl (gameAdv (commitOpenGame idFamily) A) :=
  hermine_commitment_binding_advantage_bound idFamily (fun _ => True) A trivial
    idFamily_hashCRHardQuant_top

/-! ## §4 — the `Eff` parameter, PRICED at both poles, and the CANARY. -/

/-- **(TOOTH — `Eff := ⊤` is FALSE at the deployed compressing id-commit.)** The price of `hEff`, stated
as a theorem: the class cannot be left implicit, because the implicit `⊤` is refuted at the colliding
`IdentityCommitment.badCR`.

⚑ This IS `idCommit_badCR_not_CR` — nothing is added. It used to bridge a `CollisionResistant` refutation
across `collisionResistant_iff_hashCRHardQuant_top`; with the `⊤` now written into the tooth's own
statement, the bridge is the identity and the two names denote one theorem. Both are kept because
`Verify/FloorRatchetBaseline` grandfathers refuted-floor carriers BY NAME. -/
theorem idCommit_eff_top_false :
    ¬ HashCRHardQuant (idCommitFamily Dregg2.Crypto.IdentityCommitment.badCR) (fun _ => True) :=
  idCommit_badCR_not_CR

/-- **(TOOTH — the OTHER pole: `Eff := ⊥` is vacuous.)** At the empty class the floor holds for ANY
id-commit hash. -/
theorem idCommit_eff_bot_vacuous {Pre Id : Type} [DecidableEq Pre] [DecidableEq Id]
    (cr : CommitReveal Unit Pre Id) :
    HashCRHardQuant (idCommitFamily cr) (fun _ => False) :=
  hard_bot_vacuous _

/-- **(CANARY — the gate does NOT follow from the floor applied at another adversary.)** From the floor at
some OTHER adversary `B` the enrollment-equivocator's negligibility does not follow: `hD B hB` bounds a
DIFFERENT ensemble, and only the game-advantage bridge at the extracted finder connects it. -/
example {Ed MlDsa Pre Id : Type} [DecidableEq Pre] [DecidableEq Id] (cr : CommitReveal Unit Pre Id)
    (frame : Ed → MlDsa → Pre)
    (Eff : Adversary (hashGame (idCommitFamily cr)) → Prop)
    (A : Adversary (enrollGame cr frame))
    (B : Adversary (hashGame (idCommitFamily cr))) (hB : Eff B)
    (hD : HashCRHardQuant (idCommitFamily cr) Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (enrollGame cr frame) A) := hD B hB)
  trivial

/-- **THE `Eff` GATE FIRES AT A REAL FLOOR WITNESS.** On the injective `IdentityCommitment.exCR` the
`Eff`-floor at `⊤` holds (`idCommit_exCR_CR`, an INHABITED hypothesis, unlike the vacuous injective
floor), so the `Eff` gate runs end-to-end to a genuine `Negl`. Read with `idCommit_eff_top_false`: the
gate fires HERE and cannot fire at a compressing hash, which is why the deployed discharge is §2R. -/
theorem id_commitment_binds_eff_fires
    (A : Adversary (enrollGame Dregg2.Crypto.IdentityCommitment.exCR
      Dregg2.Crypto.IdentityCommitment.exFrame)) :
    Negl (gameAdv (enrollGame Dregg2.Crypto.IdentityCommitment.exCR
      Dregg2.Crypto.IdentityCommitment.exFrame) A) :=
  id_commitment_binds_advantage_bound Dregg2.Crypto.IdentityCommitment.exCR
    Dregg2.Crypto.IdentityCommitment.exFrame Dregg2.Crypto.IdentityCommitment.exFrame_inj
    (fun _ => True) A trivial idCommit_exCR_CR

#assert_all_clean [
  enrollGame_wins_iff,
  enroll_wins_imp,
  enroll_adv_le,
  id_commitment_binds_advantage_bound,
  idCommitRomFamily_card_R,
  enrollRom_forgery_is_break,
  id_commitment_binds_rom,
  enrollRom_nonNegl_forger_excluded,
  enrollRom_fires,
  idCommit_exCR_CR,
  idCommit_badCR_not_CR,
  id_commitment_binds_fires,
  idCommit_eff_top_false,
  idCommit_eff_bot_vacuous,
  id_commitment_binds_eff_fires
]

end Dregg2.Crypto.IdentityCommitmentRegrounded

/-
# `Metatheory.Open.BlindedSpanHiding` — the ZK-HIDING of the blinded span-commitment, moved from a
prover-side hand-wave to (a) an UNCONDITIONAL statistical theorem + (b) a CONDITIONAL reduction to a
NAMED Poseidon2 preimage floor against the REAL cost-model adversary, and (c) a precisely-named OPEN.

## The object

The wide blinded membership descriptor (`Dregg2.Circuit.Emit.BlindedMembershipWideEmit`, read-only)
publishes an 8-felt blinded leaf `wBLINDED = A9(cur8 ‖ blinding)` — the deployed shape the task writes
as `hole_commit = hash_4_to_1_wide([span_digest8, C_T, BLINDING, 0])`: the 8-felt span digest and a
FRESH HIDDEN blinding felt, absorbed by the deployed wide Poseidon2 (`Poseidon2Binding.babyBearD4W16`),
with the public commit-to-tree `C_T` in the preimage. `BLINDING` and `span_digest8` stay HIDDEN — that
hiddenness IS the unlinkability the anonymous-credential show relies on. The emit file states hiding as
English prose ("leaf + blinding stay HIDDEN"); there was NO theorem. This file supplies one.

We model the preimage assembly ABSTRACTLY (`assemble`) so the theorem is faithful to the deployed arity;
`BlindedSpanCommitment.wideHash` is the `Poseidon2Binding` `List ℤ → …` object and `tagCode` its
domain-separation prefix.

## HONEST CLASSIFICATION — this is the spine of the deliverable

  * **(a) UNCONDITIONAL — the statistical / perfect-blinding fragment (`§4`, `PerfectBlinding`).** Under
    the perfect-blinding idealization — a uniform `BLINDING` makes the commitment view a WITNESS-FREE
    simulation, `view ct span = sim ct` — the verifier's view carries LITERALLY ZERO information about
    which span was committed (`spanBlind_view_indep`), and two spans are unlinkable
    (`spanBlind_unlinkable`). This is a real `Metatheory.Open.PerfectZK` instance, proved with NO
    hypothesis, kernel-clean, WITH TEETH (an unblinded/leaky view fails it). ⚠ It is the INFORMATION-
    THEORETIC IDEAL: the deployed fixed sponge does NOT satisfy it (a fixed function into one bounded
    field is not perfectly hiding); its hiding is the COMPUTATIONAL (b) half. This mirrors exactly how
    `PerfectZK` scopes its own `otp`/`fieldZK` vs the computational residue.

  * **(b) CONDITIONAL on a NAMED Poseidon2 preimage floor, vs the REAL `PolyTime` adversary (`§2`,`§3`).**
    A span-recovery hiding break of the DEPLOYED blinded leaf REDUCES to inverting the domain-separated
    wide Poseidon2 on the published commitment: `span_recovery_hard_from_preimage_floor` — for EVERY
    adversary class `Eff`, if the extracted preimage-finder is in `Eff` and the wide hash is
    preimage-hard at `Eff` (`WidePreimageFloor`), a span-recoverer has NEGLIGIBLE advantage. The reduction
    is a real extractor (`recoverToPreimage`) + advantage inequality (`recover_adv_le`), NOT a `P → P`
    unfold: the floor game (wide-hash preimage) and the consumer game (deployed span recovery) are
    DIFFERENT games, connected only by the extractor (the CANARY `floor_at_other_finder_does_not_discharge`
    pins that). The `IsPolyTime` instantiation
    (`span_recovery_hard_from_polyTime`) is DELETED (07-24): its floor is REFUTED in this file
    (`widePreimageFloor_polyTime_false`), and its DISCHARGED successor is LANDED —
    `Metatheory.Open.BlindedSpanHidingKeyed.span_hiding_from_keyed_floor` / `spanRecoverGap_le`, the
    same consumer on the PROVED keyed query-counted hiding floor
    (`KeyedRomHidingFloor.keyedRomHiding_hard`), with the hardcoder ADMITTED and DEFANGED.

    ⚠ **THE HONEST PRICE, PROVED IN-FILE.** `WidePreimageFloor D (IsPolyTime …)` — the floor the
    `polyTime` instantiation rests on — is itself REFUTED at deployed parameters
    (`widePreimageFloor_polyTime_false`): `CostAdversary.idAdv` prices ANSWER SIZE, never search
    difficulty, so the constant finder that HARDCODES the (fixed, short) honest opening is `IsPolyTime`
    and wins with probability `1`. This is the `KeyedRomFloor.sysRoots_floor_polyTime_false_babyBear`
    disease. So the `IsPolyTime` form was VACUOUS at the deployed hash, exactly like
    the deleted `WideCommitBoundary.stateCommit_binds_from_polyTime`. The NON-VACUOUS floor is the KEYED,
    QUERY-COUNTED class (challenge sampled AFTER the adversary, so it cannot hardcode) — and its hiding
    instance now EXISTS (`Dregg2.Crypto.KeyedRomHidingFloor` + `BlindedSpanHidingKeyed`), which is why
    the `IsPolyTime` form is deleted rather than kept beside it.

  * **(c) OPEN — NOT in scope, NOT claimed.** Two things stay open, faithfully, as `EpistemicDial`/
    `PerfectZK` already hold them:
      1. the FULL two-world INDISTINGUISHABILITY (semantic hiding): the genuine hiding advantage is a
         DIFFERENCE of two probabilities `|Pr[A=1|commit span₀] − Pr[A=1|commit span₁]|`, which is
         `FloorGames.distAdv`-SHAPED (§7), NOT a `gameAdv`/`winProb`, and `CostAdversary.IsPolyTime` does
         not type over `Distinguisher`s. Preimage-recovery (this file's (b)) is a SUFFICIENT hiding break
         — recover the opening and you have the span — not the indistinguishability form.
      2. the STARK HVZK simulator (that the `HidingFriPcs` random-row blinding actually SIMULATES the
         proof transcript) — the computational-ZK residue `EpistemicDial`/`PerfectZK` name.

The win is exactly (a) proven + (b) conditional-on-a-named-floor-vs-a-real-`PolyTime`-adversary, with the
floor's vacuity at `IsPolyTime` proved and the query-counted successor named — the repo's methodology.

## Axiom hygiene

`#assert_axioms` on every load-bearing arm ⊆ {propext, Classical.choice, Quot.sound}; NO `sorry`, NO
fresh `axiom`, NO `native_decide`. The named floor `WidePreimageFloor` is a `def`/HYPOTHESIS reduced to,
never an `axiom`. NEW file; imports read-only.
-/
import Dregg2.Crypto.CostAdversary
import Dregg2.Crypto.CostTactics
import Metatheory.Open.PerfectZK

namespace Metatheory.Open.BlindedSpanHiding

open Dregg2.Crypto.FloorGames
  (Game Adversary Adversary.hit Adversary.hit_eq_true gameAdv gameAdv_mem_unit Hard hard_bot_vacuous
   not_hard_top_of_always_solvable)
open Dregg2.Crypto.CostAdversary
open Dregg2.Crypto.ConcreteSecurity (Negl not_negl_one)
open Dregg2.Crypto.ProbCrypto (winProb winProb_top winProb_le_of_imp negl_of_le)

set_option autoImplicit false
set_option linter.unusedVariables false

/-! ## §1 — the deployed blinded span commitment, and its two games. -/

/-- **The deployed blinded span commitment, abstractly** — faithful to
`BlindedMembershipWideEmit.wBLINDED` (`A9(cur8 ‖ blinding)`), the task's `hash_4_to_1_wide([span_digest8,
C_T, BLINDING, 0])`.

* `wideHash` — the deployed wide Poseidon2 (`Poseidon2Binding.babyBearD4W16`), `List ℤ → List ℤ` (an
  8-felt digest; kept wide, not squeezed to one felt — the class-D lesson).
* `Tag` / `tagCode` / `deployedTag` — the domain-separation structure (the effective key), exactly as
  `Poseidon2KeyedBridge.DomainSeparatedSponge`.
* `CT` — the public commit-to-tree `C_T` (a public coordinate of the preimage; not hidden).
* `honestSpan` — the HIDDEN 8-felt span digest a real show commits (the witness); a field, exactly as
  `FloorGames.MLWEFamily.secret` is — the win relations reference it, and it is what the adversary must
  NOT learn.
* `honestBlinding` — the FRESH HIDDEN blinding felt. -/
structure BlindedSpanCommitment where
  /-- The deployed wide Poseidon2 sponge (`Poseidon2Binding`'s object), 8-felt output. -/
  wideHash : List ℤ → List ℤ
  /-- The domain-separation tag space (the effective key). -/
  Tag : Type
  /-- The tag space is finite (the game samples a uniform tag). -/
  tagFintype : Fintype Tag
  /-- The tag space is inhabited. -/
  tagNonempty : Nonempty Tag
  /-- How a domain-separation tag is absorbed: a field-element prefix ahead of the preimage. -/
  tagCode : Tag → List ℤ
  /-- The specific domain-separation tag the deployment uses. -/
  deployedTag : Tag
  /-- The public commit-to-tree `C_T` (a public coordinate of the preimage). -/
  CT : ℤ
  /-- The HIDDEN 8-felt span digest a real show commits (the witness). -/
  honestSpan : Tag → List ℤ
  /-- The span digest is 8 felts wide. -/
  honestSpanLen : ∀ t, (honestSpan t).length = 8
  /-- The FRESH HIDDEN blinding felt. -/
  honestBlinding : Tag → ℤ

namespace BlindedSpanCommitment

variable (D : BlindedSpanCommitment)

/-- **The wide preimage assembly** — `span_digest8 ‖ [C_T, BLINDING, 0]`, the task's `[span_digest8,
C_T, BLINDING, 0]` (the deployed `A9(cur8 ‖ blinding)` with `C_T` and the padding word in the
preimage). -/
def assemble (span : List ℤ) (blinding : ℤ) : List ℤ := span ++ [D.CT, blinding, 0]

@[simp] theorem assemble_length (span : List ℤ) (blinding : ℤ) :
    (D.assemble span blinding).length = span.length + 3 := by
  simp [assemble]

/-- The deployed wide hash domain-separated by a tag: `xs ↦ wideHash (tagCode t ++ xs)`. -/
def wideHashAt (t : D.Tag) (xs : List ℤ) : List ℤ := D.wideHash (D.tagCode t ++ xs)

/-- The deployed blinded-leaf commitment at a tag: the wide hash of the assembled preimage. -/
def commitAt (t : D.Tag) (span : List ℤ) (blinding : ℤ) : List ℤ :=
  D.wideHashAt t (D.assemble span blinding)

/-- The PUBLISHED blinded leaf `hole_commit` at a tag: the honest span digest, blinded. A REAL
commitment (built from a real opening) — this is what makes the games non-vacuous. -/
def holeCommitAt (t : D.Tag) : List ℤ := D.commitAt t (D.honestSpan t) (D.honestBlinding t)

/-- **The honest preimage** the deployment actually computes, at a tag. -/
def honestPreimage (t : D.Tag) : List ℤ := D.assemble (D.honestSpan t) (D.honestBlinding t)

theorem wideHashAt_honestPreimage (t : D.Tag) :
    D.wideHashAt t (D.honestPreimage t) = D.holeCommitAt t := rfl

@[simp] theorem honestPreimage_length (t : D.Tag) : (D.honestPreimage t).length = 11 := by
  simp [honestPreimage, D.honestSpanLen t]

/-! ### The two games — instances are sampled tags; NO hidden secret is in the instance. -/

/-- **THE SPAN-RECOVERY HIDING-BREAK GAME (the consumer).** The adversary is handed a sampled
domain-separation tag and WINS iff it outputs an OPENING `(span, blinding)` of the published blinded leaf
`hole_commit` at that tag — i.e. it RECOVERS the committed span. Recovering the opening is a hiding break
(you learn the span). The instance is the tag ALONE — the span/blinding are NOT in it; the adversary must
find them. -/
def spanRecoverGame : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List ℤ × ℤ
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t c => D.commitAt t c.1 c.2 = D.holeCommitAt t
  winsDec := fun _ t c => inferInstance

/-- **THE PROBLEM IS IN THE STATEMENT** — the win relation is a genuine opening of the deployed blinded
leaf. -/
theorem spanRecoverGame_wins_iff (t : D.Tag) (c : List ℤ × ℤ) :
    (D.spanRecoverGame).wins 0 t c ↔ D.commitAt t c.1 c.2 = D.holeCommitAt t := Iff.rfl

/-- **THE WIDE-POSEIDON2 PREIMAGE GAME (the floor).** The adversary is handed a sampled tag and WINS iff
it outputs a PREIMAGE of the published commitment under the domain-separated wide hash. This is
preimage-resistance / one-wayness of the deployed `wideHash` — the NAMED Poseidon2 floor the hiding break
reduces to. -/
def widePreimageGame : Game where
  Inst := fun _ => D.Tag
  Ans := fun _ => List ℤ
  instFin := fun _ => D.tagFintype
  instNe := fun _ => D.tagNonempty
  wins := fun _ t p => D.wideHashAt t p = D.holeCommitAt t
  winsDec := fun _ t p => inferInstance

theorem widePreimageGame_wins_iff (t : D.Tag) (p : List ℤ) :
    (D.widePreimageGame).wins 0 t p ↔ D.wideHashAt t p = D.holeCommitAt t := Iff.rfl

/-- **THE NAMED FLOOR — preimage-hardness of the domain-separated wide Poseidon2.** `WidePreimageFloor D
Eff`: every `Eff`-adversary inverts the deployed wide hash on the published commitment only with
negligible probability. A HYPOTHESIS (never an `axiom`), the standard preimage-resistance assumption; the
`§3` reduction rests on it. At the query-counted class it is the honest successor of the refuted
`IsPolyTime` instance (see `widePreimageFloor_polyTime_false`). -/
def WidePreimageFloor (Eff : Adversary (D.widePreimageGame) → Prop) : Prop :=
  Hard (D.widePreimageGame) Eff

/-! ### Answer-size measures (the game's, not the adversary's — `CostAdversary` design commitment 4). -/

/-- The span-recovery answer encoding: the span digest's felts plus the blinding felt. -/
def spanAnsSize : AnsSize (D.spanRecoverGame) := fun _ c => c.1.length + 1

/-- The preimage answer encoding: the claimed preimage's felts. -/
def preAnsSize : AnsSize (D.widePreimageGame) := fun _ p => p.length

/-! ## §2 — THE REDUCTION: a span-recoverer becomes a wide-hash preimage-finder. -/

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** A span-recoverer becomes a wide-hash preimage-finder by
ASSEMBLING the recovered opening into the wide preimage `[span, C_T, blinding, 0]`. This is a pure output
reshaping with the tag passed through (an `Adversary.postMap` shape), so `§3` discharges its efficiency. -/
def recoverToPreimage (A : Adversary (D.spanRecoverGame)) : Adversary (D.widePreimageGame) where
  run := fun l t => D.assemble (A.run l t).1 (A.run l t).2

/-- **⚑ WIN-PRESERVATION — the reduction, at the game level.** Every tag the span-recoverer wins, the
extracted preimage-finder wins: an opening of the blinded leaf IS a preimage of the wide hash on the
published commitment. Definitional (`commitAt = wideHashAt ∘ assemble`). -/
theorem recover_wins_imp (A : Adversary (D.spanRecoverGame)) (l : ℕ) (t : D.Tag)
    (hwin : (D.spanRecoverGame).wins l t (A.run l t)) :
    (D.widePreimageGame).wins l t ((D.recoverToPreimage A).run l t) := by
  show D.wideHashAt t (D.assemble (A.run l t).1 (A.run l t).2) = D.holeCommitAt t
  exact hwin

/-- **THE ADVANTAGE INEQUALITY.** The span-recoverer's advantage is at most the extracted
preimage-finder's, at every parameter, over the SAME sampled tag space. -/
theorem recover_adv_le (A : Adversary (D.spanRecoverGame)) (l : ℕ) :
    gameAdv (D.spanRecoverGame) A l ≤ gameAdv (D.widePreimageGame) (D.recoverToPreimage A) l := by
  refine @winProb_le_of_imp _ (D.tagFintype) _ _ (fun t ht => ?_)
  replace ht := (Adversary.hit_eq_true _ _ _).mp ht
  exact (Adversary.hit_eq_true _ _ _).mpr (D.recover_wins_imp A l t ht)

/-- **⚑ SPAN HIDING FROM THE PREIMAGE FLOOR — the general-`Eff` reduction (THE HEADLINE).** Under the
named preimage floor at a class `Eff`, a span-recoverer whose EXTRACTED preimage-finder is in `Eff` has
NEGLIGIBLE advantage: the deployed blinded leaf hides its span except with negligible probability. The
content is the reduction (`recover_adv_le`), NOT a `P → P` unfold — the floor game and the consumer game
are DIFFERENT (`floor_at_other_finder_does_not_discharge` is the canary). `hEff` is the standard "the
reduction is efficient" (`FloorGames` §8); the DISCHARGED instantiation is
`BlindedSpanHidingKeyed.span_hiding_from_keyed_floor` on the PROVED keyed hiding floor (the
`IsPolyTime` discharge that stood in §3 is DELETED — `widePreimageFloor_polyTime_false` refutes its
floor). -/
theorem span_recovery_hard_from_preimage_floor
    (Eff : Adversary (D.widePreimageGame) → Prop) (A : Adversary (D.spanRecoverGame))
    (hEff : Eff (D.recoverToPreimage A)) (hFloor : D.WidePreimageFloor Eff) :
    Negl (gameAdv (D.spanRecoverGame) A) :=
  negl_of_le (fun l => (gameAdv_mem_unit (D.spanRecoverGame) A l).1)
    (D.recover_adv_le A) (hFloor (D.recoverToPreimage A) hEff)

/-! ## §3 — ⚑ the `IsPolyTime` discharge is DELETED; the successor is LANDED.

`span_recovery_hard_from_polyTime` stood here: `Eff := IsPolyTime`, extractor efficiency discharged by
`poly_time`. Its floor `WidePreimageFloor (IsPolyTime …)` is REFUTED below
(`widePreimageFloor_polyTime_false` — the hardcoder of the FIXED published opening is `IsPolyTime` and
wins with probability `1`), so the theorem was VACUOUS at the deployed hash. It is DELETED, not kept
beside the repair; the DISCHARGED successor is `Metatheory.Open.BlindedSpanHidingKeyed`
(`span_hiding_from_keyed_floor`, `spanRecoverGap_le`, `blindedSpan_recovery_negl`): the same
span-recovery consumer on the PROVED keyed query-counted hiding floor
(`KeyedRomHidingFloor.keyedRomHiding_hard`, challenge and blinding sampled AFTER the adversary), with
the hardcoder ADMITTED at `Q = 0` and its recovery gap EXACTLY `0` — defanged, not excluded. The
refutation and the class-inhabitation teeth below are KEPT: they are the cure's record, not the
disease. -/

/-! ## §3b — NON-VACUITY: both games are winnable at ⊤; the floor's poles; the IsPolyTime price. -/

/-- **(⊤-POLE — the consumer game is NON-VACUOUS: brute force WINS it.)** The honest opening exists at
every tag, so the span-recovery game's solvable fraction is `1` and its unrestricted floor is FALSE — the
`bruteForce`/`choiceAdv` twin that recovers the span wins. This is the required "the ⊤-pole brute-force
adversary WINS the game". -/
theorem spanRecover_top_false : ¬ Hard (D.spanRecoverGame) (fun _ => True) :=
  not_hard_top_of_always_solvable (D.spanRecoverGame) (fun _ => ⟨([], 0)⟩)
    (fun _ t => ⟨(D.honestSpan t, D.honestBlinding t), rfl⟩)

/-- **(⊤-POLE — the floor game is NON-VACUOUS: a preimage exists at every tag.)** The honest price of the
floor: at the unrestricted class the preimage floor is the existence floor, and preimages exist. -/
theorem widePreimage_top_false : ¬ Hard (D.widePreimageGame) (fun _ => True) :=
  not_hard_top_of_always_solvable (D.widePreimageGame) (fun _ => ⟨[]⟩)
    (fun _ t => ⟨D.honestPreimage t, D.wideHashAt_honestPreimage t⟩)

/-- **(⊥-POLE — vacuous, recorded so satisfiability is not mistaken for evidence.)** -/
theorem widePreimage_bot_vacuous : D.WidePreimageFloor (fun _ => False) :=
  hard_bot_vacuous (D.widePreimageGame)

/-- **THE POLY-TIME CLASS IS INHABITED AT THE FLOOR GAME** (so the floor is not the `⊥` class in
disguise): the constant finder that writes the honest preimage has bounded answer size, hence is
`IsPolyTime`. -/
theorem widePreimageFloor_polyTime_inhabited :
    IsPolyTime (D.preAnsSize)
      (idAdv (G := D.widePreimageGame) (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ t => D.honestPreimage t)).toAdversary :=
  isPolyTime_inhabited (D.preAnsSize) (fun _ t => D.honestPreimage t)
    ⟨11, 0, fun _ t => by simp [preAnsSize, D.honestPreimage_length t]⟩

/-- **⚑ THE PRICE, PROVED — `WidePreimageFloor D (IsPolyTime …)` IS FALSE.** The constant finder that
HARDCODES the honest preimage of the (fixed, published) commitment is `IsPolyTime` (answer size `11`) and
wins with probability `1`, so the preimage floor at the `IsPolyTime` class is refuted — exactly the
`KeyedRomFloor.sysRoots_floor_polyTime_false_babyBear` disease (`idAdv` prices answer SIZE, never search
difficulty). Hence `span_recovery_hard_from_polyTime` is VACUOUS at the deployed hash. The non-vacuous
floor samples the challenge AFTER the adversary (the KEYED / QUERY-COUNTED class), which this abstract
`IsPolyTime` model cannot express — the named residual. -/
theorem widePreimageFloor_polyTime_false : ¬ D.WidePreimageFloor (IsPolyTime (D.preAnsSize)) := by
  intro hFloor
  have hmem := D.widePreimageFloor_polyTime_inhabited
  have hnegl := hFloor _ hmem
  have hone : gameAdv (D.widePreimageGame)
      (idAdv (G := D.widePreimageGame) (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ t => D.honestPreimage t)).toAdversary = fun _ => (1 : ℝ) := by
    funext l
    have hhit : (idAdv (G := D.widePreimageGame) (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
        (fun _ t => D.honestPreimage t)).toAdversary.hit l = fun _ => true := by
      funext t
      rw [Adversary.hit_eq_true]
      show D.wideHashAt t
          ((idAdv (G := D.widePreimageGame) (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
            (fun _ t => D.honestPreimage t)).toAdversary.run l t) = D.holeCommitAt t
      have hrun : (idAdv (G := D.widePreimageGame) (O := Unit) (Q := fun _ => Unit) (R := fun _ => Unit)
          (fun _ t => D.honestPreimage t)).toAdversary.run l t = D.honestPreimage t := rfl
      rw [hrun]
      exact D.wideHashAt_honestPreimage t
    show @winProb D.Tag (D.tagFintype) _ = 1
    rw [hhit]
    exact @winProb_top D.Tag (D.tagFintype) (D.tagNonempty)
  rw [hone] at hnegl
  exact not_negl_one hnegl

/-- **(CANARY — the span bound does NOT follow from the floor applied at an UNRELATED finder.)** Only the
extractor connects the two games; if this stops failing, the reduction has degenerated into a `P → P`
that the floor's own game would satisfy directly. -/
example (Eff : Adversary (D.widePreimageGame) → Prop) (A : Adversary (D.spanRecoverGame))
    (B : Adversary (D.widePreimageGame)) (hB : Eff B) (hFloor : D.WidePreimageFloor Eff) : True := by
  fail_if_success
    (have : Negl (gameAdv (D.spanRecoverGame) A) := hFloor B hB)
  trivial

end BlindedSpanCommitment

/-! ## §4 — (a) THE UNCONDITIONAL STATISTICAL HALF: perfect blinding ⟹ witness-independence. -/

namespace PerfectBlinding

open Metatheory.Open.PerfectZK

/-- **THE PERFECT-BLINDING IDEALIZATION as a `PerfectZK`.** The information-theoretic ideal a uniform
`BLINDING` targets: the verifier's view of the blinded commitment is a WITNESS-FREE simulation of the
public `C_T` alone — `view ct span = sim ct`, independent of the span. `S = ℤ` (the public `C_T`),
`W = List ℤ` (the hidden span digest), `V = List ℤ` (the view). `simView ct` is the simulator's output.

⚠ This is the PERFECT/STATISTICAL ideal (the marginal of a uniform-blinded commitment is span-free); the
DEPLOYED fixed sponge does NOT satisfy it — its hiding is the computational `§2/§3` half. `simView` is a
parameter so the law's CONTENT is the teeth (`leaky_span_indep_FAILS`), exactly as `PerfectZK.otp` vs
`leakyView`. -/
def spanBlindZK (simView : ℤ → List ℤ) : PerfectZK where
  S := ℤ
  W := List ℤ
  V := List ℤ
  view ct _span := simView ct
  sim ct := simView ct
  hperf _ _ := rfl

/-- **`spanBlind_view_indep` — WITNESS-INDEPENDENCE, UNCONDITIONAL, kernel-clean.** For a perfectly-blinded
commitment, any two spans yield the SAME view: the verifier extracts ZERO information about which span was
committed. `PerfectZK.view_indep_of_witness` on the blinded-span instance. -/
theorem spanBlind_view_indep (simView : ℤ → List ℤ) (ct : ℤ) (span₁ span₂ : List ℤ) :
    (spanBlindZK simView).view ct span₁ = (spanBlindZK simView).view ct span₂ :=
  (spanBlindZK simView).view_indep_of_witness ct span₁ span₂

/-- **`spanBlind_unlinkable` — UNLINKABILITY, UNCONDITIONAL.** Two anonymous shows over the same public
`C_T` committing DIFFERENT spans produce the SAME view — the verifier cannot link them to a span. The
information-theoretic form of the unlinkability the emit file states in prose. -/
theorem spanBlind_unlinkable (simView : ℤ → List ℤ) (ct : ℤ) (span₁ span₂ : List ℤ) :
    (spanBlindZK simView).view ct span₁ = (spanBlindZK simView).view ct span₂ :=
  spanBlind_view_indep simView ct span₁ span₂

/-- **The view factors through the public statement alone** — the strongest information-theoretic form:
there is a witness-free `g` (the simulator) with `view ct span = g ct` for every span. -/
theorem spanBlind_factors (simView : ℤ → List ℤ) :
    ∃ g : ℤ → List ℤ, ∀ (ct : ℤ) (span : List ℤ), (spanBlindZK simView).view ct span = g ct :=
  (spanBlindZK simView).view_factors_through_statement

/-- **A LEAKY (UN-BLINDED) view — the law FAILS (the teeth).** Without blinding the view IS the span
verbatim, and `view_indep_of_witness` is FALSE: two distinct spans give distinct views. So perfect
blinding is a GENUINE constraint, not a vacuous `True` — no simulator can perfect-hide the un-blinded
commitment. -/
def leakySpanView (_ : ℤ) (span : List ℤ) : List ℤ := span

theorem leaky_span_indep_FAILS :
    ¬ (∀ (ct : ℤ) (span₁ span₂ : List ℤ), leakySpanView ct span₁ = leakySpanView ct span₂) := by
  intro h
  exact absurd (h 0 [0] [1]) (by decide)

/-- **No simulator can perfect-hide the un-blinded commitment** — the sharpest tooth: there is NO
witness-free `sim` for which the leaky view equals a simulation. So one cannot package `leakySpanView` as
a `spanBlindZK`. -/
theorem leaky_no_simulator :
    ¬ ∃ sim : ℤ → List ℤ, ∀ (ct : ℤ) (span : List ℤ), leakySpanView ct span = sim ct := by
  rintro ⟨sim, h⟩
  have : leakySpanView 0 [0] = leakySpanView 0 [1] := (h 0 [0]).trans (h 0 [1]).symm
  exact absurd this (by decide)

end PerfectBlinding

/-! ## §5 — shape pins + axiom hygiene (every load-bearing arm). -/

open BlindedSpanCommitment

-- The assembled preimage is the task's `[span_digest8, C_T, BLINDING, 0]` — 11 felts for an 8-felt span.
example (D : BlindedSpanCommitment) (t : D.Tag) : (D.honestPreimage t).length = 11 :=
  D.honestPreimage_length t

#assert_axioms BlindedSpanCommitment.recover_wins_imp
#assert_axioms BlindedSpanCommitment.recover_adv_le
#assert_axioms BlindedSpanCommitment.span_recovery_hard_from_preimage_floor
#assert_axioms BlindedSpanCommitment.spanRecover_top_false
#assert_axioms BlindedSpanCommitment.widePreimage_top_false
#assert_axioms BlindedSpanCommitment.widePreimage_bot_vacuous
#assert_axioms BlindedSpanCommitment.widePreimageFloor_polyTime_inhabited
#assert_axioms BlindedSpanCommitment.widePreimageFloor_polyTime_false
#assert_axioms PerfectBlinding.spanBlind_view_indep
#assert_axioms PerfectBlinding.spanBlind_unlinkable
#assert_axioms PerfectBlinding.spanBlind_factors
#assert_axioms PerfectBlinding.leaky_span_indep_FAILS
#assert_axioms PerfectBlinding.leaky_no_simulator

end Metatheory.Open.BlindedSpanHiding

/-
# `Dregg2.Crypto.RomMerkleOpening` — the MERKLE-PATH OPENING as a keyed-ROM object, its
walking extractor PAYING its own queries, and the binding from the PROVED floor.

## What this re-grounds

The deployed Merkle opening (`OodCommitmentBinding.merkleRecomputeZ`, `FriVerifier.merkleRecompute`,
`FriCompressRegrounded.merkleRecompute`) recomputes an opened leaf up a sibling path — one node hash
per level, the index bit fixing the order — and compares the result to a committed root. Its binding
used to be discharged at `Eff := CostAdversary.IsPolyTime` over the FIXED-hash game
(`FloorRegroundedConsumers.oodCommitmentOpening_advantage_bound` and its siblings), and that floor is
**FALSE at deployed parameters** (`Exec.SystemRootsBindingReduction.sysRoots_floor_polyTime_false_babyBear`):
`IsPolyTime` prices answer SIZE, so a `Classical.choice` `.pure`-leaf answering a short collision is
in the class and wins with probability `1`. Nor can a better `Eff` repair the fixed-hash game
(`RomBindingReduction` header): the floor must move to a SAMPLED oracle, where the birthday bound is
a THEOREM (`KeyedRomFloor.keyedRom_hard`).

## Why neither `RomCarrier` nor `RomChainedCarrier` covers this shape

  * `RomBindingReduction.RomCarrier` is ONE query per commitment (`H (encode c v)`); a path recompute
    is a CHAIN of queries, so `mapOut` cannot extract the interior collision.
  * `RomChainedReduction.RomChainedCarrier` chains over the PAYLOAD's blocks after a HEAD QUERY
    (`chainEval … (H (encHd c v.1)) (blocks v)`), and its win compares two payloads over ONE block
    schedule owned by the payload. The Merkle opening is the TRANSPOSE: the chain's starting
    accumulator IS the payload (the opened leaf, never pre-hashed), and the block schedule (index
    bits + siblings) is CONTEXT the two claims SHARE. Its extractor therefore needs only
    LEFT-injectivity of the step encoding (same block on both sides), not pair-injectivity — which
    is exactly why `chainCollComp` cannot be reused: its correctness consumes pair-injectivity that
    the ordered node encoding `(acc, s)`/`(s, acc)` does not have.

This file supplies the missing object once: the same-context chain walk (`walkComp`), its
unconditional correctness (`walkComp_eval_collides`), the opening forgery as a
`RomCarrierSites.RomForgery` over the node-pair family, and the binding `merkleOpenRom_binds` from
`keyedRom_hard` — no cost model, no false hypothesis, the extractor's `2·depth` queries PAID in the
same currency the floor counts.

## ⚑ The modelling step every consumer inherits (say it, do not smuggle it)

Landing a deployed Merkle site here idealises the fixed Poseidon2 node hash as a keyed RANDOM ORACLE
`H : Key × (digest × digest) → Fin (2 ^ l)` at an ASYMPTOTIC digest width (`RomCarrierSites` header,
`DomainSeparatedCREffRegrounded` §5's rule): there is NO `l` at which `Fin (2 ^ l)` is the deployed
~31-bit BabyBear felt, and at the deployed width the honest reading stays "binds exactly as well as
~31 bits allow" (birthday ≈ `2^15.5`, the felt-width wound). What the move buys over the deleted
`IsPolyTime` discharge: the floor under the reduction is a THEOREM about the model instead of a
hypothesis that is FALSE at the deployed object.

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.RomCarrierSites
import Dregg2.Crypto.RomChainedReduction
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomMerkleOpening

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (romCollisionGame RomEff)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame keyedRom_hard)
open Dregg2.Crypto.RomCarrierSites
open Dregg2.Crypto.RomChainedReduction (chainEval chainEval_const)

set_option autoImplicit false

/-! ## §0 — the ordered node message, and its LEFT-injectivity (a layout fact). -/

/-- **THE ORDERED NODE MESSAGE at one path level.** The index bit fixes the side: `false` ⇒ the
accumulator on the left (`(acc, s)`, the even-index case of the deployed `nodeStep`/`nodeAt`),
`true` ⇒ on the right. This is the two-child node preimage the deployed Merkle verifier absorbs,
as a PAIR — the ROM restatement of `[acc, s]`/`[s, acc]`. -/
def nodeMsg {R : Type} (bit : Bool) (acc s : R) : R × R :=
  if bit then (s, acc) else (acc, s)

/-- **LEFT-INJECTIVITY** — at ONE level (one bit, one sibling), distinct accumulators give distinct
node messages. A layout fact (the accumulator occupies a fixed coordinate), never a hash claim; the
transpose of the deployed `nodeStep_ne`/`nodeAt_ne`. -/
theorem nodeMsg_left_inj {R : Type} (bit : Bool) (s : R) {a b : R}
    (h : nodeMsg bit a s = nodeMsg bit b s) : a = b := by
  cases bit
  · simpa [nodeMsg] using congrArg Prod.fst h
  · simpa [nodeMsg] using congrArg Prod.snd h

/-- The ROM node message carries the SAME ordered limbs as the deployed `nodeStep`'s list, at the
bit `idx % 2 ≠ 0` — the faithfulness pin a site's `merkleRecomputeZ` bridge reads off. -/
theorem nodeMsg_matches_index_bit {R : Type} (idx : ℕ) (acc s : R) :
    nodeMsg (decide (idx % 2 ≠ 0)) acc s = if idx % 2 = 0 then (acc, s) else (s, acc) := by
  by_cases hb : idx % 2 = 0 <;> simp [nodeMsg, hb]

/-! ## §1 — the node-pair keyed ROM family. -/

/-- **THE MERKLE NODE FAMILY** — keyed by the site's own domain-separation tag space, over the
two-child node-pair message shape, with the ideal `λ`-bit digest (the §-header modelling step). -/
def merkleRomFamily (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key) :
    KeyedRomFamily :=
  flatFamily Key kF kD kN (fun l => Fin (2 ^ l) × Fin (2 ^ l))
    (fun _ => inferInstance) (fun _ => inferInstance)
    (fun l => ⟨(⟨0, by positivity⟩, ⟨0, by positivity⟩)⟩)

/-- The floor's width obligation, closed by construction. -/
theorem merkleRomFamily_card_R (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (l : ℕ) :
    letI := (merkleRomFamily Key kF kD kN).rFin l
    Fintype.card ((merkleRomFamily Key kF kD kN).R l) = 2 ^ l :=
  flatFamily_card_R Key kF kD kN _ _ _ _ l

/-- **ONE LEVEL'S QUERY POINT**: the tag and the ordered node pair. -/
def stepEnc (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (l : ℕ) (t : Key) :
    Fin (2 ^ l) → (Bool × Fin (2 ^ l)) → (merkleRomFamily Key kF kD kN).toRomFamily.D l :=
  fun acc b => (t, nodeMsg b.1 acc b.2)

/-- The step encoding is LEFT-injective per level — `nodeMsg_left_inj` under the fixed tag. -/
theorem stepEnc_left_inj (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (l : ℕ) (t : Key) (b : Bool × Fin (2 ^ l)) {a c : Fin (2 ^ l)}
    (h : stepEnc Key kF kD kN l t a b = stepEnc Key kF kD kN l t c b) : a = c :=
  nodeMsg_left_inj b.1 b.2 (congrArg Prod.snd h)

/-! ## §2 — the opening forgery: two leaves, ONE shared path, one recomputed root. -/

/-- **THE MERKLE-OPENING FORGERY.** The adversary outputs a context — a tag and a `d l`-level path
of `(index bit, sibling)` pairs — and TWO leaves; it WINS iff the leaves are DISTINCT yet recompute
to the SAME root along the SHARED path, against the SAMPLED oracle. This is
`FloorRegroundedConsumers.merkleOpenBreakGame`'s win relation, transposed to the oracle model: the
recompute is `chainEval` — one oracle query per level, the previous digest threaded forward. The
depth is pinned per parameter (`d`), as deployed: a committed tree has a fixed height. -/
def merkleOpenForgery (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (d : ℕ → ℕ) : RomForgery (merkleRomFamily Key kF kD kN) where
  Ans := fun l => (Key × (Fin (d l) → Bool × Fin (2 ^ l))) × Fin (2 ^ l) × Fin (2 ^ l)
  wins := fun l H p =>
    p.2.1 ≠ p.2.2 ∧
      chainEval H (stepEnc Key kF kD kN l p.1.1) p.2.1 (List.ofFn p.1.2)
        = chainEval H (stepEnc Key kF kD kN l p.1.1) p.2.2 (List.ofFn p.1.2)
  winsDec := fun l _ _ => by
    letI := ((merkleRomFamily Key kF kD kN).toRomFamily).rDec l
    exact instDecidableAnd

/-- The opening forgery game — the deployed equivocation, at the sampled oracle. -/
abbrev merkleOpenRomGame (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (d : ℕ → ℕ) : Game :=
  (merkleOpenForgery Key kF kD kN d).game

/-! ## §3 — the SAME-CONTEXT chain walk: the extractor, paying two queries per level.

Two chains that share their block schedule but start at DISTINCT accumulators and end EQUAL must
merge at some interior level — and the merge point is a genuine collision of the sampled oracle.
Which level that is depends on the oracle's answers, so the extractor re-walks both chains, two
queries per level. Left-injectivity of the step encoding keeps the two query points distinct for as
long as the accumulators are. -/

/-- **THE WALK, AS AN ORACLE PROGRAM.** Descend the shared blocks with both accumulators; at each
level query both node points; the first level whose points differ (they do, while the accumulators
do) but whose answers AGREE is the collision — return it. `dflt` is returned only past the end of
the path, which the spec's hypotheses exclude. -/
def walkComp {D R Blk : Type} [DecidableEq D] [DecidableEq R]
    (enc : R → Blk → D) (dflt : D × D) :
    R → R → List Blk → OracleComp D R (D × D)
  | _, _, [] => .pure dflt
  | a, b, s :: rest =>
      .query (enc a s) (fun r =>
        .query (enc b s) (fun r' =>
          if enc a s ≠ enc b s ∧ r = r' then .pure (enc a s, enc b s)
          else walkComp enc dflt r r' rest))

/-- **THE WALK PAYS TWO QUERIES PER LEVEL** — `2 · |bs|`, along every path. -/
theorem walkComp_queryBounded {D R Blk : Type} [DecidableEq D] [DecidableEq R]
    (enc : R → Blk → D) (dflt : D × D) :
    ∀ (bs : List Blk) (a b : R), QueryBounded (2 * bs.length) (walkComp enc dflt a b bs) := by
  intro bs
  induction bs with
  | nil => intro a b; exact QueryBounded.pure _ _
  | cons s rest ih =>
      intro a b
      have h2 : 2 * (s :: rest).length = 2 * rest.length + 1 + 1 := by
        simp [List.length_cons]; ring
      rw [h2]
      refine QueryBounded.query _ _ _ (fun r => ?_)
      refine QueryBounded.query _ _ _ (fun r' => ?_)
      split
      · exact QueryBounded.pure _ _
      · exact ih r r'

/-- **⚑ THE WALK IS CORRECT, UNCONDITIONALLY.** Two DISTINCT accumulators whose folds over ONE
shared block schedule agree yield a genuine collision of the oracle: two distinct query points with
equal answers. The only structural input is LEFT-injectivity of the step encoding — the layout fact
`nodeMsg_left_inj` supplies. At an empty schedule the equal folds ARE the accumulators, refuting
their distinctness, so that branch is closed by contradiction. -/
theorem walkComp_eval_collides {D R Blk : Type} [DecidableEq D] [DecidableEq R]
    (enc : R → Blk → D)
    (hinj : ∀ (s : Blk) (a b : R), enc a s = enc b s → a = b)
    (H : D → R) (dflt : D × D) :
    ∀ (bs : List Blk) (a b : R), a ≠ b →
      chainEval H enc a bs = chainEval H enc b bs →
      ((walkComp enc dflt a b bs).eval H).1 ≠ ((walkComp enc dflt a b bs).eval H).2
        ∧ H ((walkComp enc dflt a b bs).eval H).1 = H ((walkComp enc dflt a b bs).eval H).2 := by
  intro bs
  induction bs with
  | nil =>
      intro a b hne heq
      exact absurd heq hne
  | cons s rest ih =>
      intro a b hne heq
      have hred : (walkComp enc dflt a b (s :: rest)).eval H
          = (if enc a s ≠ enc b s ∧ H (enc a s) = H (enc b s)
              then OracleComp.pure (enc a s, enc b s)
              else walkComp enc dflt (H (enc a s)) (H (enc b s)) rest).eval H := rfl
      rw [hred]
      have hene : enc a s ≠ enc b s := fun hc => hne (hinj s a b hc)
      have heq' : chainEval H enc (H (enc a s)) rest = chainEval H enc (H (enc b s)) rest := heq
      by_cases hcoll : H (enc a s) = H (enc b s)
      · rw [if_pos ⟨hene, hcoll⟩]
        exact ⟨hene, hcoll⟩
      · rw [if_neg (fun hc => hcoll hc.2)]
        exact ih (H (enc a s)) (H (enc b s)) hcoll heq'

/-! ## §4 — the extractor as a map of adversaries, its budget PAID, and the binding. -/

/-- **THE EXTRACTOR PROGRAM on one forgery answer** — walk the claimed path with the two claimed
leaves. Total; the default is a degenerate self-pair (never returned on a winning forgery). -/
def openExtract (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (d : ℕ → ℕ) (l : ℕ) (p : (merkleOpenForgery Key kF kD kN d).Ans l) :
    OracleComp ((merkleRomFamily Key kF kD kN).toRomFamily.D l)
      ((merkleRomFamily Key kF kD kN).toRomFamily.R l)
      ((merkleRomFamily Key kF kD kN).toRomFamily.D l
        × (merkleRomFamily Key kF kD kN).toRomFamily.D l) :=
  letI := ((merkleRomFamily Key kF kD kN).toRomFamily).dDec l
  letI := ((merkleRomFamily Key kF kD kN).toRomFamily).rDec l
  walkComp (stepEnc Key kF kD kN l p.1.1)
    ((p.1.1, (p.2.1, p.2.2)), (p.1.1, (p.2.1, p.2.2)))
    p.2.1 p.2.2 (List.ofFn p.1.2)

/-- The extractor's budget is `2 · d l` — two queries per level of the pinned depth, exactly. -/
theorem openExtract_queryBounded (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (l : ℕ) (p : (merkleOpenForgery Key kF kD kN d).Ans l) :
    QueryBounded (2 * d l) (openExtract Key kF kD kN d l p) := by
  letI := ((merkleRomFamily Key kF kD kN).toRomFamily).dDec l
  letI := ((merkleRomFamily Key kF kD kN).toRomFamily).rDec l
  have h := walkComp_queryBounded (stepEnc Key kF kD kN l p.1.1)
    ((p.1.1, (p.2.1, p.2.2)), (p.1.1, (p.2.1, p.2.2))) (List.ofFn p.1.2) p.2.1 p.2.2
  rwa [List.length_ofFn] at h

/-- **THE EXTRACTOR, AS A MAP OF ADVERSARIES.** Run the forger, then re-walk its claimed opening
against the SAME sampled oracle. -/
def merkleOpenFinder (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (d : ℕ → ℕ) (A : Adversary (merkleOpenRomGame Key kF kD kN d)) :
    Adversary (keyedRomGame (merkleRomFamily Key kF kD kN)) where
  run := fun l H => (openExtract Key kF kD kN d l (A.run l H)).eval H

/-- **⚑ WIN-PRESERVATION.** Every oracle on which the opening forger wins, the extracted finder
wins the keyed collision game — the walk's correctness at the game level. -/
theorem merkleOpen_wins_imp (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (A : Adversary (merkleOpenRomGame Key kF kD kN d))
    (l : ℕ) (H : (merkleOpenRomGame Key kF kD kN d).Inst l)
    (hwin : (merkleOpenRomGame Key kF kD kN d).wins l H (A.run l H)) :
    (keyedRomGame (merkleRomFamily Key kF kD kN)).wins l H
      ((merkleOpenFinder Key kF kD kN d A).run l H) := by
  letI := ((merkleRomFamily Key kF kD kN).toRomFamily).dDec l
  letI := ((merkleRomFamily Key kF kD kN).toRomFamily).rDec l
  obtain ⟨hne, heq⟩ := hwin
  exact walkComp_eval_collides (stepEnc Key kF kD kN l (A.run l H).1.1)
    (fun s a b h => stepEnc_left_inj Key kF kD kN l (A.run l H).1.1 s h) H
    (((A.run l H).1.1, ((A.run l H).2.1, (A.run l H).2.2)),
      ((A.run l H).1.1, ((A.run l H).2.1, (A.run l H).2.2)))
    (List.ofFn (A.run l H).1.2) (A.run l H).2.1 (A.run l H).2.2 hne heq

/-- **THE ADVANTAGE INEQUALITY — UNCONDITIONAL, over ALL adversaries.** The opening forger's
advantage is at most the extracted finder's, at every parameter; the class enters only at the
floor. -/
theorem merkleOpen_adv_le (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (A : Adversary (merkleOpenRomGame Key kF kD kN d)) (l : ℕ) :
    gameAdv (merkleOpenRomGame Key kF kD kN d) A l
      ≤ gameAdv (keyedRomGame (merkleRomFamily Key kF kD kN))
          (merkleOpenFinder Key kF kD kN d A) l := by
  refine @winProb_le_of_imp _ ((merkleOpenRomGame Key kF kD kN d).instFin l) _ _ (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  exact (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr (merkleOpen_wins_imp Key kF kD kN d A l H hH)

/-- **⚑ THE EXTRACTED FINDER IS QUERY-BOUNDED, WITH THE WALK'S QUERIES PAID.** A `Q`-query opening
forger yields a `(Q + 2·d)`-query collision finder — the forger's own tree (`bindComp`) plus the
walk's re-descent, counted in the SAME currency the floor quantifies over. -/
theorem merkleOpenFinder_in_romEff (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (Q : ℕ → ℕ)
    (A : Adversary (merkleOpenRomGame Key kF kD kN d))
    (hA : RomForgeryEff (merkleRomFamily Key kF kD kN) (merkleOpenForgery Key kF kD kN d) Q A) :
    RomEff (merkleRomFamily Key kF kD kN).toRomFamily (fun l => Q l + 2 * d l)
      (merkleOpenFinder Key kF kD kN d A) := by
  obtain ⟨M, hMQ, hrun⟩ := hA
  refine ⟨fun l => OracleComp.bindComp (M l) (openExtract Key kF kD kN d l),
    fun l => ?_, fun l H => ?_⟩
  · exact OracleComp.bindComp_queryBounded (hMQ l)
      (fun p => openExtract_queryBounded Key kF kD kN d l p)
  · show (openExtract Key kF kD kN d l (A.run l H)).eval H
      = (OracleComp.bindComp (M l) (openExtract Key kF kD kN d l)).eval H
    exact (congrArg (fun p => (openExtract Key kF kD kN d l p).eval H) (hrun l H)).trans
      (OracleComp.bindComp_eval (M l) (openExtract Key kF kD kN d l) H).symm

/-- **⚑⚑ THE MERKLE-OPENING BINDING — from the KEYED, QUERY-COUNTED floor, WHICH IS PROVED.**

A query-bounded opening forger has NEGLIGIBLE advantage: at the `λ`-bit ideal digest and a
polynomial total budget `Q'` dominating the forger's queries plus the walk's `2·d` re-descent, the
recomputed Merkle root binds the opened leaf except with negligible probability. The floor is
`keyedRom_hard` — the birthday bound, a THEOREM — and NOTHING refutable is carried: this is what
replaces every `IsPolyTime`-discharged `merkleOpen`/`oodCommitmentOpening` bound, whose floor
`sysRoots_floor_polyTime_false_babyBear` refutes. -/
theorem merkleOpenRom_binds (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (merkleOpenRomGame Key kF kD kN d))
    (hA : RomForgeryEff (merkleRomFamily Key kF kD kN) (merkleOpenForgery Key kF kD kN d) Q A) :
    Negl (gameAdv (merkleOpenRomGame Key kF kD kN d) A) := by
  have hfind : RomEff (merkleRomFamily Key kF kD kN).toRomFamily Q'
      (merkleOpenFinder Key kF kD kN d A) := by
    obtain ⟨M', hM'Q, hrun⟩ := merkleOpenFinder_in_romEff Key kF kD kN d Q A hA
    exact ⟨M', fun l => (hM'Q l).mono (hle l), hrun⟩
  exact negl_of_le (fun l => (gameAdv_mem_unit (merkleOpenRomGame Key kF kD kN d) A l).1)
    (merkleOpen_adv_le Key kF kD kN d A)
    (keyedRom_hard (merkleRomFamily Key kF kD kN) Q' hQ'
      (merkleRomFamily_card_R Key kF kD kN) (merkleOpenFinder Key kF kD kN d A) hfind)

/-! ## §5 — the counterexample dies at this layer, and the object is not vacuous. -/

/-- **⚑ A NON-NEGLIGIBLE OPENING FORGER IS OUTSIDE THE CLASS.** The `shortCollAdv` analogue at the
opening layer: were it inside, `merkleOpenRom_binds` would collapse its advantage. The strategy
that refutes the `IsPolyTime` floor cannot produce a member of this one. -/
theorem merkleOpenRom_nonNegl_forger_excluded (Key : Type) (kF : Fintype Key)
    (kD : DecidableEq Key) (kN : Nonempty Key) (d : ℕ → ℕ) (Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (merkleOpenRomGame Key kF kD kN d))
    (hnn : ¬ Negl (gameAdv (merkleOpenRomGame Key kF kD kN d) A)) :
    ¬ RomForgeryEff (merkleRomFamily Key kF kD kN) (merkleOpenForgery Key kF kD kN d) Q A :=
  fun hA => hnn (merkleOpenRom_binds Key kF kD kN d Q Q' hle hQ' A hA)

/-- **THE CONSTANT ANSWERER** — the `0`-query program returning a fixed context and two fixed
leaves: the transplant of the exact shape that refutes the `IsPolyTime` floor. Admitted by the
class; §5 shows why that is fine. -/
def constOpenComp (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (d : ℕ → ℕ) (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l)))
    (v w : ∀ l, Fin (2 ^ l)) :
    ∀ l, OracleComp ((merkleRomFamily Key kF kD kN).toRomFamily.D l)
      ((merkleRomFamily Key kF kD kN).toRomFamily.R l)
      ((merkleOpenForgery Key kF kD kN d).Ans l) :=
  fun l => OracleComp.pure (c l, v l, w l)

/-- The induced adversary: run the constant tree against the oracle. -/
def constOpenAdv (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (d : ℕ → ℕ) (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l)))
    (v w : ∀ l, Fin (2 ^ l)) : Adversary (merkleOpenRomGame Key kF kD kN d) where
  run := fun l H => (constOpenComp Key kF kD kN d c v w l).eval H

/-- **(TOOTH — the class is INHABITED at every budget.)** The constant answerer is a `0`-query
tree. -/
theorem constOpenAdv_in_eff (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l)))
    (v w : ∀ l, Fin (2 ^ l)) (Q : ℕ → ℕ) :
    RomForgeryEff (merkleRomFamily Key kF kD kN) (merkleOpenForgery Key kF kD kN d) Q
      (constOpenAdv Key kF kD kN d c v w) :=
  ⟨constOpenComp Key kF kD kN d c v w, fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩

/-- A nonempty fold at a CONSTANT oracle forgets its starting accumulator: after the first level
the accumulator is the constant, and `chainEval_const` keeps it there. -/
theorem chainEval_const_of_ne_nil {D R Blk : Type} (enc : R → Blk → D) (r₀ : R) :
    ∀ {bs : List Blk}, bs ≠ [] → ∀ a : R, chainEval (fun _ => r₀) enc a bs = r₀ := by
  intro bs hbs a
  cases bs with
  | nil => exact absurd rfl hbs
  | cons s rest =>
      show chainEval (fun _ => r₀) enc r₀ rest = r₀
      exact chainEval_const enc r₀ rest

/-- **(TOOTH — the game is genuinely WINNABLE: the constant answerer wins at the constant
oracle.)** At positive depth the fold forgets its leaf, so ANY two distinct leaves equivocate
there; the advantage the binding bounds is positive, not the advantage of an unwinnable game.
Distinct leaves exist at every `l ≥ 1` (`Fin (2 ^ l)` has two elements). -/
theorem constOpenAdv_gameAdv_pos (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l)))
    (v w : ∀ l, Fin (2 ^ l)) (l : ℕ) (hd : 1 ≤ d l) (hvw : v l ≠ w l) :
    0 < gameAdv (merkleOpenRomGame Key kF kD kN d) (constOpenAdv Key kF kD kN d c v w) l := by
  letI := ((merkleRomFamily Key kF kD kN).toRomFamily).rNe l
  obtain ⟨r₀⟩ := ((merkleRomFamily Key kF kD kN).toRomFamily).rNe l
  refine @winProb_pos_of_witness _ ((merkleOpenRomGame Key kF kD kN d).instFin l) _
    (fun _ => r₀) ?_
  refine ((constOpenAdv Key kF kD kN d c v w).hit_eq_true l _).mpr ?_
  show (merkleOpenRomGame Key kF kD kN d).wins l (fun _ => r₀) (c l, v l, w l)
  refine ⟨hvw, ?_⟩
  have hne : (List.ofFn (c l).2) ≠ ([] : List (Bool × Fin (2 ^ l))) := by
    intro hc
    have hlen := congrArg List.length hc
    rw [List.length_ofFn] at hlen
    simp at hlen
    omega
  exact (chainEval_const_of_ne_nil _ r₀ hne (v l)).trans
    (chainEval_const_of_ne_nil _ r₀ hne (w l)).symm

/-- **(TOOTH — the admitted refuter-shape is DEFANGED, not excluded.)** The constant answerer is in
the class and the binding applies to it: positive advantage where the game is winnable, NEGLIGIBLE
advantage overall — where against the FIXED public hash the same shape wins with probability `1`.
Sampling the oracle after the adversary is fixed is what does the work. -/
theorem constOpenAdv_negl (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key)
    (kN : Nonempty Key) (d : ℕ → ℕ) (Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l))) (v w : ∀ l, Fin (2 ^ l)) :
    Negl (gameAdv (merkleOpenRomGame Key kF kD kN d) (constOpenAdv Key kF kD kN d c v w)) :=
  merkleOpenRom_binds Key kF kD kN d Q Q' hle hQ' _
    (constOpenAdv_in_eff Key kF kD kN d c v w Q)

/-- **(CANARY — the bound does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: `keyedRom_hard` at an arbitrary member `B` bounds a DIFFERENT ensemble; only
`merkleOpen_adv_le` at the EXTRACTED finder connects the opening game to the floor. Reds if a
future edit disconnects them. -/
example (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (d Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (merkleOpenRomGame Key kF kD kN d))
    (B : Adversary (keyedRomGame (merkleRomFamily Key kF kD kN)))
    (hB : Dregg2.Crypto.KeyedRomFloor.KeyedRomEff (merkleRomFamily Key kF kD kN) Q B) : True := by
  fail_if_success
    (have : Negl (gameAdv (merkleOpenRomGame Key kF kD kN d) A) :=
      keyedRom_hard (merkleRomFamily Key kF kD kN) Q hQ
        (merkleRomFamily_card_R Key kF kD kN) B hB)
  trivial

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  nodeMsg_left_inj,
  nodeMsg_matches_index_bit,
  merkleRomFamily_card_R,
  stepEnc_left_inj,
  walkComp_queryBounded,
  walkComp_eval_collides,
  openExtract_queryBounded,
  merkleOpen_wins_imp,
  merkleOpen_adv_le,
  merkleOpenFinder_in_romEff,
  merkleOpenRom_binds,
  merkleOpenRom_nonNegl_forger_excluded,
  constOpenAdv_in_eff,
  chainEval_const_of_ne_nil,
  constOpenAdv_gameAdv_pos,
  constOpenAdv_negl
]

end Dregg2.Crypto.RomMerkleOpening

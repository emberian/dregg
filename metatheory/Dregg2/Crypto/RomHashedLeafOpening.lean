/-
# `Dregg2.Crypto.RomHashedLeafOpening` — the HASHED-LEAF Merkle opening as a keyed-ROM object:
one family for a whole deployed tree (leaf blocks ⊕ node pairs), its single-absorb carriers, the
pure-path walk, and the LEAF-LEVEL opening whose extractor pays two leaf queries plus the walk.

## What this re-grounds

The deployed native-8-felt trees (`Circuit.DeployedCapTree`, `Circuit.DeployedHeapTree`,
`Circuit.DeployedFieldsTree`) each ride ONE chip (`descriptor_ir2::chip_absorb_all_lanes`) in two
arities: a short LEAF block (7 cap fields / 3 IMT limbs) and the arity-16 `node8` pack of two 8-felt
children, and their binding surface is currently exported as `…_binds_or_collides` DISJUNCTIONS —
"bind, or here is the colliding pair". At deployed parameters a collision EXISTS by pigeonhole, so a
bare disjunction is satisfiable through its right branch without any binding; the disjunction is an
extractor witness, not a security statement. The security statement lives HERE: the forger is an
ORACLE PROGRAM over a SAMPLED tag-separated oracle, fixed before the oracle is drawn, and every
export closes from `KeyedRomFloor.keyedRom_hard` — the birthday bound, a THEOREM, with no refuted
floor and no cost model.

## The one family, and why the shapes live together

`hlFam` domain-separates the two deployed absorbs by constructor inside ONE message space:

  * `Sum.inl (b : Leaf l)` — the truncated leaf block (the site's `leafFields` image);
  * `Sum.inr (x, y)`       — the ordered two-child node pair, at the IDEAL digest width.

One family means the leaf carrier, the node carrier, the pure-path walk and the hashed-leaf opening
all play over the SAME sampled oracle, so the opening's union-free case split (leaf digests collide /
they differ and the path walk lands on an interior node collision) is a single-game reduction.

## The four exported shapes (per deployed tree, instantiated per site)

  1. `hlLeaf_binds_rom` — the leaf digest binds its whole block (`flatSite_binds` at `hlLeafCarrier`);
  2. `hlNode_binds_rom` — the node digest binds BOTH ordered children (`flatSite_binds` at
     `hlNodeCarrier`) — the `nodeOf8`/`pack8` layout content at the ideal width;
  3. `hlPathRom_binds` — the `recomposeUp8` shape: two DISTINCT starting digests folding one SHARED
     `(bit, sibling)` schedule to one root cost an interior node collision, found by the re-walking
     extractor (`walkComp`, `2·depth` queries PAID);
  4. `hlOpenRom_binds` (+ the published-root form `hlOpenRootRom_binds`) — the `capOpen8`/GENTIAN
     shape: two DISTINCT leaves whose HASHED digests fold up one shared path to one root. The
     extractor queries both leaf points (2 queries); equal answers ARE the leaf-block collision,
     distinct answers hand the walk two distinct accumulators.

## ⚑ The modelling step every consumer inherits (say it, do not smuggle it)

Landing a deployed tree here idealises the fixed 8-output Poseidon2 chip as a keyed random oracle
into `Fin (2 ^ l)` (`RomCarrierSites` header discipline): an 8-felt child digest is ONE sampled
ideal value, the ordered pair `(x, y)` carries exactly the layout content `pack8` carries (order
preserved, both children bound), and there is NO `l` at which `Fin (2 ^ l)` is the deployed 8×~31-bit
digest. What this buys over the disjunction: a floor that is PROVED where the disjunction's right
branch was FREE. What it does not buy: any statement about the fixed public chip itself — collision
resistance of a fixed function is a conjecture, not a Lean theorem (`RomBindingReduction` header).

## Axiom hygiene

`#assert_all_clean` ⊆ {propext, Classical.choice, Quot.sound}; no `sorry`, no fresh `axiom`, no
`native_decide`.
-/
import Dregg2.Crypto.RomMerkleOpening
import Dregg2.Tactics
import Mathlib.Tactic

namespace Dregg2.Crypto.RomHashedLeafOpening

open Dregg2.Crypto.ConcreteSecurity (Negl PolyBounded)
open Dregg2.Crypto.FloorGames (Game Adversary gameAdv gameAdv_mem_unit)
open Dregg2.Crypto.ProbCrypto (winProb_le_of_imp negl_of_le)
open Dregg2.Crypto.RomOracle (OracleComp QueryBounded)
open Dregg2.Crypto.RomQueryFloor (romCollisionGame RomEff)
open Dregg2.Crypto.KeyedRomFloor (KeyedRomFamily keyedRomGame keyedRom_hard)
open Dregg2.Crypto.RomBindingReduction
open Dregg2.Crypto.RomCarrierSites
open Dregg2.Crypto.RomChainedReduction (chainEval chainEval_const)
open Dregg2.Crypto.RomMerkleOpening
  (nodeMsg nodeMsg_left_inj walkComp walkComp_queryBounded walkComp_eval_collides
   chainEval_const_of_ne_nil)

set_option autoImplicit false

/-! ## §0 — the family: a truncated leaf block ⊕ an ordered node pair, keyed by the site's tags. -/

/-- **THE HASHED-LEAF TREE FAMILY.** Messages are the site's truncated leaf blocks (`inl`) and the
ordered two-child node pairs at the ideal digest width (`inr`), domain-separated by constructor —
the ROM image of the deployed chip's arity separation (leaf arity vs `CHIP_NODE8_ARITY = 16`).
Keyed by the site's own domain-separation tag space. -/
abbrev hlFam (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
    (Leaf : ℕ → Type) (lF : ∀ l, Fintype (Leaf l)) (lD : ∀ l, DecidableEq (Leaf l)) :
    KeyedRomFamily :=
  flatFamily Key kF kD kN (fun l => Leaf l ⊕ (Fin (2 ^ l) × Fin (2 ^ l)))
    (fun l => letI := lF l; inferInstance)
    (fun l => letI := lD l; inferInstance)
    (fun l => ⟨Sum.inr (⟨0, by positivity⟩, ⟨0, by positivity⟩)⟩)

variable (Key : Type) (kF : Fintype Key) (kD : DecidableEq Key) (kN : Nonempty Key)
  (Leaf : ℕ → Type) (lF : ∀ l, Fintype (Leaf l)) (lD : ∀ l, DecidableEq (Leaf l))

/-- The floor's width obligation, closed by construction. -/
theorem hlFam_card_R (l : ℕ) :
    letI := (hlFam Key kF kD kN Leaf lF lD).rFin l
    Fintype.card ((hlFam Key kF kD kN Leaf lF lD).R l) = 2 ^ l := by
  show Fintype.card (Fin (2 ^ l)) = 2 ^ l
  simp

/-! ## §1 — the SINGLE-ABSORB carriers: the leaf digest and the node digest. -/

/-- **THE LEAF CARRIER** — commitment `H (t, inl block)`: the leaf digest binds its WHOLE truncated
block. The embedding is by constructor, injective on the nose (the site's `leafFields_inj` content
is absorbed into `Leaf`'s own equality). -/
def hlLeafCarrier : RomCarrier (hlFam Key kF kD kN Leaf lF lD) :=
  taggedCarrier _ (fun _ => Unit) Leaf lD
    (fun _ _ v => Sum.inl v) (fun _ _ _ _ h => Sum.inl_injective h)

/-- **THE NODE CARRIER** — commitment `H (t, inr (x, y))`: the node digest binds BOTH ordered
children. The ordered pair is the `pack8 l r = L8 ‖ R8` layout at the ideal width (`pack8_inj`'s
content: order preserved, both coordinates bound). -/
def hlNodeCarrier : RomCarrier (hlFam Key kF kD kN Leaf lF lD) :=
  taggedCarrier _ (fun _ => Unit) (fun l => Fin (2 ^ l) × Fin (2 ^ l))
    (fun _ => inferInstance)
    (fun _ _ v => Sum.inr v) (fun _ _ _ _ h => Sum.inr_injective h)

/-- **⚑ THE LEAF BINDING, ON THE PROVED FLOOR** — every query-bounded forger that equivocates one
leaf digest between two DISTINCT truncated blocks has NEGLIGIBLE advantage. NO floor hypothesis:
`flatSite_binds`, hence `keyedRom_hard`, hence the birthday bound. -/
theorem hlLeaf_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (hlFam Key kF kD kN Leaf lF lD)
      (hlLeafCarrier Key kF kD kN Leaf lF lD)))
    (hA : RomCarrierEff (hlFam Key kF kD kN Leaf lF lD)
      (hlLeafCarrier Key kF kD kN Leaf lF lD) Q A) :
    Negl (gameAdv (romCarrierGame (hlFam Key kF kD kN Leaf lF lD)
      (hlLeafCarrier Key kF kD kN Leaf lF lD)) A) :=
  flatSite_binds Key kF kD kN _ _ _ _ (hlLeafCarrier Key kF kD kN Leaf lF lD) Q hQ A hA

/-- **⚑ THE NODE BINDING, ON THE PROVED FLOOR** — every query-bounded forger that equivocates one
node digest between two DISTINCT ordered child pairs has NEGLIGIBLE advantage. -/
theorem hlNode_binds_rom (Q : ℕ → ℕ)
    (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (romCarrierGame (hlFam Key kF kD kN Leaf lF lD)
      (hlNodeCarrier Key kF kD kN Leaf lF lD)))
    (hA : RomCarrierEff (hlFam Key kF kD kN Leaf lF lD)
      (hlNodeCarrier Key kF kD kN Leaf lF lD) Q A) :
    Negl (gameAdv (romCarrierGame (hlFam Key kF kD kN Leaf lF lD)
      (hlNodeCarrier Key kF kD kN Leaf lF lD)) A) :=
  flatSite_binds Key kF kD kN _ _ _ _ (hlNodeCarrier Key kF kD kN Leaf lF lD) Q hQ A hA

/-! ## §2 — the query points of the two absorbs. -/

/-- The LEAF query point — the tag and the truncated leaf block. -/
def hlLeafPt (l : ℕ) (t : Key) (v : Leaf l) :
    (hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l :=
  (t, Sum.inl v)

/-- ONE PATH LEVEL's query point — the tag and the ordered node pair, the index bit fixing the
side (`RomMerkleOpening.nodeMsg`: the deployed `[acc, s]`/`[s, acc]` order). -/
def hlStepEnc (l : ℕ) (t : Key) :
    Fin (2 ^ l) → (Bool × Fin (2 ^ l)) → (hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l :=
  fun acc b => (t, Sum.inr (nodeMsg b.1 acc b.2))

/-- The step encoding is LEFT-injective per level — the layout fact the walk consumes. -/
theorem hlStepEnc_left_inj (l : ℕ) (t : Key) (b : Bool × Fin (2 ^ l)) {a c : Fin (2 ^ l)}
    (h : hlStepEnc Key kF kD kN Leaf lF lD l t a b
       = hlStepEnc Key kF kD kN Leaf lF lD l t c b) : a = c :=
  nodeMsg_left_inj b.1 b.2 (Sum.inr_injective (congrArg Prod.snd h))

/-- The leaf point and every step point are DISTINCT messages (constructor separation) — the ROM
image of the deployed arity separation. Recorded as a pin; the reductions do not need it. -/
theorem hlLeafPt_ne_stepEnc (l : ℕ) (t t' : Key) (v : Leaf l) (acc : Fin (2 ^ l))
    (b : Bool × Fin (2 ^ l)) :
    hlLeafPt Key kF kD kN Leaf lF lD l t v ≠ hlStepEnc Key kF kD kN Leaf lF lD l t' acc b :=
  fun h => Sum.inl_ne_inr (congrArg Prod.snd h)

/-! ## §3 — the PURE-PATH forgery (the `recomposeUp8` shape): two DISTINCT starting digests, one
SHARED `(bit, sibling)` schedule, equal recomposed roots. -/

/-- **THE PATH FORGERY.** The adversary outputs a tag, a `d l`-level shared path and TWO starting
digests; it WINS iff the digests are DISTINCT yet fold to the SAME root along the shared path at
the sampled oracle. The ROM restatement of `recomposeUp8_binds_or_collides`'s break. -/
def hlPathForgery (d : ℕ → ℕ) : RomForgery (hlFam Key kF kD kN Leaf lF lD) where
  Ans := fun l => (Key × (Fin (d l) → Bool × Fin (2 ^ l))) × Fin (2 ^ l) × Fin (2 ^ l)
  wins := fun l H p =>
    p.2.1 ≠ p.2.2 ∧
      chainEval H (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1) p.2.1 (List.ofFn p.1.2)
        = chainEval H (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1) p.2.2 (List.ofFn p.1.2)
  winsDec := fun l _ _ => by
    letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
    exact instDecidableAnd

/-- The path extractor program on one forgery answer: re-walk the shared schedule with both
accumulators (`walkComp`), two queries per level. The default is a degenerate self-pair, returned
only past the end of the path, which a winning forgery excludes. -/
def hlPathExtract (d : ℕ → ℕ) (l : ℕ)
    (p : (hlPathForgery Key kF kD kN Leaf lF lD d).Ans l) :
    OracleComp ((hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l)
      ((hlFam Key kF kD kN Leaf lF lD).toRomFamily.R l)
      ((hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l
        × (hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l) :=
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).dDec l
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
  walkComp (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
    ((p.1.1, Sum.inr (p.2.1, p.2.2)), (p.1.1, Sum.inr (p.2.1, p.2.2)))
    p.2.1 p.2.2 (List.ofFn p.1.2)

/-- The path extractor pays exactly `2 · d l` queries. -/
theorem hlPathExtract_queryBounded (d : ℕ → ℕ) (l : ℕ)
    (p : (hlPathForgery Key kF kD kN Leaf lF lD d).Ans l) :
    QueryBounded (2 * d l) (hlPathExtract Key kF kD kN Leaf lF lD d l p) := by
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).dDec l
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
  have h := walkComp_queryBounded (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
    ((p.1.1, Sum.inr (p.2.1, p.2.2)), (p.1.1, Sum.inr (p.2.1, p.2.2)))
    (List.ofFn p.1.2) p.2.1 p.2.2
  rwa [List.length_ofFn] at h

/-- The extracted collision finder: run the forger, re-walk its claimed schedule. -/
def hlPathFinder (d : ℕ → ℕ)
    (A : Adversary (hlPathForgery Key kF kD kN Leaf lF lD d).game) :
    Adversary (keyedRomGame (hlFam Key kF kD kN Leaf lF lD)) where
  run := fun l H => (hlPathExtract Key kF kD kN Leaf lF lD d l (A.run l H)).eval H

/-- **⚑ WIN-PRESERVATION** — the walk's correctness at the game level: wherever the path forger
wins, the re-walk returns two DISTINCT query points with EQUAL sampled answers. -/
theorem hlPath_wins_imp (d : ℕ → ℕ)
    (A : Adversary (hlPathForgery Key kF kD kN Leaf lF lD d).game)
    (l : ℕ) (H : (hlPathForgery Key kF kD kN Leaf lF lD d).game.Inst l)
    (hwin : (hlPathForgery Key kF kD kN Leaf lF lD d).game.wins l H (A.run l H)) :
    (keyedRomGame (hlFam Key kF kD kN Leaf lF lD)).wins l H
      ((hlPathFinder Key kF kD kN Leaf lF lD d A).run l H) := by
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).dDec l
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
  obtain ⟨hne, heq⟩ := hwin
  exact walkComp_eval_collides (hlStepEnc Key kF kD kN Leaf lF lD l (A.run l H).1.1)
    (fun b a c h => hlStepEnc_left_inj Key kF kD kN Leaf lF lD l (A.run l H).1.1 b h) H
    (((A.run l H).1.1, Sum.inr ((A.run l H).2.1, (A.run l H).2.2)),
      ((A.run l H).1.1, Sum.inr ((A.run l H).2.1, (A.run l H).2.2)))
    (List.ofFn (A.run l H).1.2) (A.run l H).2.1 (A.run l H).2.2 hne heq

/-- The advantage inequality — unconditional, over ALL adversaries. -/
theorem hlPath_adv_le (d : ℕ → ℕ)
    (A : Adversary (hlPathForgery Key kF kD kN Leaf lF lD d).game) (l : ℕ) :
    gameAdv (hlPathForgery Key kF kD kN Leaf lF lD d).game A l
      ≤ gameAdv (keyedRomGame (hlFam Key kF kD kN Leaf lF lD))
          (hlPathFinder Key kF kD kN Leaf lF lD d A) l := by
  refine @winProb_le_of_imp _ ((hlPathForgery Key kF kD kN Leaf lF lD d).game.instFin l) _ _
    (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  exact (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr (hlPath_wins_imp Key kF kD kN Leaf lF lD d A l H hH)

/-- The extracted finder is query-bounded, the walk's queries PAID: `Q + 2·d`. -/
theorem hlPathFinder_in_romEff (d : ℕ → ℕ) (Q : ℕ → ℕ)
    (A : Adversary (hlPathForgery Key kF kD kN Leaf lF lD d).game)
    (hA : RomForgeryEff (hlFam Key kF kD kN Leaf lF lD)
      (hlPathForgery Key kF kD kN Leaf lF lD d) Q A) :
    RomEff (hlFam Key kF kD kN Leaf lF lD).toRomFamily (fun l => Q l + 2 * d l)
      (hlPathFinder Key kF kD kN Leaf lF lD d A) := by
  obtain ⟨M, hMQ, hrun⟩ := hA
  refine ⟨fun l => OracleComp.bindComp (M l) (hlPathExtract Key kF kD kN Leaf lF lD d l),
    fun l => ?_, fun l H => ?_⟩
  · exact OracleComp.bindComp_queryBounded (hMQ l)
      (fun p => hlPathExtract_queryBounded Key kF kD kN Leaf lF lD d l p)
  · show (hlPathExtract Key kF kD kN Leaf lF lD d l (A.run l H)).eval H = _
    exact (congrArg (fun p => (hlPathExtract Key kF kD kN Leaf lF lD d l p).eval H) (hrun l H)).trans
      (OracleComp.bindComp_eval (M l) (hlPathExtract Key kF kD kN Leaf lF lD d l) H).symm

/-- **⚑⚑ THE PATH BINDING, FROM THE PROVED FLOOR** — the ROM successor shape for
`recomposeUp8_binds_or_collides`: a query-bounded forger that folds two DISTINCT starting digests
up one shared path to one root has NEGLIGIBLE advantage, at any polynomial total budget `Q'`
dominating the forger's queries plus the walk's `2·d` re-descent. NO refuted floor. -/
theorem hlPathRom_binds (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + 2 * d l ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlPathForgery Key kF kD kN Leaf lF lD d).game)
    (hA : RomForgeryEff (hlFam Key kF kD kN Leaf lF lD)
      (hlPathForgery Key kF kD kN Leaf lF lD d) Q A) :
    Negl (gameAdv (hlPathForgery Key kF kD kN Leaf lF lD d).game A) := by
  have hfind : RomEff (hlFam Key kF kD kN Leaf lF lD).toRomFamily Q'
      (hlPathFinder Key kF kD kN Leaf lF lD d A) := by
    obtain ⟨M', hM'Q, hrun⟩ := hlPathFinder_in_romEff Key kF kD kN Leaf lF lD d Q A hA
    exact ⟨M', fun l => (hM'Q l).mono (hle l), hrun⟩
  exact negl_of_le
    (fun l => (gameAdv_mem_unit (hlPathForgery Key kF kD kN Leaf lF lD d).game A l).1)
    (hlPath_adv_le Key kF kD kN Leaf lF lD d A)
    (keyedRom_hard (hlFam Key kF kD kN Leaf lF lD) Q' hQ'
      (hlFam_card_R Key kF kD kN Leaf lF lD)
      (hlPathFinder Key kF kD kN Leaf lF lD d A) hfind)

/-! ## §4 — the HASHED-LEAF OPENING forgery (the `capOpen8`/GENTIAN shape): two DISTINCT leaves,
their digests folded up one SHARED path to one root. -/

/-- **THE HASHED-LEAF OPENING FORGERY.** The adversary outputs a tag, a shared `d l`-level path and
TWO leaves; it WINS iff the leaves are DISTINCT yet their HASHED leaf digests fold to the SAME root
along the shared path, at the sampled oracle. This is `capOpen8_binds_leaf_or_collides`'s /
`membersAt8_functional_on_path`'s break, stated at the oracle: the leaf digest is `H (t, inl leaf)`
and the fold re-absorbs it level by level — the oracle appears INSIDE the win relation, which is
what no single carrier could say. -/
def hlOpenForgery (d : ℕ → ℕ) : RomForgery (hlFam Key kF kD kN Leaf lF lD) where
  Ans := fun l => (Key × (Fin (d l) → Bool × Fin (2 ^ l))) × Leaf l × Leaf l
  wins := fun l H p =>
    p.2.1 ≠ p.2.2 ∧
      chainEval H (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
          (H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1)) (List.ofFn p.1.2)
        = chainEval H (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
            (H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2)) (List.ofFn p.1.2)
  winsDec := fun l _ _ => by
    letI := lD l
    letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
    exact instDecidableAnd

/-- **THE OPENING EXTRACTOR PROGRAM** on one forgery answer: query BOTH leaf points; equal answers
ARE the collision (the two leaf blocks are distinct messages); distinct answers hand the walk two
distinct accumulators over the shared schedule. Budget `2 · d l + 2`. -/
def hlOpenExtract (d : ℕ → ℕ) (l : ℕ)
    (p : (hlOpenForgery Key kF kD kN Leaf lF lD d).Ans l) :
    OracleComp ((hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l)
      ((hlFam Key kF kD kN Leaf lF lD).toRomFamily.R l)
      ((hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l
        × (hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l) :=
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).dDec l
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
  OracleComp.query (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1) (fun r₁ =>
  OracleComp.query (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2) (fun r₂ =>
  if r₁ = r₂ then
    OracleComp.pure (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1,
      hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2)
  else
    walkComp (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
      (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1,
        hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1)
      r₁ r₂ (List.ofFn p.1.2)))

/-- The opening extractor pays exactly `2 · d l + 2` queries: the two leaf points plus the walk. -/
theorem hlOpenExtract_queryBounded (d : ℕ → ℕ) (l : ℕ)
    (p : (hlOpenForgery Key kF kD kN Leaf lF lD d).Ans l) :
    QueryBounded (2 * d l + 2) (hlOpenExtract Key kF kD kN Leaf lF lD d l p) := by
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).dDec l
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
  refine QueryBounded.query (2 * d l + 1) _ _ (fun r₁ => ?_)
  refine QueryBounded.query (2 * d l) _ _ (fun r₂ => ?_)
  split
  · exact QueryBounded.pure _ _
  · have h := walkComp_queryBounded (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
      (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1,
        hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1)
      (List.ofFn p.1.2) r₁ r₂
    rwa [List.length_ofFn] at h

/-- **⚑ THE OPENING EXTRACTOR IS CORRECT, UNCONDITIONALLY** — on every winning answer it returns
two DISTINCT query points with EQUAL sampled answers: equal leaf digests make the two (distinct)
leaf blocks the collision; distinct digests hand the walk two distinct accumulators whose shared
fold agrees, and the walk finds the interior merge (`walkComp_eval_collides`). -/
theorem hlOpenExtract_eval_collides (d : ℕ → ℕ) (l : ℕ)
    (H : (hlFam Key kF kD kN Leaf lF lD).toRomFamily.D l
      → (hlFam Key kF kD kN Leaf lF lD).toRomFamily.R l)
    (p : (hlOpenForgery Key kF kD kN Leaf lF lD d).Ans l)
    (hwin : (hlOpenForgery Key kF kD kN Leaf lF lD d).wins l H p) :
    ((hlOpenExtract Key kF kD kN Leaf lF lD d l p).eval H).1
        ≠ ((hlOpenExtract Key kF kD kN Leaf lF lD d l p).eval H).2
      ∧ H ((hlOpenExtract Key kF kD kN Leaf lF lD d l p).eval H).1
        = H ((hlOpenExtract Key kF kD kN Leaf lF lD d l p).eval H).2 := by
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).dDec l
  letI := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
  obtain ⟨hne, heq⟩ := hwin
  have hred : (hlOpenExtract Key kF kD kN Leaf lF lD d l p).eval H
      = (if H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1)
            = H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2) then
          OracleComp.pure (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1,
            hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2)
        else
          walkComp (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
            (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1,
              hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1)
            (H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1))
            (H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2))
            (List.ofFn p.1.2)).eval H := rfl
  by_cases hcoll : H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1)
      = H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2)
  · rw [hred, if_pos hcoll]
    exact ⟨fun hc => hne (Sum.inl_injective (congrArg Prod.snd hc)), hcoll⟩
  · rw [hred, if_neg hcoll]
    exact walkComp_eval_collides (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
      (fun b a c h => hlStepEnc_left_inj Key kF kD kN Leaf lF lD l p.1.1 b h) H
      (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1,
        hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.1)
      (List.ofFn p.1.2) _ _ hcoll heq

/-- The extracted collision finder: run the forger, query its two leaf points, walk if needed. -/
def hlOpenFinder (d : ℕ → ℕ)
    (A : Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game) :
    Adversary (keyedRomGame (hlFam Key kF kD kN Leaf lF lD)) where
  run := fun l H => (hlOpenExtract Key kF kD kN Leaf lF lD d l (A.run l H)).eval H

/-- **⚑ WIN-PRESERVATION** at the game level. -/
theorem hlOpen_wins_imp (d : ℕ → ℕ)
    (A : Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game)
    (l : ℕ) (H : (hlOpenForgery Key kF kD kN Leaf lF lD d).game.Inst l)
    (hwin : (hlOpenForgery Key kF kD kN Leaf lF lD d).game.wins l H (A.run l H)) :
    (keyedRomGame (hlFam Key kF kD kN Leaf lF lD)).wins l H
      ((hlOpenFinder Key kF kD kN Leaf lF lD d A).run l H) :=
  hlOpenExtract_eval_collides Key kF kD kN Leaf lF lD d l H (A.run l H) hwin

/-- The advantage inequality — unconditional, over ALL adversaries. -/
theorem hlOpen_adv_le (d : ℕ → ℕ)
    (A : Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game) (l : ℕ) :
    gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game A l
      ≤ gameAdv (keyedRomGame (hlFam Key kF kD kN Leaf lF lD))
          (hlOpenFinder Key kF kD kN Leaf lF lD d A) l := by
  refine @winProb_le_of_imp _ ((hlOpenForgery Key kF kD kN Leaf lF lD d).game.instFin l) _ _
    (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  exact (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr (hlOpen_wins_imp Key kF kD kN Leaf lF lD d A l H hH)

/-- The extracted finder is query-bounded, its queries PAID: `Q + (2·d + 2)`. -/
theorem hlOpenFinder_in_romEff (d : ℕ → ℕ) (Q : ℕ → ℕ)
    (A : Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game)
    (hA : RomForgeryEff (hlFam Key kF kD kN Leaf lF lD)
      (hlOpenForgery Key kF kD kN Leaf lF lD d) Q A) :
    RomEff (hlFam Key kF kD kN Leaf lF lD).toRomFamily (fun l => Q l + (2 * d l + 2))
      (hlOpenFinder Key kF kD kN Leaf lF lD d A) := by
  obtain ⟨M, hMQ, hrun⟩ := hA
  refine ⟨fun l => OracleComp.bindComp (M l) (hlOpenExtract Key kF kD kN Leaf lF lD d l),
    fun l => ?_, fun l H => ?_⟩
  · exact OracleComp.bindComp_queryBounded (hMQ l)
      (fun p => hlOpenExtract_queryBounded Key kF kD kN Leaf lF lD d l p)
  · show (hlOpenExtract Key kF kD kN Leaf lF lD d l (A.run l H)).eval H = _
    exact (congrArg (fun p => (hlOpenExtract Key kF kD kN Leaf lF lD d l p).eval H) (hrun l H)).trans
      (OracleComp.bindComp_eval (M l) (hlOpenExtract Key kF kD kN Leaf lF lD d l) H).symm

/-- **⚑⚑ THE HASHED-LEAF OPENING BINDING, FROM THE PROVED FLOOR** — the ROM successor shape for
`capOpen8_binds_leaf_or_collides` / `fieldsOpen8_binds_leaf_or_collides` /
`heapOpen8_binds_leaf_or_collides`: a query-bounded forger that opens one root to two DISTINCT
leaves along one shared path has NEGLIGIBLE advantage, at any polynomial total budget `Q'`
dominating `Q + 2·d + 2`. The floor is `keyedRom_hard` — the birthday bound, a THEOREM — and
NOTHING refutable is carried. -/
theorem hlOpenRom_binds (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * d l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game)
    (hA : RomForgeryEff (hlFam Key kF kD kN Leaf lF lD)
      (hlOpenForgery Key kF kD kN Leaf lF lD d) Q A) :
    Negl (gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game A) := by
  have hfind : RomEff (hlFam Key kF kD kN Leaf lF lD).toRomFamily Q'
      (hlOpenFinder Key kF kD kN Leaf lF lD d A) := by
    obtain ⟨M', hM'Q, hrun⟩ := hlOpenFinder_in_romEff Key kF kD kN Leaf lF lD d Q A hA
    exact ⟨M', fun l => (hM'Q l).mono (hle l), hrun⟩
  exact negl_of_le
    (fun l => (gameAdv_mem_unit (hlOpenForgery Key kF kD kN Leaf lF lD d).game A l).1)
    (hlOpen_adv_le Key kF kD kN Leaf lF lD d A)
    (keyedRom_hard (hlFam Key kF kD kN Leaf lF lD) Q' hQ'
      (hlFam_card_R Key kF kD kN Leaf lF lD)
      (hlOpenFinder Key kF kD kN Leaf lF lD d A) hfind)

/-! ## §5 — the PUBLISHED-ROOT form (the `membersAt8_functional_on_path` shape): two leaves both
opening ONE published root. The extractor DROPS the root (`mapOut`, budget preserved) and the two
openings collide through it. -/

/-- **THE PUBLISHED-ROOT OPENING FORGERY** — the adversary also outputs the root both openings
recompute to; the win relation is the two-membership functional break the consumers state. -/
def hlOpenRootForgery (d : ℕ → ℕ) : RomForgery (hlFam Key kF kD kN Leaf lF lD) where
  Ans := fun l => (Key × (Fin (d l) → Bool × Fin (2 ^ l))) × Fin (2 ^ l) × Leaf l × Leaf l
  wins := fun l H p =>
    p.2.2.1 ≠ p.2.2.2 ∧
      chainEval H (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
          (H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2.1)) (List.ofFn p.1.2) = p.2.1 ∧
      chainEval H (hlStepEnc Key kF kD kN Leaf lF lD l p.1.1)
          (H (hlLeafPt Key kF kD kN Leaf lF lD l p.1.1 p.2.2.2)) (List.ofFn p.1.2) = p.2.1
  winsDec := fun l _ _ => by
    letI := lD l
    letI hR := ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rDec l
    exact @instDecidableAnd _ _ inferInstance (@instDecidableAnd _ _ (hR _ _) (hR _ _))

/-- The root-dropping map of adversaries into the opening forgery. -/
def hlRootToOpen (d : ℕ → ℕ)
    (A : Adversary (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game) :
    Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game where
  run := fun l H => let p := A.run l H; (p.1, p.2.2)

/-- Two openings of ONE published root are one equivocation: win-preservation under root-drop. -/
theorem hlRoot_wins_imp (d : ℕ → ℕ)
    (A : Adversary (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game)
    (l : ℕ) (H : (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game.Inst l)
    (hwin : (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game.wins l H (A.run l H)) :
    (hlOpenForgery Key kF kD kN Leaf lF lD d).game.wins l H
      ((hlRootToOpen Key kF kD kN Leaf lF lD d A).run l H) := by
  obtain ⟨hne, h1, h2⟩ := hwin
  exact ⟨hne, h1.trans h2.symm⟩

/-- The advantage inequality under root-drop. -/
theorem hlRoot_adv_le (d : ℕ → ℕ)
    (A : Adversary (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game) (l : ℕ) :
    gameAdv (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game A l
      ≤ gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game
          (hlRootToOpen Key kF kD kN Leaf lF lD d A) l := by
  refine @winProb_le_of_imp _
    ((hlOpenRootForgery Key kF kD kN Leaf lF lD d).game.instFin l) _ _ (fun H hH => ?_)
  replace hH := (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mp hH
  exact (Dregg2.Crypto.FloorGames.Adversary.hit_eq_true _ _ _).mpr (hlRoot_wins_imp Key kF kD kN Leaf lF lD d A l H hH)

/-- **⚑⚑ THE PUBLISHED-ROOT OPENING BINDING** — the ROM successor shape for
`membersAt8_functional_on_path_or_collides` and the `deployed_…Open8_binds_leaf_or_collides`
instantiations: two query-bounded openings of ONE published root to two DISTINCT leaves along one
shared path succeed with NEGLIGIBLE probability. The root-drop is a `mapOut` (budget preserved);
the rest is `hlOpenRom_binds`. -/
theorem hlOpenRootRom_binds (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * d l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game)
    (hA : RomForgeryEff (hlFam Key kF kD kN Leaf lF lD)
      (hlOpenRootForgery Key kF kD kN Leaf lF lD d) Q A) :
    Negl (gameAdv (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game A) := by
  obtain ⟨M, hMQ, hrun⟩ := hA
  have hopen : Negl (gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game
      (hlRootToOpen Key kF kD kN Leaf lF lD d A)) := by
    refine hlOpenRom_binds Key kF kD kN Leaf lF lD d Q Q' hle hQ' _
      ⟨fun l => OracleComp.mapOut (fun p => (p.1, p.2.2)) (M l),
        fun l => OracleComp.mapOut_queryBounded _ (hMQ l), fun l H => ?_⟩
    show (let p := A.run l H; (p.1, p.2.2)) = _
    exact (congrArg (fun p => (p.1, p.2.2)) (hrun l H)).trans
      (OracleComp.mapOut_eval (fun p => (p.1, p.2.2)) (M l) H).symm
  refine negl_of_le
    (fun l => (gameAdv_mem_unit (hlOpenRootForgery Key kF kD kN Leaf lF lD d).game A l).1)
    (hlRoot_adv_le Key kF kD kN Leaf lF lD d A) hopen

/-! ## §6 — non-fake teeth: the class is inhabited, the game winnable, the admitted refuter-shape
DEFANGED, the non-negligible forger EXCLUDED, and the floor-at-another-finder canary. -/

/-- The `0`-query constant opening answerer — the transplant of the exact shape that refutes the
`IsPolyTime` floors. Admitted by the class; the teeth below show why that is fine. -/
def hlConstOpenAdv (d : ℕ → ℕ) (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l)))
    (v w : ∀ l, Leaf l) :
    Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game where
  run := fun l _ => (c l, v l, w l)

/-- **(TOOTH — the class is INHABITED at every budget.)** -/
theorem hlConstOpenAdv_in_eff (d : ℕ → ℕ) (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l)))
    (v w : ∀ l, Leaf l) (Q : ℕ → ℕ) :
    RomForgeryEff (hlFam Key kF kD kN Leaf lF lD) (hlOpenForgery Key kF kD kN Leaf lF lD d) Q
      (hlConstOpenAdv Key kF kD kN Leaf lF lD d c v w) :=
  ⟨fun l => OracleComp.pure (c l, v l, w l),
    fun l => QueryBounded.pure (Q l) _, fun _ _ => rfl⟩

/-- **(TOOTH — the game is genuinely WINNABLE.)** At the constant oracle every fold collapses to
the constant, so ANY two distinct leaves equivocate: the advantage the binding bounds is positive,
not the advantage of an unwinnable game. -/
theorem hlConstOpenAdv_gameAdv_pos (d : ℕ → ℕ)
    (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l))) (v w : ∀ l, Leaf l)
    (l : ℕ) (hvw : v l ≠ w l) :
    0 < gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game
      (hlConstOpenAdv Key kF kD kN Leaf lF lD d c v w) l := by
  obtain ⟨r₀⟩ : Nonempty ((hlFam Key kF kD kN Leaf lF lD).toRomFamily.R l) :=
    ((hlFam Key kF kD kN Leaf lF lD).toRomFamily).rNe l
  refine @winProb_pos_of_witness _
    ((hlOpenForgery Key kF kD kN Leaf lF lD d).game.instFin l) _ (fun _ => r₀) ?_
  refine ((hlConstOpenAdv Key kF kD kN Leaf lF lD d c v w).hit_eq_true l _).mpr ?_
  refine ⟨hvw, ?_⟩
  exact (chainEval_const _ r₀ _).trans (chainEval_const _ r₀ _).symm

/-- **(TOOTH — the admitted refuter-shape is DEFANGED, not excluded.)** The constant answerer is in
the class, wins at the constant oracle, and its advantage is NEGLIGIBLE — where against the FIXED
public chip the same shape wins with probability `1`. Sampling the oracle after the adversary is
fixed is what does the work. -/
theorem hlConstOpenAdv_negl (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * d l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (c : ∀ l, Key × (Fin (d l) → Bool × Fin (2 ^ l))) (v w : ∀ l, Leaf l) :
    Negl (gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game
      (hlConstOpenAdv Key kF kD kN Leaf lF lD d c v w)) :=
  hlOpenRom_binds Key kF kD kN Leaf lF lD d Q Q' hle hQ' _
    (hlConstOpenAdv_in_eff Key kF kD kN Leaf lF lD d c v w Q)

/-- **(TOOTH — a non-negligible opening forger is OUTSIDE the class.)** The strategy that refutes
the `IsPolyTime` floors cannot produce a member of this one. -/
theorem hlOpen_nonNegl_forger_excluded (d Q Q' : ℕ → ℕ)
    (hle : ∀ l, Q l + (2 * d l + 2) ≤ Q' l)
    (hQ' : PolyBounded (fun l => ((Q' l : ℝ) * (Q' l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game)
    (hnn : ¬ Negl (gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game A)) :
    ¬ RomForgeryEff (hlFam Key kF kD kN Leaf lF lD)
      (hlOpenForgery Key kF kD kN Leaf lF lD d) Q A :=
  fun hA => hnn (hlOpenRom_binds Key kF kD kN Leaf lF lD d Q Q' hle hQ' A hA)

/-- **(CANARY — the bound does NOT follow from the floor applied at ANOTHER finder.)** Strip the
reduction: `keyedRom_hard` at an arbitrary member `B` bounds a DIFFERENT ensemble; only
`hlOpen_adv_le` at the EXTRACTED finder connects the opening game to the floor. Reds if a future
edit disconnects them. -/
example (d Q : ℕ → ℕ) (hQ : PolyBounded (fun l => ((Q l : ℝ) * (Q l : ℝ) + 1)))
    (A : Adversary (hlOpenForgery Key kF kD kN Leaf lF lD d).game)
    (B : Adversary (keyedRomGame (hlFam Key kF kD kN Leaf lF lD)))
    (hB : Dregg2.Crypto.KeyedRomFloor.KeyedRomEff (hlFam Key kF kD kN Leaf lF lD) Q B) :
    True := by
  fail_if_success
    (have : Negl (gameAdv (hlOpenForgery Key kF kD kN Leaf lF lD d).game A) :=
      keyedRom_hard (hlFam Key kF kD kN Leaf lF lD) Q hQ
        (hlFam_card_R Key kF kD kN Leaf lF lD) B hB)
  trivial

/-! ## Kernel-clean keystones. -/

#assert_all_clean [
  hlFam_card_R,
  hlLeaf_binds_rom,
  hlNode_binds_rom,
  hlStepEnc_left_inj,
  hlLeafPt_ne_stepEnc,
  hlPathExtract_queryBounded,
  hlPath_wins_imp,
  hlPath_adv_le,
  hlPathFinder_in_romEff,
  hlPathRom_binds,
  hlOpenExtract_queryBounded,
  hlOpenExtract_eval_collides,
  hlOpen_wins_imp,
  hlOpen_adv_le,
  hlOpenFinder_in_romEff,
  hlOpenRom_binds,
  hlRoot_wins_imp,
  hlRoot_adv_le,
  hlOpenRootRom_binds,
  hlConstOpenAdv_in_eff,
  hlConstOpenAdv_gameAdv_pos,
  hlConstOpenAdv_negl,
  hlOpen_nonNegl_forger_excluded
]

end Dregg2.Crypto.RomHashedLeafOpening

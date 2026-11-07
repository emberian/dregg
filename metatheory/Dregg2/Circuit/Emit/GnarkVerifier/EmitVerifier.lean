/-
# Dregg2.Circuit.Emit.GnarkVerifier.EmitVerifier — THE KEYSTONE: the five committed
leaf refinements + canonicity composed into the top verifier refinement, firing the
already-proven `FriVerifier.wrap_sound`.

`FriVerifier.verifyAlgoO` (FriVerifierO.lean:521) is the deployed verifier as a SIX-way
`&&` of exactly five checks + the VK/canonicity pin:

    vk.shapeMatches proof              -- (canonicity / shape)
      && checks.foldConsistent …       -- FRI arity-2 fold  (FriFoldEmit)
      && checks.merklePaths …          -- Merkle-BN254 path  (MerkleEmit)
      && checks.batchTables …          -- batch-table check  (BatchTableEmit)
      && checks.queryPow …             -- grinding PoW        (QueryPowEmit)
      && segmentTooth proof pub        -- settlement segment  (SegmentEmit)

This module composes the six committed `gHolds`-refinements — `canonicity_refines`,
`friFold_leaf_refines`, `merkle_path_refines`, `batchTable_refines`, `queryPow_refines`,
`segment_refines`/`segment_refines_segmentTooth` — into ONE emitted `GnarkCircuitData`
(`emitVerifier`) whose satisfaction walks the SAME six-way structure. The leaves are
CITED and COMPOSED, never re-proved: the whole `gHolds` splits (disjoint `Nat.pair`
variable blocks — one generic `remap_eval_mkM` plumbing lemma, no per-leaf offset work)
into the conjunction of the six leaf `gHolds`, each committed leaf supplies its polarity.

Deliverables:

  * **`emitVerifier I proof pub : GnarkCircuitData`** — the six leaf circuits laid down in
    disjoint variable blocks (block `i` = `Nat.pair i ·`), walking `verifyAlgoO`'s order.
  * **`emitVerifier_refines`** — `gHolds (emitVerifier …) (encodeWitness …) ↔
    verifyAlgo perm … (mkVk I) (mkChecks I) … proof pub = true`, where `mkVk`/`mkChecks`
    are the FriChecks/RecursionVk whose per-check Bools ARE the emitted leaves' verdicts.
    Composed from the six committed leaves + `segment_refines_segmentTooth`.
  * **`emitVerifier_refines_deployed`** — the same `gHolds` shown equivalent to the
    conjunction of the six DEPLOYED spec-sides (canonical residue, `foldCheckV`, the
    `refRoot` walk, `batchTablesCheckUnified`, the grind mask, the segment equality),
    citing each committed leaf refinement by name.
  * **`gnarkDenote I : GnarkCircuit Fr`** with **`emitVerifier_is_GnarkRefines`** proving
    it IS `FriVerifier.GnarkRefines`, so the already-proven **`wrap_sound`**
    (FriVerifier.lean:1037) FIRES: **`emitVerifier_wrap_sound`** exposes the resulting
    soundness statement — the abstract-Bool refinement obligation is now a STRUCTURAL
    theorem (conditional, as `wrap_sound` is, on the named `FriLowDegreeSound` carrier).

Classified seam (named, not silent): the four `FriChecks` fields + the VK pin are
INSTANTIATED at the emitted leaves' fixed verdicts — the leaf inputs (extension siblings,
Merkle openings, batch instances, grind challenge) live OUTSIDE `BatchProofData`, so those
five conjuncts are evaluated at the bundle `I`'s data; each leaf independently refines its
deployed Go check over ALL its inputs (the committed `*_refines`). The segment tooth reads
`proof`/`pub` LIVE. `wrap_sound`'s soundness rests, exactly as before, on the assumed
`FriLowDegreeSound` carrier for this instance — this module discharges the REFINEMENT leg
(gnark computes the same Bool as the spec), not the carrier.
-/
import Dregg2.Tactics
import Dregg2.Circuit.R1csFr
import Dregg2.Circuit.BatchTablesSingleAir
import Dregg2.Circuit.FriVerifier
import Dregg2.Circuit.Emit.GnarkVerifier.EmitFaithful
import Dregg2.Circuit.Emit.GnarkVerifier.CanonicityToy
import Dregg2.Circuit.Emit.GnarkVerifier.SegmentEmit
import Dregg2.Circuit.Emit.GnarkVerifier.QueryPowEmit
import Dregg2.Circuit.Emit.GnarkVerifier.BatchTableEmit
import Dregg2.Circuit.Emit.GnarkVerifier.MerkleEmit
import Dregg2.Circuit.Emit.GnarkVerifier.FriFoldEmit

namespace Dregg2.Circuit.Emit.GnarkVerifier

open Dregg2.Circuit.R1csFr
open Dregg2.Circuit.FriVerifier
open Dregg2.Circuit.BabyBearFr (ExtV)
open Dregg2.Circuit.BatchTablesSingleAir (batchTablesCheckUnified)

-- The leaf packages and their honest witnesses are builder-generated (the batch/fold
-- circuits are whole gadget programs). Keep them OPAQUE heads: without this, unifying the
-- composed circuit's blocks against `block_ok` / the leaf refinements makes `whnf` reduce
-- the full gadget monads and blow the heartbeat limit. Semantics are unchanged — every
-- leaf theorem is applied as a lemma, never by reduction.
attribute [local irreducible]
  canonicityData FriFold.friFoldData Merkle.merklePathData batchTableData emitQueryPow
  segmentData canonAsg FriFold.friFoldAsg Merkle.pathAsg encodeBatchTable powAsg segAsg

/-! ## §1 Generic disjoint-block composition (one plumbing lemma, reused six times).

Block `i` renames every frontend variable `v ↦ Nat.pair i v`; blocks are disjoint because
`Nat.pair` is injective, and the merged witness reads block `i` back through `Nat.unpair`
— so `(remapWire i w).eval (mkM sel) = w.eval (sel i)` holds UNCONDITIONALLY (no maxvar
bounds), the entire reason six heterogeneous leaf layouts compose without offset work. -/

/-- Rename every variable of a wire into block `i` via `Nat.pair`. -/
def remapWire (i : ℕ) : Wire → Wire
  | .var v        => .var (Nat.pair i v)
  | .const c      => .const c
  | .add x y      => .add (remapWire i x) (remapWire i y)
  | .mul x y      => .mul (remapWire i x) (remapWire i y)
  | .select b x y => .select (remapWire i b) (remapWire i x) (remapWire i y)

/-- Rename an assert list into block `i`. -/
def remapAsserts (i : ℕ) (l : List (Wire × Wire)) : List (Wire × Wire) :=
  l.map fun p => (remapWire i p.1, remapWire i p.2)

/-- The merged witness: variable `u` belongs to block `(Nat.unpair u).1`, at local index
`(Nat.unpair u).2`, and reads that block's assignment `sel`. -/
def mkM (sel : ℕ → Assignment) : Assignment :=
  fun u => sel (Nat.unpair u).1 (Nat.unpair u).2

/-- **The plumbing lemma.** A block-`i`-renamed wire, under the merged witness, evaluates
exactly as the original wire under block `i`'s own assignment. Unconditional. -/
theorem remap_eval_mkM (i : ℕ) (sel : ℕ → Assignment) (w : Wire) :
    (remapWire i w).eval (mkM sel) = w.eval (sel i) := by
  induction w with
  | var v => simp only [remapWire, Wire.eval, mkM, Nat.unpair_pair]
  | const c => rfl
  | add x y ihx ihy => simp only [remapWire, Wire.eval, ihx, ihy]
  | mul x y ihx ihy => simp only [remapWire, Wire.eval, ihx, ihy]
  | select b x y ihb ihx ihy => simp only [remapWire, Wire.eval, ihb, ihx, ihy]

/-- One block's asserts are satisfied by the merged witness IFF the leaf circuit is
satisfied by its own block assignment. -/
theorem block_ok (i : ℕ) (c : Circuit) (sel : ℕ → Assignment) :
    (∀ p ∈ remapAsserts i c.asserts, p.1.eval (mkM sel) = p.2.eval (mkM sel))
      ↔ c.satisfied (sel i) := by
  unfold Circuit.satisfied remapAsserts
  constructor
  · intro h q hq
    have hb := h (remapWire i q.1, remapWire i q.2) (List.mem_map_of_mem hq)
    simpa only [remap_eval_mkM] using hb
  · intro h p hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.mp hp
    simpa only [remap_eval_mkM] using h q hq

/-- `gHolds` of a package is, definitionally through the foundation's proven bridge,
frontend satisfaction of its circuit. -/
theorem gsat (d : GnarkCircuitData) (a : Assignment) :
    d.circuit.satisfied a ↔ gHolds d a :=
  R1csFr.gHolds d.circuit a

/-! ## §2 The input bundle and the six leaf blocks. -/

/-- The leaf inputs the composed verifier is quantified over. `proof`/`pub` (the segment
lanes) are threaded separately, live. -/
structure Inputs where
  /-- canonicity leaf input -/
  cv : Fr
  /-- FRI fold leaf inputs -/
  s0 : ExtV
  s1 : ExtV
  beta : ExtV
  claimed : ExtV
  fbits : List Bool
  /-- Merkle-path leaf inputs -/
  mleaf : Fr
  mroot : Fr
  msibs : List Fr
  mbits : List Bool
  /-- batch-table leaf input -/
  insts : List (InstShape × InstData)
  /-- grinding-PoW leaf inputs -/
  qn : ℕ
  qv : Fr

/-- Block assignments, in `verifyAlgoO` order: 0 canonicity, 1 fold, 2 merkle,
3 batch, 4 queryPow, 5 segment. -/
def sel (I : Inputs) (proof : BatchProofData Fr) (pub : WrapPublics Fr) : ℕ → Assignment
  | 0 => canonAsg I.cv
  | 1 => FriFold.friFoldAsg I.s0 I.s1 I.beta I.claimed I.fbits
  | 2 => Merkle.pathAsg I.msibs.length I.mleaf I.mroot I.msibs I.mbits
  | 3 => encodeBatchTable I.insts
  | 4 => powAsg I.qv
  | 5 => segAsg pub.segment proof.exposedSegment
  | _ => fun _ => 0

/-- **The composed emitted verifier** — the six leaf circuits in disjoint `Nat.pair`
blocks, walking `verifyAlgoO`'s six-way structure. -/
def emitVerifier (I : Inputs) (proof : BatchProofData Fr) (pub : WrapPublics Fr) :
    GnarkCircuitData :=
  { name         := "gnark_fri_verifier_composed_v1"
    publicInputs := []
    gadgets      := []
    circuit      :=
      ⟨ remapAsserts 0 canonicityData.circuit.asserts
          ++ remapAsserts 1 (FriFold.friFoldData I.s0 I.s1 I.beta I.claimed I.fbits).circuit.asserts
          ++ remapAsserts 2 (Merkle.merklePathData I.msibs.length).circuit.asserts
          ++ remapAsserts 3 (batchTableData (I.insts.map Prod.fst)).circuit.asserts
          ++ remapAsserts 4 (emitQueryPow I.qn).circuit.asserts
          ++ remapAsserts 5 segmentData.circuit.asserts ⟩ }

/-- The composed honest witness (the six leaves' honest fills, scattered into blocks). -/
def encodeWitness (I : Inputs) (proof : BatchProofData Fr) (pub : WrapPublics Fr) :
    Assignment :=
  mkM (sel I proof pub)

/-! ## §3 The block split — `gHolds` of the whole ↔ conjunction of the six leaf `gHolds`. -/

theorem emitVerifier_satisfied (I : Inputs) (proof : BatchProofData Fr) (pub : WrapPublics Fr) :
    (emitVerifier I proof pub).circuit.satisfied (encodeWitness I proof pub)
      ↔ canonicityData.circuit.satisfied (canonAsg I.cv)
        ∧ (FriFold.friFoldData I.s0 I.s1 I.beta I.claimed I.fbits).circuit.satisfied
            (FriFold.friFoldAsg I.s0 I.s1 I.beta I.claimed I.fbits)
        ∧ (Merkle.merklePathData I.msibs.length).circuit.satisfied
            (Merkle.pathAsg I.msibs.length I.mleaf I.mroot I.msibs I.mbits)
        ∧ (batchTableData (I.insts.map Prod.fst)).circuit.satisfied (encodeBatchTable I.insts)
        ∧ (emitQueryPow I.qn).circuit.satisfied (powAsg I.qv)
        ∧ segmentData.circuit.satisfied (segAsg pub.segment proof.exposedSegment) := by
  have e : (emitVerifier I proof pub).circuit.satisfied (encodeWitness I proof pub)
      ↔ (∀ p ∈ remapAsserts 0 canonicityData.circuit.asserts
            ++ remapAsserts 1 (FriFold.friFoldData I.s0 I.s1 I.beta I.claimed I.fbits).circuit.asserts
            ++ remapAsserts 2 (Merkle.merklePathData I.msibs.length).circuit.asserts
            ++ remapAsserts 3 (batchTableData (I.insts.map Prod.fst)).circuit.asserts
            ++ remapAsserts 4 (emitQueryPow I.qn).circuit.asserts
            ++ remapAsserts 5 segmentData.circuit.asserts,
          p.1.eval (mkM (sel I proof pub)) = p.2.eval (mkM (sel I proof pub))) := Iff.rfl
  rw [e, List.forall_mem_append, List.forall_mem_append, List.forall_mem_append,
    List.forall_mem_append, List.forall_mem_append,
    block_ok 0, block_ok 1, block_ok 2, block_ok 3, block_ok 4, block_ok 5]
  simp only [sel]
  tauto

/-- **The block split.** `gHolds` of the composed verifier is exactly the conjunction of
the six committed leaf `gHolds` — the AND-composition `verifyAlgoO` walks. -/
theorem merged_split (I : Inputs) (proof : BatchProofData Fr) (pub : WrapPublics Fr) :
    gHolds (emitVerifier I proof pub) (encodeWitness I proof pub)
      ↔ gHolds canonicityData (canonAsg I.cv)
        ∧ gHolds (FriFold.friFoldData I.s0 I.s1 I.beta I.claimed I.fbits)
            (FriFold.friFoldAsg I.s0 I.s1 I.beta I.claimed I.fbits)
        ∧ gHolds (Merkle.merklePathData I.msibs.length)
            (Merkle.pathAsg I.msibs.length I.mleaf I.mroot I.msibs I.mbits)
        ∧ gHolds (batchTableData (I.insts.map Prod.fst)) (encodeBatchTable I.insts)
        ∧ gHolds (emitQueryPow I.qn) (powAsg I.qv)
        ∧ gHolds segmentData (segAsg pub.segment proof.exposedSegment) := by
  rw [← gsat (emitVerifier I proof pub) (encodeWitness I proof pub), emitVerifier_satisfied,
    gsat canonicityData, gsat (FriFold.friFoldData I.s0 I.s1 I.beta I.claimed I.fbits),
    gsat (Merkle.merklePathData I.msibs.length), gsat (batchTableData (I.insts.map Prod.fst)),
    gsat (emitQueryPow I.qn), gsat segmentData]

/-! ## §4 The FriChecks / RecursionVk instance whose per-check Bools ARE the leaf verdicts. -/

/-- Canonicity / VK-shape verdict = the emitted canonicity leaf. -/
def bCanon (I : Inputs) : Bool := decide (gHolds canonicityData (canonAsg I.cv))
/-- FRI fold-consistency verdict = the emitted fold leaf. -/
def bFold (I : Inputs) : Bool :=
  decide (gHolds (FriFold.friFoldData I.s0 I.s1 I.beta I.claimed I.fbits)
    (FriFold.friFoldAsg I.s0 I.s1 I.beta I.claimed I.fbits))
/-- Merkle-path verdict = the emitted merkle leaf. -/
def bMerkle (I : Inputs) : Bool :=
  decide (gHolds (Merkle.merklePathData I.msibs.length)
    (Merkle.pathAsg I.msibs.length I.mleaf I.mroot I.msibs I.mbits))
/-- Batch-table verdict = the emitted batch leaf. -/
def bBatch (I : Inputs) : Bool :=
  decide (gHolds (batchTableData (I.insts.map Prod.fst)) (encodeBatchTable I.insts))
/-- Grinding-PoW verdict = the emitted queryPow leaf. -/
def bQPow (I : Inputs) : Bool := decide (gHolds (emitQueryPow I.qn) (powAsg I.qv))

/-- The `FriChecks` instantiated at the emitted leaves' verdicts. -/
def mkChecks (I : Inputs) : FriChecks Fr where
  foldConsistent _ _ _ := bFold I
  merklePaths _ _ := bMerkle I
  batchTables _ _ := bBatch I
  queryPow _ := bQPow I

/-- The `RecursionVk` shape pin instantiated at the emitted canonicity verdict. -/
def mkVk (I : Inputs) : RecursionVk Fr where
  shapeMatches _ := bCanon I

/-- `verifyAlgo` at `(mkVk I, mkChecks I)` collapses to the six-way `&&` of the leaf
verdicts and the live segment tooth (the derived transcript `d` is dropped by the
constant check fields — defeq). -/
theorem verifyAlgo_mk (I : Inputs) (perm : List Fr → List Fr) (RATE : ℕ) (toNat : Fr → ℕ)
    (params : FriParams) (initState : List Fr) (logN : ℕ)
    (proof : BatchProofData Fr) (pub : WrapPublics Fr) :
    verifyAlgo perm RATE toNat params (mkVk I) (mkChecks I) initState logN proof pub
      = (bCanon I && bFold I && bMerkle I && bBatch I && bQPow I && segmentTooth proof pub) := by
  simp only [verifyAlgo, mkVk, mkChecks]

/-! ## §5 THE KEYSTONE — the composed refinement, both faces. -/

set_option maxRecDepth 8192 in
/-- **`emitVerifier_refines` — the structural keystone.** The emitted composed circuit is
satisfied by its honest witness IFF the specified verifier `verifyAlgo`, instantiated at
the checks/VK that ARE the emitted leaves' verdicts, accepts — for the verifier's own
`proof`/`pub` whose 25-lane segment channels are pinned. Composes the block split with the
committed `segment_refines_segmentTooth`; every conjunct is one committed leaf. -/
theorem emitVerifier_refines (I : Inputs) (perm : List Fr → List Fr) (RATE : ℕ)
    (toNat : Fr → ℕ) (params : FriParams) (initState : List Fr) (logN : ℕ)
    (proof : BatchProofData Fr) (pub : WrapPublics Fr)
    (hs : pub.segment.length = numPublicLanes)
    (hc : proof.exposedSegment.length = numPublicLanes) :
    gHolds (emitVerifier I proof pub) (encodeWitness I proof pub)
      ↔ verifyAlgo perm RATE toNat params (mkVk I) (mkChecks I) initState logN proof pub
          = true := by
  rw [merged_split, verifyAlgo_mk, Bool.and_eq_true, Bool.and_eq_true, Bool.and_eq_true,
    Bool.and_eq_true, Bool.and_eq_true]
  simp only [bCanon, bFold, bMerkle, bBatch, bQPow, decide_eq_true_eq]
  rw [← segment_refines_segmentTooth proof pub hs hc]
  tauto

/-- **`emitVerifier_refines_deployed` — the deployed-semantics keystone.** The emitted
composed circuit is satisfied IFF the conjunction of the six DEPLOYED spec-sides holds:
the canonical-residue pin, the FRI fold `foldCheckV`, the Merkle `refRoot` walk, the batch
`batchTablesCheckUnified`, the grind mask, and the settlement segment equality. Each
conjunct is discharged by CITING its committed leaf refinement (`canonicity_refines`,
`friFold_leaf_refines`, `merkle_path_refines`, `batchTable_refines`, `queryPow_refines`,
`segment_refines`) — the leaves are composed, not re-proved. -/
theorem emitVerifier_refines_deployed (I : Inputs) (proof : BatchProofData Fr)
    (pub : WrapPublics Fr)
    (hmlen : I.msibs.length = I.mbits.length)
    (hs0 : FriFold.ExtCanon I.s0) (hs1 : FriFold.ExtCanon I.s1)
    (hbeta : FriFold.ExtCanon I.beta) (hclaimed : FriFold.ExtCanon I.claimed)
    (hqn : I.qn ≤ 31) (hwf : BatchWF I.insts)
    (hs : pub.segment.length = numPublicLanes)
    (hc : proof.exposedSegment.length = numPublicLanes) :
    gHolds (emitVerifier I proof pub) (encodeWitness I proof pub)
      ↔ I.cv.val < 2013265921
        ∧ FriFold.foldCheckV I.s0 I.s1 I.beta I.claimed I.fbits = true
        ∧ Merkle.refRoot I.mleaf (I.msibs.zip I.mbits) = I.mroot
        ∧ batchTablesCheckUnified frArith (openingsOf I.insts) = true
        ∧ (I.qv.val < 2 ^ 31 ∧ I.qv.val % 2 ^ I.qn = 0)
        ∧ proof.exposedSegment = pub.segment := by
  rw [merged_split, canonicity_refines I.cv,
    FriFold.friFold_leaf_refines I.s0 I.s1 I.beta I.claimed I.fbits hs0 hs1 hbeta hclaimed,
    Merkle.merkle_path_refines I.mleaf I.mroot I.msibs I.mbits hmlen,
    batchTable_refines I.insts hwf, queryPow_refines I.qn hqn I.qv,
    segment_refines pub.segment proof.exposedSegment hs hc]

/-! ## §6 Firing `wrap_sound` — the abstract-Bool obligation is now structural. -/

/-- The composed emitted circuit's Bool denotation over `proof`/`pub`: the five leaf
verdicts (from the emitted leaves) ANDed with the live segment tooth. -/
def gnarkDenote (I : Inputs) : GnarkCircuit Fr :=
  fun proof pub =>
    bCanon I && bFold I && bMerkle I && bBatch I && bQPow I && segmentTooth proof pub

/-- **`gnarkDenote` IS `GnarkRefines`.** For every proof/pub the composed emitted Bool
equals `verifyAlgo` at `(mkVk I, mkChecks I)` — the refinement obligation `wrap_sound`
consumes, discharged structurally (`verifyAlgo_mk`). -/
theorem emitVerifier_is_GnarkRefines (I : Inputs) (perm : List Fr → List Fr) (RATE : ℕ)
    (toNat : Fr → ℕ) (params : FriParams) (initState : List Fr) (logN : ℕ) :
    GnarkRefines perm RATE toNat params (mkVk I) (mkChecks I) initState logN (gnarkDenote I) :=
  fun proof pub => (verifyAlgo_mk I perm RATE toNat params initState logN proof pub).symm

/-- **`emitVerifier_wrap_sound` — THE PAYOFF FIRES.** Instantiating the already-proven
`FriVerifier.wrap_sound` at the composed `gnarkDenote`: under the named `FriLowDegreeSound`
carrier for this instance, a `gnarkDenote`-accepted proof yields a genuine extractable
transition whose exposed segment is the carried publics. The wrap introduces NO new
assumption beyond the FRI carrier — the transcript-fidelity/refinement leg that was a
differential-testing trust is now the STRUCTURAL `emitVerifier_is_GnarkRefines`. -/
theorem emitVerifier_wrap_sound (I : Inputs) (perm : List Fr → List Fr) (RATE : ℕ)
    (toNat : Fr → ℕ) (params : FriParams) (initState : List Fr) (logN : ℕ)
    [carrier : FriLowDegreeSound perm RATE toNat params (mkVk I) (mkChecks I) initState logN]
    (proof : BatchProofData Fr) (pub : WrapPublics Fr)
    (haccept : gnarkDenote I proof pub = true) :
    ∃ w : GenuineWitness Fr, w.exists_ ∧ proof.exposedSegment = pub.segment :=
  wrap_sound perm RATE toNat params (mkVk I) (mkChecks I) initState logN (gnarkDenote I)
    (emitVerifier_is_GnarkRefines I perm RATE toNat params initState logN) proof pub haccept

#assert_axioms remap_eval_mkM
#assert_axioms merged_split
#assert_axioms verifyAlgo_mk
#assert_axioms emitVerifier_refines
#assert_axioms emitVerifier_refines_deployed
#assert_axioms emitVerifier_is_GnarkRefines
#assert_axioms emitVerifier_wrap_sound

end Dregg2.Circuit.Emit.GnarkVerifier

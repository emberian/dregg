/-
# `Dregg2.Circuit.Emit.MinaPhase1TapeBinding` — **whose points**: the phase-1 tape's 53 elements,
decomposed, put on the curve, and welded to the objects that DETERMINE them.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** It authors no new constraint and emits no new descriptor: every wire
fact below is stated about `MinaPhase1Chain.chainPIs`, the public inputs the already-deployed
`dregg-pasta-fp-chainlink::v1` publishes. Rust parses that descriptor, fills trace cells, runs the
deployed prover and compares slices. House Law #1.

## ⚑⚑ THE HOLE THIS ADDRESSES, IN ITS AUTHOR'S WORDS

`MinaPhase1Chain` §8 residual 1, unrepaired since it was written:

> *"Nothing here says a `(x, y)` pair is on the curve, that `public_comm` commits to the 40-element
> public input, or that a `RecursionChallenge`'s `comm` is `⟨b_poly_coefficients(chals), G⟩`. Phase 1
> derives `fq_digest` FROM those coordinates; it does not authenticate them."*

⚑ **AND THE MEASURED SHAPE OF THE HOLE IS NOT WHAT THAT PARAGRAPH SAYS IT IS.** The tree already
CONTAINS the facts. `MinaWrapPublicCommGate.publicComm_is_the_transcript_preimage` derives
`PUBCOMM_XY` from the block's own 40-element public input and the SRS Lagrange basis, in the kernel,
and has done since rung 5e. `MinaWrapOpeningGate.opening_relation_holds` closes the IPA relation over
the 47-term aggregate of the block's commitments, in the kernel. What is missing is not a
derivation — it is a **WELD**: the block's commitments live in the tree as **two independently
hand-transcribed decimal lists** (`MinaRealBlockTranscript.{PREVCOMM,PUBCOMM,WCOMM,ZCOMM,TCOMM}_XY`
and `MinaWrapAggregationGate.COMBINE_POINTS`) with **no theorem saying they are the same points**,
and the chain publishes its 53 elements as free public-input felts that no consumer's fact reaches.

Two shapes that agree today are two shapes that will disagree later. §4 and §5 make them one object.

## ⚠⚠ WHAT THIS CHECK IS STRUCTURALLY INCAPABLE OF NOTICING — WRITTEN DOWN FIRST

`the_on_curve_check_cannot_see_provenance` is that sentence **as a theorem**, not as a comment: a
point that is on the Pallas curve and is *the wrong commitment* passes §3's on-curve leg in full,
26/26, with the substitution in place. An on-curve predicate answers *"is this a point"*; it cannot
answer *"is this THIS block's commitment"*, and the sibling cone paid months for the difference —
thirty-three wrap-transcript `lr` points were fifty SRS Lagrange bases cycled, and `onCurveQ` could
never have caught it **because cycled SRS bases are on-curve**.

⚑ So the strength of every binding below is exactly the strength of the object on its far side:

| tape elements | count | what determines them, in this tree | can an on-curve-and-wrong point survive? |
|---|---|---|---|
| `public_comm` `(x,y)` | 2 | the block's **40-element public input** + the SRS Lagrange basis (rung 5e) | **NO** — §4 |
| 2 prev, `z_comm`, 15 `w_comm` | 36 | the 47-term aggregate, hence `opening_relation_holds` | only if substituted in BOTH lists — §5, §7 |
| 7 `t_comm` chunks | 14 | `ftComm`'s own chunks, hence slot 3, hence the same opening — §6b | only if substituted in BOTH lists |
| verifier-index digest | 1 | the pinned Wrap VK's 28 commitments — `MinaWrapVkDigestChain` | only by re-deriving it from a substituted VK |

## WHAT IS AND IS NOT ESTABLISHED

  * **Kernel-clean and general in the link:** `the_wire_lane0` / `the_wire_lane1` — the 32 felts the
    deployed descriptor publishes at PI slots `[6·SK, 7·SK)` and `[7·SK, 8·SK)` ARE the absorbed
    pair's limbs, at every `j`, by `rfl`. No evaluation, no permutation run.
  * **Kernel, this block:** the shape, the on-curve leg, the blind-spot theorem, the aggregate weld,
    and `the_tape_public_comm_is_the_msm_of_the_public_input` (which is rung 5e's own theorem
    rewritten, not a second `decide` over the same 40 ladders).
  * **Compiler-trusted, said out loud:** the pairing census and the two forgery poles that run the
    27-permutation chain.
  * **CLOSED 2026-08-06 — both of the two things this file's first draft could not establish.** The
    7 `t_comm` chunks' tie to `ftComm` is §6b; the verifier-index digest is derived by
    `MinaWrapVkDigestChain`, exactly the 28 links §8 residual 1 priced. ⚠ §8's residuals 1 and 2 now
    carry what is LEFT of each rather than the whole of each — read them, and read
    `MinaWrapVkDigestChain` §7, before quoting a strength.

Import line for the CI aggregate: `import Dregg2.Circuit.Emit.MinaPhase1TapeBinding`
(rooted in `Dregg2.MinaBridgeGuards`, so a red assertion here reds a plain `lake build`).
-/
import Dregg2.Circuit.Emit.MinaPhase1Chain
import Dregg2.Circuit.Emit.MinaWrapPublicCommGate

namespace Dregg2.Circuit.Emit.MinaPhase1TapeBinding

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt chunkedComm)
open Dregg2.Circuit.Emit.MinaWrapAggregationGate (XI COMBINE_POINTS COMBINED_GOLD)
open Dregg2.Circuit.Emit.MinaRealBlockTranscript
  (VKDIGEST PREVCOMM_XY PUBCOMM_XY WCOMM_XY ZCOMM_XY TCOMM_XY fpTape)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 4000000

/-! ## §1 — THE 53, DECOMPOSED: one digest and twenty-six points.

⚑ **PROVENANCE, AT SOURCE.** Every number below is a hand transcription of
`metatheory/mina_real_block_proof.json` lines 111-118 (`verifier_index_digest`,
`phase1_prev_comm_xy`, `phase1_public_comm_xy`, `phase1_w_comm_xy`, `phase1_z_comm_xy`,
`phase1_t_comm_xy`), emitted by `metatheory/fixtures/pickles-extractors/src/main.rs` `fn transcript`
(`:958-1170`) off the committed fixture `mina_devnet_block.json` — Mina devnet block **539508**,
`state_hash 3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`. `main.rs:931-939`'s `xy_of` is
`absorb_g`'s own order: **`x` then `y`, as WHOLE base-field elements** — the tape is 53 `Fp`
elements and not one bit is packed. Nothing is emitted until `BlockVerifier::make()` (`:276`),
`accumulator_check` (`:284-289`) and `kimchi::verifier::verify == Ok(())` (`:343-356`) have all
passed, and `:1041-1045` asserts the FLAT coordinate tape reproduces the structured
`absorb_commitment` run.

⚠ **AND THE TRANSCRIPTION IS BY HAND.** No generator writes these literals and, until the Rust leg
this file ships with, nothing diffed them against the JSON. That is a provenance gap in its own
right and it is closed by `mina_phase1_tape_binding_proves.rs` §1, which compares the EMITTED WIRE
against the extractor's JSON — the emitter, not the source text, so a mistyped digit reds. -/

/-- The flat absorb stream the 27 links chunk: the phase-1 tape, the odd tail's padding zero, then
`z_comm` and the 7 `t_comm` chunks. `MinaPhase1Chain.the_chain_absorbs_the_tape_in_order` is the
statement that the chain consumes exactly this, in order. -/
def flatTape : List Nat := (fpTape ++ [0]) ++ ZCOMM_XY ++ TCOMM_XY

/-- The 52 COORDINATES, contiguous — the flat stream with the index digest and the padding zero
removed. Two per point, `x` then `y`. -/
def tapeCoords : List Nat := PREVCOMM_XY ++ PUBCOMM_XY ++ WCOMM_XY ++ ZCOMM_XY ++ TCOMM_XY

/-- The number of group elements the phase-1 transcript eats. -/
def NPTS : Nat := 26

/-- Point `i`, in the projective form the whole Pasta cone shares. -/
def tapePt (i : Nat) : Pt := (tapeCoords.getD (2 * i) 0, tapeCoords.getD (2 * i + 1) 0, 1)

/-- ⚑ Where coordinate `m` sits in the flat stream. The index digest takes slot 0, and the odd
37-element first segment forces exactly one padding zero — at slot **37**, between `w_comm[14].y`
and `z_comm.x`. A binding that ignored the pad would be off by one for every element after it. -/
def flatIx (m : Nat) : Nat := if m < 36 then m + 1 else m + 2

/-- ⚑⚑ **THE 53 ARE ONE DIGEST AND TWENTY-SIX POINTS, AND THE INDEXING IS CHECKED, NOT ASSUMED.**
The flat stream is 54 long (53 absorbed elements plus the pad), slot 0 is the verifier-index digest,
slot 37 is the pad and is zero, and every one of the 52 coordinates appears at `flatIx`. -/
theorem the_tape_is_a_digest_and_twenty_six_points :
    fpTape.length + ZCOMM_XY.length + TCOMM_XY.length = 53
    ∧ flatTape.length = 54
    ∧ tapeCoords.length = 2 * NPTS
    ∧ flatTape.getD 0 0 = VKDIGEST
    ∧ flatTape.getD 37 0 = 0
    ∧ ((List.range (2 * NPTS)).all
        (fun m => decide (flatTape.getD (flatIx m) 0 = tapeCoords.getD m 0))) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- …and the padding zero is the ONLY slot of the stream that is not a coordinate or the digest, so
`flatIx` is injective onto everything else. Without this the census above would be consistent with a
stream that repeated a coordinate and dropped one. -/
theorem the_pad_is_the_only_non_coordinate_slot :
    ((List.range 54).all (fun m =>
      decide (m = 0 ∨ m = 37
        ∨ ((List.range (2 * NPTS)).any (fun k => decide (flatIx k = m)) = true)))) = true := by
  native_decide

/-! ## §2 — THE WIRE, KERNEL-CLEAN AND GENERAL IN THE LINK.

The deployed descriptor's PI layout is `in(3) ++ out(3) ++ absorbed(2)` at `SK = 32` eight-bit
limbs, so the absorbed pair occupies `[6·SK, 8·SK)`. Both theorems are `rfl`: `drop`/`take` walk a
spine of known length and never open a limb, so this costs no evaluation and holds at EVERY link. -/

/-- ⚑ **THE `[6·SK, 7·SK)` SLICE IS THE FIRST ABSORBED ELEMENT'S LIMBS**, at every link. -/
theorem the_wire_lane0 (j : Nat) :
    ((MinaPhase1Chain.chainPIs j).drop (6 * SK)).take SK
      = (List.range SK).map (limbAt (MinaPhase1Chain.linkX j).1) := rfl

/-- ⚑ **AND `[7·SK, 8·SK)` IS THE SECOND'S.** -/
theorem the_wire_lane1 (j : Nat) :
    ((MinaPhase1Chain.chainPIs j).drop (7 * SK)).take SK
      = (List.range SK).map (limbAt (MinaPhase1Chain.linkX j).2) := rfl

/-- The 32 felts the chain publishes for flat slot `m`: link `m / 2`, lane `m % 2`. -/
def wireSlot (m : Nat) : List ℤ :=
  ((MinaPhase1Chain.chainPIs (m / 2)).drop ((6 + m % 2) * SK)).take SK

/-- ⚑⚑ **EVERY FLAT SLOT IS ON THE WIRE, AT FULL LIMB WIDTH.** The absorbed pair of link `m / 2`
carries flat element `m`, for all 54 — so `wireSlot` really is the published image of the tape and
not a re-encoding of it. ⚑ This evaluates `linkX` only (a `pairsOf` over three literal lists); it
runs no permutation. -/
theorem the_absorbed_pairs_are_the_flat_tape :
    ((List.range 54).all (fun m =>
      decide ((if m % 2 = 0 then (MinaPhase1Chain.linkX (m / 2)).1
                             else (MinaPhase1Chain.linkX (m / 2)).2)
                = flatTape.getD m 0))) = true := by
  native_decide

/-- The wire slice of flat slot `m` IS that element's limbs — the two lanes of §2 composed with the
census above, so a slot's 32 published felts are the whole 254-bit element and nothing else. -/
theorem the_wire_slot_is_the_elements_limbs (m : Nat) :
    wireSlot m
      = (List.range SK).map
          (limbAt (if m % 2 = 0 then (MinaPhase1Chain.linkX (m / 2)).1
                                else (MinaPhase1Chain.linkX (m / 2)).2)) := by
  unfold wireSlot
  rcases Nat.mod_two_eq_zero_or_one m with h | h
  · rw [h]; simpa using the_wire_lane0 (m / 2)
  · rw [h]; simpa using the_wire_lane1 (m / 2)

/-! ## §3 — EVERY ABSORBED POINT IS ON PALLAS.

Necessary, and named as necessary. `y²·z = x³ + 5·z³` over `Fp = ZMod pN` — `projOnCurveM`, the
predicate `PastaMsmOnCurve.onCurve_forces` forces in the emitted 98-constraint row and the one
`MinaWrapOpeningGate.opening_inputs_are_real_pallas_points` uses on the opening side. -/

/-- ⚑ **26/26 ON THE CURVE.** -/
theorem every_tape_point_is_on_pallas :
    ((List.range NPTS).all (fun i => projOnCurveM pN curveB (tapePt i))) = true := by native_decide

/-- …and none of them is the point at infinity, so the curve equation is not being satisfied by a
degenerate triple. `projOnCurveM` is HOMOGENEOUS of degree 3 and `(0,0,0)` satisfies it — the
absorbing state `PastaMsmOnCurve` exists to refuse. -/
theorem no_tape_point_is_the_identity :
    ((List.range NPTS).all (fun i => !isInfM pN (tapePt i))) = true := by native_decide

/-! ## §4 — ⚑⚑ THE BLIND SPOT, AS A THEOREM.

⚠ **THIS IS THE SECTION TO READ BEFORE BELIEVING §3.** -/

/-- The forgery: a point that is **on the Pallas curve** and is the **wrong commitment**. It is not
a constructed curiosity — it is `w_comm[0]` **of this very block**, so a forger needs no new point
and no search. This is the exact substitution `every_tape_point_is_on_pallas` cannot see. -/
def FORGED_PUBCOMM : Pt := tapePt 3

/-- ⚑⚑ **`the_on_curve_check_cannot_see_provenance`** — the sentence, machine-checked. The forgery
is on the curve, it is NOT `public_comm`, and the whole 26-point on-curve leg **still passes** with
it substituted at slot 2. An on-curve predicate answers *"is this a point"*; the question is
*"is this THIS block's commitment"*, and it is structurally incapable of reaching it. -/
theorem the_on_curve_check_cannot_see_provenance :
    projOnCurveM pN curveB FORGED_PUBCOMM = true
    ∧ projEqM pN FORGED_PUBCOMM (tapePt 2) = false
    ∧ ((List.range NPTS).all
        (fun i => projOnCurveM pN curveB (if i = 2 then FORGED_PUBCOMM else tapePt i))) = true := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE FALSIFIER FALSIFIES.** Both coordinates of the forgery are non-zero and differ from
the honest ones — checked, not assumed, because a control that moved a zero into a zero is exactly
how the first draft of `a_tampered_witness_coordinate_moves_the_digest` was refuted. -/
theorem the_forgery_is_a_real_displacement :
    FORGED_PUBCOMM.1 ≠ 0 ∧ FORGED_PUBCOMM.2.1 ≠ 0
    ∧ FORGED_PUBCOMM.1 ≠ (tapePt 2).1 ∧ FORGED_PUBCOMM.2.1 ≠ (tapePt 2).2.1
    ∧ FORGED_PUBCOMM = (WCOMM_XY.getD 0 0, WCOMM_XY.getD 1 0, 1) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §5 — ⚑⚑ THE BINDING THAT FORCES IDENTITY: `public_comm` IS THE MSM OF THE PUBLIC INPUT.

This is the one tape point whose value is **computed from the block's statement** rather than read
off the block's proof, so it is the one place an on-curve-and-wrong substitution is refused outright
rather than merely propagated. `MinaWrapPublicCommGate.publicComm` is
`Σ_{i<40} (−publicᵢ)·Lᵢ + 1·srs.h` over openmina's own `PreparedStatement::to_public_input` — the
protocol-state hash, the two `messages_for_next_*_proof` digests and the deferred values.

⚠ **NOT a second `decide` over the same forty ladders.** Rung 5e already proved the point; this
rewrites its theorem onto §1's decomposition and onto the wire, so the two rungs compose instead of
re-deciding. -/

/-- Tape point 2 is the transcript's `PUBCOMM_XY`, in this file's indexing. List indexing only. -/
theorem tapePt_two_is_the_transcript_public_comm :
    tapePt 2 = (PUBCOMM_XY.getD 0 0, PUBCOMM_XY.getD 1 0, 1) := by decide

/-- ⚑⚑ **`the_tape_public_comm_is_the_msm_of_the_public_input`** — the third point the phase-1
transcript absorbs, from which β, γ, α′, ζ′ and `fq_digest` all descend, **is the commitment the
kernel builds from the block's 40-element public input.** -/
theorem the_tape_public_comm_is_the_msm_of_the_public_input :
    projEqM pN MinaWrapPublicCommGate.publicComm (tapePt 2) = true := by
  rw [tapePt_two_is_the_transcript_public_comm]
  exact MinaWrapPublicCommGate.publicComm_is_the_transcript_preimage

/-- ⚑ **AND IT IS ON THE WIRE, ELEMENTWISE AT FULL LIMB WIDTH.** `public_comm.x` is flat slot 5 —
link 2's absorbed lane 1 — and `public_comm.y` is flat slot 6, link 3's lane 0. Both are 32 eight-bit
limbs of a 254-bit element, so a batch verifier compares two slices and does **no arithmetic**: no
digest, therefore no birthday bound, and a forger must match all 32 limbs. -/
theorem the_public_comm_is_on_the_wire :
    wireSlot 5 = (List.range SK).map (limbAt (tapePt 2).1)
    ∧ wireSlot 6 = (List.range SK).map (limbAt (tapePt 2).2.1) := by
  constructor <;> native_decide

/-- ⚑⚑ **AND THE ON-CURVE-AND-WRONG FORGERY MOVES THE PUBLISHED FELTS.** The same substitution §4
proved invisible to the curve check is refused here, by an equality between two independently
sourced objects: the wire (Lean's emitted PI block) and the MSM (openmina's public input). -/
theorem the_forged_public_comm_moves_the_wire :
    wireSlot 5 ≠ (List.range SK).map (limbAt FORGED_PUBCOMM.1)
    ∧ wireSlot 6 ≠ (List.range SK).map (limbAt FORGED_PUBCOMM.2.1) := by
  constructor <;> native_decide

/-! ## §6 — ⚑ ONE OBJECT, TWO CONSUMERS: the tape's points ARE the aggregate's generators.

`MinaWrapAggregationGate.COMBINE_POINTS` is `combine_commitments`' own 47-point output on this block,
and it is the list `MinaWrapXiAggregateMsm.xiAggMsmDesc` declares as ROM immediates and
`MinaWrapOpeningGate.opening_relation_holds` closes the IPA relation over. Until this section the
two lists were two hand transcriptions that happened to agree; nothing said so, and a one-digit drift
in either would have left both files green, the transcript sampling challenges from one set of
commitments while the opening argument opened another. -/

/-- The aggregate slot carrying tape point `i`: 2 recursion at 0-1, `public_comm` at 2, `z_comm` at
4, `w_comm[k]` at `11 + k`. (Slot 3 is `ft_comm` and slots 5-10, 26-46 are index, coefficient and
sigma commitments, which the phase-1 tape does not absorb.) -/
def aggSlot (i : Nat) : Nat :=
  if i ≤ 2 then i else if i = 18 then 4 else 11 + (i - 3)

/-- The 19 tape points both consumers see. -/
def SHARED : List Nat := [0, 1, 2] ++ (List.range 15).map (fun k => 3 + k) ++ [18]

theorem shared_is_nineteen_points : SHARED.length = 19 ∧ SHARED.eraseDups.length = 19 := by
  constructor <;> native_decide

/-- ⚑⚑ **`the_tape_points_are_the_aggregated_commitments`** — 19/19, elementwise. The transcript's
commitments and the aggregation's are ONE object, so a prover cannot present one set to the sponge
that samples its challenges and another to the argument that opens them. -/
theorem the_tape_points_are_the_aggregated_commitments :
    (SHARED.all (fun i => projEqM pN (tapePt i) (COMBINE_POINTS.getD (aggSlot i) Oproj))) = true := by
  native_decide

/-- …and the map is INJECTIVE, so the previous theorem is not 19 points all matching one slot. -/
theorem the_aggregate_slots_are_distinct :
    (SHARED.map aggSlot).eraseDups.length = 19 := by native_decide

/-- ⚑ **AND THE TIE IS TO THE ARGUMENT, NOT TO A NAME.** Replacing tape point 2 with the
on-curve-and-wrong forgery inside the 47-term aggregate stops it being o1-labs' own
`Σᵢ ξⁱ·Cᵢ` — the point `MinaWrapOpeningGate.opening_relation_holds` folds. So the substitution §4
proved invisible to the curve check is refused a second time, by the block's own opening. -/
theorem the_forged_public_comm_breaks_the_aggregate :
    projEqM pN (chunkedComm XI (COMBINE_POINTS.set 2 FORGED_PUBCOMM)) COMBINED_GOLD = false := by
  native_decide

/-! ## §6b — ⚑ AND THE SEVEN `t_comm` CHUNKS ARE THE ONES `ft_comm` CONSUMED.

§8 residual 2 said the 7 quotient-commitment chunks "reach the aggregate only through `ft_comm`
(slot 3) … but no theorem here says the 7 chunks the TAPE absorbs are the 7 that `ftComm`
consumed." They were a THIRD independently hand-transcribed decimal list
(`MinaWrapGroupGate.TCHUNKS`), agreeing with `TCOMM_XY` and with nothing saying so.

⚑ The route this weld opens is real and it is named at its true strength: `TCHUNKS` is what
`MinaWrapGroupGate.chunkedT_reproduces_kimchi` folds with `ζ^(2^15)` into o1-labs' own
`CHUNKED_T_GOLD`, what `ftComm_reproduces_kimchi` assembles into the `ft_comm` **o1-labs'
`SRS::verify` accepts on this block's opening proof**, and what
`MinaWrapAggregationGate.combine_slot_3_is_our_ftComm` ties to aggregate slot 3 — hence to
`opening_relation_holds`. So after this section the 14 `t_comm` coordinates sit at exactly the
strength of §6's 36: **bound to a second list which the block's own opening closes over**, and
inheriting the IPA `msm == 0` floor (P10), which is unmoved. -/

/-- Tape points 19-25 are the transcript's 7 `t_comm` chunks. -/
theorem the_tape_t_comm_chunks_are_the_ftComm_chunks :
    ((List.range 7).all (fun k =>
      projEqM pN (tapePt (19 + k)) (MinaWrapGroupGate.TCHUNKS.getD k Oproj))) = true := by native_decide

/-- …and the 7 are 7 DIFFERENT points, so the census above is not seven slots matching one chunk. -/
theorem the_seven_t_comm_chunks_are_distinct :
    ((List.range 7).all (fun k =>
      (List.range 7).all (fun l =>
        decide (k = l) || !projEqM pN (tapePt (19 + k)) (tapePt (19 + l))))) = true := by native_decide

/-- ⚑ **AND THE TIE IS TO THE ARGUMENT, NOT TO A NAME.** Substituting the on-curve-and-wrong forgery
for the first `t_comm` chunk stops the Maller assembly being the `ft_comm` o1-labs' own `SRS::verify`
accepts — so a chunk the phase-1 tape absorbs cannot be swapped for another real Pallas point of this
very block without the block's own opening refusing. -/
theorem the_forged_t_comm_chunk_breaks_the_ft_comm :
    projEqM pN
        (MinaWrapGroupGate.ftCommOf MinaWrapGroupGate.ZETA_SRS MinaWrapGroupGate.ZETA_DOM_M1
          MinaWrapGroupGate.F_TERMS (MinaWrapGroupGate.TCHUNKS.set 0 FORGED_PUBCOMM))
        MinaWrapGroupGate.FT_COMM_GOLD = false := by
  native_decide

/-- ⚑ **AND THAT FALSIFIER FALSIFIES.** The substituted chunk is on the curve, is not the chunk it
replaces, and both its coordinates are non-zero — so the refusal above is not a swap of a value for
itself, and it is not an off-curve point being caught by a curve check that is not there. -/
theorem the_t_comm_forgery_is_a_real_on_curve_displacement :
    projOnCurveM pN curveB FORGED_PUBCOMM = true
    ∧ projEqM pN FORGED_PUBCOMM (tapePt 19) = false
    ∧ FORGED_PUBCOMM.1 ≠ (tapePt 19).1 ∧ FORGED_PUBCOMM.2.1 ≠ (tapePt 19).2.1
    ∧ (tapePt 19).1 ≠ 0 ∧ (tapePt 19).2.1 ≠ 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §7 — ⚑ AND IT MOVES `fq_digest`, HENCE THE PHASE-1 ↔ PHASE-2 WELD.

The third refusal, and the one that reaches the deployed chain: `public_comm.x` is link 2's second
absorbed slot, twenty-five permutations upstream of the digest. -/

/-- ⚑ Substituting the forgery at flat slot 5 changes `fq_digest`, so link 26's outgoing lane 1 no
longer equals phase 2's tape head and the 32/32 slice comparison refuses. -/
theorem the_forged_public_comm_moves_the_digest :
    (let lx : Nat → Nat × Nat :=
       fun j => if j = 2 then ((MinaPhase1Chain.linkX 2).1, FORGED_PUBCOMM.1)
                else MinaPhase1Chain.linkX j
     let st : Nat → List Nat := fun n => Nat.rec ([0, 0, 0] : List Nat)
       (fun j ih => MinaPhase1Chain.linkStepOf PastaPoseidonFq.fpParams ih (lx j)) n
     (st 27).getD 1 0) ≠ MinaRealBlockTranscript.FQ_DIGEST := by
  native_decide

/-- ⚑ **AND THAT FALSIFIER FALSIFIES.** Link 2's second slot really is `public_comm.x`, it is
non-zero, and the value moved into it differs from it — the three checks the refuted first draft of
the sibling control lacked. -/
theorem the_digest_tamper_target_is_the_public_comm :
    (MinaPhase1Chain.linkX 2).2 = (tapePt 2).1
    ∧ (MinaPhase1Chain.linkX 2).2 ≠ 0
    ∧ (MinaPhase1Chain.linkX 2).2 ≠ FORGED_PUBCOMM.1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## §8 — RESIDUALS, NAMED WITH NUMBERS.

⚑ **1. CLOSED 2026-08-06 — THE VERIFIER-INDEX DIGEST IS DERIVED.** It was named here with its
number and the number was right: `Dregg2.Circuit.Emit.MinaWrapVkDigestChain` runs **28 more links of
`dregg-pasta-fp-chainlink::v1` — the same descriptor, no new AIR** — over the sha256-pinned
blockchain Wrap VK's 7 `sigma_comm` + 15 `coefficients_comm` + 6 selector commitments = 28 points =
56 coordinates, and `the_vk_wire_blocks_are_equal` welds link 27's outgoing lane 0 to flat slot 0 by
the same 32-felt elementwise comparison §5 uses. ⚠ **What remains is smaller and is stated there as
two theorems, not as this paragraph**: `the_index_digest_cannot_see_the_circuit_shape` (kimchi's
`digest()` binds `domain`, `public`, `zk_rows`, `shift` … to `_`, so it is a function of the 28
commitments alone) and `the_derivation_cannot_see_which_verifier_index_this_is` (the devnet
*transaction* Wrap VK runs the same 28 links perfectly and derives its own digest — the sha256 pin
is what selects, and that is a build-tree fact).

⚑ **2. CLOSED 2026-08-06 — THE 7 `t_comm` CHUNKS ARE WELDED**, §6b. They were a THIRD hand
transcription (`MinaWrapGroupGate.TCHUNKS`) agreeing with `TCOMM_XY` and with nothing saying so;
`the_tape_t_comm_chunks_are_the_ftComm_chunks` makes them one object, so they now reach `ftComm` →
aggregate slot 3 → `opening_relation_holds` — the SAME route, and the SAME strength, as residual 3's
36. ⚠ That strength is bounded by residual 3 below and by P10; do not read this as more.

⚑ **3. THE 50 COORDINATES OF §6 AND §6b ARE BOUND ONLY AGAINST A SECOND LIST.** The prev-challenge,
`z_comm`, `w_comm` and `t_comm` points are forced to be the aggregate's — and the aggregate's opening
holds — but
`COMBINE_POINTS` is itself a transcription of the same proof. A forger who substitutes an
on-curve-and-wrong point **in both lists** is refused by `opening_relation_holds` and by nothing
here; and `opening_relation_holds` inherits P10, the IPA `msm == 0` opening-soundness floor, which
is **unmoved**. The two prev-challenge commitments have a stronger determinant that is not built:
`accumulator_check`'s `comm = ⟨b_poly_coefficients(chals), srs.g⟩`, a **2^15 = 32 768-term MSM** per
commitment against `MinaWrapSrsG.SRS_G` — the reason it is named rather than done.

⚑ **4. NOTHING HERE IS AN IN-AIR CURVE GATE.** §3 is a kernel `decide` over the emitted constants,
not `PastaMsmOnCurve.onCurveGates` instantiated on the tape. The 8-constraint forced gate exists and
this file does not use it; wiring it would cost 26 × 135 columns and is the cheapest remaining rung.

⚑ **5. AND §5's FAR SIDE IS A KERNEL MSM, NOT A CIRCUIT.** `publicComm` is 40 × 255-bit ladders by
`decide`. The wire equality is real and elementwise, but what it welds the wire TO is a
kernel-evaluated constant, not a second proved instance. `MinaWrapXiAggregateMsm` is what a
circuit-side public-comm MSM would look like; it does not exist for the Lagrange basis.
-/

#assert_axioms the_wire_lane0
#assert_axioms the_wire_lane1
#assert_axioms the_wire_slot_is_the_elements_limbs
#assert_compiled the_tape_is_a_digest_and_twenty_six_points
#assert_compiled the_pad_is_the_only_non_coordinate_slot
#assert_compiled every_tape_point_is_on_pallas
#assert_compiled no_tape_point_is_the_identity
#assert_compiled the_on_curve_check_cannot_see_provenance
#assert_compiled the_forgery_is_a_real_displacement
#assert_axioms tapePt_two_is_the_transcript_public_comm
#assert_axioms the_tape_public_comm_is_the_msm_of_the_public_input
#assert_compiled shared_is_nineteen_points
#assert_compiled the_tape_points_are_the_aggregated_commitments
#assert_compiled the_aggregate_slots_are_distinct
#assert_compiled the_forged_public_comm_breaks_the_aggregate
#assert_compiled the_tape_t_comm_chunks_are_the_ftComm_chunks
#assert_compiled the_seven_t_comm_chunks_are_distinct
#assert_compiled the_forged_t_comm_chunk_breaks_the_ft_comm
#assert_compiled the_t_comm_forgery_is_a_real_on_curve_displacement
#assert_compiled the_digest_tamper_target_is_the_public_comm

-- ⚑ COMPILER-TRUSTED, and said out loud: the pairing census, the two wire evaluations and the
-- 27-permutation forgery pole, where the `decide` proof-term path overflows on a 255-bit state.
#assert_compiled the_absorbed_pairs_are_the_flat_tape
#assert_compiled the_public_comm_is_on_the_wire
#assert_compiled the_forged_public_comm_moves_the_wire
#assert_compiled the_forged_public_comm_moves_the_digest

end Dregg2.Circuit.Emit.MinaPhase1TapeBinding

/-
`KimchiStepMain` pins — §12j §12b′.

The values these are stated about are in `…Fixture`; the emission is in `…Core`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul)
open Dregg2.Circuit.Emit.KimchiRenderCompleteAdd (completeAddWitness)
open Dregg2.Circuit.Emit.KimchiCustomGates (poseidonRowCoeffs)
open Dregg2.Circuit.Emit.KimchiRenderEndoMulScalar (cFuncFp dFuncFp)
open Dregg2.Circuit.Emit.KimchiComposeStepFragment
  (TermData EndoBlock runVbm endoStep dblA addA onCurveA jOf jDbl jAdd jNeg)
open Dregg2.Circuit.Emit.KimchiVerify
  (varBaseMulConstraints completeAddConstraints endoMulConstraints endomulScalarConstraints)
open Dregg2.Circuit.Emit.PastaCurve (jacEqM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaPoseidon (rcsN)
open Dregg2.Bridge.MinaWrapFtEval0 (IDX_Z IDX_SEL IDX_W IDX_COEFF IDX_S)

set_option autoImplicit false
set_option maxRecDepth 100000

-- ── ⚑⚑ §12j — **THE THREE CLOSURES, EACH WITH THE WITNESS ITS HOLE ADMITTED** ──────────────────
-- A wire without an exhibited alternative is unverified. For each of the three: the word was a
-- `msgVal` FIXTURE the sponge ate and no row read, so a prover could absorb one value and act on
-- another — and nothing in the assembly could tell. Each block below constructs the witness that
-- bought, shows the emitted gate polynomials ACCEPTING it in the shape that had no consumer, and
-- shows the new row REFUSING it.

-- ── (a) `sg_old[0]` — `combine_split_commitments`' `~init` (`step_verifier.ml:606`) ─────────────
#guard onCurveA sgAlt && sgAlt != Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
-- the fold's FIRST add really reads `qInit`, and `qInit` really is block `oSgOld0`'s absorbed word.
#guard caRowIxOf (ipx shapeSmoke (qInit shapeSmoke)) > 0
#guard msgVar shapeSmoke oSgOld0 0 == ipx shapeSmoke (qInit shapeSmoke)
-- ⚑⚑ ACCEPTED BEFORE — with no row reading it, `sg_old[0]` sat in exactly ONE cell (the absorb row)
-- and the fold was self-consistent whatever it held. Now its class spans the sponge, the add and
-- `assert_on_curve`, which is the difference between absorbing a commitment and consuming one.
#guard (classCells posS (ipx shapeSmoke (qInit shapeSmoke))).length ≥ 4
-- ⚑⚑ REFUSED AFTER: `completeAddConstraints` — proof-systems' own, read-only — is 0 on the honest
-- row and NONZERO with the substitute in the accumulator's slot.
#guard caHolds (gridRow witS (pubS + caRowIxOf (ipx shapeSmoke (qInit shapeSmoke))))
#guard caHolds (caCellsAt (caRowIxOf (ipx shapeSmoke (qInit shapeSmoke))) 0 sgAlt) == false

-- ── (b) `combined_inner_product` — `absorb sponge Scalar advice.cip` (`:256`) ───────────────────
-- ⚑⚑ ACCEPTED BEFORE: with the word a fixture, R1's blocks were all still exactly `Ref.perm` of
-- their own absorbed state — a `Poseidon` gate constrains the permutation, never its input.
#guard (List.range (tBlocks shapeSmoke)).all (fun b =>
  let pre := spCip.states.getD b []
  let ms := spCip.msgs.getD b []
  let post := [ (pre.getD 0 0 + ms.getD 0 0) % pN, (pre.getD 1 0 + ms.getD 1 0) % pN, pre.getD 2 0 ]
  spCip.states.getD (b + 1) [] == Dregg2.Circuit.Emit.PastaPoseidon.Ref.perm post)
-- ⚑⚑ REFUSED AFTER, twice over. (i) the absorbed word IS `vCipShift`, so a claimed `cip` that is not
-- the Horner chain's output fails R8's `Shifted_value.Type1` unshift comparison…
#guard fAdd (fAdd cipForged cipForged) SHIFT_C != tS.df.ca.getLastD 0
#guard fAdd (fAdd tS.fin.cipShift tS.fin.cipShift) SHIFT_C == tS.df.ca.getLastD 0
-- …and (ii) absorbing a different word MOVES every squeeze from `u` onward, so the bulletproof
-- challenges, `check_bulletproof`'s `c` and the whole tail move with it — while β/γ/α/ζ, which are
-- squeezed BEFORE `:256`, do not. That split is upstream's own and it is why this is not a cycle.
#guard (List.range 4).all (fun c => chalOf shapeSmoke spCip c == chalOf shapeSmoke tS.sp c)
#guard ((List.range shapeSmoke.chals).drop 4).all (fun c =>
  chalOf shapeSmoke spCip c != chalOf shapeSmoke tS.sp c)
-- …and the BIT is Boolean-constrained, so the second lane is not a second free field element.
#guard fMul (cipWordOf tS).2 (cipWordOf tS).2 == (cipWordOf tS).2
#guard (fMul 2 2 == 2) == false
-- ⚑ …and since 2026-08-03 it is DERIVED and not merely Boolean: the absorbed bit IS §19 ladder 0's
-- `s_odd`, the parity the `Shifted_value.Type2` split row forces off `vCipShift`.
#guard msgVar shapeSmoke (oCip shapeSmoke) 1 == bpOdd shapeSmoke 0
#guard (cipWordOf tS).2 == tS.fin.cipShift % 2
#guard fAdd (fAdd (tS.bp.scals.getD 0 0 / 2) (tS.bp.scals.getD 0 0 / 2)) ((cipWordOf tS).2)
         == tS.fin.cipShift

-- ── (c) `delta` — `absorb sponge PC delta` (`:321`), `lhs = endo q c + delta` (`:326-327`) ──────
#guard onCurveA delAlt && delAlt != Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
#guard msgVar shapeSmoke (oDelta shapeSmoke) 0 == ipx shapeSmoke (qDel shapeSmoke)
-- ⚑⚑ ACCEPTED BEFORE: one cell, the absorb row. REFUSED AFTER: the closing `add_fast` reads it, so
-- its class spans the sponge, that row and `assert_on_curve`…
#guard (classCells posS (ipx shapeSmoke (qDel shapeSmoke))).length ≥ 4
-- …and the emitted `CompleteAdd` body is 0 on `cq + delta` and NONZERO on `cq + delta'`.
#guard caHolds (gridRow witS (pubS + caRowIxOf (ipx shapeSmoke (qLhsAcc shapeSmoke
                  shapeSmoke.ipaBlocks))))
#guard caHolds (caCellsAt (caRowIxOf (ipx shapeSmoke (qLhsAcc shapeSmoke shapeSmoke.ipaBlocks)))
                  2 delAlt) == false
-- ⚑ …and the ladder that produces `cq` multiplies by the LAST transcript squeeze, `c` (`:322`), not
-- by a challenge chosen for it: its counter chain closes on `c`'s own `to_field_checked` cell.
#guard vLhsN shapeSmoke shapeSmoke.ipaBlocks
        == vN shapeSmoke shapeSmoke.cChal shapeSmoke.emsRows
#guard tS.ipa.lhsNs.getLastD 0 == chalOf shapeSmoke tS.sp shapeSmoke.cChal
-- …and the SEGMENT-C count, which is the other half and the bigger one: the `Not_opt` prefix was
-- 58 `hmVal` fixtures and is now `sponge_after_index`'s 56 derived words plus the two app-state
-- words. **58 free → 2.**
#guard (List.range N_HM_FIX).countP (fun i =>
  (List.range N_HM_APP).any (fun a =>
    (tS.specC.ws.getD i (xv 0, 0)).1 == vHm shapeSmoke a)) == N_HM_APP
#guard (List.range N_HM_APP).all (fun a =>
  (tS.specC.ws.getD (N_IDX_WORDS + a) (xv 0, 0)).1 == vHm shapeSmoke a)
-- …and the other 56 are the plonk index, word for word, in `index_to_field_elements` order.
#guard (List.range N_IDX_WORDS).all (fun i =>
  (tS.specC.ws.getD i (xv 0, 0)) == (idxVar shapeSmoke (i / 2) (i % 2), idxVal (i / 2) (i % 2)))
#guard N_HM_APP == 2 && N_IDX_WORDS == 56 && N_HM_FIX == 58
-- …and at the SMOKE shape too there is NO free word left: every item is a wired variable, and the
-- single unpaired rate-2 lane is `tPadCell`, pinned to zero. (`…Pins18` states this as an equality
-- at both shapes.)
#guard (List.range shapeSmoke.absorbs).countP (fun b => blockRound shapeSmoke b == none)
        == 4 + tCommN shapeSmoke
-- …so the pin rows are exactly the constants, one `Generic` row per point.
#guard (msmBaseRows shapeSmoke tS.msm).length == shapeSmoke.msmTerms
#guard (ipaBaseRows shapeSmoke tS.ipa).length
        == ((List.range shapeSmoke.ipaRounds).filter
              (fun r => ipaSrc shapeSmoke r == BaseSrc.const)).length

-- ⚑ ONE σ CLASS SPANS THE SPONGE AND THE FOLD. An absorbed base's coordinate variable is read by
-- `ipaBlocks` `EndoMul` rows AND by the transcript's own absorb row — stated as an EQUALITY on the
-- class, and on how many of its cells lie in R1's row range, so a deleted wire cannot satisfy it.
-- ⚑ Since §19d (`0047cb876`) an absorbed combine commitment is a Horner ADDEND, not a ladder base:
-- the only combine base is `qT (nCombine−1)` and the running accumulator, so its class has NO
-- `EndoMul` reads. What is left: the transcript's absorb row, the INNER
-- `hash_messages_for_next_step_proof_opt`'s absorb row (fold round 0 is `sg_old[1]`), the three
-- `assert_on_curve` halves (`x` three times, `y` twice) and the fold's `CompleteAdd` operand.
-- `x`: 1 + 1 + 3 + 1 = 6; `y`: 1 + 1 + 2 + 1 = 5.
/-- **`the_absorbed_ipa_base_is_read_once_in_the_transcript`** — ⚑ FOUR `#guard`s over ONE point,
converted 2026-08-03 (`metatheory/docs/GUARD-DISCIPLINE.md`). Both coordinates of the ABSORBED fold
commitment have a class of two absorb rows, their `assert_on_curve` halves (`x` three times, `y`
twice) and the fold add that takes the commitment as its Horner addend (since §19d it is no
ladder's base), and — the half that is the actual tooth — EXACTLY ONE of those cells lies in the
transcript's row range. One cell is what makes it absorbed; zero would make it a pin, and more than
one would mean the transcript reads it somewhere nobody accounted for. Stating the four together
keeps the length and the transcript share from drifting apart. -/
theorem the_absorbed_ipa_base_is_read_once_in_the_transcript :
    ((classCells posS (ipx shapeSmoke (qT shapeSmoke absR0))).length == 6
     && (classCells posS (ipy shapeSmoke (qT shapeSmoke absR0))).length == 5
     && ((classCells posS (ipx shapeSmoke (qT shapeSmoke absR0))).filter
          (fun c => c.row < nTrans)).length == 1
     && ((classCells posS (ipy shapeSmoke (qT shapeSmoke absR0))).filter
          (fun c => c.row < nTrans)).length == 1) = true := by
  native_decide

#assert_compiled the_absorbed_ipa_base_is_read_once_in_the_transcript
-- …and a CONSTANT base has NO cell in the transcript: it is pinned, not absorbed. Its class is
-- `ipaBlocks` `EndoMul` reads + the `Inner_curve.constant` pin + segment C's `sponge_after_index`
-- absorb, because the smoke shape's one constant fold round IS plonk-index commitment 22 (§3c).
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke constR0))).length == shapeSmoke.ipaBlocks + 4
#guard ((classCells posS (ipx shapeSmoke (qT shapeSmoke constR0))).filter
          (fun c => c.row < nTrans)).length == 0
#guard idxSrc shapeSmoke 22 == some constR0
-- …and R3's bases likewise: pinned, never absorbed. ⚑ `+ 3` and not `+ 1` since §12f: the seed row
-- `add_fast base base` reads the base TWICE (cols 0,1 and 2,3) on top of the pin row and the
-- `msmChunksAt 0` `VarBaseMul` reads.
#guard ((classCells posS (mpx shapeSmoke (pT shapeSmoke 0))).filter
          (fun c => c.row < nTrans)).length == 0
#guard (classCells posS (mpx shapeSmoke (pT shapeSmoke 0))).length == msmChunksAt 0 + 3

-- ⚑⚑ **THE BITING RED CONTROL FOR #3: BENDING A SUPPLIED COMMITMENT MOVES THE MSM.** With
-- `basePts` this was impossible in both directions — the bases were unabsorbed, so a swapped
-- commitment left every challenge alone, and they were free witnesses, so nothing pinned them.
-- Swap ONE absorbed commitment and EVERY challenge moves, because the transcript sponge swallowed
-- its coordinates before the first squeeze.
#guard (List.range shapeSmoke.chals).all (fun c =>
  chalOf shapeSmoke tSwapAbs.sp c != chalOf shapeSmoke tS.sp c)
-- …the fold output moves,
#guard tSwapAbs.ipa.sums.getLastD (0, 0) != tS.ipa.sums.getLastD (0, 0)
-- …the x_hat MSM moves too (its scalars are those challenges), though its own bases did not,
#guard tSwapAbs.msm.sums.getLastD (0, 0) != tS.msm.sums.getLastD (0, 0)
-- …and it reaches all the way to `combined_inner_product` and `b(ζ)`.
#guard tSwapAbs.df.ca.getLastD 0 != tS.df.ca.getLastD 0
#guard tSwapAbs.df.accs.getLastD 0 != tS.df.accs.getLastD 0

-- ⚑ THE CONTRAST THAT MAKES IT A CENSUS AND NOT A BLANKET. A CONSTANT base is not absorbed, so
-- swapping it leaves every challenge exactly where it was — and it still moves the fold, which is
-- what the pin row exists to forbid.
#guard (List.range shapeSmoke.chals).all (fun c =>
  chalOf shapeSmoke tSwapConst.sp c == chalOf shapeSmoke tS.sp c)
#guard tSwapConst.ipa.sums.getLastD (0, 0) != tS.ipa.sums.getLastD (0, 0)

-- ⚑ …and the pin ROW is what refuses it. `Inner_curve.constant` emits `w₀ = x` ∥ `w₃ = y`, and the
-- SAME row's generic-gate body — `KimchiVerify.genericGateConstraint`, read-only — is 0 on the
-- honest coordinates and NONZERO on the swapped ones. So a prover who supplies a different SRS /
-- verifier-key point is refused, not believed.
#guard pinBody (pinRowOf constR0) (tS.ipa.bases.getD constR0 (0, 0)) == 0
#guard (pinBody (pinRowOf constR0) (tSwapConst.ipa.bases.getD constR0 (0, 0)) == 0) == false
-- …and the swap really did change the point, so the red control is not testing equality with itself.
#guard tSwapConst.ipa.bases.getD constR0 (0, 0) != tS.ipa.bases.getD constR0 (0, 0)
#guard tSwapAbs.ipa.bases.getD absR0 (0, 0) != tS.ipa.bases.getD absR0 (0, 0)

-- ── §12b′ — ⚑ A SUPPLIED POINT IS NOW CHECKED ON THE CURVE (§7b, #3's second residue) ──────────
-- Every kimchi curve gate constrains the ADDITION ARITHMETIC and nothing else: `EndoMul`'s
-- polynomials hold for any `(x, y)` in the field. Upstream never has to say so, because a supplied
-- point arrives through `Inner_curve.typ`, whose `check` IS `assert_on_curve`
-- (`snarky_curve.ml:212-229`). This file read the previous proof's commitments in as bare
-- coordinate variables. The exhibit below is an off-curve one, and it passed.

-- The exhibited point is genuinely OFF the curve, and the honest one is on it — same `x`.
#guard onCurveA honPt
#guard onCurveA offPt == false
#guard offPt.1 == honPt.1 && offPt.2 != honPt.2
-- …and every honest supplied point is on the curve, so the check is SATISFIABLE as well as
-- refutable, at both shapes.
#guard (absRoundList shapeSmoke).all (fun r => onCurveA (tS.ipa.bases.getD r (0, 0)))
#guard (Dregg2.Bridge.MinaStepPrevCommitments.ALL_XY).all onCurveA

-- ⚑⚑ **THE EXHIBIT: EVERY CURVE GATE ACCEPTS THE OFF-CURVE POINT.** `KimchiVerify`'s read-only
-- transcriptions of proof-systems' own `EndoMul` and `CompleteAdd` polynomials are ZERO on every
-- one of those rows of the BENT assembly's composed grid. That is the hole, stated on the emitted
-- object: the fold gadget never looks at membership, so the whole of R4 was satisfied.
#guard ((List.range rowsOff.length).filter
          (fun i => (rowsOff.getD i default).kind == KGateType.endoMul)).all
  (fun i => (endoMulConstraints (R := ZMod pN) (KimchiRenderEndoMul.endo : ZMod pN)
      ((gridRow witOff i).map (fun n => (n : ZMod pN)))
      ((gridRow witOff (i + 1)).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))
#guard ((List.range rowsOff.length).filter
          (fun i => (rowsOff.getD i default).kind == KGateType.completeAdd)).all
  (fun i => (completeAddConstraints (R := ZMod pN)
      ((gridRow witOff i).map (fun n => (n : ZMod pN)))).all (fun z => decide (z = 0)))

-- ⚑⚑ **AND THE NEW ROWS REFUSE IT.** The same grid, the same rows: `assert_on_curve`'s own
-- `Generic` body is ZERO on the honest assembly and NONZERO on the bent one. Refused where it was
-- accepted, on the emitted object rather than in the value layer.
#guard (List.range nOnCRows).all (fun k => genBodyAt rowsS witS pubS (pubS + onCRow0 + k) == 0)
#guard ((List.range nOnCRows).all (fun k => genBodyAt rowsOff witOff 0 (onCRow0 + k) == 0)) == false
-- …and it is the `assert_square` half that goes red and NOT the `x²`/`x³` ones: the bend was in
-- `y`, which enters `assert_on_curve` only through `y·y − x³ − b`. That is the first point's THIRD
-- half, so it lands in row `onCRow0 + 1`, and row `onCRow0` — the two halves that read `x` alone —
-- still holds. A control that reddened both rows would be measuring the re-run, not the check.
#guard genBodyAt rowsOff witOff 0 onCRow0 == 0
#guard (genBodyAt rowsOff witOff 0 (onCRow0 + 1) == 0) == false

-- ⚑ EVERY `Generic` ROW OF THE HONEST ASSEMBLY SATISFIES ITS OWN BODY, on the composed grid — the
-- one gate family §12's sweeps did not evaluate. (The `pubS` public rows are excluded: a public row
-- is `w₀ − pᵣ = 0` and the `pᵣ` term is the prover's, `generic.rs:297-304`.)
#guard ((List.range nRowsS).filter (fun i => (rowsS.getD i default).kind == KGateType.generic)).all
  (fun i => genBodyAt rowsS witS pubS (pubS + i) == 0)

-- ⚑ THE ROWS ARE THE CENSUS, stated as equalities. One `assert_on_curve` per ABSORBED base — three
-- `Generic` halves each, packed two to a row — and NOT ONE for a constant base, which is pinned
-- coordinate-for-coordinate instead. A deleted check moves both numbers.
-- ⚑ …and since §19d a FOURTH class: `bullet_reduce`'s `nBulletPairs` `endo_inv` witnesses, which
-- `Scalar_challenge.endo_inv` `exists`-es through `Inner_curve.typ` exactly as a commitment
-- arrives. 58 → 73 at the committed shape; `shapeSmoke` has no bullet pairs, so its number is
-- unmoved and the smoke fixtures exercise NONE of the fifteen.
-- ⚑ …and since `16b6d9b8a` a FOURTH non-round point, segment D's own `G` (`vGaX`): 73 → 74.
#guard nOnC shapeSmoke
        == (absRoundList shapeSmoke).length + tCommN shapeSmoke + 4 + nBulletPairs shapeSmoke
#guard nOnC shapeStep == 48 + 7 + 4 + 15 && nBulletPairs shapeStep == 15
        && nBulletPairs shapeSmoke == 0
#guard nOnCRows == (3 * nOnC shapeSmoke + 1) / 2
#guard (onCurveRows shapeStep).length == (3 * 74 + 1) / 2
-- ⚑ …and the four non-round points are `sg_old[0]`, `delta`, §19's `G` (`vGx`) and segment D's
-- own `G` (`vGaX`, the accumulator the record publishes), at the tail of the checked list and over
-- the very variables the fold's `~init`, the `cq + delta` add, §19's `add_fast` and the outer hash
-- read.
#guard onCVar shapeStep (48 + 7) == (ipx shapeStep (qInit shapeStep), ipy shapeStep (qInit shapeStep))
#guard onCVar shapeStep (48 + 8) == (ipx shapeStep (qDel shapeStep), ipy shapeStep (qDel shapeStep))
#guard onCVar shapeStep (48 + 9) == (vGx shapeStep, vGy shapeStep)
        && onCVar shapeStep (48 + 10) == (vGaX shapeStep, vGaY shapeStep)
        && onCVar shapeStep (48 + 11)
             == (ipx shapeStep (qEndoInv shapeStep 0), ipy shapeStep (qEndoInv shapeStep 0))
        && onCVar shapeStep (48 + 25)
             == (ipx shapeStep (qEndoInv shapeStep 14), ipy shapeStep (qEndoInv shapeStep 14))
#guard Dregg2.Bridge.MinaStepPrevCommitments.onCurve
         Dregg2.Bridge.MinaStepPrevCommitments.SG_OLD0_XY
#guard Dregg2.Bridge.MinaStepPrevCommitments.onCurve
         Dregg2.Bridge.MinaStepPrevCommitments.DELTA_XY
#guard onCurveA tS.gXY
-- …and the checked variables ARE the fold's own addend coordinates, not a fresh copy: `x`'s class
-- holds the three `assert_on_curve` halves that read it, both absorb rows and the fold add (§19d).
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke absR0))).length == 6
#guard (classCells posS (ipy shapeSmoke (qT shapeSmoke absR0))).length == 5
-- …and a CONSTANT base's class gains NOTHING from §7b — pinned, not checked, which is upstream's
-- own split (`Inner_curve.constant` is a literal and carries no `check`). Its `ipaBlocks + 2` is the
-- `EndoMul` reads, the pin row and segment C's index absorb, and no `assert_on_curve` half.
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke constR0))).length == shapeSmoke.ipaBlocks + 4
-- …and the two intermediates really are `x²` and `x³` of that point.
#guard tS.ipa.bases.getD absR0 (0, 0) == honPt
#guard fMul honPt.1 honPt.1 == fMul honPt.1 honPt.1
#guard fMul (fMul honPt.1 honPt.1) honPt.1 != 0

end Dregg2.Circuit.Emit.KimchiStepMain

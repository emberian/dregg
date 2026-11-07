/-
`KimchiStepMain` pins — §15.

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

/-! ## §15 — the LADDER is monotone, REACHED BY THE EMITTER, and each rung really adds its
sub-circuit.

⚑ THE REACHED-BY-THE-EMITTER PINS ARE THE FIRST BLOCK, and they exist because of a measured defect:
`cipRows` once lived in a function `rungRows` never called, so `r5_full` was proved seven times
without the `combined_inner_product` chain its own commit subject named, and `vCa cipEvals` reached
the public tie as a FREE variable — while every σ probe, every control and every public-input leg
passed. A length identity per rung, stated as the SUM OF ITS OWN SUB-LISTS, is what turns that from
a silence into a red; `stepRows == rungRows .opening` closes the same hole on the other emitter. -/

-- Each rung IS the rung below plus exactly its own sub-circuit's rows.
#guard (rungRows tS .challenges true).length
        == (rungRows tS .transcript true).length + (endoConstRow shapeSmoke).length
           + ((List.range shapeSmoke.chals).flatMap (challengeRows shapeSmoke tS.sp true)).length
#guard (rungRows tS .msm true).length
        == (rungRows tS .challenges true).length + (msmRows shapeSmoke tS.msm true).length
           + (ftcRows shapeSmoke tS.ftw tS.ftc true).length
#guard (rungRows tS .ipa true).length
        == (rungRows tS .msm true).length + (ipaRows shapeSmoke tS.ipa true).length
#guard (rungRows tS .full true).length
        == (rungRows tS .ipa true).length + (deferredRows shapeSmoke true).length
           + (sgEvalRows shapeSmoke FT_OMEGA true).length
           + (branchRows shapeSmoke true).length + (xiDefRows shapeSmoke tS.defc true).length
           + (cipRows shapeSmoke true).length + (closingRows shapeSmoke).length
#guard (rungRows tS .ftEval0 true).length
        == (rungRows tS .full true).length + (ftRows shapeSmoke tS.ft true).length
#guard (rungRows tS .absorb true).length
        == (rungRows tS .ftEval0 true).length + (absRows tS true).length
#guard (rungRows tS .finalize true).length
        == (rungRows tS .absorb true).length + (finRows shapeSmoke tS.ft tS.fin true).length
-- ⚑ §19 — `group_map`, the four `scale_fast2`s, `rhs` and `equal_g`.
#guard (rungRows tS .opening true).length
        == (rungRows tS .finalize true).length + (bpRows shapeSmoke tS.bp true).length
#guard (bpRows shapeSmoke tS.bp true).length > 0 && (gmRows shapeSmoke true).length > 0
-- …and the OTHER emitter (`stepRows`, the schedule) is the top rung, row for row.
#guard (stepRows tS true).map (fun r => r.kind) == (rungRows tS .opening true).map (fun r => r.kind)
#guard (stepRows tS true).length == (rungRows tS .opening true).length
-- …and each sub-list is NON-EMPTY, so "the sum matches" cannot be satisfied by a vanished rung.
#guard (cipRows shapeSmoke true).length > 0 && (deferredRows shapeSmoke true).length > 0
/-- ⚑ `cipRows`' own length as a CLOSED FORM of what it emits, so the mux cannot quietly lose a
masked step: the `acc₀ = 0` pin, one A-row per column, then the B-fold packed two halves to a row at
`2` halves per `Some` step and `5` per `Maybe` one, then two probes and the `cip` bit's booleanity
row with its probe. Gains a NAME, not a ∀ — `shapeSmoke` is the one assembly this file measures. -/
theorem cipRows_length_closed_form :
    (cipRows shapeSmoke true).length
      = 1 + shapeSmoke.cipEvals
        + (2 * (shapeSmoke.cipEvals - N_CIP_MASKED) + 5 * N_CIP_MASKED + 1) / 2
        + 4 := by native_decide
#assert_compiled cipRows_length_closed_form

/-- …and the mux is what makes it longer than the unconditional fold would be. Stated as the DELTA
against the shape this rung replaced — `1 + cipEvals` A-rows, `cipEvals` unconditional B-rows and
the three-row trailer — because four rows is the whole cost of this rung. -/
theorem cipRows_length_is_the_unmuxed_shape_plus_four :
    (cipRows shapeSmoke true).length
      = (1 + shapeSmoke.cipEvals + shapeSmoke.cipEvals + 3) + 4 := by native_decide
#assert_compiled cipRows_length_is_the_unmuxed_shape_plus_four
-- ⚑ …and §8i's own sub-list, which is the rung this file last added. Its length is stated as the
-- CLOSED FORM of what it emits — the `zetaw` row, ζω's `bRounds − 1` squaring halves packed two to
-- a row, `N_EC · bRounds` fused factor rows and `N_EC` probes — so a ladder that quietly loses a
-- slot or a point reds here rather than shrinking silently.
#guard (sgEvalRows shapeSmoke FT_OMEGA true).length
        == 1 + (shapeSmoke.bRounds - 1 + 1) / 2 + N_EC * shapeSmoke.bRounds + N_EC
#guard (ftRows shapeSmoke tS.ft true).length > 0 && (absRows tS true).length > 0
#guard (finRows shapeSmoke tS.ft tS.fin true).length > 0 && (endoConstRow shapeSmoke).length > 0
#guard (xiDefRows shapeSmoke tS.defc true).length > 0
        && (rDefRows shapeSmoke tS.defc true).length > 0
-- ⚑ …and R7's own sub-list really is the FOUR segments, §3c's index pins and §8g's `r` chain.
-- ⚑ `idxDigestRows` is now EMPTY (2026-08-03) and is kept as a summand precisely so that stays
-- visible: the digest permutation was a 29th over 56 words where Mina performs 28.
-- Stated as an equality over every summand, so a dropped sub-list reds here.
#guard (absRows tS true).length
        == (segRows (baseSegA shapeSmoke) tS.specA tS.segA true).length
           + (segRows (baseSegB shapeSmoke) tS.specB tS.segB true).length
           + (idxConstRows shapeSmoke).length
           + (segRows (baseSegC shapeSmoke) tS.specC tS.segC true).length
           + (segRows (baseSegD shapeSmoke) tS.specD tS.segD true).length
           + (idxDigestRows shapeSmoke true).length
           + (rDefRows shapeSmoke tS.defc true).length
-- ⚑ …and segment D is NON-EMPTY: TWO init pin rows (it starts from a fresh sponge), `nbD` absorb
-- blocks (13 rows each) and NO squeeze block at all — its single squeeze is the last absorb block's
-- own permutation — plus the one probe on the state that squeeze reads.
-- ⚠ **THIS READ `13·nbD + 1` WITH "NO init pin row, which is what `Sponge.copy` means here" UNTIL
-- 2026-08-07.** `segRows` emits the two init rows exactly when `copyFrom.isNone`, and segment D's
-- `copyFrom` is now `none` because it runs its own `sponge_after_index` over the instance's own
-- wrap key (`step.rs:2718`). `nbD` also went 4 → 32 at this shape for the same reason, so the
-- absolute figure moved 53 → 419; the FORM is what this pins.
#guard (segRows (baseSegD shapeSmoke) tS.specD tS.segD true).length
        == 2 + 13 * nbD shapeSmoke + 1
-- ⚑ …and NO segment is a copy any more. `tS.specD.copyFrom.isSome` was the single most explicit
-- "segment D is a copy" proposition in the tree; it is `false` now and this is where that is said.
#guard tS.specD.copyFrom.isNone && tS.specA.copyFrom.isNone && tS.specC.copyFrom.isNone
-- …and §3c's digest sub-list is EMPTY while its pin sub-list is one `Generic` row per index
-- commitment this shape must hold itself.
#guard (idxDigestRows shapeSmoke true).length == 0
#guard (idxConstRows shapeSmoke).length == (idxOwn shapeSmoke).length

-- ⚑ **WHICH RUNG BINDS WHICH MULTIPLIER** (#10's honest residue, machine-checked). ξ's chain rides
-- with R5 because its source is a STATEMENT word, so `vDLift 0` has a computing row from `r5_full`
-- up. `r`'s source is the fr-sponge's second squeeze, an R7 variable, so `vDLift 1` has NO computing
-- row below `r7_absorption` and has one at and above it. Stated as a pin so the ladder position is
-- a fact rather than a sentence in a header.
-- ⚑ THE SEGMENT-C DIGEST's LADDER POSITION, stated the same way. It is a public word from `r5_full`
-- up, but the rows that COMPUTE it are R7's, so below `r7_absorption` its class is the closing tie
-- and nothing else — a free witness, exactly as `vDLift 1` is. Equalities, not floors.
#guard (classCells (posAt .full) (hmDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .ftEval0) (hmDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .absorb) (hmDigestVar shapeSmoke)).length == 3
#guard (classCells (posAt .opening) (hmDigestVar shapeSmoke)).length == 3
-- ⚑ …and the OUTER digest reads exactly the same way, so segment D inherits the same caveat and
-- gets it said rather than assumed.
#guard (classCells (posAt .full) (hmOutDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .ftEval0) (hmOutDigestVar shapeSmoke)).length == 1
#guard (classCells (posAt .absorb) (hmOutDigestVar shapeSmoke)).length == 3
#guard (classCells (posAt .opening) (hmOutDigestVar shapeSmoke)).length == 3
-- ⚑ **`G`'s LADDER POSITION, and it is the honest statement of what segment D bought.** From
-- `r4_ipa` (where `assert_on_curve` lands) to `r6_ft_eval0`, `G`'s whole class is those three
-- halves — a witness the circuit checks is on the curve and reads NOWHERE ELSE. `r7_absorption` is
-- the rung that adds the absorption, and it adds exactly ONE cell per coordinate. Below `r4` it has
-- no cell at all, which is what "zero occurrences" meant before this rung.
#guard (classCells (posAt .msm) (vGx shapeSmoke)).length == 0
#guard (classCells (posAt .ipa) (vGx shapeSmoke)).length == 3
#guard (classCells (posAt .ftEval0) (vGx shapeSmoke)).length == 3
-- ⚑ Since `16b6d9b8a` segment D absorbs its OWN `G` (`vGaX`, the record's accumulator), so the
-- absorption cell moved off §19's solved `G`: `vGx` gains nothing at `r7`, and `vGaX` gains the one
-- cell instead (its three halves plus the absorb row).
#guard (classCells (posAt .absorb) (vGx shapeSmoke)).length == 3
#guard (classCells (posAt .ipa) (vGaX shapeSmoke)).length == 3
#guard (classCells (posAt .absorb) (vGaX shapeSmoke)).length == 4
#guard (classCells (posAt .opening) (vGaX shapeSmoke)).length == 4
-- ⚑ …and §19 adds the FOURTH (the fifth before `16b6d9b8a`):
-- `Ops.add_fast challenge_polynomial_commitment b_u`
-- (`step_verifier.ml:333`), which is `G`'s first occurrence inside `check_bulletproof`
-- itself rather than in the statement hash.
#guard (classCells (posAt .opening) (vGx shapeSmoke)).length == 4
-- ⚠ ⚑ **AND `index_digest` HAS THE SAME LADDER POSITION, so say it rather than let the retirement
-- read as unconditional.** §3c's derivation lives in R7 — the permutation is squeezed off segment
-- C's own state, and segment C is an R7 sub-circuit — while R1 ABSORBS the result at block 0. So
-- from `r1_transcript` to `r6_ft_eval0` `vIdxD 0` is a free witness the transcript eats (class = the
-- absorb row alone), and it is DERIVED at `r7_absorption` and `r8_finalize`. ⚑ THREE since
-- 2026-08-07: `vIdxD` names segment C's block-28 state lane, whose class is that block's own absorb
-- row, block 27's closing `Zero`, and the σ probe on the state.
-- ⚠ **IT WAS FOUR, AND THE FOURTH CELL WAS SEGMENT D READING SEGMENT C'S STATE.** While `hmOutSpec`
-- carried `copyFrom`, segment D's block-0 addend row read this very lane, so segment C's index
-- boundary had a consumer in the OUTER hash. Segment D now runs its own `sponge_after_index` over
-- the instance's own wrap key (`step.rs:2718`) and reads nothing of segment C's — which is the
-- stratification `KimchiStepWrapChain`'s pass order depends on, measured here as a cell count.
-- The reportable object is the full assembly; the lower rungs are sub-circuits and this is where
-- that costs something.
/-- **`the_index_digest_word_class_grows_with_the_rung`** — ⚑ FOUR `#guard`s that were four
instances of ONE fact, converted 2026-08-03 (`metatheory/docs/GUARD-DISCIPLINE.md`). The claim is
not "this rung has 4 cells"; it is that `vIdxD 0`'s class GROWS as sub-circuits land — 1 at
`r1_transcript`, still 1 at `r6_ftEval0`, then 3 once `r7_absorb` wires the block-28 state lane and
3 again at `r9_opening`. Written as ONE statement over the rungs in order, a rung whose count FELL
while another ROSE can no longer pass, which four independent equalities allowed. -/
theorem the_index_digest_word_class_grows_with_the_rung :
    ((classCells (posAt .transcript) (vIdxD shapeSmoke 0)).length == 1
     && (classCells (posAt .ftEval0) (vIdxD shapeSmoke 0)).length == 1
     && (classCells (posAt .absorb) (vIdxD shapeSmoke 0)).length == 3
     && (classCells (posAt .opening) (vIdxD shapeSmoke 0)).length == 3) = true := by
  native_decide

#assert_compiled the_index_digest_word_class_grows_with_the_rung
-- …and the plonk-index pin rows are R7's too, so the same reading applies to the 56 absorbed words.
#guard (classCells (posAt .ftEval0) (vIdxX shapeSmoke 27)).length == 0
#guard (classCells (posAt .absorb) (vIdxX shapeSmoke 27)).length == 2

-- ⚑ **§6b's LADDER POSITION, and it is the honest half of the retirement.** `ft_comm`'s scalars are
-- R6's OWN cells, and R6's rows arrive at `r6_ft_eval0`. So from `r3_msm` to `r5_full` the `perm`
-- and `ζ^n` cells are FREE WITNESSES — read by §6b's `Shifted_value.Type2` split row and by NOTHING
-- else — and they are DERIVED at `r6_ft_eval0` and above. Stated the way `index_digest`'s and
-- `vDLift 1`'s are, because the reportable object is the full assembly and the lower rungs are
-- sub-circuits. Equalities, not floors.
-- (the `permV` profile is one statement, below.)
-- ⚑ THREE, not four, since `permClaimed` was deleted (2026-08-03): R6 used to close with
-- `eEq perm permClaimed`, a row whose only novel operand was a variable no other row read — an
-- assert that could not fail. Its deletion took exactly one cell out of `perm`'s class.
/-- **`the_permutation_word_class_per_rung`** — the same conversion for `perm`: 1 cell at `r3_msm`
and at `r4_ipa`, THREE at `r6_ftEval0`. ⚑ Three and not four since `permClaimed` was deleted
(2026-08-03) — R6 used to close with `eEq perm permClaimed`, a row whose only novel operand was a
variable no other row read, i.e. an assert that could not fail. Its deletion took exactly one cell
out of this class, and that is the motion this statement exists to hold: a FOURTH here would be the
vacuous row coming back. -/
theorem the_permutation_word_class_per_rung :
    ((classCells (posAt .msm) tS.ftw.permV).length == 1
     && (classCells (posAt .ipa) tS.ftw.permV).length == 1
     && (classCells (posAt .ftEval0) tS.ftw.permV).length == 3) = true := by
  native_decide

#assert_compiled the_permutation_word_class_per_rung
-- ⚑ …and since §21 the `ζ^n` cell carries ONE MORE CELL AT EVERY RUNG FROM `r3_msm` UP than `perm`
-- does: it is Wrap statement WORD 2/3 as well as `ft_comm`'s scalar, so the x_hat ladder's own
-- terminal counter lands in its class. That asymmetry between the two §6b scalars is exactly §21 —
-- `perm` is word 4 and its cell there is `vPermShift`, R8's statement word, not this derived one.
#guard (classCells (posAt .msm) tS.ftw.zetaV).length == 2
#guard (classCells (posAt .ipa) tS.ftw.zetaV).length == 2
#guard (classCells (posAt .ftEval0) tS.ftw.zetaV).length == 4
-- …and `sigma_comm_last`'s `Inner_curve.constant` pin is R7's (§3c), so term 0's BASE reads the same
-- way: the ladder, the doubling and the odd-branch add at `r3_msm`, plus the pin and segment C's
-- absorb from `r7_absorption`.
#guard (classCells (posAt .msm) (vIdxX shapeSmoke 6)).length == FTC_CHUNKS + 3
#guard (classCells (posAt .absorb) (vIdxX shapeSmoke 6)).length == FTC_CHUNKS + 5
-- ⚑ …whereas `t_comm`'s own words are ABSORBED at `r1_transcript` and CONSUMED from `r3_msm` up —
-- no ladder position at all, which is what makes the retirement unconditional for them.
#guard (classCells (posAt .transcript) (vTcX shapeSmoke 0)).length == 1
#guard (classCells (posAt .msm) (vTcX shapeSmoke 0)).length == 2
#guard (classCells (posAt .ipa) (vTcX shapeSmoke 0)).length == 5

-- ξ's class is COMPLETE at `r5_full`: nothing above r5 adds a cell to it, because its chain is
-- already there. (A floor `≥ 2` would pass here even with the chain deleted — the fold's own reads
-- alone give 47 — so this is stated as an EQUALITY against the top rung.)
#guard (classCells (posAt .full) (vDLift shapeSmoke 0)).length
        == (classCells (posAt .opening) (vDLift shapeSmoke 0)).length
#guard (classCells (posAt .full) (vDLift shapeSmoke 0)).length == shapeSmoke.cipEvals + 2
-- r's is NOT: below the fr-sponge it is exactly the fold's `cipEvals` reads and NO defining row;
-- `r7_absorption` is the rung that adds the chain's lift row and its probe.
#guard (classCells (posAt .full) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals
#guard (classCells (posAt .ftEval0) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals
#guard (classCells (posAt .absorb) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 2
#guard (classCells (posAt .opening) (vDLift shapeSmoke 1)).length == shapeSmoke.cipEvals + 3
-- …and the ξ chain's `EndoMulScalar` rows are in r5 while the r chain's are not.
-- ⚑ **PLUS `RNG_DOMLOG2_ROWS` FROM r5 UP (2026-08-03)**, and the `+ 1` is the whole point of it:
-- `Branch_data.typ`'s `~assert_16_bits` (`per_proof_witness.ml:166-168`) is a `to_field_checked` at
-- `~num_bits:16`, i.e. ONE `EndoMulScalar` row, not a `chalBits`-wide chain. A count that stayed a
-- multiple of `emsRows` would mean the 16-bit chain is not there.
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 1) * shapeSmoke.emsRows + RNG_DOMLOG2_ROWS
#guard ((rungRows tS .ftEval0 true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 1) * shapeSmoke.emsRows + RNG_DOMLOG2_ROWS
-- …and R7 adds TWO: `r_actual`'s own chain and the `assert_128_bits` of its high part.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 3) * shapeSmoke.emsRows + RNG_DOMLOG2_ROWS
-- ⚑ …and R8 adds TWO MORE — the THIRD `lowest_128_bits`, `xi_actual`'s, both parts (§12c′). This is
-- the pin that would have caught the hole: before it landed, R8's EndoMulScalar delta was ZERO and
-- the finalize rung split a field element with nothing constraining either half.
#guard ((rungRows tS .finalize true).filter (fun r => r.kind == KGateType.endoMulScalar)).length
        == (2 * shapeSmoke.chals + 5) * shapeSmoke.emsRows + RNG_DOMLOG2_ROWS

#guard (rungRows tS .full true).length < (rungRows tS .ftEval0 true).length
#guard (rungRows tS .ftEval0 true).length < (rungRows tS .absorb true).length
#guard (rungRows tS .absorb true).length < (rungRows tS .finalize true).length
-- R8 over R7 is scalar arithmetic + the boolean gadgets + the two `assert_128_bits` chains of its
-- own `lowest_128_bits` (§12c′) — so `Generic`/`Zero`/`EndoMulScalar` and NOT ONE CURVE GATE. It
-- was `Generic`/`Zero` only until the third high chain landed; that is a stated change, not drift.
#guard ((rungRows tS .finalize true).drop (rungRows tS .absorb true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero
                  || r.kind == KGateType.endoMulScalar)
#guard (List.range 4).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul, .poseidon].getD i .zero
  ((rungRows tS .finalize true).filter (fun r => r.kind == k)).length
    == ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length)
-- R6 is `Generic`-only (it is scalar arithmetic; every other gate family is unchanged by it).
#guard ((rungRows tS .ftEval0 true).drop (rungRows tS .full true).length).all
        (fun r => r.kind == KGateType.generic || r.kind == KGateType.zero)
-- R7 adds `Poseidon` (11 rows per permutation, upstream's own run length) and — since §8g — exactly
-- ONE further `to_field_checked` chain, `r_actual`'s. No curve gate, no second chain.
#guard ((rungRows tS .absorb true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * (tBlocks shapeSmoke + tS.specA.blocks + tS.specB.blocks + tS.specC.blocks
                 + tS.specD.blocks)
#guard ((rungRows tS .full true).filter (fun r => r.kind == KGateType.poseidon)).length
        == 11 * tBlocks shapeSmoke
#guard (List.range 4).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul, .zero].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    ≥ ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
#guard (List.range 3).all (fun i =>
  let k : KGateType := [KGateType.completeAdd, .varBaseMul, .endoMul].getD i .zero
  ((rungRows tS .absorb true).filter (fun r => r.kind == k)).length
    == ((rungRows tS .ftEval0 true).filter (fun r => r.kind == k)).length)
-- …and the compiled ft program is a real program, not a stub.
#guard ftS.fp.prog.size ≥ 900
#guard (aHalfSlots ftS.fp.prog).length ≥ 700

end Dregg2.Circuit.Emit.KimchiStepMain

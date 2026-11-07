/-
`KimchiStepMain` pins — §12e.

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

-- ── §12e — ⚑ `Common.ft_comm`'s MSM, AND `t_comm` STOPS BEING FREE (#5's head, retired) ────────
-- The previous rung derived `sponge_after_index` and left 45 of R1's 142 absorbed words free,
-- naming `t_comm`'s 14 as the ones that could only leave the list by being CONSUMED. §6b consumes
-- them, and everything below is stated on the EMITTED object rather than on the intention.

-- ⚑ THE SHAPE IS `common.ml`'s, counted. Eight `scale_fast2`s at `chunks_needed ~num_bits:254 = 51`
-- five-bit chunks (`plonk_curve_ops.ml:69-70,254-257`), and the `tCommN` cap does NOT bind at the
-- committed shape — so no quotient chunk silently stays a free witness there.
#guard tCommN shapeStep == N_TCOMM
#guard tCommN shapeStep == Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.length
#guard ftcTerms shapeStep == 8
#guard tCommN shapeSmoke == 3 && ftcTerms shapeSmoke == 4
#guard FTC_CHUNKS == (254 + 4) / 5 && 5 * FTC_CHUNKS == 255
-- …and it is a DIFFERENT width from R3's, which is exactly what #2's warning is about.
#guard FTC_CHUNKS != msmChunksAt 5

-- ⚑ THE ROW CENSUS, as an equality over its own sub-lists: the two `Shifted_value.Type2` splits,
-- `ftcTerms` ladders and `common.ml`'s add chain. A vanished sub-list moves this number.
#guard (ftcRows shapeSmoke tS.ftw tS.ftc true).length
        == (ftcScalRows shapeSmoke tS.ftw true).length
           + (ftcNZeroRows shapeSmoke).length
           + ftcTerms shapeSmoke * (ftcTermRows shapeSmoke tS.ftc true 0).length
           + (ftcAddRows shapeSmoke tS.ftc true).length
-- ⚑ …and `plonk_curve_ops.ml:158`'s counter seed is pinned for every one of them (§12f): one
-- `Generic` half per `scale_fast2`, packed two to a row.
#guard (ftcNZeroRows shapeSmoke).length == (ftcTerms shapeSmoke + 1) / 2
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (classCells posS (ftcN shapeSmoke k 0)).length == 2)
-- …one term is `2·FTC_CHUNKS` chunk rows, the doubling and odd-branch `add_fast`s, two probes and
-- the four `Generic` rows of the top-bit assert, the negate and `G.if_`'s six halves.
#guard (ftcTermRows shapeSmoke tS.ftc true 0).length == 2 * FTC_CHUNKS + 8
#guard (ftcAddRows shapeSmoke tS.ftc true).length == 2 * (tCommN shapeSmoke - 1) + 5
#guard (ftcRows shapeSmoke tS.ftw tS.ftc true).length == 455
-- …and `common.ml`'s own operation count: `tCommN + 1` `Ops.add_fast`s, `ftcTerms` scales.
#guard tS.ftc.addCells.length == tCommN shapeSmoke + 1
#guard tS.ftc.terms.length == ftcTerms shapeSmoke
#guard tS.ftc.adds.length == tCommN shapeSmoke

-- ⚑⚑ **`t_comm`'s COORDINATES ARE THE TRANSCRIPT'S WORDS AND THE MSM's OPERANDS.** One σ class
-- spanning `Poseidon`, `assert_on_curve` and `VarBaseMul`. The Horner SEED `t_comm[n−1]` is term 1's
-- base, so its class is the whole ladder; a chunk that is only an ADDEND still has five cells.
-- Equalities, so a deleted leg reds rather than passing a floor.
#guard (classCells posS (vTcX shapeSmoke (tCommN shapeSmoke - 1))).length == FTC_CHUNKS + 7
#guard (classCells posS (vTcY shapeSmoke (tCommN shapeSmoke - 1))).length == FTC_CHUNKS + 6
#guard (classCells posS (vTcX shapeSmoke 0)).length == 5
#guard (classCells posS (vTcY shapeSmoke 0)).length == 4
#guard ((classCells posS (vTcX shapeSmoke 0)).filter (fun c => c.row < nTrans)).length == 1
#guard ((classCells posS (vTcY shapeSmoke 0)).filter (fun c => c.row < nTrans)).length == 1
-- ⚑ …AND THE CONTRAST THAT SAYS WHAT "FREE" MEANT. The transcript's ONE pad cell has a class of TWO
-- — the absorb row that reads it and the `Generic` row that PINS IT TO ZERO. Until 2026-08-03 that
-- lane carried a `msgVal` FIXTURE whose class was ONE cell: no row pinned it, no gadget read it, and
-- a `Poseidon` gate constrains the permutation and not what was fed to it. That was the class every
-- `t_comm` word was in before §6b, and it is now empty.
#guard (classCells posS (vTPad shapeSmoke)).length == 2
-- …and `t_comm` is the FOURTH provenance in the assembly, in none of the other three lists.
#guard Dregg2.Bridge.MinaStepPrevCommitments.T_COMM_XY.all (fun p =>
  !(Dregg2.Bridge.MinaStepPrevCommitments.ALL_XY.contains p)
  && !(Dregg2.Bridge.MinaStepPrevCommitments.INDEX_XY.contains p))

-- ⚑ THE SCALARS ARE R6's OWN CELLS and not statement words (§6b's named divergence, a
-- strengthening): `Plonk_checks.checked`'s `perm` and the `ζ^n` slot.
#guard tS.ftw.permV == aVarAt (baseFtS shapeSmoke) tS.ft.fp.prog tS.ft.fp.slots.perm
#guard tS.ftw.zetaV == aVarAt (baseFtS shapeSmoke) tS.ft.fp.prog tS.ft.fp.slots.zetaN
#guard tS.ftw.permVal == tS.ft.vals.getD tS.ft.fp.slots.perm 0
#guard tS.ftw.zetaVal == tS.ft.vals.getD tS.ft.fp.slots.zetaN 0
#guard tS.ftw.permVal != 0 && tS.ftw.zetaVal != 0 && tS.ftw.permVal != tS.ftw.zetaVal
-- …`Shifted_value.Type2`'s split reconstructs each of them, and `s_div_2 < 2^254`, so
-- `scale_fast2`'s top-bit assert is SATISFIABLE and not decoration.
#guard (List.range N_FTC_SCAL).all (fun c =>
  let v := ftcScalVal tS.ftw c
  2 * (v / 2) + v % 2 == v && v / 2 < 2 ^ 254)
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (tS.ftc.terms.getD k default).bits.headD 1 == 0)
-- …the ladder's FINAL counter cell IS `s_div_2`'s variable, per term — `Field.Assert.equal !n_acc
-- scalar` (`plonk_curve_ops.ml:208`) — and every term's chain really reconstructs it.
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  ftcN shapeSmoke k FTC_CHUNKS == ftcDiv2 shapeSmoke (ftcScalOf k))
#guard (List.range (ftcTerms shapeSmoke)).all (fun k =>
  (tS.ftc.terms.getD k default).td.ns.getLastD 0 == ftcScalVal tS.ftw (ftcScalOf k) / 2)
-- …and the SHARING is upstream's: `scale_fast2` takes an already-split pair, so the `n−1` Horner
-- scales and the closing one read ONE `s_div_2` class and `perm` reads its own.
#guard (classCells posS (ftcDiv2 shapeSmoke 0)).length == 3
#guard (classCells posS (ftcDiv2 shapeSmoke 1)).length == 5
#guard (classCells posS (ftcOdd shapeSmoke 1)).length == 11

-- ⚑⚑ **THE LADDER COMPUTES WHAT `scale_fast2` SAYS IT DOES**, checked against that oracle without
-- inversion. Both scalar blocks, so `perm` and `ζ^n` are each exercised.
#guard jacEqM pN (jOf (tS.ftc.terms.getD 0 default).res) (ftcJacScale ftcSigma tS.ftw.permVal)
#guard jacEqM pN (jOf (tS.ftc.terms.getD 1 default).res)
                 (ftcJacScale (ftcTc (tCommN shapeSmoke - 1)) tS.ftw.zetaVal)
-- …and the oracle DISCRIMINATES: a one-off scalar gives a different point, so the pin is not
-- comparing a value with itself.
#guard (jacEqM pN (jOf (tS.ftc.terms.getD 0 default).res)
                  (ftcJacScale ftcSigma (tS.ftw.permVal + 1))) == false

-- ⚑⚑ **AND THE `Ops.add_fast` CHAIN IS `common.ml:246-256`, add for add**, recomputed in Jacobian
-- from the ladders' own outputs: the `n−1` Horner adds, `f_comm + chunked_t_comm`, and the closing
-- `+ negate (scale chunked_t_comm zeta_to_domain_size)`.
#guard (List.range (tCommN shapeSmoke - 1)).all (fun a =>
  jacEqM pN (jOf (tS.ftc.adds.getD a (0, 0)))
            (jAdd (jOf (ftcTc (tCommN shapeSmoke - 2 - a)))
                  (jOf (tS.ftc.terms.getD (a + 1) default).res)))
#guard jacEqM pN (jOf (tS.ftc.adds.getD (tCommN shapeSmoke - 1) (0, 0)))
                 (jAdd (jOf (tS.ftc.terms.getD 0 default).res)
                       (jOf (tS.ftc.adds.getD (tCommN shapeSmoke - 2) (0, 0))))
#guard jacEqM pN (jOf tS.ftc.out)
                 (jAdd (jOf (tS.ftc.adds.getD (tCommN shapeSmoke - 1) (0, 0)))
                       (jNeg (jOf (tS.ftc.terms.getD (tCommN shapeSmoke) default).res)))
-- …and `ft_comm` is a genuine curve point, not a coordinate pair that happens to satisfy the gates.
#guard onCurveA tS.ftc.out

-- ⚑⚑ **R4 ROUND `FTC_ROUND`'s BASE IS THIS MSM's OUTPUT.** Not a supplied commitment and not an
-- `Inner_curve.constant`: the `complete_add` closing `common.ml:255-256` writes the fold's own base
-- variables. `combine_split_commitments`' commitment 3 IS `ft_comm` (`step_verifier.ml:606`), and
-- round `r` folds commitment `r+1`.
#guard ipaSrc shapeSmoke FTC_ROUND == BaseSrc.computed
#guard ipaSrc shapeStep FTC_ROUND == BaseSrc.computed
#guard tS.ipa.bases.getD FTC_ROUND (0, 0) == tS.ftc.out
#guard ((ftcAddRows shapeSmoke tS.ftc true).getLastD default).perm
        == [ some (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))
           , some (ipy shapeSmoke (qT shapeSmoke FTC_ROUND)), none, none, none, none, none ]
#guard (let rs := ftcAddRows shapeSmoke tS.ftc true
        let r := rs.getD (rs.length - 2) default
        r.kind == KGateType.completeAdd
        && r.perm.getD 4 none == some (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))
        && r.perm.getD 5 none == some (ipy shapeSmoke (qT shapeSmoke FTC_ROUND)))
-- …the supplied list still carries the real block's own `COMBINE_XY[3]` and the assembly IGNORES
-- it — which is the point: a derived value cannot agree with a fixture by construction, because the
-- scalars here are R6's and not the block's `Fq` deferred values.
#guard ipaBaseOf shapeSmoke (stepBases shapeSmoke) FTC_ROUND
        == Dregg2.Bridge.MinaStepPrevCommitments.COMBINE_XY.getD 3 (0, 0)
#guard tS.ftc.out != Dregg2.Bridge.MinaStepPrevCommitments.COMBINE_XY.getD 3 (0, 0)
-- …no pin row for it, and its class is the add's output, the probe, and — since §19d
-- (`0047cb876`), where a combine commitment is a Horner ADDEND and no ladder's base — the fold add
-- that takes it. It had the 32 `EndoMul` reads in place of that add before.
#guard (ipaBaseRows shapeSmoke tS.ipa).all (fun r =>
  r.perm.headD none != some (ipx shapeSmoke (qT shapeSmoke FTC_ROUND)))
#guard (classCells posS (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))).length == 3
#guard ((classCells posS (ipx shapeSmoke (qT shapeSmoke FTC_ROUND))).filter
          (fun c => c.row < nTrans)).length == 0

-- ⚑⚑ **IT IS CONSUMED, AND THAT IS THE WHOLE DIFFERENCE FROM ABSORBING IT.** Substitute ONE
-- quotient chunk — chunk 0, which is only a Horner ADDEND and no scale's base — and `ft_comm` moves,
-- so R4 round `FTC_ROUND`'s base moves and the fold moves with it. Before §6b that substitution
-- changed one sponge input and NOTHING else in the circuit.
#guard ftcSwap0.out != tS.ftc.out
#guard (runIpa shapeSmoke (stepBases shapeSmoke) tS.sp ftcSwap0.out (tS.bp.term 0).res
          (tS.defc.pre.getD 0 0)).sums.getLastD (0, 0)
        != tS.ipa.sums.getLastD (0, 0)
-- …and the Horner SEED matters too, through the ladder rather than through an add.
#guard (ftcScaleTerm (Dregg2.Bridge.MinaStepPrevCommitments.GAMMA_XY.getD 29 (0, 0))
                     tS.ftw.zetaVal).res != (tS.ftc.terms.getD 1 default).res
-- …and so does each SCALAR: bend `perm` by one and `f_comm` moves, so `ft_comm` does.
#guard (ftcScaleTerm ftcSigma (tS.ftw.permVal + 1)).res != (tS.ftc.terms.getD 0 default).res
-- ⚠ ⚑ **AND SAY WHAT THAT DOES NOT DO.** An ON-CURVE substitution is REFUSED by no rung in this
-- assembly. It moves `ft_comm`, R4 round `FTC_ROUND`'s base, the fold and every downstream value —
-- and the check that would refuse it is the IPA opening, i.e. `verified`, which is simplification
-- #11 and is still a witnessed boolean. What §6b buys is narrower and is the thing that was
-- missing: `t_comm` is no longer a word the sponge eats and NOTHING reads. It is an
-- `Inner_curve.typ` value carrying a membership check, an operand of a sub-circuit, and a term in
-- the point R4 folds — so a grind on it is refused (below) instead of being invisible.

-- ⚑⚑ **THE FORMULA, AGAINST A GOLD o1-labs' OWN `SRS::verify` PINNED.** Everything above checks
-- the assembly against itself and against `PastaCurve`. This checks `common.ml:246-256` — the shape
-- §6b's row schedule implements — against the REAL block. `MinaWrapGroupGate` reproduces devnet
-- block 539508's `ft_comm` over the group law (`ftComm_reproduces_kimchi`) and o1-labs' `SRS::verify`
-- accepts the opening proof at that point. The transcription below is §6b's OWN order — seed at
-- `t_comm.(n−1)`, fold `t_comm.(i) + scale res zeta_to_srs_length` downto 0, then
-- `f_comm + chunked + negate (scale chunked zeta_to_domain_size)` — over `MinaWrapGroupGate`'s
-- projective primitives, at the block's own `perm` / ζ powers / commitments. It lands on the gold.
-- ⚠ AND IT SETTLES THE ζ QUESTION §6b names: at the real block the two ζ powers are DIFFERENT
-- (`max_poly_size = 2^15` against `domain_size = 2^14`), where this assembly's `log2n =
-- srs_length_log2 = 16` collapses them. That is a shape fact and it is why the two Horner scalars
-- share one `Shifted_value.Type2` pair HERE and would not THERE.

#guard Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN (ftcRealAt ZETA_DOM)
         Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD
-- …and the Horner alone reproduces kimchi's own `chunk_commitment(zeta_to_srs_len)` gold, so the
-- `downto` order is right and not merely consistent with the sum.
#guard Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN ftcHornerReal
         Dregg2.Circuit.Emit.MinaWrapGroupGate.CHUNKED_T_GOLD
-- ⚑ …and the MALLER FACTOR is load-bearing. `common.ml:256` scales by `zeta_to_domain_size` and the
-- `+ chunked` term is what leaves `(ζⁿ − 1)`; reading `zeta_to_domain_size` AS the Maller factor —
-- the conflation this transcription could most easily have made — gives a DIFFERENT point.
#guard (Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN
          (ftcRealAt Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_DOM_M1)
          Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD) == false
-- …and the two ζ powers really are DIFFERENT at the real block, so `ZETA_SRS` cannot be standing in
-- for `ZETA_DOM` in the pin above.
#guard Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_SRS != ZETA_DOM
#guard (Dregg2.Circuit.Emit.PastaCurveComplete.projEqM pN
          (ftcRealAt Dregg2.Circuit.Emit.MinaWrapGroupGate.ZETA_SRS)
          Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD) == false
-- ⚑ …and the POINTS the assembly consumes ARE that gold's own inputs: `ftcSigma` is
-- `sigma_comm[6]` and `ftcTc` is the block's `t_comm`, coordinate for coordinate.
#guard (List.range N_TCOMM).all (fun i =>
  let p := Dregg2.Circuit.Emit.MinaWrapGroupGate.TCHUNKS.getD i (0, 0, 0)
  ftcTc i == (p.1, p.2.1))

end Dregg2.Circuit.Emit.KimchiStepMain

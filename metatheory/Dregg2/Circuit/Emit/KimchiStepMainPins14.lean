/-
`KimchiStepMain` pins — §19: `group_map`, `p_prime`'s `uc`, `rhs`, `equal_g`.

⚑ NAMED THEOREMS, NOT `#guard`. `metatheory/docs/GUARD-DISCIPLINE.md`: a `#guard` is the same
`unsafe evalExpr` a `native_decide` theorem runs, minus the name, the term and the axiom record.
`KimchiStepMain`'s 838 guards are baselined; this module adds none.

The values these are stated about are in `…Fixture`; the emission is in `…Core`.
-/
import Dregg2.Circuit.Emit.KimchiStepMainFixture

namespace Dregg2.Circuit.Emit.KimchiStepMain

open Dregg2.Circuit.Emit.KimchiTarget (KGateType K_PERMUTS)
open Dregg2.Circuit.Emit.KimchiPlacement
open Dregg2.Circuit.Emit.WitnessBuilder
  (VarEnv GateWitness gridAt envIndex envLookupAt gateVarWitnessAt compose)
open Dregg2.Circuit.Emit.KimchiRenderVarBaseMul (fAdd fMul)
open Dregg2.Circuit.Emit.KimchiComposeStepFragment (onCurveA jOf jAdd jNeg)
open Dregg2.Circuit.Emit.PastaCurve (jacEqM scMulM)
open Dregg2.Circuit.Emit.PastaField (pN)

set_option autoImplicit false
set_option maxRecDepth 100000

/-! ## §19 — the four ladders are EMITTED, and the verdict they change is NOT the one queued.

Read the label before the numbers. What landed:

  * `group_map` is a row-set, and `u` is a function of the transcript rather than a witness;
  * `p_prime`'s `uc` term is a row-set, so `combined_inner_product` — a STATEMENT word — reaches the
    curve side and hence `lhs`;
  * `rhs`'s three `scale_fast2`s and both `Ops.add_fast`s are row-sets;
  * `equal_g` is a row-set, and **R8's `verified` is its output cell instead of an `AOp.wit`.**

What did NOT land, stated as the failure it is: `equal_g` refuses no on-curve substitution. `G`, `z₁`
and `z₂` are free, the honest witness this file emits SOLVES `G` off `lhs`, and the substituted
assembly solves its own — both close. The theorems below measure that on the emitted objects. -/

/-! ### `group_map`: the emitted cells ARE `gmapFp`, and the argument is the FULL squeeze. -/

/-- ⚑ TWO INDEPENDENT COMPUTATIONS AGREE. `gmVals` is the straight-line program the rows encode,
slot for slot; `gmapFp` is §17's first-square-of-three definition. Neither is written in terms of the
other, and they agree at the assembly's own transcript point. -/
theorem gm_cells_are_gmapFp :
    gmOut (uSqueezeVal shapeSmoke tS.sp) = gmapFp (uSqueezeVal shapeSmoke tS.sp) := by
  native_decide
#assert_compiled gm_cells_are_gmapFp

/-- …and the result is on Pallas, which is what makes it a legal `scale_fast2` base. `sqrt_flagged`'s
`assert_square` plus `Boolean.Assert.any` and the first-of-three selection ARE the on-curve proof, so
no `assert_on_curve` row is emitted for `u` — upstream emits none either. -/
theorem gm_output_is_on_curve : onCurveA (gmOut (uSqueezeVal shapeSmoke tS.sp)) = true := by
  native_decide
#assert_compiled gm_output_is_on_curve

/-- ⚑⚑ **THE CORRECTION, MEASURED.** `step_verifier.ml:264` is `Sponge.squeeze_field` — the whole
element. §17's exhibit passed `chalOf`, the LOW 128 bits, and this pins that the two arguments differ
AND that `group_map` sends them to different points. A `u` off the wrong `t` is a different curve
base and hence a different `rhs`. -/
theorem u_squeeze_is_the_full_element_not_the_low_128 :
    (uSqueezeVal shapeSmoke tS.sp ≠ chalOf shapeSmoke tS.sp (uChalIx shapeSmoke)
     ∧ gmOut (uSqueezeVal shapeSmoke tS.sp)
         ≠ gmapFp (chalOf shapeSmoke tS.sp (uChalIx shapeSmoke))) := by
  native_decide
#assert_compiled u_squeeze_is_the_full_element_not_the_low_128

/-- …and the cell the rows read really is that squeeze's own lane, not a copy of it. -/
theorem u_squeeze_var_is_the_scheduled_lane :
    uSqueezeVar shapeSmoke
      = vSt shapeSmoke (sqStBlock shapeSmoke (uChalIx shapeSmoke))
            (sqStLane shapeSmoke (uChalIx shapeSmoke)) := by
  native_decide
#assert_compiled u_squeeze_var_is_the_scheduled_lane

/-! ### `p_prime`'s `uc`: the statement word reaches the curve. -/

/-- ⚑ **`uc = [2^255 + cip]·u`** — the ladder's own output against a scalar multiplication computed
by `PastaCurve.scMulM`, which shares no code with `runVbm`. `bpK` is `Shifted_value.Type2`'s
effective multiplier. -/
theorem uc_ladder_multiplies_u_by_the_statement_word :
    jacEqM pN (jOf (tS.bp.term 0).res)
      ((scMulM pN (bpK tS.fin.cipShift) (jOf (gmOut (uSqueezeVal shapeSmoke tS.sp)))).getD (0, 0, 0))
      = true := by
  native_decide
#assert_compiled uc_ladder_multiplies_u_by_the_statement_word

/-- …and the scalar the LADDER is wired to is the statement word `vCipShift` and not a second copy:
its `Shifted_value.Type2` split cell holds `cipShift / 2`, which is the value the closing
`Field.Assert.equal !n_acc scalar` (`plonk_curve_ops.ml:208`) forces. -/
theorem uc_scalar_source_is_vCipShift :
    (bpScalV shapeSmoke 0 = vCipShift shapeSmoke
     ∧ tS.bp.scals.getD 0 0 = tS.fin.cipShift) := by
  native_decide
#assert_compiled uc_scalar_source_is_vCipShift

/-- ⚑ **`q = p_prime + lr_prod` REALLY MOVED.** The point `Scalar_challenge.endo q c` reads is not
the fold sum: `uc` is a nonzero contribution, so a rung that dropped it would red here rather than
quietly compute the old `lhs`. -/
theorem q_prime_is_not_the_fold_sum :
    tS.ipa.qPrimePt ≠ tS.ipa.sums.getLastD (0, 0) := by
  native_decide
#assert_compiled q_prime_is_not_the_fold_sum

/-- …and `lhs` is the endo of THAT point: the tail's base slot is `qPrime`, an equality against the
slot record rather than a claim about a row. -/
theorem lhs_endo_base_is_q_prime : (lhsSlots shapeSmoke).base = qPrime shapeSmoke := by
  native_decide
#assert_compiled lhs_endo_base_is_q_prime

/-! ### `rhs` and `equal_g`. -/

/-- ⚑ **THE HONEST WITNESS CLOSES**, on the emitted values: `rhs = z₁·(G + b·u) + z₂·H` equals
`lhs = c·q + δ`, coordinate for coordinate. This is `equal_g`'s own equality, evaluated on the
assembly's own numbers rather than on an exhibit's. -/
theorem honest_rhs_equals_lhs : tS.bp.rhs = tS.bp.lhs := by native_decide
#assert_compiled honest_rhs_equals_lhs

/-- …and `equal_g`'s output cell is therefore `1`. -/
theorem equal_g_closes_on_the_honest_witness : tS.bp.ver = 1 := by native_decide
#assert_compiled equal_g_closes_on_the_honest_witness

/-- ⚑ …and it closes because `G` was SOLVED, which is the whole finding: the honest `G` this file
emits IS `z₁⁻¹·(lhs − z₂·H) − b·u`. Stated as an equality against `KimchiStepMainField.bpSolveG`, so
"the prover can always produce one" is a fact about the emitted witness and not a sentence. -/
theorem honest_G_is_the_prover_solve :
    tS.gXY = jAffOf (bpSolveG (gmOut (uSqueezeVal shapeSmoke tS.sp)) GENERATORS_H
                       tS.bp.lhs tS.fin.bShift BP_Z1_VAL BP_Z2_VAL) := by
  native_decide
#assert_compiled honest_G_is_the_prover_solve

/-- ⚑ **`H` is the MEASURED constant and it is pinned by a row**, not carried as a witness: the
ladder-3 base variables are `bpHx`/`bpHy` and `bpRows` emits one `Generic` row fixing both. -/
theorem generators_h_is_pinned_by_a_row :
    ((bpRows shapeSmoke tS.bp true).any (fun r =>
        r.kind == KGateType.generic
        && r.perm.getD 0 none == some (bpHx shapeSmoke)
        && r.coeffs == cConst (GENERATORS_H.1 : Int) ++ cConst (GENERATORS_H.2 : Int)))
      = true := by
  native_decide
#assert_compiled generators_h_is_pinned_by_a_row

/-! ### ⚑⚑ WHAT §19 DOES NOT BUY — the free witnesses, stated as σ-class facts.

`G`, `z₁` and `z₂` are the prover's. `z₁`/`z₂` have exactly ONE occurrence each — ladder 2's and
ladder 3's `Shifted_value.Type2` split row — and a single occurrence cannot tie a cell to anything:
the split `s = 2·div2 + odd` is one equation in three unknowns, all three of them the prover's. -/

/-- ⚑ ONE cell each. Equalities, not lower bounds: a future rung that consumed `z₁` would red here
rather than pass a floor. -/
theorem z1_and_z2_occur_exactly_once :
    ((classCells posS (bpZ1 shapeSmoke)).length = 1
     ∧ (classCells posS (bpZ2 shapeSmoke)).length = 1) := by
  native_decide
#assert_compiled z1_and_z2_occur_exactly_once

/-- …whereas `u`, which §19 DERIVES, spans the `group_map` dot-product and both ladders that use it
as a base. Stated as an equality so a lost consumer reds. -/
theorem u_x_is_consumed_by_group_map_and_both_ladders :
    (classCells posS (vUx shapeSmoke)).length = 2 + 2 * (FTC_CHUNKS + 3) := by native_decide
#assert_compiled u_x_is_consumed_by_group_map_and_both_ladders

/-! ### ⚑⚑ `verified` IS NO LONGER A WITNESS — the one thing emitting `rhs` actually buys. -/

/-- The finalize wire's `verified` field is an `.inp` of `equal_g`'s output cell. Before §19 it was
`AOp.wit 1`: a cell no row defined, which R8's `Boolean.all` then forced to `1` — i.e. an assert that
constrained the prover not at all. -/
theorem verified_is_wired_to_equal_g :
    (finWireOf shapeSmoke tS.ft).verified = AOp.inp (bpEq shapeSmoke) := by native_decide
#assert_compiled verified_is_wired_to_equal_g

/-- …and that cell HAS a defining row: `equal_g`'s `Boolean.all` half writes it, and R8's program
reads it, so its σ class has both ends. -/
theorem equal_g_output_has_a_defining_row_and_a_consumer :
    (classCells posS (bpEq shapeSmoke)).length = 5 := by native_decide
#assert_compiled equal_g_output_has_a_defining_row_and_a_consumer

/-! ### ⚑⚑ THE SUBSTITUTION VERDICT, RE-RUN ON THE EMITTED CIRCUIT — READ IT LITERALLY.

§17(e) said the substituted-with-re-solved-`G` witness is ACCEPTED, and that `rhs`/`equal_g` were not
emitted. They are emitted now. **The verdict is UNCHANGED.** -/

/-- ⚑⚑ **(e′) THE SUBSTITUTED ASSEMBLY'S `equal_g` CLOSES TOO.** `tSwapAbs` is `tS` with one absorbed
fold commitment replaced by another of block 539508's own on-curve points; it is a different
transcript, a different `u`, a different `lhs` — and its `G`, solved by the same identity, closes the
same equality. Emitting 484 rows did not make this refuse. -/
theorem substituted_assembly_still_closes_equal_g : tSwapAbs.bp.ver = 1 := by native_decide
#assert_compiled substituted_assembly_still_closes_equal_g

/-- …and it really is a DIFFERENT witness and not a re-run of the honest one: `u`, `lhs` and `G` all
moved. -/
theorem the_substitution_moves_u_lhs_and_G :
    (tSwapAbs.bp.u ≠ tS.bp.u ∧ tSwapAbs.bp.lhs ≠ tS.bp.lhs ∧ tSwapAbs.gXY ≠ tS.gXY) := by
  native_decide
#assert_compiled the_substitution_moves_u_lhs_and_G

/-- ⚑ …and the ONLY thing that moved with it is the public word, exactly as §17(d) measured — which
is a refusal one recursion step later and, per §18, not one there either. -/
theorem the_substitution_moves_public_word_seven :
    hmOutDigestOf shapeSmoke tSwapAbs.sp tSwapAbs.gXY
      ≠ hmOutDigestOf shapeSmoke tS.sp tS.gXY := by native_decide
#assert_compiled the_substitution_moves_public_word_seven

/-! ### ⚑⚑ THE CLASS THIS RUNG BROKE, AND THE PIN THAT NOW CATCHES IT.

`qPrime` was added to the row schedule and NOT to `circuitEnv`, and the `Ops.add_fast` output was a
silent `0` while the endo seed was taken at the OLD point. Every σ-class pin, every row-count pin and
every closed form in this file stayed GREEN; the *prover* rejected the honest `r4_ipa` witness with
`Prover("rest of division by vanishing polynomial")`.

**A row schedule and a witness environment are two places, and only the prover read both.** This is
the pin that makes them one: every variable any row WIRES must have an entry in `stepEnv`, not a
default. It is an `all`, so a single unwired-but-scheduled cell reds. -/

/-- ⚑ Every permutation-column variable of every row has a witness value — none falls through
`envLookupAt`'s `getD … 0` default. Stated over the top rung, so it covers §19 and everything below
it. -/
theorem every_scheduled_variable_has_a_witness_entry :
    (let ix := envIndex (stepEnv tS)
     rowsS.all (fun r => r.perm.all (fun o =>
       match o with
       | none => true
       | some v => (ix.getD (varIx v) none).isSome))) = true := by
  native_decide
#assert_compiled every_scheduled_variable_has_a_witness_entry

/-- …and it is not vacuous: `rowsS` really does wire variables (a schedule of all-`none` perms would
satisfy the `all` above trivially). ⚑ An EQUALITY, not a bound — a bound is what "a deleted chain
would still satisfy" looks like. `4236` rows carry `13325` wired permutation cells; both numbers
move deliberately or not at all. ⚑ It was `4235`/`13316` until 2026-08-11 (`16b6d9b8a`), when
segment D's own `G` became a fourth checked non-round point: three more `assert_on_curve` halves,
packed two to a row, are `(3·10+1)/2 − (3·9+1)/2` = **+1 row**, and they wire three variables
each, **+9 cells**. ⚑ It was `3869`/`12977` until 2026-08-07, when segment D stopped being a
`Sponge.copy` of segment C and started running its own `sponge_after_index` over the instance's own
wrap verification key (`step.rs:2718`): +56 absorbed words is `nbD` 4 → 32 at this shape, plus the
two init pin rows a non-copied segment emits. **+366 rows, +339 cells**, and the same +366 takes
`shapeStep` from 10 349 to 10 715 — still inside `2 ^ 14`. ⚑ It was `4025`/`13054` until §23 (`…Pins18`) made the sponge LAZY:
five permutations left the assembly (one per segment squeeze that a preceding absorb block already
supplies, two of them segment B's) plus §3c's whole `index_digest` block, and the transcript went
from `absorbs + chals = 18` permutations to `tBlocks = 11`. **−164 rows, −95 cells**, and the pad
lane moved from block 0's second lane to the last lane of the pre-β run. -/
theorem the_schedule_wires_variables :
    (rowsS.length = 4236 ∧ (rowsS.flatMap (fun r => r.perm.filterMap id)).length = 13325) := by
  native_decide
#assert_compiled the_schedule_wires_variables

/-! ### The row-set, as a closed form of what it emits. -/

/-- ⚑ `bpRows`' length, summand by summand: `group_map`'s 44 halves packed two to a row plus its
probe; `H`'s pin row; the four `Shifted_value.Type2` splits and `n_acc` seeds, 12 halves; four
`sfTermRows` at `4 + 1 + 2·FTC_CHUNKS + 3` rows each; two `Ops.add_fast`s with a probe each;
`equal_g`'s 15 halves. A ladder that quietly loses a chunk reds here. -/
theorem bpRows_length_closed_form :
    (bpRows shapeSmoke tS.bp true).length
      = (22 + 1) + 1 + 6 + N_SF * (4 + 1 + 2 * FTC_CHUNKS + 3) + 4 + 8 := by native_decide
#assert_compiled bpRows_length_closed_form

/-- …and R4 grew by exactly the `q = p_prime + lr_prod` add and its probe. -/
theorem ipa_rung_grew_by_the_q_prime_add :
    (ipaRows shapeSmoke tS.ipa true).length
      = (ipaBaseRows shapeSmoke tS.ipa).length + (ipaSeedPinRows shapeSmoke).length
        + (onCurveRows shapeSmoke).length
        + shapeSmoke.ipaRounds * (3 + (shapeSmoke.ipaBlocks + 1) + 1 + 1 + 1)
        + 2 + (lhsRows shapeSmoke tS.ipa true).length := by native_decide
#assert_compiled ipa_rung_grew_by_the_q_prime_add

/-- ⚑ **`EndoMul` is UNTOUCHED at `32 × 77`.** §19 emits `VarBaseMul` ladders, not `EndoMul` ones, so
the gate histogram's `endo_mul` count is still `ipaBlocks` per fold round plus the `c`-endo tail —
the count that matches Mina's own. Stated over the whole `.opening` rung, i.e. after §19. -/
theorem endomul_rows_are_still_thirty_two_by_seventy_seven :
    ((rungRows tS .opening true).filter (fun r => r.kind == KGateType.endoMul)).length
      = shapeSmoke.ipaBlocks * (shapeSmoke.ipaRounds + 1) := by native_decide
#assert_compiled endomul_rows_are_still_thirty_two_by_seventy_seven

end Dregg2.Circuit.Emit.KimchiStepMain

/-
`KimchiStepMain` pins — §17.

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

/-! ## §17 — `check_bulletproof`'s `rhs` and `equal_g`: WHAT IT WOULD REFUSE, AND WHAT IT WOULD NOT.

`step_verifier.ml:328-340`, verbatim:

    let rhs =
      with_label __LOC__ (fun () ->
          let b_u = scale_fast2 u advice.b in
          let z_1_g_plus_b_u = scale_fast2 (challenge_polynomial_commitment + b_u) z_1 in
          let z2_h = scale_fast2 (Inner_curve.constant (Lazy.force Generators.h)) z_2 in
          z_1_g_plus_b_u + z2_h )
    in
    (`Success (equal_g lhs rhs), challenges)

R4 already emits `lhs = Scalar_challenge.endo q c + delta` (`:325-327`, `lhsRows`). This section is
the OTHER side, evaluated on the assembly's own values — and the reason it is an EXHIBIT and not a
row-set is a MEASURED fact that inverts the reason the rung was queued.

## ⚑ THE FINDING: `equal_g` ALONE REFUSES NOTHING

`equal_g lhs rhs` is `Boolean.all (List.map2 Field.equal …)` (`:69-73`) — a two-coordinate equality
between `lhs = c·q + δ` and `rhs = z₁·(G + b·u) + z₂·H`, where

  * `q` is the fold of every consumed commitment, `c` the last transcript squeeze, `δ` an absorbed
    word — **all three bound** (R1/R4, and `assert_on_curve` on the supplied ones);
  * `b` is `advice.b`, a statement word (R8's `vBShift`) — **bound**;
  * `u = group_map (Sponge.squeeze_field sponge)` (`:263-266`) — **derivable**, and this section
    derives it (`gmapFp`), so it is a function of the transcript;
  * `H = Generators.h` — an `Inner_curve.constant`, **pinnable** (`GENERATORS_H`);
  * and `G = challenge_polynomial_commitment`, `z₁`, `z₂` — **FREE WITNESSES.** Read at source, `G`
    occurs at exactly two places in `step_verifier.ml` (`:253` destructure, `:333` use) and `z₁`/`z₂`
    at exactly two (`:253`, `:332-336`). No absorption, no pin, no statement word, no other consumer.

So for ANY `lhs` a prover sets `G := z₁⁻¹·(lhs − z₂·H) − b·u` — one scalar-field inverse and three
scalar multiplications, **no discrete log** — and `equal_g` holds. `bpExhibit` below measures exactly
that on the assembly's own numbers: the honest witness closes, the on-curve-substituted assembly with
the SAME `G` is REFUSED, and the same substitution with `G` RE-SOLVED is ACCEPTED again.

⚠ **So the previous rung's note — "`equal_g` is the first rung that can refuse an on-curve
substitution" — is FALSE as stated, and this is where it is measured.** What `equal_g` buys is that
`verified` (#11) stops being a free boolean and becomes a function of `(q, c, δ, b, u, G, z₁, z₂)`.
What it does NOT buy is any refusal, because the last three of those are the prover's.

## ⚑ WHAT WOULD REFUSE IT, NAMED AT SOURCE

`G`'s binder exists and it is **one rung ABOVE `verify_one`**: `step_main.ml:526-545` hashes
`acc.wrap_proof.opening.challenge_polynomial_commitment` — this very `G`, one per previous proof —
into `hash_messages_for_next_step_proof`, whose digest is the step statement's
`messages_for_next_step_proof` (`step_main.ml:571-575`), a PUBLIC output. With that assembled, a
re-solved `G` moves a public word and the public-vector tie refuses it; `z₁`/`z₂` alone then leave a
two-dimensional discrete log in `⟨G + b·u, H⟩`, which is the IPA opening's own hardness and not a
gate. Without it, `equal_g` is satisfiable for every `lhs`.

⚠ **AND THAT HASH IS NOT SEGMENT C.** §8e's segment C is the OTHER call —
`hash_messages_for_next_step_proof_opt` inside `verify_one` (`step_main.ml:59-81`), over
`prev_challenge_polynomial_commitments` (= `sg_old`) and `prev_challenges`, masked by
`branch_data.proofs_verified_mask`.

## ⚑ WHAT LANDED 2026-08-02, AND THE TWO PLACES THIS SECTION WAS WRONG AT SOURCE

**(1) Segment C's commitment slots are corrected**, and §12k exhibits it in both directions. The
slots were R3's x_hat sum and R4's fold output `q` — neither is `sg_old`. ⚠ This section said the
second half "needs `sg_old[1]`, the `Wrap_hack.Checked.pad_commitments` second slot", i.e. a variable
this assembly did not have. **It did have it.** `sg_old[1]` is census commitment 1, which is fold
ROUND 0's base (`ipx/ipy (qT s 0)`) because round `r` folds commitment `r+1` — the correction was a
FOUR-word swap with no new variable at all.

**(2) The two vectors are INTERLEAVED PER PROOF**, which neither this section nor `hmSpec` had:
`to_field_elements_without_index` (`composition_types.ml:595-607`) is
`Array.concat [app_state; Vector.map2 comms chals ~f:(fun c ch -> g c ++ ch)]`, so the order is
`comm₀ · chals₀ · comm₁ · chals₁`, not four coordinates followed by every challenge. §12k pins that
the concatenated order over the SAME four correct words gives a DIFFERENT digest, so the layout was
load-bearing on its own.

**(3) The outer hash IS assembled** — segment D, `hmOutSpec`, a `Sponge.copy` of `sponge_after_index`
(`step_verifier.ml:1164`) absorbing the app state, `G`, and `finalize_other_proof`'s returned
`bulletproof_challenges`, with its squeeze exposed as public word 7. `G` now has an
`assert_on_curve` and an absorption where it had **no occurrence at all**.

## ⚑⚑ AND THE VERDICT ON THE SUBSTITUTION, RE-RUN BELOW WITH `G` BOUND — READ IT BEFORE QUOTING

**The substituted-with-re-solved-`G` witness is STILL ACCEPTED.** `bpCloses` is unchanged and it is
still `true`; nothing in this file refuses it, and binding `G` to a public digest did not make it
refuse. What changed is measurable and it is smaller than a refusal:

  * `G` was a witness with **zero occurrences** — any on-curve point sat in it, and no constraint and
    no public word moved. It is now absorbed, so **a re-solved `G` MOVES public word 7**, exhibited
    below at the honest and at the re-solved commitment.
  * That is a refusal only for a consumer that **compares** `messages_for_next_step_proof` against
    what it expects — which is the next step's `verify_one`, through the very inner hash segment C
    reconstructs and the wrap-proof tie at `step_main.ml:83-86,108`. **One recursion step later.**
    This circuit alone still accepts; it just no longer proves the honest statement.
    ⚠ ⚑ **AND THAT CONSUMER IS NOW BUILT — §18 — AND IT IS NOT A REFUSAL EITHER.** The sentence
    above says "that is a refusal only for a consumer that compares"; §18 builds the comparison and
    the substituted chain CLOSES, because the prover carries the fake `G` forward as `sg_old` and the
    reconstruction reproduces the moved word. Read §18 before quoting this bullet as a deferral.
  * The prover who is willing to move that public word is not refused here at all. `equal_g` is not
    emitted, so **no row in this assembly relates `G` to the opening** — segment D binds `G` to the
    STATEMENT, not to the IPA.

⚠ So the answer to "is the previous proof's commitment bound now" is: **bound to the statement, not
to the opening, and the opening is not checked here.** And with `G` fixed, `z₁`/`z₂` still leave a
two-dimensional discrete log in `⟨G + b·u, H⟩` — the IPA opening's own hardness, an ASSUMPTION and
not a gate.

## THE UNDONE ROW-SET, PRICED

Three `scale_fast2`s at `~num_bits:255` (`:240-242`) = 3 × 51 chunks, reusing §6b's `ftcScaleTerm`
and its `Shifted_value.Type2` split rows; two `Ops.add_fast`s; one `Inner_curve.constant` pin for
`H`; `group_map` as ~13 double-`Generic` rows (`potential_xs` is 6 multiplications and one inverse,
then three `sqrt_flagged` at 3 constraints each, `Boolean.Assert.any`, and the first-of-three
selection); and `equal_g` as two `Field.equal` plus one `Boolean.all`.
≈ **373 rows** (`assert_on_curve` on `G` left this list — segment D needed it and it is emitted).
Every constant it needs is measured below. -/

/-! ### Field roots — Tonelli–Shanks over `Fp`, which `group_map` needs and no other rung did. -/

#guard fIsSquare 4 && fIsSquare 3 && fIsSquare 2 && !fIsSquare FP_NONRES
#guard pN - 1 == 2 ^ FP_S * FP_M && FP_M % 2 == 1
#guard fMul (fSqrt 3) (fSqrt 3) == 3

/-! ### `Group_map.Bw19`'s parameters for Pallas (`b = 5`).

`Group_map.Bw19.Params.create (module Field.Constant) { b = Inner_curve.Params.b }`
(`step_verifier.ml:214-224`, `bw19.ml:40-65`). MEASURED off `groupmap`'s own
`BWParameters<PallasParameters>` (`metatheory/fixtures/pickles-stepmain-harness/src/bin/gmprobe.rs`),
and each one re-derived here from its DEFINING identity, so the pin is not a copy of itself. -/

-- `u` is the first nonzero `u` with `f(u) = u³ + 5 ≠ 0`, and `fu = f(u)`.
#guard BW_U == 1 && BW_FU == fAdd (fMul BW_U (fMul BW_U BW_U)) 5
-- `sqrt_neg_three_u_squared² = −3u²`, and it is the root TS returns.
#guard fMul BW_SQ3 BW_SQ3 == fSub 0 (fMul 3 (fMul BW_U BW_U))
#guard BW_SQ3 == fSqrt (fSub 0 (fMul 3 (fMul BW_U BW_U)))
-- `sqrt_neg_three_u_squared_minus_u_over_2 = (sqrt(−3u²) − u)/2`.
#guard fAdd (fMul 2 BW_SQ3_MU2) BW_U == BW_SQ3
-- `inv_three_u_squared = 1/(3u²)`.
#guard fMul BW_INV3U2 (fMul 3 (fMul BW_U BW_U)) == 1

-- ⚑ TWO INDEPENDENT SOURCES: this Lean evaluator against `groupmap`'s Rust `to_group`, x AND y,
-- at three points. A shared bug would have to be mirrored in an arkworks Tonelli–Shanks.
#guard gmapFp 1 ==
  (9649340769776349618630915417390658987787685493980520238651558921449989210097,
   3950737189590882296854259000931426390023175717834009675387235630316976417171)
#guard gmapFp 2 ==
  (7490297615487088126677272056937205155610944112134090485255527413633040282968,
   24422916109215858790805163472192903212291163064750739225981256297054129088675)
#guard gmapFp 12345 ==
  (24906630028487510826194306484278106810353957277345535608514541304332784387649,
   18687091782981476925585512723474604782144949211138020305971037232472882709057)
-- …and its output is on the curve, which is what makes it a legal `scale_fast2` base.
#guard onCurveA (gmapFp 1) && onCurveA (gmapFp 12345)

#guard onCurveA GENERATORS_H

/-! ### `scale_fast2`'s EFFECTIVE MULTIPLIER, and the group arithmetic `rhs` is.

`ftcScaleTerm g sv` runs `acc ← 2·acc + (2bₖ−1)·g` from `acc₀ = 2g`, `n₀ = 0` over the 255 bits of
`sv/2`, then takes the `s_odd` branch — which is `[2^255 + sv]·g`, i.e. §6b's stated
`Shifted_value.Type2` residue, here as an arithmetic definition rather than a sentence. -/

-- …stated as an identity against the emitter that actually produces the ladder rows, on a real base.
#guard (scMulM pN (bpK 12345) (jOf GENERATORS_H)).isSome
#guard jacEqM pN ((scMulM pN (bpK 12345) (jOf GENERATORS_H)).getD (0, 0, 0))
                 (jOf (ftcScaleTerm GENERATORS_H 12345).res)

#guard qInv 12345 * 12345 % Dregg2.Circuit.Emit.PastaField.qN == 1

/-! ### The exhibit, on the assembly's own numbers.

`tS` is the honest smoke assembly; `tSwapAbs` is the SAME assembly with one ABSORBED fold commitment
replaced by another of block 539508's own valid on-curve points (§12b). Both are already proved
objects here — the substitution is accepted by every gate in `r8_finalize`, which is the "(a) today's
assembly accepts it" half stated as a fact about a circuit rather than about a value. -/

#guard uChalIx shapeSmoke == 4
#guard uChalIx shapeStep == 4

-- The honest witness CLOSES, and its `G` is a legal `Inner_curve.typ` value.
#guard bpCloses (bpUOf tS) GENERATORS_H (bpLhsOf tS) bpGHonest (bpBOf tS) BP_Z1 BP_Z2
#guard Dregg2.Circuit.Emit.PastaCurve.oncurveM pN bpGHonest

-- ⚑ The substitution really is a DIFFERENT circuit: it moves the `u` squeeze (hence `u` itself, a
-- curve point), and it moves `lhs`. Neither is a restatement of the other.
#guard bpUOf tSwapAbs != bpUOf tS
#guard bpLhsOf tSwapAbs != bpLhsOf tS
#guard onCurveA (bpUOf tS) && onCurveA (bpUOf tSwapAbs)

-- ⚑⚑ **(b) THE SUBSTITUTED ASSEMBLY WITH THE HONEST `G` IS REFUSED.** This is what `equal_g` buys.
#guard !bpCloses (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) bpGHonest
                 (bpBOf tSwapAbs) BP_Z1 BP_Z2

-- ⚑⚑ **(c) …AND THE SAME SUBSTITUTION WITH `G` RE-SOLVED IS ACCEPTED.** Same `z₁`, same `z₂`, same
-- everything a rung here binds; one scalar-field inverse and three scalar multiplications on the
-- prover's side. **This is the measurement that `equal_g` alone refuses no on-curve substitution**,
-- and it is why `G`'s binder (`step_main.ml:526-545`) is the item and not the row count.
#guard bpCloses (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) bpGResolved
                (bpBOf tSwapAbs) BP_Z1 BP_Z2
#guard Dregg2.Circuit.Emit.PastaCurve.oncurveM pN bpGResolved
-- …and it IS a different commitment, so (b) and (c) are not the same witness twice.
#guard !jacEqM pN bpGResolved bpGHonest

-- ⚑ …and the free scalars alone suffice too: `z₁ = z₂ = 1` re-closes it with a different `G`, so
-- neither of the two response scalars is doing any work either.
#guard bpCloses (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs)
                (bpSolveG (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) (bpBOf tSwapAbs) 1 1)
                (bpBOf tSwapAbs) 1 1

/-! ### ⚑⚑ THE EXHIBIT RE-RUN WITH SEGMENT D IN PLACE — and its LITERAL verdict.

The question this rung was queued on: does binding `G` into `hash_messages_for_next_step_proof`
refuse the substitution? **It does not.** What it does is make the substitution move a public word.
Both halves are measured here, on the emitted object, and neither is inferred from the other. -/

-- the affine forms are on the curve and really are two different points.
#guard onCurveA bpGHonestA && onCurveA bpGResolvedA
#guard bpGHonestA != bpGResolvedA
-- …and `jAff` is faithful: re-lifting each one lands back on its Jacobian class.
#guard jacEqM pN (jOf bpGHonestA) bpGHonest && jacEqM pN (jOf bpGResolvedA) bpGResolved

-- ⚑⚑ **(d) THE RE-SOLVED `G` MOVES THE STEP STATEMENT'S PUBLIC WORD.** Same assembly, same
-- transcript, same everything else — only the commitment in segment D's one slot differs, and
-- `messages_for_next_step_proof` (`step_main.ml:572-575`) is a different field element. Before this
-- rung `G` had no occurrence at all and this difference was ZERO by construction.
#guard hmOutDigestOf shapeSmoke tS.sp bpGResolvedA != hmOutDigestOf shapeSmoke tS.sp bpGHonestA
-- …and the digest really is the public word, so this is a statement about the emitted vector.
#guard hmOutDigestOf shapeSmoke tS.sp tS.gAccXY == (tS.segD.states.getLastD []).getD 0 0
#guard (stepPublic tS).getD 7 0 == (hmOutDigestOf shapeSmoke tS.sp tS.gAccXY : Int)
-- …and it is `G` and not something else in that segment doing it: bending EITHER coordinate alone
-- moves the digest, and bending nothing leaves it.
#guard hmOutDigestOf shapeSmoke tS.sp (fAdd tS.gAccXY.1 1, tS.gAccXY.2)
        != hmOutDigestOf shapeSmoke tS.sp tS.gAccXY
#guard hmOutDigestOf shapeSmoke tS.sp (tS.gAccXY.1, fAdd tS.gAccXY.2 1)
        != hmOutDigestOf shapeSmoke tS.sp tS.gAccXY

-- ⚠ ⚑⚑ **(e) AND `equal_g` STILL ACCEPTS IT — the deliverable, stated as the failure it is.**
-- This is exactly `#guard` (c) above, re-asserted after segment D landed so that the record cannot
-- read as if the rung closed it. The witness that was ACCEPTED before is ACCEPTED after.
#guard bpCloses (bpUOf tSwapAbs) GENERATORS_H (bpLhsOf tSwapAbs) bpGResolved
                (bpBOf tSwapAbs) BP_Z1 BP_Z2
-- ⚠ ⚑ **CORRECTED 2026-08-03 (§19).** This said "no row in this assembly relates `G` to the
-- opening: `G`'s ENTIRE class is its `assert_on_curve` halves and segment D's absorb row." `rhs` IS
-- emitted now, so there is a FIFTH cell — `Ops.add_fast G b_u` (`:333`) — and `G` does reach the
-- opening. ⚠ AND THE VERDICT BELOW IS UNCHANGED, which is the point: relating `G` to `lhs` does not
-- refuse the substitution, because the prover solves for `G`. (`assert_on_curve` reads `x` three
-- times and `y` twice; segment D's absorb row reads each once; §19's `add_fast` reads each once.
-- Equalities, so a lost consumer reds here rather than passing a floor.)
-- ⚑ **MOVED 2026-08-11 (`16b6d9b8a`)**: segment D now absorbs its OWN `G` (`vGaX`/`vGaY`, the
-- accumulator the record publishes), not §19's solve, so the absorb cell left this class: `x` is
-- its three halves plus `add_fast`, `y` its two halves plus `add_fast`.
-- The verdict below is unchanged.
#guard (classCells posS (vGx shapeSmoke)).length == 4
#guard (classCells posS (vGy shapeSmoke)).length == 3
-- …whereas the fold's `~init` — a commitment this file DOES consume — spans four row families.
#guard (classCells posS (ipx shapeSmoke (qInit shapeSmoke))).length ≥ 5

-- ⚑ **(f) WHAT WOULD HAVE TO BE TRUE FOR (e) TO BECOME A REFUSAL**, stated as the two pins that
-- are NOT here rather than as prose. Neither is satisfiable in this assembly today:
--   (i) a row relating `G` to `lhs` — that is `rhs` + `equal_g`, the ≈373 rows above, still unemitted;
--   (ii) a consumer that compares public word 7 against an INDEPENDENTLY known digest — that is the
--        next step's `verify_one`, i.e. segment C's reconstruction plus the wrap-proof tie, which is
--        outside this circuit by construction. ⚠ ⚑ **AND (ii) IS NOW BUILT AND IT IS NOT SUFFICIENT
--        EITHER** — §18 measures it; the digest the next step "independently knows" is the one the
--        prover carried, so the comparison is satisfied by the substituted chain. The pin that would
--        make (e) a refusal is neither of these two: it is the accumulator check's OPENING leg
--        (`per_proof_witness.ml:12-32`), i.e. #11.
-- What IS pinned is that the two hashes are the two ENDS of that chain and are wired to the two
-- different objects upstream wires them to: segment C to `sg_old`, segment D to `G` — since
-- `16b6d9b8a` segment D's OWN `G` (`vGaX`), and NOT §19's solved one, which no sponge reads.
#guard sgOldVar shapeSmoke 0 0 == ipx shapeSmoke (qInit shapeSmoke)
#guard (tS.specD.ws.getD (N_IDX_WORDS + N_HM_APP) (xv 0, 0)).1 == vGaX shapeSmoke
#guard (tS.specD.ws.map (·.1)).all (fun v => v != vGx shapeSmoke && v != vGy shapeSmoke)
#guard (tS.specC.ws.map (·.1)).all (fun v => v != vGx shapeSmoke && v != vGy shapeSmoke)
#guard (tS.specD.ws.map (·.1)).all (fun v =>
  v != ipx shapeSmoke (qInit shapeSmoke) && v != ipx shapeSmoke (qT shapeSmoke 0))

-- ⚑ **(g) THE RESIDUE IS A DISCRETE LOG, AND IT IS AN ASSUMPTION.** With `G` fixed, re-closing
-- `equal_g` for a moved `lhs` means solving `z₁·(G + b·u) + z₂·H = lhs` in the two unknowns
-- `z₁, z₂` — two scalars against a two-generator subgroup, i.e. the IPA opening's own hardness.
-- ⚠ There is NO pin below asserting that is hard; a `#guard` cannot say so. What the two pins here
-- do say is that the solve `bpSolveG` uses is NOT available in that direction: it inverts `z₁` to
-- get `G`, and with `G` fixed the same identity gives no `z₁` without a log of `lhs − z₂·H` to base
-- `G + b·u`. So the exhibit stops at `G` on purpose.
#guard (jacEqM pN (bpRhs (bpUOf tSwapAbs) GENERATORS_H bpGHonest (bpBOf tSwapAbs) BP_Z1 BP_Z2)
                  (jOf (bpLhsOf tSwapAbs))) == false
#guard jacEqM pN (bpRhs (bpUOf tS) GENERATORS_H bpGHonest (bpBOf tS) BP_Z1 BP_Z2)
                 (jOf (bpLhsOf tS))

end Dregg2.Circuit.Emit.KimchiStepMain

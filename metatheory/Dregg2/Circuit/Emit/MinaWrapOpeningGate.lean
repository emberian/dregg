import Dregg2.Circuit.Emit.MinaWrapAggregationData
import Dregg2.Circuit.Emit.MinaRealBlockTranscript
import Dregg2.Circuit.Emit.MinaWrapOpeningGateData
/-!
# Dregg2.Circuit.Emit.MinaWrapOpeningGate — RUNG 5f: **the rung that OPENS a commitment.**

Everything before this in `docs/MINA-REAL-BLOCK-GATE.md` §6.1 checks that our arithmetic agrees
with kimchi's on real objects. 5a-5d assemble commitments; 5e derives one. **None of them says a
commitment is a commitment TO anything.** This file states the equation that does, on Mina devnet
block **539508**.

## The object

`SRS::verify` (`poly-commitment/src/ipa.rs:118-300`) folds TWO independent statements into one
randomised MSM, with independent randomisers `rand_base` and `sg_rand_base`:

```text
(A)  sg == <s, srs.g>                                             -- the sg / accumulator leg
(B)  c·Q + delta − z1·sg − z1·b0·U − z2·H == O                    -- THE OPENING RELATION
     where  Q  = Σ_j (chal_invⱼ·Lⱼ + chalⱼ·Rⱼ) + Σ_i ξⁱ·Cᵢ + cip·U
            U  = groupMap(sponge.challenge_fq())
            b0 = Σ_j evalscaleʲ · b_poly(chal, evaluation_pointⱼ)
```

**(B) is this rung.** With `rand_base = 1` it is exactly `check_bulletproof`'s verifier equation.
The 47-term `Σ ξⁱ·Cᵢ` inside `Q` is 5d's aggregate — which carries the block's `w_comm`, `z_comm`,
`t_comm` (through `ft_comm`), the index's `sigma_comm`/`coefficients_comm`/selector commitments,
and 5e's `public_comm`. `cip` is `combined_inner_product`, which `MinaRealBlockGate`'s C8 already
proved is the `(ξ, r)`-fold of the block's **claimed evaluations**. So (B) holding says: the
polynomials those commitments commit to really do take the claimed values at ζ and ζω.

## What was blocking it, and what unblocked it

Every scalar in (B) that is not in the proof is an **Fq-sponge output**: `u_base` is the group map
applied to `challenge_fq()`, and `c` and the 15 IPA challenges are `opening.challenges::<EFqSponge>`.
Until `MinaRealBlockTranscript` landed there was no sponge on this block to continue. There is now:
§3 below picks the phase-1 sponge up at the state `SRS::verify` receives it in — `o.fq_sponge`,
the state right after ζ′ — and runs it forward through `absorb_fr(shift_scalar(cip))`,
`challenge_fq`, the 15 `absorb_g(L)/absorb_g(R)/squeeze` rounds and `absorb_g(delta)`. **All 16
challenges of the opening argument are derived here, not carried.**

## What this rung establishes, and what it still assumes — say both

**Establishes**, in-kernel, over the real group law mod the real prime, on a real Mina block:
the IPA verifier's opening equation holds for this proof at the challenges its own transcript
samples.

**Assumes, and does not discharge:**

1. **P10, the opening-soundness floor.** (B) is the verifier's *check*; that a prover which
   passes it must KNOW an opening is the IPA/dlog extraction argument, which is undischarged here
   and everywhere in this stack. "We opened a commitment" means "the opening check passes", not
   "the opening is sound".
2. **(A), the `<s, srs.g>` leg — rung 5h, DEFERRED BY MEASUREMENT.** (B) uses `sg` as the IPA's
   final `G`; that `sg` really is `<b_poly_coefficients(chal), srs.g>` is a 2^15-term SRS MSM,
   extrapolated at **~18 hours and ~7 TB** of elaborator memory in-kernel (§6.1). It is measured
   TRUE in Rust by the extractor (`[gt8]`) and discharged out-of-circuit by openmina's own
   `accumulator_check`; it is **not** checked in this kernel. Without (A), (B) is a statement
   about an opening against a `G` the proof supplied.
3. **Poseidon's collision resistance**, as everywhere a transcript is used.
4. **`p` is prime** — §4's non-residue certificates are Euler's criterion.
5. The SRS itself: that `srs.g` and `srs.h` are what they claim is not checked by anything here.

## Cost, measured

34 × 255-bit RCB ladders per instance of the relation (2×15 `lr` + the aggregate + `u_base` + `sg`
+ `h`) ≈ 13 s of kernel at §6.1's 0.19 s/ladder unit; `delta` enters with coefficient 1 and costs
no ladder. The sponge continuation is ~50 Poseidon permutations, evaluated by the COMPILER — as
`MinaRealBlockTranscript`'s are, and as these were when they were `#guard`s. Ten instances of the relation plus the transcript: **153 s /
14.3 GB peak RSS measured on hbox** (`lake build`; 174 s standalone on a loaded box) — the
prediction and the measurement agree, which is what makes the 5h extrapolation in §6.1 worth
anything.

## What pins the gold

The extractor asserts (B) **directly, deterministically, with arkworks group arithmetic**, before
emitting: `[gt6]` is `residual.is_zero()`, and `[gt7]` re-runs it at `z1 + 1` and at
`combined + G` and requires BOTH to be non-zero. `[gt8]` asserts (A). All of it sits behind
`kimchi::verifier::verify = Ok(())` and `SRS::verify = true` on the same object.

## Axiom hygiene — ⚠ CORRECTED 2026-08-05, because the old line was FALSE-BY-OMISSION

`#assert_namespace_axioms` pins **26 theorems kernel-clean**, and **9 are `except`ed** as
`native_decide` + `#assert_compiled`: the IPA-transcript replay and its non-vacuity controls.

⚠ This header used to read *"Axiom-clean: `by decide` and `#guard`; no `sorry`, no `native_decide`"*.
Every clause was literally true and the sentence was misleading, because the nine `#guard`s ran the
**same unsafe compiled evaluator `native_decide` runs on** — the file was already trusting the
compiler for the whole sponge replay, and the phrase "no `native_decide`" read as though it were not.
Converting them changed no trust; it made the trust COUNTABLE, and it is counted in the `except`
clause at the end of the file. No `sorry`. Zero `#guard`s.

NEW file. NOT imported by the `Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapOpeningGate`
-/

namespace Dregg2.Circuit.Emit.MinaWrapOpeningGate

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt padd msmComm)
open Dregg2.Circuit.Emit.PastaPoseidonFq (SpongeSt fpParams newSponge absorbMany challenge squeeze1)
open Dregg2.Circuit.Emit.KimchiVerify (endoMap)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 4000000

open Dregg2.Circuit.Emit.MinaRealBlockTranscript (fpTape ZCOMM_XY TCOMM_XY FQ_DIGEST ENDO_R)
open Dregg2.Circuit.Emit.MinaRealBlockGate (ZETA ZETAW UU CIP)
open Dregg2.Circuit.Emit.MinaWrapAggregationGate (COMBINED_GOLD)


/-! ## §1 — the block's opening proof, as group elements and scalars -/

/-! ## §2 — the IPA challenges, DERIVED (§3) and then USED -/

/-! ## §3 — ⚑ THE TRANSCRIPT CONTINUES: every challenge of the opening argument, DERIVED.

`MinaRealBlockTranscript.wrapPhase1` ran the Fq-sponge to ζ′ and stopped. `oracles(...)` takes
its `digest()` on a CLONE (`verifier.rs:283`), so the sponge `SRS::verify` receives is exactly
that state. It is rebuilt here from the transcript module's own tape and pinned by the digest
before a single further absorb. -/

/-- ⚑ **IT IS THE TRANSCRIPT'S PHASE-1 STATE**: its digest is the `FQ_DIGEST` phase 2 chains on.

⚠ `native_decide`, and it says so. This was a `#guard` until 2026-08-05, which ran the SAME unsafe
compiled evaluator with the name, the term and the axiom record deleted — so nothing is trusted here
that was not trusted before, and `#assert_compiled` now makes that trust COUNTABLE. -/
theorem the_phase1_state_digests_to_the_transcript_digest :
    (Dregg2.Circuit.Emit.PastaPoseidonFq.digestInto fpParams wrapPhase1State qN == FQ_DIGEST)
      = true := by native_decide
#assert_compiled the_phase1_state_digests_to_the_transcript_digest

/-- ⚑ **THE RESULT**: `t`, all 15 IPA prechallenges and `c′` of a REAL Mina block's opening
argument fall out of the sponge the block's own transcript leaves behind.

⚠ These eight were `#guard`s until 2026-08-05. Each is `native_decide` — the SAME unsafe compiled
evaluator a `#guard` already ran — now carrying a name, a term and an axiom record. -/
theorem the_ipa_transcript_replays_the_blocks_own_opening :
    (ipaTranscript CIP_SHIFTED LR_XY DELTA_XY == (T_FQ, IPA_PRECHALS, C_PRE)) = true := by
  native_decide
#assert_compiled the_ipa_transcript_replays_the_blocks_own_opening

/-! ⚑ Non-vacuity, one per stage of the stream. Without these the replay above would be satisfied by
a sponge that ignored most of its input. -/

/-- The absorbed `combined_inner_product` is INSIDE the transcript: move it and `t` moves. -/
theorem moving_the_inner_product_moves_t :
    ((ipaTranscript (CIP_SHIFTED + 1) LR_XY DELTA_XY).1 != T_FQ) = true := by native_decide
#assert_compiled moving_the_inner_product_moves_t

/-- An IPA round point moves its own challenge and every later one, but NOT `t` — `t` is squeezed
before the rounds are absorbed, and this is that ordering as a fact. -/
theorem a_round_point_leaves_t_alone :
    ((ipaTranscript CIP_SHIFTED (LR_XY.set 0 ((LR_XY.getD 0 []).set 0 0)) DELTA_XY).1 == T_FQ)
      = true := by native_decide
#assert_compiled a_round_point_leaves_t_alone

/-- …and DOES move the prechallenges. -/
theorem a_round_point_moves_the_prechallenges :
    ((ipaTranscript CIP_SHIFTED (LR_XY.set 0 ((LR_XY.getD 0 []).set 0 0)) DELTA_XY).2.1
      != IPA_PRECHALS) = true := by native_decide
#assert_compiled a_round_point_moves_the_prechallenges

/-- ⚑ The LAST round is read too — a fold that stopped early would pass the first control and fail
this one. -/
theorem the_last_ipa_round_is_absorbed :
    ((ipaTranscript CIP_SHIFTED (LR_XY.set 14 ((LR_XY.getD 14 []).set 3 0)) DELTA_XY).2.1
      != IPA_PRECHALS) = true := by native_decide
#assert_compiled the_last_ipa_round_is_absorbed

/-- `delta` is absorbed AFTER the rounds, so it leaves the 15 prechallenges alone… -/
theorem delta_leaves_the_prechallenges_alone :
    ((ipaTranscript CIP_SHIFTED LR_XY (DELTA_XY.set 0 0)).2.1 == IPA_PRECHALS) = true := by
  native_decide
#assert_compiled delta_leaves_the_prechallenges_alone

/-- …and moves `c′`. -/
theorem delta_moves_c_prime :
    ((ipaTranscript CIP_SHIFTED LR_XY (DELTA_XY.set 0 0)).2.2 != C_PRE) = true := by native_decide
#assert_compiled delta_moves_c_prime

/-- ⚑ **AND THE SPLIT ABSORB IS THE RIGHT ONE.** Absorbing `cip` UNSPLIT is a different transcript,
so `sponge.rs`'s `q > p` branch is load-bearing rather than cosmetic. -/
theorem the_split_absorb_of_absorb_fr_is_load_bearing :
    ((let s := absorbMany fpParams wrapPhase1State [CIP_SHIFTED]
      (squeeze1 fpParams s).2) != T_FQ) = true := by native_decide
#assert_compiled the_split_absorb_of_absorb_fr_is_load_bearing

/-- **`derived_ipa_challenges`** — the 15 prechallenges endo-lift to the `chal` the relation
scales `L` and `R` by. -/
theorem derived_ipa_challenges : IPA_PRECHALS.map (endoMap ENDO_R) = CHAL_F := by decide +kernel

/-- **`derived_c`** — and `c′` lifts to `c`, the scalar the whole of `Q` is multiplied by. -/
theorem derived_c : endoMap ENDO_R C_PRE = (C : Fq) := by decide +kernel

/-- **`derived_endo_discriminates_here`** — the lift is not true for free at these values. -/
theorem derived_endo_discriminates_here :
    endoMap ENDO_R (C_PRE + 1) ≠ (C : Fq)
    ∧ endoMap ENDO_R (IPA_PRECHALS.getD 0 0) ≠ (CHAL.getD 1 0 : Fq) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-! ## §3b — the remaining scalars, derived from the derived challenges -/

/-- **`chal_inv_are_inverses`** — `chal_inv` really is `batch_inversion(chal)`; the `L` scalars
are the inverses of the `R` scalars, which is the whole shape of the IPA fold. -/
theorem chal_inv_are_inverses :
    (CHAL_F.zip CHAL_INV_F).all (fun p => decide (p.1 * p.2 = 1)) = true := by decide +kernel

/-- ⚑ **`b0_is_the_b_polynomial`** — `b0` is `b_poly(chal, ζ) + r·b_poly(chal, ζω)` at the gate's
OWN ζ and evalscale `r`, both of which `MinaRealBlockTranscript` derives. So the `u_base`
coefficient in the relation descends from the transcript too. -/
theorem b0_is_the_b_polynomial :
    bPoly CHAL_F ZETA + UU * bPoly CHAL_F ZETAW = (B0 : Fq) := by decide +kernel

/-- **`b0_reads_every_challenge`** — and moving the first or the last challenge moves it. -/
theorem b0_reads_every_challenge :
    bPoly (CHAL_F.set 0 (CHAL_F.getD 0 0 + 1)) ZETA
        + UU * bPoly (CHAL_F.set 0 (CHAL_F.getD 0 0 + 1)) ZETAW ≠ (B0 : Fq)
    ∧ bPoly (CHAL_F.set 14 (CHAL_F.getD 14 0 + 1)) ZETA
        + UU * bPoly (CHAL_F.set 14 (CHAL_F.getD 14 0 + 1)) ZETAW ≠ (B0 : Fq) := by
  refine ⟨?_, ?_⟩ <;> decide +kernel

/-- **`cip_is_the_gates_cip`** — the `combined_inner_product` this relation folds is the one
`MinaRealBlockGate`'s C8 proved is the `(ξ, r)`-fold of the block's claimed evaluations. Without
this the relation would be about an unrelated number. -/
theorem cip_is_the_gates_cip : (CIP_N : Fq) = CIP := by decide +kernel

/-- **`cip_shifted_is_shift_scalar`** — and what the sponge absorbed is that value minus `2^255`,
`shift_scalar`'s `q > p` branch. -/
theorem cip_shifted_is_shift_scalar : (CIP_SHIFTED : Fq) + (2 : Fq) ^ 255 = CIP := by decide +kernel

/-! ## §4 — `u_base`, through the group map

`ipa.rs:190-194`: `U = of_coordinates(group_map.to_group(challenge_fq()))`. The map is SvdW06
(`groupmap/src/lib.rs:65-125`): three candidate x-coordinates, take the first whose `x³ + 5` is a
square. The in-kernel version takes the inverse and the square root as WITNESSES and certifies the
skipped candidates as non-residues by Euler's criterion. -/

/-- **`group_map_params_are_what_setup_builds`** — every one of the five constants satisfies the
equation `setup()` defines it by, so they are not five opaque numbers. `u = 1` because `f(1) = 6`
is the first non-zero value of the search. -/
theorem group_map_params_are_what_setup_builds :
    GM_U = 1 ∧ GM_FU = GM_U ^ 3 + 5 ∧ GM_FU ≠ 0
    ∧ GM_SQRT3 * GM_SQRT3 = -(3 * GM_U * GM_U)
    ∧ GM_SQRT3_MU2 * 2 = GM_SQRT3 - GM_U
    ∧ GM_INV3U2 * (3 * GM_U * GM_U) = 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

/-- **`gm_alpha_is_the_inverse`** — `alpha` is the inverse `potential_xs` computes, at the `t`
the sponge produced. -/
theorem gm_alpha_is_the_inverse :
    GM_ALPHA * ((T_FP * T_FP + GM_FU) * (T_FP * T_FP)) = 1 := by decide +kernel

/-- **`group_map_selects_the_third_candidate`** — the first two candidates' `x³ + 5` are
NON-RESIDUES, so `get_xy`'s search really does fall through to the third. Without this the choice
of branch would be transcribed rather than derived. -/
theorem group_map_selects_the_third_candidate :
    (isNonResidue (ZMod.val ((potentialXs (T_FP * T_FP) GM_ALPHA).1 ^ 3 + 5))
      && isNonResidue (ZMod.val ((potentialXs (T_FP * T_FP) GM_ALPHA).2.1 ^ 3 + 5))) = true := by
  decide +kernel

/-- **`nonresidue_test_discriminates`** — and the test is not true for free. The SELECTED
candidate's `x³ + 5` is NOT a non-residue by the same certificate, and neither are `1` or `4`.
Without this, `group_map_selects_the_third_candidate` would be consistent with an `isNonResidue`
that says yes to everything, and the branch derivation would be theatre. -/
theorem nonresidue_test_discriminates :
    (isNonResidue (ZMod.val ((potentialXs (T_FP * T_FP) GM_ALPHA).2.2 ^ 3 + 5))
      || isNonResidue 1 || isNonResidue 4) = false := by decide +kernel

/-- **`group_map_y_is_a_square_root`** — and the third candidate's `x³ + 5` IS a square, with
`GM_Y` a root of it. -/
theorem group_map_y_is_a_square_root :
    GM_Y * GM_Y = (potentialXs (T_FP * T_FP) GM_ALPHA).2.2 ^ 3 + 5 := by decide +kernel

/-- ⚑ **`u_base_is_o1labs_u_base`** — and the point that construction lands on IS the `u_base`
o1-labs' `SRS::verify` computes on this block. -/
theorem u_base_is_o1labs_u_base :
    projEqM pN U_BASE (7847223366405709834624373952445684657634586309849412081950229810208103281928, 25813443087253962394072244031100642980583105487873972469944046669628245627812, 1) = true := by decide +kernel

/-- **`u_base_is_on_pallas`**. -/
theorem u_base_is_on_pallas : projOnCurveM pN curveB U_BASE = true := by decide +kernel

/-! **Residual, named**: which of the two roots `sqrt()` returns is arkworks' Tonelli-Shanks
convention, and `GM_Y` is transcribed from it rather than derived. `tamper_u_base_sign` below is
what makes that a bounded gap rather than an unexamined one: the OTHER root breaks the relation,
so the sign is load-bearing and is pinned by o1-labs' own output. -/

/-! ## §5 — ⚑ THE RUNG: the opening relation -/

/-- **`opening_inputs_are_real_pallas_points`** — the 15 `L`, 15 `R`, `sg`, `delta`, `u_base`,
`srs.h` and the aggregate are all on `y² = x³ + 5` over `Fp`, and `sg` and `delta` are distinct
finite points. -/
theorem opening_inputs_are_real_pallas_points :
    (LR_L.all (projOnCurveM pN curveB) && LR_R.all (projOnCurveM pN curveB)
      && projOnCurveM pN curveB SG && projOnCurveM pN curveB DELTA
      && projOnCurveM pN curveB SRS_H && projOnCurveM pN curveB COMBINED_GOLD
      && !isInfM pN SG && !isInfM pN DELTA && !projEqM pN SG DELTA) = true := by decide +kernel

/-- ⚑⚑ **`opening_relation_holds`** — **the IPA opening relation of a REAL Mina devnet block
holds in the Lean kernel.** 34 × 255-bit RCB ladders and 35 complete adds over the block's own
`lr` chain, its `sg`, its `delta`, the 47-term aggregate of all its commitments, and the
`u_base` §4 derived; at the `c`, `chal` and `b0` §3 derived from its own transcript. The result
is the point at infinity.

This is the first statement in this campaign whose truth says a COMMITTED polynomial has the
evaluation the proof claims — subject to the two assumptions the header names and does not
discharge: P10, and rung 5h's `sg == <s, srs.g>`. -/
theorem opening_relation_holds : isInfM pN realResidual = true := by decide +kernel

/-! ## §6 — tamper poles

Each moves exactly one input of the relation and the residual stops being `O`. Without these,
§5 would be consistent with a fold that collapses to the identity for structural reasons. -/

/-- **`tamper_z1`** — one added to the prover's `z1`. It appears in three terms at once. -/
theorem tamper_z1 :
    isInfM pN (openingResidual C (Z1 + 1) Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE SG DELTA)
      = false := by decide +kernel

/-- **`tamper_z2`** — one added to `z2`, the `srs.h` blinding-balance scalar. -/
theorem tamper_z2 :
    isInfM pN (openingResidual C Z1 (Z2 + 1) CHAL CHAL_INV COMBINED_GOLD U_BASE SG DELTA)
      = false := by decide +kernel

/-- **`tamper_c`** — one added to the challenge `c` that scales the whole of `Q`. -/
theorem tamper_c :
    isInfM pN (openingResidual (C + 1) Z1 Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE SG DELTA)
      = false := by decide +kernel

/-- **`tamper_first_ipa_challenge`** — one added to `chal[0]`, which scales `R[0]`. -/
theorem tamper_first_ipa_challenge :
    isInfM pN (openingResidual C Z1 Z2 (CHAL.set 0 (CHAL.getD 0 0 + 1)) CHAL_INV
      COMBINED_GOLD U_BASE SG DELTA) = false := by decide +kernel

/-- **`tamper_last_ipa_challenge_inverse`** — and one added to `chal_inv[14]`, which scales
`L[14]`. So both ends of the 15-round chain and both sides of each round are read. -/
theorem tamper_last_ipa_challenge_inverse :
    isInfM pN (openingResidual C Z1 Z2 CHAL (CHAL_INV.set 14 (CHAL_INV.getD 14 0 + 1))
      COMBINED_GOLD U_BASE SG DELTA) = false := by decide +kernel

/-- ⚑ **`tamper_aggregate`** — the 47-term aggregate replaced by a DIFFERENT real Pallas point of
the same block (`ft_comm`, which is one of its 47 summands). This is the pole that says the
commitments are what is being opened: change what was committed and the opening fails. -/
theorem tamper_aggregate :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV
      Dregg2.Circuit.Emit.MinaWrapGroupGate.FT_COMM_GOLD U_BASE SG DELTA) = false := by decide +kernel

/-- **`tamper_sg`** — `sg` replaced by `delta`. `sg` is the IPA's final `G`; the relation is a
statement about it, and rung 5h is what would say it is `<s, srs.g>`. -/
theorem tamper_sg :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE DELTA DELTA)
      = false := by decide +kernel

/-- **`tamper_delta_dropped`** — the `+delta` term omitted (the identity in its place). -/
theorem tamper_delta_dropped :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV COMBINED_GOLD U_BASE SG Oproj)
      = false := by decide +kernel

/-- ⚑ **`tamper_u_base_sign`** — `u_base` negated, i.e. the OTHER square root of §4's `x³ + 5`.
This is what bounds the residual §4 names: the sign arkworks' `sqrt()` chooses is load-bearing,
so it is pinned by o1-labs' own output rather than free. -/
theorem tamper_u_base_sign :
    isInfM pN (openingResidual C Z1 Z2 CHAL CHAL_INV COMBINED_GOLD
      (U_BASE.1, (pN - U_BASE.2.1 % pN) % pN, U_BASE.2.2) SG DELTA) = false := by decide +kernel

-- ⚑ The nine `except`ed theorems are the IPA-transcript replay and its non-vacuity controls. They
-- were `#guard`s until 2026-08-05, which ran the SAME unsafe compiled evaluator with the name, the
-- term and the axiom record DELETED — invisible to this very assertion. As `native_decide` +
-- `#assert_compiled` the trust is identical and now COUNTABLE: it appears here, by name, as nine
-- theorems this namespace does not claim kernel-clean. That is the point of the conversion.
-- ⚠ Not `decide`: the replay is ~100 Poseidon permutations over 255-bit `Fp`, which is where the
-- kernel stops reaching and the compiled evaluator does not.
#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapOpeningGate
  except the_phase1_state_digests_to_the_transcript_digest
    the_ipa_transcript_replays_the_blocks_own_opening
    moving_the_inner_product_moves_t a_round_point_leaves_t_alone
    a_round_point_moves_the_prechallenges the_last_ipa_round_is_absorbed
    delta_leaves_the_prechallenges_alone delta_moves_c_prime
    the_split_absorb_of_absorb_fr_is_load_bearing

end Dregg2.Circuit.Emit.MinaWrapOpeningGate

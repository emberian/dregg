import Dregg2.Circuit.Emit.MinaWrapGroupData
/-!
# Dregg2.Circuit.Emit.MinaWrapGroupGate — the Wrap **`ft_comm`** assembly, in-kernel, on the
REAL Mina devnet block's own Pallas commitments.

`docs/MINA-REAL-BLOCK-GATE.md` §3 stated the honest scope of the reality gate: the commitments
"are dumped as Pallas points but **nothing in-kernel touches them**". This file is the first
thing that does. Every check below consumes group elements of Mina devnet block **539508**
(state hash `3NLmVB6Fs3dm4kXNkgwheHXzJXNpCCwEDe76RpTVeBTNujm12zNk`) and lands on a value
produced by o1-labs' own code.

## The object

`kimchi/src/verifier.rs:897-963` — Maller's optimization — builds

```text
f_comm       = MSM(commitments, linearization scalars)          -- verifier.rs:897
ft_comm      = f_comm.chunk_commitment(zeta^max_poly_size)
                 - t_comm.chunk_commitment(zeta^max_poly_size).scale(zeta^n - 1)
```

`PicklesFinalize.picklesFtComm` transcribes that shape over a commutative ring and proves the
`zeta_to_domain_size` tie (`ftComm_ties_zeta_to_domain_size`, `ftComm_honest_agrees`,
`ftComm_forgery_moves_it`). It has never been **evaluated on points**. Here the same assembly
runs over K4a's RCB complete add and K4b's `scMulLadderM` ladder — the gadgets
`pallasCompleteAdd_forces` / `pallasLadder_forces` prove compute the real group law mod the
real prime — on the real block's real commitments.

## Why this rung is affordable, measured

The devnet blockchain Wrap verifier index has **zero** `linearization.index_terms`. Every
selector / coefficient / witness column the linearization could reference has its evaluation
SUPPLIED by the proof, so kimchi folds it into the linearization *constant term* — which is
exactly the scalar C5/`ftEval0R` already reproduces on this block. The only column with no
supplied evaluation is `sigma_comm[PERMUTS-1]`: `s` carries `PERMUTS-1 = 6` evaluations, not 7.
So **`f_comm` is a ONE-term MSM**, and the whole `ft_comm` assembly is 10 scalar
multiplications, not the open-ended MSM the plan assumed.

## What pins the gold values

`to_batch` is private, so `metatheory/fixtures/pickles-extractors/src/bin/wrap_group_export.rs`
rebuilds `f_comm` / `ft_comm` from o1-labs' own `perm_scalars`, `PolishToken::evaluate`,
`Context::get_column`, `PolyComm::multi_scalar_mul`, `chunk_commitment` and `scale`, and then
hands the reconstruction — inside the full 47-entry `evaluations` list — to **o1-labs' own
`SRS::verify`**, the real verifier's final IPA opening check. It returns `true`; with `ft_comm`
displaced by `+G` it returns `false`. So `FT_COMM_GOLD` below is not our arithmetic restated:
it is the only point that satisfies the real block's opening proof.

## What this is NOT

It is **one rung**. The Wrap group check also needs the 40-term `public_comm` Lagrange MSM, the
47-term `combine_commitments` polyscale fold, and `check_bulletproof`, whose `<s,G>` term is a
`2^15`-scalar MSM over the SRS and is **deferred by design** (K4c / P10). See
`docs/MINA-REAL-BLOCK-GATE.md` §6. Nothing here discharges the P10 opening floor.

Facts about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06);
no `sorry`. NEW file; imports read-only
(`PastaScalarMul`, transitively `PastaCurveComplete`/`PastaCurve`/`PastaField`). NOT imported by
the `Dregg2` root, per house practice for gates.

⚑ **SPLIT (data ⇢ `MinaWrapGroupData`).** The type `Pt`, the group operations
(`smul`/`padd`/`pneg`/`chunkedComm`/`msmComm`/`ftCommOf`), the block's literal commitments and
the computed objects (`fComm`/`chunkedT`/`ftComm`) now live in
`Dregg2.Circuit.Emit.MinaWrapGroupData`, in THIS namespace, imported below. Nothing moved out of
this module's *statements* — the thirteen theorems are unchanged, and
`#assert_namespace_axioms` still covers the whole namespace, data included. The move exists so a
consumer that needs `Pt` or a literal does not have to reduce thirteen 255-bit Pallas ladders in
the kernel to get it.
-/

namespace Dregg2.Circuit.Emit.MinaWrapGroupGate

open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete
  (curveB3 rcbAddM Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.PastaScalarMul (scMulLadderM)

set_option autoImplicit false
set_option maxRecDepth 4000000


/-! ## §4 — the inputs are real Pallas points

Anti-vacuity floor: if these were junk the checks below would be about nothing. Each of the 8
input commitments and each of the 3 gold outputs satisfies `Y^2 Z = X^3 + 5 Z^3 (mod p)` — the
real Pallas curve at the real prime. -/

/-- **`real_inputs_are_on_pallas`** — the block's own `t_comm` chunks and the verifier index's
`sigma_comm[6]` are on `y^2 = x^3 + 5` over `Fp`. -/
theorem real_inputs_are_on_pallas :
    (TCHUNKS.all (projOnCurveM pN curveB) && projOnCurveM pN curveB SIGMA6) = true := by native_decide

/-- **`gold_outputs_are_on_pallas`** — and so are the three values o1-labs' code produced. -/
theorem gold_outputs_are_on_pallas :
    (projOnCurveM pN curveB CHUNKED_T_GOLD && projOnCurveM pN curveB F_COMM_GOLD
      && projOnCurveM pN curveB FT_COMM_GOLD) = true := by native_decide

/-- **`gold_outputs_are_distinct_affine_points`** — and they are three DIFFERENT finite points,
so an assembly that collapsed to a constant could not pass all three checks in §5. -/
theorem gold_outputs_are_distinct_affine_points :
    (projEqM pN CHUNKED_T_GOLD F_COMM_GOLD || projEqM pN F_COMM_GOLD FT_COMM_GOLD
      || projEqM pN CHUNKED_T_GOLD FT_COMM_GOLD
      || isInfM pN CHUNKED_T_GOLD || isInfM pN F_COMM_GOLD || isInfM pN FT_COMM_GOLD)
      = false := by native_decide

/-! ## §5 — THE RUNG: the assembly reproduces o1-labs' values on the real block -/

/-- **`chunkedT_reproduces_kimchi`** — the Horner fold of the block's **7 real `t_comm` Pallas
points** with `zeta^(2^15)`, over the RCB complete add, IS `PolyComm::chunk_commitment`'s output.
Six 255-bit ladders and seven complete adds on real group elements. -/
theorem chunkedT_reproduces_kimchi : projEqM pN chunkedT CHUNKED_T_GOLD = true := by native_decide

/-- **`fComm_reproduces_kimchi`** — the linearization MSM (`perm_scalars * sigma_comm[6]`) IS
`PolyComm::multi_scalar_mul`'s output. -/
theorem fComm_reproduces_kimchi : projEqM pN fComm F_COMM_GOLD = true := by native_decide

/-- **`ftComm_reproduces_kimchi`** — and the whole Maller assembly reproduces the `ft_comm` that
o1-labs' own `SRS::verify` accepts against this block's opening proof. This is the first check in
the campaign whose value depends on a group element. -/
theorem ftComm_reproduces_kimchi : projEqM pN ftComm FT_COMM_GOLD = true := by native_decide

/-- **`ftComm_is_a_finite_point`** — and the result is not the point at infinity, so
`projEqM`'s `Z = 0` degeneracy cannot be what made the previous theorem true. -/
theorem ftComm_is_a_finite_point : isInfM pN ftComm = false := by native_decide

/-- **`fComm_chunking_is_a_no_op`** — `chunk_commitment` on the one-chunk `f_comm` is the
identity, which is WHY `zeta^srs_len` reaches `ft_comm` only through `t_comm`. The group-side
counterpart of `PicklesFinalize.ftComm_srs_length_unused_at_one_chunk`; stated on the real
value rather than assumed. -/
theorem fComm_chunking_is_a_no_op :
    projEqM pN (chunkedComm ZETA_SRS [F_COMM_GOLD]) F_COMM_GOLD = true := by native_decide

/-! ## §6 — tamper poles

Each pole moves exactly one input of the assembly and the result stops matching o1-labs' value.
Without these, §5 would be consistent with an assembly that ignores its inputs. -/

/-- **`tamper_perm_scalar`** — one added to the linearization scalar. -/
theorem tamper_perm_scalar :
    projEqM pN (msmComm [(PERM_SCALAR + 1, SIGMA6)]) F_COMM_GOLD = false := by native_decide

/-- **`tamper_msm_base_point`** — the same scalar against a DIFFERENT real Pallas point from the
same block (`t_comm[0]` in place of `sigma_comm[6]`). -/
theorem tamper_msm_base_point :
    projEqM pN (msmComm [(PERM_SCALAR, TCHUNKS.headD Oproj)]) F_COMM_GOLD = false := by native_decide

/-- **`tamper_zeta_to_srs_length`** — one added to `zeta^(2^15)`. At 7 chunks the SRS-length
scalar IS read (the counterpart of `ftComm_srs_length_used_at_two_chunks`). -/
theorem tamper_zeta_to_srs_length :
    projEqM pN (chunkedComm (ZETA_SRS + 1) TCHUNKS) CHUNKED_T_GOLD = false := by native_decide

/-- **`tamper_chunk_order`** — the same 7 points folded the other way round. Horner is not
symmetric, so a fold that got the chunk order wrong is caught. -/
theorem tamper_chunk_order :
    projEqM pN (chunkedComm ZETA_SRS TCHUNKS.reverse) CHUNKED_T_GOLD = false := by native_decide

/-- **`tamper_zeta_to_domain_size`** — one added to the Maller scale factor `zeta^n - 1`. -/
theorem tamper_zeta_to_domain_size :
    projEqM pN (ftCommOf ZETA_SRS (ZETA_DOM_M1 + 1) F_TERMS TCHUNKS) FT_COMM_GOLD
      = false := by native_decide

/-- **`tamper_drop_maller_term`** — dropping the `- (zeta^n - 1) * chunk(t_comm)` subtraction
entirely, i.e. claiming `ft_comm = f_comm`. This is the pole that says the `t_comm` points are
load-bearing in `ft_comm` and not merely computed alongside it. -/
theorem tamper_drop_maller_term :
    projEqM pN (chunkedComm ZETA_SRS [fComm]) FT_COMM_GOLD = false := by native_decide

/-- **`tamper_add_instead_of_subtract`** — and the SIGN of the Maller term is load-bearing:
`f_comm + (zeta^n - 1) * chunk(t_comm)` is not `ft_comm`. -/
theorem tamper_add_instead_of_subtract :
    projEqM pN (padd (chunkedComm ZETA_SRS [msmComm F_TERMS])
                     (smul ZETA_DOM_M1 (chunkedComm ZETA_SRS TCHUNKS)))
               FT_COMM_GOLD = false := by native_decide

-- Every theorem in this file is a fact about block 539508's data, checked by compiled evaluation and
-- pinned `#assert_compiled` (since 2026-11-06), so there is no kernel-clean namespace to pin.

#assert_compiled tamper_add_instead_of_subtract
#assert_compiled tamper_drop_maller_term
#assert_compiled tamper_zeta_to_domain_size
#assert_compiled tamper_chunk_order
#assert_compiled tamper_zeta_to_srs_length
#assert_compiled tamper_msm_base_point
#assert_compiled tamper_perm_scalar
#assert_compiled fComm_chunking_is_a_no_op
#assert_compiled ftComm_is_a_finite_point
#assert_compiled ftComm_reproduces_kimchi
#assert_compiled fComm_reproduces_kimchi
#assert_compiled chunkedT_reproduces_kimchi
#assert_compiled gold_outputs_are_distinct_affine_points
#assert_compiled gold_outputs_are_on_pallas
#assert_compiled real_inputs_are_on_pallas
end Dregg2.Circuit.Emit.MinaWrapGroupGate

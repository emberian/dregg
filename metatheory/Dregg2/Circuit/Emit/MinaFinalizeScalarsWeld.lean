/-
# `Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld` — ⚑ the finalize-scalars program on Mina devnet
block 539508's OWN wire, against upstream's OWN answers — now including the gate-linearization
derivation.

## What is measured here, and against what

`MinaFinalizeScalars.finalizeProg` is a 1046-op straight-line rendering of `ftEval0R` + `cipR` +
`permScalarR` **+ `gateLinConst`** (stage 11, the v2 addition). This file runs its DENOTATION
(`progEval` — the same function the forcing story is about, not the emit driver's memoized
renderer) on the real block's environment and pins:

  * **cip** — the program's ξ-fold equals `MinaRealBlockGate.CIP`, the `combined_inner_product`
    `proof.oracles(…)` computed for the block;
  * **perm** — the program's permutation scalar equals `MinaWrapGroupGate.PERM_SCALAR`, o1-labs'
    own `perm_scalars` output for the block;
  * ⚑ **lct** — the program's stage-11 derivation equals `MinaRealBlockGate.LCT`, the block's
    own `PolishToken::evaluate(linearization.constant_term)` (the number
    `Bridge/MinaWrapFtEval0Weld` §2b-head showed `gateLinConst` reproduces byte-for-byte). This
    is the value the closing eq gate forces the `LCT` claim to be — the weld that turns the
    `lct-shift` family from ACCEPTED into REFUSED.
  * **the reference tie at the fixture point** — `cipRef`/`permRef`/`lctRef` (the thin
    compositions of the shipped bodies stated in the Prog file's §5) equal the same numbers, so
    program and reference are tied AT THIS POINT through the block rather than through each
    other. ⚑ And `every_selector_isolates_its_body` bumps each of the six gate selectors and
    pins program == reference at each bumped point: since `gateLinConst` is affine in each
    selector with the body's α-combined value as coefficient, the six differences isolate each
    TRANSCRIBED BODY's value individually — a transcription error in any one body cannot hide.
    ⚠ Still a differential (seven points, real data, both sides upstream-derived), NOT the
    generic `progEval = reference` theorem; that stays the named §5 residual.
  * **the constants** — `OMEGA_Q` derived AND the fixture's; the three `zkPolyR` roots its
    powers; the seven shifts the conformance fixture's own list; the witnessed inverse inverts.
    (The v2 constants — endo, MDS, the quotient trio — carry their ring checks as named theorems
    in the AIR file; their fidelity to the DEPLOYED verifier index is what the lct equality
    above measures, since a wrong endo or a wrong MDS entry moves `gateLinConst` on this block —
    `Bridge/MinaWrapFtEval0Weld.a_wrong_endo_moves_the_constant_term`.)
  * **the discriminations** — one bumped eval moves the cip; a bumped σ eval moves the perm; and
    ⚑ a bumped `LCT` CLAIM now leaves the derivation fixed while the claim moves — the eq gate's
    refusal content, stated at the fixture. (At v1 the same bump moved the cip and the trace
    still PROVED; that acceptance is what stage 11 closes.)

## Axiom hygiene

Facts about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06);
no `#guard`.
Rooted in `MinaBridgeGuards` (CI), per the 2026-08-08 orphan burn-down.
-/
import Dregg2.Circuit.Emit.MinaFinalizeScalars
import Dregg2.Circuit.Emit.MinaRealBlockGate
import Dregg2.Circuit.Emit.MinaWrapGroupData
import Dregg2.Bridge.MinaMultiBlockConformance

namespace Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld

open Dregg2.Circuit.Emit.MinaFinalizeScalars
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Bridge.MinaWrapFtEval0 (invCand invOk rootOfUnity powFast)

abbrev Fq := ZMod qN

set_option autoImplicit false
set_option maxRecDepth 1000000

open Dregg2.Circuit.Emit.MinaRealBlockGate in
/-- ⚑ **THE REAL BLOCK'S ENVIRONMENT**, index for index the Prog file's §1 value table. The eval
columns are `EVZ`/`EVZW`'s slices (their indices 4… are the wire's 43 columns; 0..3 the prefix),
the challenges are the block's raw/mapped scalars, the claims are upstream's own outputs
(`LCT` included — the linearization constant term IS a claim block now), `DINV` is produced HERE
by Fermat's ladder, and the v2 constant blocks (endo, the `fq_kimchi` MDS, the `EndomulScalar`
quotient trio, the small literals) are the AIR file's own derived literals. -/
def env0Real : Nat → Fq := fun v =>
  if v < 43 then EVZ.getD (4 + v) 0
  else if v < 86 then EVZW.getD (4 + (v - 43)) 0
  else if v = vFT1 then EVZW.getD 3 0
  else if v = vPUBZ then EVZ.getD 2 0
  else if v = vPUBW then EVZW.getD 2 0
  else if v = vBETA then BETA
  else if v = vGAMMA then GAMMA
  else if v = vALPHA then ALPHA
  else if v = vZETA then ZETA
  else if v = vXI then VV
  else if v = vRSQ then UU
  else if v = vBP0Z then EVZ.getD 0 0
  else if v = vBP1Z then EVZ.getD 1 0
  else if v = vBP0W then EVZW.getD 0 0
  else if v = vBP1W then EVZW.getD 1 0
  else if v = vCIPCL then CIP
  else if v = vPERMCL then ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq)
  else if v = vDINV then invCand ((ZETA - ((OM3_C : Nat) : Fq)) * (ZETA - 1))
  else if v = vLCT then LCT
  else if v = vONE then 1
  else if v = vZERO then 0
  else if v = vOM3 then ((OM3_C : Nat) : Fq)
  else if v = vOM2 then ((OM2_C : Nat) : Fq)
  else if v = vOM1 then ((OM1_C : Nat) : Fq)
  else if 108 ≤ v ∧ v < 115 then ((SHIFTS_Q.getD (v - 108) 0 : Nat) : Fq)
  else if v = vENDO then ((ENDO_Q : Nat) : Fq)
  else if 116 ≤ v ∧ v < 125 then ((MDS_Q.getD (v - 116) 0 : Nat) : Fq)
  else if v = vCA then ((CA_Q : Nat) : Fq)
  else if v = vCB then ((CB_Q : Nat) : Fq)
  else if v = vCC then ((CC_Q : Nat) : Fq)
  else if v = vC3 then 3
  else if v = vC6 then 6
  else if v = vC11 then 11
  else 0

/-- The computed-value indices the three claim equalities read — extracted from the program by
the claim block each compares (`.y` is the derived value), not hand-numbered. ⚠ v1 read the cip
result as "the last op's `.y`"; stage 11's appended ops made that op the LCT eq, so all three
now use the same filter shape. -/
def cipResultV : Nat :=
  ((finalizeProg.filter (fun o => o.k == FKind.eq && o.x == vCIPCL)).headD ⟨.eq, 0, 0⟩).y
def permResultV : Nat :=
  ((finalizeProg.filter (fun o => o.k == FKind.eq && o.x == vPERMCL)).headD ⟨.eq, 0, 0⟩).y
def lctResultV : Nat :=
  ((finalizeProg.filter (fun o => o.k == FKind.eq && o.x == vLCT)).headD ⟨.eq, 0, 0⟩).y

/-- A one-index perturbation. -/
def bump (env0 : Nat → Fq) (v : Nat) (d : Fq) : Nat → Fq :=
  fun u => if u = v then env0 v + d else env0 u

/-! ## §1 — the constants are the deployed Wrap domain's, from two sources each. -/

set_option maxHeartbeats 1000000000 in
/-- ⚑ `OMEGA_Q` is simultaneously the fixture's generator (`MinaRealBlockGate.OMEGA`) and the
DERIVED `2^14`-th root of unity — carried nowhere, checked both ways. -/
theorem the_domain_generator_is_derived_and_the_fixtures :
    ((OMEGA_Q : Nat) : Fq) = Dregg2.Circuit.Emit.MinaRealBlockGate.OMEGA
    ∧ ((OMEGA_Q : Nat) : Fq) = rootOfUnity qN LOG2N := by
  refine ⟨by native_decide, by native_decide⟩

set_option maxHeartbeats 1000000000 in
/-- The three `zkPolyR` roots are the generator's `n−3`, `n−2`, `n−1` powers. -/
theorem the_zk_roots_are_the_generators_powers :
    ((OM3_C : Nat) : Fq) = powFast ((OMEGA_Q : Nat) : Fq) (DOMN - 3)
    ∧ ((OM2_C : Nat) : Fq) = powFast ((OMEGA_Q : Nat) : Fq) (DOMN - 2)
    ∧ ((OM1_C : Nat) : Fq) = powFast ((OMEGA_Q : Nat) : Fq) (DOMN - 1) := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

set_option maxHeartbeats 1000000000 in
/-- The seven shifts are the Wrap fixture's own list — for EVERY wrap block the conformance
fixture carries (shifts are per-index constants), and the fixture list is non-empty, so the
`all` is not vacuous. -/
theorem the_shifts_are_the_wrap_fixtures :
    (Dregg2.Bridge.MinaMultiBlockConformance.WRAP_BLOCKS.map (fun b => b.shift)).all
        (fun s => s == SHIFTS_Q) = true
    ∧ Dregg2.Bridge.MinaMultiBlockConformance.WRAP_BLOCKS.isEmpty = false := by
  refine ⟨by native_decide, by native_decide⟩

set_option maxHeartbeats 1000000000 in
/-- The witnessed inverse inverts the block's own C5 denominator — the check the AIR performs
in-trace (`den·DINV = 1`), performed here on the fixture. -/
theorem the_witnessed_inverse_inverts :
    ((Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - ((OM3_C : Nat) : Fq))
        * (Dregg2.Circuit.Emit.MinaRealBlockGate.ZETA - 1)) * env0Real vDINV = 1 := by
  native_decide

/-! ## §2 — ⚑⚑ THE DIFFERENTIAL: the program reproduces upstream's three numbers. -/

set_option maxHeartbeats 1000000000 in
/-- ⚑⚑ **THE PROGRAM'S ξ-FOLD IS THE BLOCK'S `combined_inner_product`** — ft_eval0 recomputed in
the middle from the same wire, landing on `proof.oracles(…)`'s own number. -/
theorem the_program_reproduces_the_blocks_cip :
    progEval env0Real cipResultV = Dregg2.Circuit.Emit.MinaRealBlockGate.CIP := by
  native_decide

set_option maxHeartbeats 1000000000 in
/-- ⚑⚑ **THE PROGRAM'S PERMUTATION SCALAR IS o1-labs' OWN `perm_scalars` VALUE** — conjunct 4's
number, reached through the shared σ-factor chain. -/
theorem the_program_reproduces_perm_scalars :
    progEval env0Real permResultV
      = ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq) := by
  native_decide

set_option maxHeartbeats 1000000000 in
/-- ⚑⚑ **THE PROGRAM'S STAGE-11 DERIVATION IS THE BLOCK'S OWN LINEARIZATION CONSTANT TERM** —
`MinaRealBlockGate.LCT`, the number `PolishToken::evaluate(linearization.constant_term)` produced
and `Bridge/MinaWrapFtEval0Weld` §2b-head tied to `gateLinConst`. This is the value the closing
eq gate forces the `LCT` claim block to be. -/
theorem the_program_derives_the_blocks_lct :
    progEval env0Real lctResultV = Dregg2.Circuit.Emit.MinaRealBlockGate.LCT := by
  native_decide

set_option maxHeartbeats 1000000000 in
/-- The reference composition (the Prog file's §5 `cipRef`/`permRef`/`lctRef`) meets the same
numbers at the same point — program and reference tied through the block. -/
theorem the_reference_meets_the_same_numbers :
    cipRef env0Real ((OMEGA_Q : Nat) : Fq) = Dregg2.Circuit.Emit.MinaRealBlockGate.CIP
    ∧ permRef env0Real ((OMEGA_Q : Nat) : Fq)
        = ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq)
    ∧ lctRef env0Real = Dregg2.Circuit.Emit.MinaRealBlockGate.LCT := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

set_option maxHeartbeats 4000000000 in
/-- ⚑ **EACH GATE BODY'S VALUE, ISOLATED.** Bump each of the six selector evals by 1 and the
program's derived lct STILL equals `gateLinConst` of the bumped environment (`lctRef`).
`gateLinConst` is affine in each selector with that body's α-combined value as the coefficient,
so together with `the_program_derives_the_blocks_lct` these six equalities pin every transcribed
BODY's value against the reference individually — a mis-transcribed body would need the bumped
and honest points to agree on a wrong value simultaneously. Differential, seven points total. -/
theorem every_selector_isolates_its_body :
    (List.range 6).all (fun k =>
      progEval (bump env0Real (selCol k) 1) lctResultV
        == lctRef (bump env0Real (selCol k) 1)) = true := by
  native_decide

/-! ## §3 — the discriminations: each equality above can go red. -/

set_option maxHeartbeats 1000000000 in
/-- One bumped eval column moves the cip — the ξ-fold genuinely reads the wire. -/
theorem a_bumped_eval_moves_the_cip :
    progEval (bump env0Real (vEZ 5) 1) cipResultV
      ≠ Dregg2.Circuit.Emit.MinaRealBlockGate.CIP := by
  native_decide

set_option maxHeartbeats 1000000000 in
/-- ⚑⚑ **THE `lct-shift` FAMILY'S REFUSAL CONTENT, AT THE FIXTURE.** Bumping the `LCT` CLAIM
leaves the stage-11 DERIVATION fixed (the derivation reads only the welded evals and constants),
while the claim moves off it — so the closing eq gate's two compared blocks now differ, which is
exactly what the deployed prover refuses in
`circuit/tests/mina_finalize_scalars_proves.rs` §5. At v1 the same bump produced an ACCEPTING
trace (the port's one-parameter family); this pair of facts is that family's closure, stated in
the denotation. -/
theorem a_bumped_lct_claim_diverges_from_its_derivation :
    progEval (bump env0Real vLCT 1) lctResultV = Dregg2.Circuit.Emit.MinaRealBlockGate.LCT
    ∧ bump env0Real vLCT 1 vLCT ≠ Dregg2.Circuit.Emit.MinaRealBlockGate.LCT := by
  refine ⟨by native_decide, by native_decide⟩

set_option maxHeartbeats 1000000000 in
/-- A bumped σ eval moves the perm — conjunct 4 genuinely reads the permutation columns. -/
theorem a_bumped_sigma_moves_the_perm :
    progEval (bump env0Real (sCol 2) 1) permResultV
      ≠ ((Dregg2.Circuit.Emit.MinaWrapGroupGate.PERM_SCALAR : Nat) : Fq) := by
  native_decide

set_option maxHeartbeats 1000000000 in
/-- A bumped witness eval moves the derived lct — the bodies genuinely read the wire (w₆ is
Poseidon's s1 group head, endomul's `n` and `EndomulScalar`'s x₀ — three bodies at once). -/
theorem a_bumped_witness_eval_moves_the_derived_lct :
    progEval (bump env0Real (wCol 6) 1) lctResultV
      ≠ Dregg2.Circuit.Emit.MinaRealBlockGate.LCT := by
  native_decide

#assert_compiled the_domain_generator_is_derived_and_the_fixtures
#assert_compiled the_zk_roots_are_the_generators_powers
#assert_compiled the_shifts_are_the_wrap_fixtures
#assert_compiled the_witnessed_inverse_inverts
#assert_compiled the_program_reproduces_the_blocks_cip
#assert_compiled the_program_reproduces_perm_scalars
#assert_compiled the_program_derives_the_blocks_lct
#assert_compiled the_reference_meets_the_same_numbers
#assert_compiled every_selector_isolates_its_body
#assert_compiled a_bumped_eval_moves_the_cip
#assert_compiled a_bumped_lct_claim_diverges_from_its_derivation
#assert_compiled a_bumped_sigma_moves_the_perm
#assert_compiled a_bumped_witness_eval_moves_the_derived_lct

end Dregg2.Circuit.Emit.MinaFinalizeScalarsWeld

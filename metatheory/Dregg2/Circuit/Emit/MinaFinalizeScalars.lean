/-
# `Dregg2.Circuit.Emit.MinaFinalizeScalars` — ⚑⚑ **`dregg-mina-finalize-scalars::v2`: Pickles'
finalize conjuncts 3 and 4, rendered as a Lean-authored scheduled AIR at the Pallas-scalar
prime — now WITH the gate-linearization leaf, so the `LCT` port is CLOSED.**

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** Every op, every selector leg, every carry mask, every pin below is
authored here (program: `MinaFinalizeScalarsProg.lean`, same namespace) and lowered by
`EffectLower.lowerAir`. Rust parses the emitted descriptor, fills cells from the Lean-rendered
witness, and runs the deployed prover. It authors no constraint. House Law #1.

## THE OBJECT — a lowering, not new mathematics

`PicklesFinalize.finalizeOtherProof` is a four-way AND (`step.rs:876-884`):
`xi_correct && b_correct && combined_inner_product_correct && plonk_checks_passed`.
This descriptor renders conjuncts 3 and 4 whole: the Wrap-side `ft_eval0` (C5), the FULL
47-entry `combined_inner_product` ξ-fold (C8) with the in-AIR `ft_eval0` in slot 3,
`perm_scalars`, **and — new at v2 — `KimchiVerify.gateLinConst`'s six transcribed gate bodies,
whose closing eq gate forces the `LCT` claim block against the trace's own derivation.** 1046
sound field ops at the Pallas-scalar prime, one op per row, on the scheduled substrate
`PastaCurveScheduled`/`AirCrossRow`/`AirSelectorForcing`.

## ⚑⚑ v1 → v2: THE `LCT` PORT IS CLOSED, AND THE FALSIFIER IS NAMED

At v1 the linearization constant term was a PI-pinned PORT welded to NOTHING: `cipActualOf` is
affine in `LCT`, so the **`lct-shift`** adversarial trace — `LCT` bumped, the cip claim
recomputed — PROVED AND VERIFIED, a one-parameter family of accepting cip claims. Stage 11
(`MinaFinalizeScalarsProg` §2) derives `gateLinConst` in-AIR over the same 86 welded eval blocks
and eq-forces the claim, so **that exact family is now REFUSED by this descriptor's own gates**
(`circuit/tests/mina_finalize_scalars_proves.rs` §5 measures the refusal by name). `LCT` now
stands where `CIP_CLAIM`/`PERM_CLAIM` stand: a published claim compared against the trace's own
arithmetic.

## ⚑ WHAT THIS LEAF FORCES, AND WHERE EACH FORCING LIVES

Stated per conjunct, at this tree's resolution:

1. **Conjunct 3, `cipCorrect` — IN-AIR, whole** (this descriptor): `CIP_CLAIM ≡ cipR ξ r esZ
   esW` where `esZ`/`esW` are assembled from this trace's own input blocks, the `ft` slot is the
   in-AIR `ftEval0R` value (ζ-ladder, `zkPolyR`, the witnessed inverse forced by `den·DINV = 1`,
   both C5 folds), and the `LCT` its closing subtraction reads is FORCED by stage 11's eq gate
   to be `gateLinConst` of the same welded evals. No in-trace free input remains.
2. **Conjunct 4, `plonkChecksPassed` — IN-AIR, whole**: `PERM_CLAIM ≡ permScalarR` (upstream's
   comparison list is the literal `[perm]`, `plonk_checks.rs:363-366`).
3. **The eval inputs — AT THE FOLD, not here**: every `EZ_k`/`EW_k`/`FT1`/`PUBZ`/`PUBW` block is
   a PI-pinned PORT of this leaf; the recursion fold `cb.connect`s them elementwise to the
   phase-2 chain links' absorbed pairs. Until those connects run, this leaf's statement is "the
   ξ-fold and gate linearization of the blocks this claim names", not "of the block's
   transcript".
4. **The challenges — AT THE FOLD**: β/γ weld to `MinaPhase1Chain`'s squeezes (low-128 reads:
   in-leaf zero-pins on limbs 16..31); α, ζ, ξ, r weld to `dregg-mina-xi-endo-lift::v1`
   instances (the descriptor is challenge-independent; each instance is a witness/PI regen).
5. **The b-halves `BP0Z/BP1Z/BP0W/BP1W` — PORTS, never recomputed.** They weld to conjunction
   instances' published registers at the fold.
6. **`CIP_CLAIM`/`PERM_CLAIM`'s consumers — AT THE FOLD/HOST**: `CIP_CLAIM` connects to the
   conjunction's `CIP` block, `PERM_CLAIM` to the `f_comm` MSM's scalar lane. `LCT` has NO
   external consumer and needs none — it is forced in-trace.

## PORTS, in `SeamSpec` §4's sense: NONE — and that is a statement, not an omission

Every published block here is CONSUMED by gates — the evals by the folds AND the six gate
bodies, the challenges by the ladders, the claims (`CIP`, `PERM`, now `LCT` too) by eq
comparisons — so `portIslandFree` is FALSE of each and none is representable as a `PiPort`. The
external-forcing obligations are CLAIM-WELD obligations, `SeamSpec`-shaped, one per row of the
table above. **`LCT`'s row is GONE from that obligation list**: its weld is in-trace, this
descriptor's own eq gates, not a seam. No `proofBind` leg exists in this AIR, so no
`bound := none` seam is created here.

## THE SCHEDULE, THE REGISTER, AND WHAT IS REUSED

One op per row, 1046 ops, 2048-row trace (power of two, idle tail). A 1047-wide one-hot phase
register, `AirSelectorForcing`'s own register discipline at this size. Values live in 32-limb
slots allocated by `AirColumnAlloc.allocate` over the program's own live ranges (rendered by
`FsAllocRender.lean` — machine-spliced, never hand-typed: the v1 `hiTable` hand-paste with a
fabricated tail is the standing reason); slots are carried across rows by **complement-masked**
transition legs. The sound cores are `PastaCurveSound.mulCore/addSubCore` at `qLimb`, verbatim.

## WHAT IS PROVED HERE vs WHAT IS PENDING — read before citing

* PROVED (kernel): the layout facts — op count, table coverage, read coverage, same-slot
  disjointness (restated at v2 over the zipped tables — same fact, an O(n²) walk instead of an
  O(n³) `getD` scan the kernel cannot afford at 1177 values), width, committed width, constraint
  census, the quotient-constant and endo ring checks. PROVED (compiled, confessed at the
  statements): `mainRailOk`, `pinsTied`.
* PROVED in `MinaFinalizeScalarsWeld` (kernel): the real-block differential — the program's
  denotation on Mina devnet block 539508's own wire reproduces `proof.oracles(…)`'s
  `combined_inner_product`, o1-labs' own `perm_scalars`, AND the block's `linConstTerm`
  (`MinaRealBlockGate.LCT`), with the six selector bumps pinning program-vs-reference at six
  further points (each gate body's value isolated). ⚠ The GENERIC `progEval = reference` theorem
  is pending and named in the Prog file's §5 — the weld is a differential, not a proof about all
  inputs.
* ⚠ PENDING, NAMED: the trace-level forcing composition (this trace's rows + carries + phase
  register ⇒ the slot values ARE the denotation) is `AirCrossRow`'s walk at 1046 ops, NOT built
  here. Until it lands, this descriptor's polarity evidence is the deployed prover's refusal
  (real, measured in `circuit/tests/mina_finalize_scalars_proves.rs`), which is behavioural, not
  a proof — say it that way.

## Axiom hygiene

`#assert_axioms` on every named theorem; no `sorry`/`admit`; zero `#guard`s. ⚠ TWO theorems are
compiler-trusted and say so at their statements (`finalizeAir_mainRailOk`, `finalizeAir_pinsTied`
— `native_decide` + `#assert_compiled`, the `SeamSpec` §4 wall). Since 2026-11-06 the facts about
concrete data are `native_decide` + `#assert_compiled` too; the general theorems are kernel.
-/
import Dregg2.Circuit.Emit.MinaFinalizeScalarsProg
import Dregg2.Circuit.Emit.PastaCurveScheduled
import Dregg2.Circuit.Emit.EffectLowerCertified
import Dregg2.Circuit.Emit.PastaPoseidonFq
import Dregg2.Bridge.MinaWrapFtEval0

namespace Dregg2.Circuit.Emit.MinaFinalizeScalars

open Dregg2.Circuit (Assignment Expr Constraint)
open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2 TableDef TableId mainTableDef WindowExpr)
open Dregg2.Circuit.EffectAirIR (EffectAir AirLeg LimbsLeg WindowLeg PiPinLeg)
open Dregg2.Circuit.TableAirIR (RowSel)
open Dregg2.Circuit.Emit.EffectLower (lowerAir P)
open Dregg2.Circuit.Emit.EffectVmEmit (VmRow)
open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK SB CB NG limbCols carryCols rangeTidW qLimb limbAt)
open Dregg2.Circuit.Emit.PastaAddSubSound (NA ACB CBITS acarryCols)
open Dregg2.Circuit.Emit.PastaCurveSound (SoundCore mulCore addSubCore)
open Dregg2.Circuit.Emit.PastaCurveScheduled (sumLoc)
open Dregg2.Circuit.Emit.AirColumnAlloc (SsaOp LiveRange liveRanges allocate allocWidth defTime lastUse)
open Dregg2.Circuit.Emit.KimchiVerify (PERMUTS)

set_option autoImplicit false
set_option maxRecDepth 1000000

/-! ## §4 — THE SCHEDULE AS DATA, and the allocation.

⚑ **The allocation is MATERIALIZED as three literal tables**, not called at every use site. The
reason is kernel arithmetic, not taste: `slotOfF` appears inside every leg, and a `by decide`
that re-ran `AirColumnAlloc.allocate` (a huge fold at 1177 values × 1046 ops) per reference
would never terminate. The tables are the allocator's own answer — RENDERED by
`FsAllocRender.lean` and machine-spliced (never hand-typed); what the kernel then checks —
directly, cheaply, and about the object the legs actually use — are the three facts the layout
needs:

  * `the_ranges_cover_the_reads` — every op reads its sources inside their live windows and
    defines its value at its own row;
  * `same_slot_ranges_are_disjoint` — two values sharing a slot never overlap;
  * `the_tables_cover_the_values` — the tables span the value space and the slots fit.

Those three are what the forcing walk consumes; the allocator itself is tooling. -/

def slotTable : List Nat := [28, 120, 118, 116, 114, 112, 110, 32, 33, 34, 35, 36, 37, 31, 101, 99, 97, 95, 93, 91, 89, 87, 85, 83, 81, 79, 77, 75, 73, 71, 69, 67, 65, 63, 61, 59, 57, 22, 23, 24, 25, 26, 27, 20, 119, 117, 115, 113, 111, 109, 108, 107, 106, 105, 104, 103, 102, 100, 98, 96, 94, 92, 90, 88, 86, 84, 82, 80, 78, 76, 74, 72, 70, 68, 66, 64, 62, 60, 58, 56, 55, 54, 53, 52, 51, 49, 121, 44, 122, 21, 19, 30, 15, 50, 48, 126, 124, 125, 123, 127, 47, 18, 45, 29, 46, 2, 3, 4, 17, 38, 39, 40, 41, 42, 43, 137, 128, 129, 130, 131, 132, 133, 134, 135, 136, 140, 139, 138, 141, 142, 143, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 1, 0, 2, 3, 4, 2, 3, 4, 5, 4, 4, 1, 5, 1, 5, 1, 5, 1, 6, 7, 8, 7, 8, 7, 9, 7, 9, 8, 10, 8, 10, 9, 11, 9, 11, 10, 12, 10, 12, 11, 13, 11, 13, 12, 14, 12, 14, 13, 15, 16, 15, 17, 15, 17, 15, 16, 15, 16, 15, 17, 15, 17, 15, 16, 15, 16, 15, 17, 15, 17, 15, 16, 15, 16, 15, 13, 15, 13, 15, 14, 13, 1, 0, 4, 0, 1, 3, 0, 1, 0, 1, 3, 1, 2, 1, 2, 1, 2, 1, 2, 1, 1, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 2, 1, 2, 3, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 2, 0, 1, 0, 1, 2, 0, 1, 0, 2, 0, 1, 0, 2, 3, 0, 2, 0, 3, 0, 2, 0, 2, 0, 1, 2, 1, 2, 1, 3, 1, 3, 1, 4, 1, 4, 1, 5, 1, 5, 1, 6, 1, 6, 1, 7, 1, 7, 1, 8, 1, 8, 1, 9, 1, 9, 1, 10, 1, 10, 1, 11, 1, 11, 1, 12, 1, 12, 1, 13, 1, 13, 1, 14, 1, 14, 1, 15, 1, 15, 1, 16, 1, 16, 1, 17, 18, 19, 1, 17, 1, 17, 18, 19, 20, 17, 18, 17, 18, 2, 3, 4, 18, 2, 3, 2, 4, 18, 19, 2, 4, 2, 4, 18, 19, 20, 4, 18, 4, 18, 5, 6, 7, 18, 5, 6, 5, 7, 18, 19, 5, 7, 5, 7, 18, 19, 20, 7, 18, 7, 18, 8, 9, 10, 18, 8, 9, 8, 10, 18, 19, 8, 10, 8, 10, 18, 19, 20, 10, 18, 10, 18, 11, 12, 13, 18, 11, 12, 11, 13, 18, 19, 11, 13, 11, 13, 18, 19, 20, 13, 18, 13, 18, 14, 15, 16, 18, 14, 15, 14, 15, 13, 14, 11, 13, 11, 12, 10, 11, 8, 10, 8, 9, 7, 8, 5, 7, 5, 6, 4, 5, 2, 4, 2, 3, 2, 3, 1, 2, 3, 4, 5, 6, 7, 6, 8, 9, 8, 10, 4, 8, 4, 2, 4, 2, 4, 5, 4, 8, 4, 5, 4, 5, 4, 9, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 2, 3, 2, 3, 2, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 3, 4, 5, 4, 6, 4, 7, 8, 7, 8, 9, 10, 8, 9, 8, 6, 8, 6, 9, 11, 12, 4, 9, 4, 6, 4, 7, 4, 6, 7, 6, 10, 6, 11, 12, 11, 12, 13, 14, 12, 13, 12, 10, 12, 10, 13, 15, 16, 6, 13, 6, 10, 6, 11, 6, 10, 11, 10, 14, 10, 15, 16, 15, 16, 17, 18, 16, 17, 16, 14, 16, 14, 17, 19, 20, 10, 17, 10, 14, 10, 15, 10, 14, 15, 14, 18, 14, 19, 20, 19, 20, 21, 22, 20, 21, 20, 18, 20, 18, 21, 23, 24, 14, 21, 14, 18, 14, 19, 14, 18, 19, 18, 22, 18, 23, 24, 23, 24, 25, 26, 24, 25, 24, 22, 24, 22, 25, 27, 28, 18, 25, 18, 22, 18, 23, 18, 22, 18, 22, 18, 22, 18, 19, 18, 14, 18, 14, 18, 14, 18, 14, 15, 10, 14, 10, 14, 10, 14, 10, 11, 6, 10, 6, 10, 6, 10, 6, 7, 4, 6, 4, 6, 4, 6, 4, 5, 3, 4, 5, 6, 5, 6, 4, 6, 4, 7, 4, 7, 8, 7, 8, 9, 10, 11, 10, 11, 10, 11, 10, 11, 10, 11, 12, 13, 14, 15, 16, 15, 17, 15, 18, 15, 19, 15, 20, 15, 4, 15, 20, 15, 20, 21, 20, 15, 21, 15, 20, 14, 11, 5, 8, 5, 8, 11, 8, 7, 8, 11, 8, 11, 14, 11, 8, 14, 8, 11, 13, 12, 6, 9, 6, 9, 10, 6, 9, 6, 8, 6, 7, 5, 6, 5, 6, 4, 5, 4, 5, 4, 5, 4, 5, 4, 5, 6, 5, 6, 5, 6, 7, 6, 7, 6, 7, 8, 7, 8, 7, 8, 9, 8, 9, 8, 9, 10, 9, 10, 9, 10, 11, 10, 11, 10, 11, 12, 11, 12, 11, 12, 13, 12, 13, 12, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 13, 14, 15, 14, 15, 14, 15, 14, 15, 14, 15, 14, 15, 14, 15, 14, 15, 14, 15, 16, 15, 16, 5, 15, 5, 16, 5, 16, 5, 6, 5, 15, 5, 15, 5, 6, 5, 7, 5, 7, 5, 6, 5, 7, 5, 7, 5, 6, 5, 7, 5, 7, 5, 6, 5, 7, 5, 7, 5, 6, 5, 7, 5, 7, 5, 6, 5, 6, 7, 6, 7, 6, 7, 6, 8, 6, 8, 6, 8, 6, 9, 6, 9, 6, 9, 6, 10, 6, 10, 6, 10, 6, 11, 6, 11, 6, 11, 6, 12, 6, 12, 6, 12, 6, 15, 6, 15, 6, 15, 6, 16, 6, 16, 6, 16, 6, 16, 6, 15, 6, 12, 6, 11, 6, 10, 6, 9, 6, 8, 6, 7, 5, 6, 5, 6, 5, 6, 0, 1, 0, 1, 0] -- FS-SPLICE:slotTable
def loTable : List Nat := [0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 50, 51, 52, 53, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63, 64, 65, 66, 67, 68, 69, 70, 71, 72, 73, 74, 75, 76, 77, 78, 79, 80, 81, 82, 83, 84, 85, 86, 87, 88, 89, 90, 91, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 114, 115, 116, 117, 118, 119, 120, 121, 122, 123, 124, 125, 126, 127, 128, 129, 130, 131, 132, 133, 134, 135, 136, 137, 138, 139, 140, 141, 142, 143, 144, 145, 146, 147, 148, 149, 150, 151, 152, 153, 154, 155, 156, 157, 158, 159, 160, 161, 162, 163, 164, 165, 166, 167, 168, 169, 170, 171, 172, 173, 174, 175, 176, 177, 178, 179, 180, 181, 182, 183, 184, 185, 186, 187, 188, 189, 190, 191, 192, 193, 194, 195, 196, 197, 198, 199, 200, 201, 202, 203, 204, 205, 206, 207, 208, 209, 210, 211, 212, 213, 214, 215, 216, 217, 218, 219, 220, 221, 222, 223, 224, 225, 226, 227, 228, 229, 230, 231, 232, 233, 234, 235, 236, 237, 238, 239, 240, 241, 242, 243, 244, 245, 246, 247, 248, 249, 250, 251, 252, 253, 254, 255, 256, 257, 258, 259, 260, 261, 262, 263, 264, 265, 266, 267, 268, 269, 270, 271, 272, 273, 274, 275, 276, 277, 278, 279, 280, 281, 282, 283, 284, 285, 286, 287, 288, 289, 290, 291, 292, 293, 294, 295, 296, 297, 298, 299, 300, 301, 302, 303, 304, 305, 306, 307, 308, 309, 310, 311, 312, 313, 314, 315, 316, 317, 318, 319, 320, 321, 322, 323, 324, 325, 326, 327, 328, 329, 330, 331, 332, 333, 334, 335, 336, 337, 338, 339, 340, 341, 342, 343, 344, 345, 346, 347, 348, 349, 350, 351, 352, 353, 354, 355, 356, 357, 358, 359, 360, 361, 362, 363, 364, 365, 366, 367, 368, 369, 370, 371, 372, 373, 374, 375, 376, 377, 378, 379, 380, 381, 382, 383, 384, 385, 386, 387, 388, 389, 390, 391, 392, 393, 394, 395, 396, 397, 398, 399, 400, 401, 402, 403, 404, 405, 406, 407, 408, 409, 410, 411, 412, 413, 414, 415, 416, 417, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455, 456, 457, 458, 459, 460, 461, 462, 463, 464, 465, 466, 467, 468, 469, 470, 471, 472, 473, 474, 475, 476, 477, 478, 479, 480, 481, 482, 483, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 516, 517, 518, 519, 520, 521, 522, 523, 524, 525, 526, 527, 528, 529, 530, 531, 532, 533, 534, 535, 536, 537, 538, 539, 540, 541, 542, 543, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 558, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 569, 570, 571, 572, 573, 574, 575, 576, 577, 578, 579, 580, 581, 582, 583, 584, 585, 586, 587, 588, 589, 590, 591, 592, 593, 594, 595, 596, 597, 598, 599, 600, 601, 602, 603, 604, 605, 606, 607, 608, 609, 610, 611, 612, 613, 614, 615, 616, 617, 618, 619, 620, 621, 622, 623, 624, 625, 626, 627, 628, 629, 630, 631, 632, 633, 634, 635, 636, 637, 638, 639, 640, 641, 642, 643, 644, 645, 646, 647, 648, 649, 650, 651, 652, 653, 654, 655, 656, 657, 658, 659, 660, 661, 662, 663, 664, 665, 666, 667, 668, 669, 670, 671, 672, 673, 674, 675, 676, 677, 678, 679, 680, 681, 682, 683, 684, 685, 686, 687, 688, 689, 690, 691, 692, 693, 694, 695, 696, 697, 698, 699, 700, 701, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 745, 746, 747, 748, 749, 750, 751, 752, 753, 754, 755, 756, 757, 758, 759, 760, 761, 762, 763, 764, 765, 766, 767, 768, 769, 770, 771, 772, 773, 774, 775, 776, 777, 778, 779, 780, 781, 782, 783, 784, 785, 786, 787, 788, 789, 790, 791, 792, 793, 794, 795, 796, 797, 798, 799, 800, 801, 802, 803, 804, 805, 806, 807, 808, 809, 810, 811, 812, 813, 814, 815, 816, 817, 818, 819, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 840, 841, 842, 843, 844, 845, 846, 847, 848, 849, 850, 851, 852, 853, 854, 855, 856, 857, 858, 859, 860, 861, 862, 863, 864, 865, 866, 867, 868, 869, 870, 871, 872, 873, 874, 875, 876, 877, 878, 879, 880, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 905, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 922, 923, 924, 925, 926, 927, 928, 929, 930, 931, 932, 933, 934, 935, 936, 937, 938, 939, 940, 941, 942, 943, 944, 945, 946, 947, 948, 949, 950, 951, 952, 953, 954, 955, 956, 957, 958, 959, 960, 961, 962, 963, 964, 965, 966, 967, 968, 969, 970, 971, 972, 973, 974, 975, 976, 977, 978, 979, 980, 981, 982, 983, 984, 985, 986, 987, 988, 989, 990, 991, 992, 993, 994, 995, 996, 997, 998, 999, 1000, 1001, 1002, 1003, 1004, 1005, 1006, 1007, 1008, 1009, 1010, 1011, 1012, 1013, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1040, 1041, 1042, 1043, 1044, 1045] -- FS-SPLICE:loTable
def hiTable : List Nat := [282, 321, 515, 557, 744, 839, 1039, 880, 904, 905, 926, 921, 970, 976, 982, 988, 994, 1000, 1006, 1012, 1018, 780, 385, 392, 399, 406, 413, 420, 427, 434, 441, 448, 455, 462, 469, 476, 483, 134, 130, 126, 122, 118, 115, 281, 277, 273, 269, 265, 261, 257, 701, 699, 571, 598, 816, 771, 768, 581, 608, 635, 662, 689, 205, 201, 197, 193, 189, 185, 181, 177, 173, 169, 165, 161, 157, 153, 149, 145, 141, 137, 133, 129, 125, 121, 117, 114, 285, 290, 289, 103, 88, 1037, 60, 296, 297, 298, 294, 297, 293, 300, 113, 100, 1045, 966, 112, 14, 15, 16, 63, 67, 71, 75, 79, 83, 87, 745, 466, 467, 468, 473, 474, 475, 480, 481, 482, 878, 876, 875, 964, 1017, 1015, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 23, 94, 17, 18, 18, 105, 96, 21, 22, 22, 95, 25, 26, 27, 28, 29, 104, 93, 95, 33, 34, 35, 39, 37, 38, 106, 43, 41, 42, 107, 47, 45, 46, 108, 51, 49, 50, 109, 55, 53, 54, 110, 59, 57, 58, 111, 91, 87, 62, 66, 64, 65, 66, 70, 68, 69, 70, 74, 72, 73, 74, 78, 76, 77, 78, 82, 80, 81, 82, 86, 84, 85, 86, 90, 88, 89, 90, 92, 92, 101, 94, 97, 96, 97, 99, 99, 100, 101, 102, 286, 104, 105, 106, 107, 108, 109, 110, 111, 112, 113, 113, 115, 116, 119, 118, 119, 120, 123, 122, 123, 124, 127, 126, 127, 128, 131, 130, 131, 132, 135, 134, 135, 136, 139, 138, 139, 140, 143, 142, 143, 144, 147, 146, 147, 148, 151, 150, 151, 152, 155, 154, 155, 156, 159, 158, 159, 160, 163, 162, 163, 164, 167, 166, 167, 168, 171, 170, 171, 172, 175, 174, 175, 176, 179, 178, 179, 180, 183, 182, 183, 184, 187, 186, 187, 188, 191, 190, 191, 192, 195, 194, 195, 196, 199, 198, 199, 200, 203, 202, 203, 204, 207, 206, 207, 208, 211, 210, 211, 212, 215, 214, 215, 216, 219, 218, 219, 220, 223, 222, 223, 224, 227, 226, 227, 228, 231, 230, 231, 232, 235, 234, 235, 236, 239, 238, 239, 240, 243, 242, 243, 244, 247, 246, 247, 248, 251, 250, 251, 252, 255, 254, 255, 256, 259, 258, 259, 260, 263, 262, 263, 264, 267, 266, 267, 268, 271, 270, 271, 272, 275, 274, 275, 276, 279, 278, 279, 280, 283, 282, 283, 284, 287, 286, 287, 288, 291, 290, 291, 292, 295, 294, 295, 296, 299, 298, 299, 300, 300, 303, 303, 305, 305, 308, 307, 308, 309, 320, 312, 312, 314, 314, 317, 316, 317, 318, 319, 320, 321, 1040, 323, 324, 325, 396, 327, 328, 329, 397, 331, 332, 333, 398, 335, 336, 337, 417, 339, 340, 341, 418, 343, 344, 345, 419, 347, 348, 349, 438, 351, 352, 353, 439, 355, 356, 357, 440, 359, 360, 361, 459, 363, 364, 365, 460, 367, 368, 369, 461, 371, 372, 373, 480, 375, 376, 377, 481, 379, 380, 381, 482, 385, 386, 387, 386, 387, 388, 514, 392, 393, 394, 393, 394, 395, 512, 399, 400, 401, 400, 401, 402, 510, 406, 407, 408, 407, 408, 409, 508, 413, 414, 415, 414, 415, 416, 506, 420, 421, 422, 421, 422, 423, 504, 427, 428, 429, 428, 429, 430, 502, 434, 435, 436, 435, 436, 437, 500, 441, 442, 443, 442, 443, 444, 498, 448, 449, 450, 449, 450, 451, 496, 455, 456, 457, 456, 457, 458, 494, 462, 463, 464, 463, 464, 465, 492, 469, 470, 471, 470, 471, 472, 490, 476, 477, 478, 477, 478, 479, 488, 483, 484, 485, 484, 485, 486, 487, 488, 489, 490, 491, 492, 493, 494, 495, 496, 497, 498, 499, 500, 501, 502, 503, 504, 505, 506, 507, 508, 509, 510, 511, 512, 513, 514, 515, 1040, 529, 543, 526, 531, 521, 556, 554, 524, 527, 526, 527, 528, 532, 530, 531, 532, 552, 534, 536, 536, 550, 538, 539, 540, 548, 542, 546, 544, 545, 546, 547, 548, 549, 550, 551, 552, 553, 554, 555, 556, 557, 1041, 559, 560, 561, 562, 563, 564, 565, 566, 567, 568, 743, 570, 741, 572, 582, 588, 575, 576, 592, 579, 579, 594, 581, 584, 583, 584, 739, 590, 589, 588, 589, 590, 737, 592, 595, 594, 595, 735, 597, 733, 599, 609, 615, 602, 603, 619, 606, 606, 621, 608, 611, 610, 611, 731, 617, 616, 615, 616, 617, 729, 619, 622, 621, 622, 727, 624, 725, 626, 636, 642, 629, 630, 646, 633, 633, 648, 635, 638, 637, 638, 723, 644, 643, 642, 643, 644, 721, 646, 649, 648, 649, 719, 651, 717, 653, 663, 669, 656, 657, 673, 660, 660, 675, 662, 665, 664, 665, 715, 671, 670, 669, 670, 671, 713, 673, 676, 675, 676, 711, 678, 709, 680, 690, 696, 683, 684, 700, 687, 687, 702, 689, 692, 691, 692, 707, 698, 697, 696, 697, 698, 705, 700, 703, 702, 703, 704, 705, 706, 707, 708, 709, 710, 711, 712, 713, 714, 715, 716, 717, 718, 719, 720, 721, 722, 723, 724, 725, 726, 727, 728, 729, 730, 731, 732, 733, 734, 735, 736, 737, 738, 739, 740, 741, 742, 743, 744, 1042, 749, 747, 748, 796, 750, 751, 815, 753, 754, 783, 756, 757, 802, 796, 815, 761, 762, 763, 764, 765, 766, 767, 768, 819, 795, 814, 813, 794, 774, 838, 776, 836, 778, 834, 780, 832, 782, 784, 784, 830, 786, 787, 790, 789, 790, 793, 792, 793, 828, 799, 798, 797, 798, 799, 826, 801, 803, 803, 824, 805, 806, 809, 808, 809, 812, 811, 812, 822, 818, 817, 816, 817, 818, 820, 820, 821, 822, 823, 824, 825, 826, 827, 828, 829, 830, 831, 832, 833, 834, 835, 836, 837, 838, 839, 1043, 841, 842, 843, 844, 925, 846, 847, 848, 849, 931, 851, 852, 853, 854, 937, 856, 857, 858, 859, 943, 861, 862, 863, 864, 949, 866, 867, 868, 869, 955, 871, 872, 873, 874, 961, 876, 877, 878, 879, 967, 881, 882, 883, 884, 885, 886, 887, 888, 889, 890, 891, 892, 893, 894, 895, 896, 897, 898, 899, 900, 901, 902, 903, 904, 1038, 906, 907, 908, 909, 910, 911, 912, 913, 914, 915, 916, 917, 918, 919, 920, 921, 1036, 923, 924, 925, 927, 927, 932, 929, 930, 931, 933, 933, 938, 935, 936, 937, 939, 939, 944, 941, 942, 943, 945, 945, 950, 947, 948, 949, 951, 951, 956, 953, 954, 955, 957, 957, 962, 959, 960, 961, 963, 963, 968, 965, 966, 967, 969, 969, 970, 1034, 972, 973, 974, 975, 976, 1032, 978, 979, 980, 981, 982, 1030, 984, 985, 986, 987, 988, 1028, 990, 991, 992, 993, 994, 1026, 996, 997, 998, 999, 1000, 1024, 1002, 1003, 1004, 1005, 1006, 1022, 1008, 1009, 1010, 1011, 1012, 1020, 1014, 1015, 1016, 1017, 1018, 1019, 1020, 1021, 1022, 1023, 1024, 1025, 1026, 1027, 1028, 1029, 1030, 1031, 1032, 1033, 1034, 1035, 1036, 1037, 1038, 1039, 1044, 1041, 1042, 1043, 1044, 1045, 1045] -- FS-SPLICE:hiTable

def slotOfF (v : Nat) : Nat := slotTable.getD v 0
def loOfF (v : Nat) : Nat := loTable.getD v 0
def hiOfF (v : Nat) : Nat := hiTable.getD v 0

/-- The physical slot count. -/
def NSLOTS : Nat := 144 -- FS-SPLICE:nslots

set_option maxHeartbeats 40000000 in
/-- The three tables cover the value space and the slots fit. -/
theorem the_tables_cover_the_values :
    slotTable.length = NVALS ∧ loTable.length = NVALS ∧ hiTable.length = NVALS
    ∧ slotTable.all (· < NSLOTS) = true := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

set_option maxHeartbeats 400000000 in
/-- ⚑ **EVERY READ IS INSIDE ITS SOURCE'S LIVE WINDOW, AND EVERY DEFINITION IS AT ITS OWN ROW.**
This is the fact the cross-row gather consumes: op `i`'s gate reads its sources' slots AT row `i`,
and the carries hold each slot constant from the value's definition row to `i`. -/
theorem the_ranges_cover_the_reads :
    (List.range finalizeProg.length).all (fun i =>
      match finalizeProg[i]? with
      | some o =>
          loOfF o.x ≤ i && i ≤ hiOfF o.x && o.x < NVALS
          && (loOfF o.y ≤ i && i ≤ hiOfF o.y && o.y < NVALS)
          && loOfF (NIN_VALS + i) == i && i ≤ hiOfF (NIN_VALS + i)
      | none => false) = true := by native_decide

/-- The zipped `(slot, lo, hi)` table — what the pairwise disjointness walk consumes
element-wise. -/
def slotRanges : List (Nat × Nat × Nat) := slotTable.zip (loTable.zip hiTable)

/-- The pairwise check as one structural pass: each entry against every later entry — different
slot, or disjoint closed ranges. -/
def sameSlotDisjoint : List (Nat × Nat × Nat) → Bool
  | [] => true
  | t :: rest =>
      rest.all (fun u => t.1 != u.1 || decide (t.2.2 < u.2.1) || decide (u.2.2 < t.2.1))
      && sameSlotDisjoint rest

set_option maxHeartbeats 400000000 in
/-- ⚑ **TWO VALUES SHARING A SLOT NEVER OVERLAP.** The same fact v1 stated with an indexed
`getD` double-scan, restated at v2 over the zipped tables (`slotRanges`) so the kernel walks
~692K list cells once instead of `getD`-indexing each of them through 1177-entry literals — the
O(n³) form stopped being kernel-affordable at this op count. Stated over ALL pairs; the
same-slot filter is the `!=` disjunct. -/
theorem same_slot_ranges_are_disjoint : sameSlotDisjoint slotRanges = true := by native_decide

set_option maxHeartbeats 40000000 in
/-- Inputs and constants are live from row 0 — which is what makes a `.first` pin a pin on the
value every consuming gate reads. -/
theorem inputs_are_live_from_the_top :
    (List.range NIN_VALS).all (fun v => loOfF v == 0) = true := by native_decide

/-! ## §6 — THE COLUMN LAYOUT. -/

/-- Selector columns: phases `0 … 1045` then IDLE at 1046. `SEL` is the identity, as in
`PastaCurveScheduled` — a property of this layout, stated so it can be cited. -/
def NPHASE : Nat := finalizeProg.length
def SEL (i : Nat) : Nat := i
def SEL_IDLE : Nat := NPHASE

/-- The value slots begin after the selectors. -/
def VAL_BASE : Nat := NPHASE + 1
def valueColF (v : Nat) : Nat := VAL_BASE + SK * slotOfF v

/-- The witness pools, `PastaCurveScheduled`'s order: w1, then w8 (32), then w16 (62), adjacent
so each core's `wB`/`wB+1`/`wB+SK` strides land inside the right range class. -/
def W1_COL : Nat := VAL_BASE + SK * NSLOTS
def W8_BASE : Nat := W1_COL + 1
def W16_BASE : Nat := W8_BASE + SK
def FS_WIDTH : Nat := W16_BASE + (NG - 1)

def MUL_WIT : Nat := W8_BASE
def ADDSUB_WIT : Nat := W1_COL

/-! ## §7 — THE LEGS. -/

/-- Booleanity of every phase column, on every row (`.window .all`, not `.gate`, so the last row
is bound too — `PastaCurveScheduled`'s own reasoning). -/
def selBooleanLegs : List AirLeg :=
  (List.range (NPHASE + 1)).map (fun i =>
    AirLeg.window ⟨.all, .mul (.loc (SEL i)) (.add (.loc (SEL i)) (.const (-1)))⟩)

/-- Exactly one phase live per row. -/
def selOneHotLeg : AirLeg :=
  AirLeg.window ⟨.all, .add (sumLoc (List.range (NPHASE + 1))) (.const (-1))⟩

/-- The shift register: row 0 is phase 0; the indicator walks right; the idle column absorbs the
last phase and itself; phase 0 never returns. -/
def selShiftLegs : List AirLeg :=
  AirLeg.window ⟨.first, .add (.loc (SEL 0)) (.const (-1))⟩
  :: AirLeg.window ⟨.transition, .nxt (SEL 0)⟩
  :: AirLeg.window ⟨.transition,
       .add (.nxt SEL_IDLE)
         (.mul (.const (-1)) (.add (.loc (SEL (NPHASE - 1))) (.loc SEL_IDLE)))⟩
  :: (List.range (NPHASE - 1)).map (fun i =>
       AirLeg.window ⟨.transition,
         .add (.nxt (SEL (i + 1))) (.mul (.const (-1)) (.loc (SEL i)))⟩)

/-- Every value slot is byte-pooled on every row. -/
def valuePoolLegs : List AirLeg :=
  (List.range NSLOTS).map (fun k =>
    AirLeg.limbs ⟨limbCols (VAL_BASE + SK * k), SB, rangeTidW SB⟩)

/-- The three witness pools, by range class. -/
def witnessPoolLegs : List AirLeg :=
  [ AirLeg.limbs ⟨[W1_COL], CBITS, rangeTidW CBITS⟩
  , AirLeg.limbs ⟨(List.range SK).map (W8_BASE + ·), SB, rangeTidW SB⟩
  , AirLeg.limbs ⟨(List.range (NG - 1)).map (W16_BASE + ·), CB, rangeTidW CB⟩ ]

/-! ### The complement-masked carries.

A slot must carry its value across every transition EXCEPT the one that hands it to a new tenant.
The handover phases of slot `s` are `d − 1` for each value defined into `s` at row `d ≥ 1`; the
mask is `1 − Σ SEL(handovers)`, so the leg's size is the slot's TENANT count, not its live
length. On a live transition the mask reads 1 (`PhaseIndicator` + the handovers being elsewhere),
so `carried_constant` applies verbatim; on a handover it reads 0 and the slot is free. -/

/-- The rows at which slot `s` acquires a NEW tenant (the tenant's definition row), minus one:
the transitions the carry must NOT constrain. From the zipped literal tables (one structural
walk — the v1 indexed scan re-ran `getD` per value), so a leg build never runs the allocator. -/
def handoverPhases (s : Nat) : List Nat :=
  ((slotTable.zip loTable).filterMap (fun p =>
    if p.1 == s && decide (0 < p.2) then some (p.2 - 1) else none)).eraseDups

def carryMaskF (s : Nat) : WindowExpr :=
  .add (.const 1) (.mul (.const (-1)) (sumLoc ((handoverPhases s).map SEL)))

def carryLegsF : List AirLeg :=
  (List.range NSLOTS).flatMap (fun s =>
    (List.range SK).map (fun j =>
      AirLeg.window ⟨.transition,
        .mul (carryMaskF s)
          (.add (.nxt (VAL_BASE + SK * s + j))
                (.mul (.const (-1)) (.loc (VAL_BASE + SK * s + j))))⟩))

/-! ### The scheduled op gates. -/

def coreOfF : FKind → SoundCore
  | .mul => mulCore qLimb
  | .add => addSubCore qLimb 1 (-1)
  | .sub => addSubCore qLimb (-1) 1
  | .eq => { legs := fun _ _ _ _ => [], width := 0 }

def witOfF : FKind → Nat
  | .mul => MUL_WIT
  | _ => ADDSUB_WIT

def isGate : AirLeg → Bool
  | .gate _ => true
  | _ => false

def gateBy (sel : Nat) : AirLeg → AirLeg
  | .gate c => .gate ⟨.mul (.var sel) c.lhs, c.rhs⟩
  | l => l

/-- The 32 equality gates of an `eq` op — `SEL i · (x_j − y_j)`. -/
def eqLegs (i xB yB : Nat) : List AirLeg :=
  (List.range SK).map (fun j =>
    AirLeg.gate ⟨.mul (.var (SEL i))
      (.add (.var (xB + j)) (.mul (.const (-1)) (.var (yB + j)))), .const 0⟩)

def opLegsF (i : Nat) (o : FOp) : List AirLeg :=
  match o.k with
  | .eq => eqLegs i (valueColF o.x) (valueColF o.y)
  | k =>
      (((coreOfF k).legs (valueColF o.x) (valueColF o.y) (valueColF (NIN_VALS + i))
          (witOfF k)).filter isGate).map (gateBy (SEL i))

def scheduleLegsF : List AirLeg :=
  (List.range finalizeProg.length).flatMap
    (fun i => match finalizeProg[i]? with | some o => opLegsF i o | none => [])

/-! ### The constant pins, the zero-high pins, and the PI pins — all `.first`, all carried. -/

/-- Pin a block at row 0 to a 255-bit literal, limb by limb. -/
def constFirstBlock (col : Nat) (v : Nat) : List AirLeg :=
  (List.range SK).map (fun j =>
    AirLeg.window ⟨.first, .add (.loc (col + j)) (.const (-(limbAt v j)))⟩)

/-- ⚑ The Wrap-side domain generator (`MinaRealBlockGate.OMEGA`'s own value, the `2^14` domain),
and `zkPolyR`'s three roots as descriptor literals, computed by the kernel-friendly ladder
(`MinaWrapFtEval0.powFast`, 28 multiplies) rather than unary `Monoid.npow`. The weld checks
`OMEGA_Q` against `MinaWrapFtEval0.rootOfUnity qN 14` and the roots against `OMEGA_Q`'s powers. -/
def OMEGA_Q : Nat := 13720502009405270468270247285101677286753189198487843249698478072631298866919
def OM3_C : Nat := (Dregg2.Bridge.MinaWrapFtEval0.powFast ((OMEGA_Q : Nat) : ZMod qN) (DOMN - 3)).val
def OM2_C : Nat := (Dregg2.Bridge.MinaWrapFtEval0.powFast ((OMEGA_Q : Nat) : ZMod qN) (DOMN - 2)).val
def OM1_C : Nat := (Dregg2.Bridge.MinaWrapFtEval0.powFast ((OMEGA_Q : Nat) : ZMod qN) (DOMN - 1)).val

/-- The seven Tock coset shifts of the deployed Wrap verifier index —
`MinaMultiBlockConformance`'s own `shift` fixture (identical across every wrap block: shifts are
per-INDEX constants). The weld pins the equality against that fixture. -/
def SHIFTS_Q : List Nat :=
  [ 1
  , 328286983623303317637963920346571898945724874896624808297627776768640590563
  , 220790353665890403705559231885806581221301230221265349993193424985261418438
  , 211720422259245489258933986578227917398506328781182391541883955346082631533
  , 211634429328372259348572816867521795029192573698954618296359582461568682420
  , 317476258975906211462498873025720239242336777696786967497139785505242641540
  , 99141114743446054294525453467100398765600279346526770105380817318185104545 ]

/-! ### ⚑ Stage 11's constants — DERIVED descriptor literals, each with its ring check below.

`ENDO_Q` is the BASE endomorphism eigenvalue `5^((q−1)/3)` — `vi.endo`, the endomul body's only
config read, the value `Bridge/MinaWrapFtEval0Weld.ENDO_COEFF` measures (NOT `er`; conflating
the two cube roots was half the 2026-08-01 `gateLinConst` defect). `MDS_Q` is the `fq_kimchi`
MDS, flat row-major, straight from `PastaPoseidonFq.mdsQ` — carried nowhere else. The three
`EndomulScalar` quotient constants are Fermat-witnessed quotients, the `vDINV` device; their
`6·cA = 11`-style checks are the named theorems, the exact content of
`KimchiVerify.endomulScalarConstsOk`. -/

def ENDO_Q : Nat :=
  (Dregg2.Bridge.MinaWrapFtEval0.powFast ((5 : Nat) : ZMod qN) ((qN - 1) / 3)).val
def MDS_Q : List Nat := Dregg2.Circuit.Emit.PastaPoseidonFq.mdsQ.flatten
def CA_Q : Nat :=
  (((11 : Nat) : ZMod qN) * Dregg2.Bridge.MinaWrapFtEval0.invCand ((6 : Nat) : ZMod qN)).val
def CB_Q : Nat :=
  ((-((5 : Nat) : ZMod qN)) * Dregg2.Bridge.MinaWrapFtEval0.invCand ((2 : Nat) : ZMod qN)).val
def CC_Q : Nat :=
  (((2 : Nat) : ZMod qN) * Dregg2.Bridge.MinaWrapFtEval0.invCand ((3 : Nat) : ZMod qN)).val

set_option maxHeartbeats 400000000 in
/-- The three `EndomulScalar` quotient literals check in the ring — `endomulScalarConstsOk`'s
content, stated of the DESCRIPTOR's own literals. -/
theorem the_quotient_constants_check_in_the_ring :
    6 * ((CA_Q : Nat) : ZMod qN) = 11
    ∧ 2 * ((CB_Q : Nat) : ZMod qN) = -5
    ∧ 3 * ((CC_Q : Nat) : ZMod qN) = 2 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

set_option maxHeartbeats 400000000 in
/-- The endo literal is a NONTRIVIAL cube root of unity (the base endomorphism eigenvalue), and
it is `Bridge/MinaWrapFtEval0Weld.ENDO_COEFF`'s measured value — two sources, one number. -/
theorem the_endo_is_the_base_eigenvalue :
    ((ENDO_Q : Nat) : ZMod qN) ^ 3 = 1
    ∧ ((ENDO_Q : Nat) : ZMod qN) ≠ 1
    ∧ ENDO_Q = 2942865608506852014473558576493638302197734138389222805617480874486368177743 := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

def constLegsF : List AirLeg :=
  constFirstBlock (valueColF vONE) 1
  ++ constFirstBlock (valueColF vZERO) 0
  ++ constFirstBlock (valueColF vOM3) OM3_C
  ++ constFirstBlock (valueColF vOM2) OM2_C
  ++ constFirstBlock (valueColF vOM1) OM1_C
  ++ (List.range PERMUTS).flatMap (fun i =>
       constFirstBlock (valueColF (vSH i)) (SHIFTS_Q.getD i 0))
  ++ constFirstBlock (valueColF vENDO) ENDO_Q
  ++ (List.range 9).flatMap (fun i =>
       constFirstBlock (valueColF (vMDS i)) (MDS_Q.getD i 0))
  ++ constFirstBlock (valueColF vCA) CA_Q
  ++ constFirstBlock (valueColF vCB) CB_Q
  ++ constFirstBlock (valueColF vCC) CC_Q
  ++ constFirstBlock (valueColF vC3) 3
  ++ constFirstBlock (valueColF vC6) 6
  ++ constFirstBlock (valueColF vC11) 11

/-- β and γ are LOW-128-BIT squeezes: limbs 16..31 are pinned zero, so the phase-1 weld is
16 limbs + 16 zero-pins — the `v′` pattern, in-leaf. -/
def zeroHighLegs : List AirLeg :=
  [vBETA, vGAMMA].flatMap (fun v =>
    (List.range (SK / 2)).map (fun j =>
      AirLeg.window ⟨.first, .loc (valueColF v + SK / 2 + j)⟩))

/-- The PI pins: the 103 input blocks, in value order, at row 0. -/
def piPinsF : List AirLeg :=
  (List.range NPI_BLOCKS).flatMap (fun v =>
    (List.range SK).map (fun j =>
      AirLeg.pin ⟨VmRow.first, valueColF v + SK * 0 + j, SK * v + j⟩))

def FS_PI_COUNT : Nat := NPI_BLOCKS * SK

theorem fs_pi_count_eq : FS_PI_COUNT = 3296 := by native_decide

/-! ## §8 — THE AIR AND THE DESCRIPTOR. -/

def fsTables : List TableDef :=
  [ mainTableDef FS_WIDTH
  , ⟨rangeTidW SB, "range_w8", 1, .rangeLimb SB⟩
  , ⟨rangeTidW CB, "range_w16", 1, .rangeLimb CB⟩
  , ⟨rangeTidW CBITS, "range_w1", 1, .rangeLimb CBITS⟩ ]

def finalizeAir : EffectAir :=
  { tables := fsTables
  , legs := selBooleanLegs ++ [selOneHotLeg] ++ selShiftLegs
      ++ valuePoolLegs ++ witnessPoolLegs
      ++ carryLegsF
      ++ scheduleLegsF
      ++ constLegsF ++ zeroHighLegs
      ++ piPinsF }

def finalizeDesc : EffectVmDescriptor2 :=
  lowerAir "dregg-mina-finalize-scalars::v2" FS_WIDTH FS_PI_COUNT [] finalizeAir

/-! ## §9 — THE CENSUS, against the corrected numbers, and the two rail verdicts.

Declared **5 750** columns (1 047 selectors + 144 × 32 value slots + 95 witness pool), committed
**15 280** (`AirColumnAlloc.committedWidth`'s aux law over the pool legs), 64 324 constraints,
2 048 rows — the inner LDE at the descriptor engine (`log_blowup 6`) is `2^17`.

Scale, priced honestly against v1 (4 461 / 12 903 / 27 319 / 512): stage 11 added ZERO input
blocks — the PI surface stays 3 296; the 16 new blocks are `.first`-pinned constants — so this
delta is the ARITHMETIC's: +745 selector columns and +17 slots. Committed cells
15 280 × 2 048 ≈ 3.13 × 10⁷ ≈ 19 % of `MinaWrapVerifierAir.WRAP_CELLS = 161 308 368` (v1 was
4 %). ⚠ The brief's "~320 more ops" estimate for this leaf was 2.3× LOW (745 measured) — this
time the under-count was the constraint bodies' multiplies, not the pin surface; both failure
modes are now on record, price BOTH. -/

set_option maxHeartbeats 400000000 in
theorem fs_width_eq : FS_WIDTH = 5750 := by native_decide

set_option maxHeartbeats 1000000000 in
theorem fs_layout_eq :
    NPHASE = 1046 ∧ VAL_BASE = 1047 ∧ W1_COL = 5655 ∧ NSLOTS = 144 := by
  refine ⟨by native_decide, by native_decide, by native_decide, by native_decide⟩

set_option maxHeartbeats 4000000000 in
theorem fs_committed_width :
    Dregg2.Circuit.Emit.AirColumnAlloc.committedWidth FS_WIDTH finalizeAir = 15280 := by native_decide

set_option maxHeartbeats 4000000000 in
theorem fs_constraint_count : finalizeDesc.constraints.length = 64324 := by native_decide

/-- ⚑ **THE COMPILER ACCEPTS EVERY LEG.** Window legs read `nxt` only under `.transition`, every
pool is `0 < bits ≤ 29`, and no leg is refused — the verdict `lowerAir` gates on.

⚠ **COMPILER-TRUSTED, and said out loud** (`native_decide` + `#assert_compiled`): the kernel
measurably cannot walk this leg list — the v1 verdict at 23 290 legs already re-instantiated the
list under the traversal lambdas past any whnf cache (21 min / 16 GiB / 3 % CPU before the
switch), and v2 is ~2.4× that. `SeamSpec` §4 records the wall; `PastaCurveScheduled`'s
kernel-decided twin of this verdict stands at 33 ops. -/
theorem finalizeAir_mainRailOk : finalizeAir.mainRailOk = true := by native_decide

/-- ⚑ **EVERY PUBLISHED COLUMN IS READ BY ANOTHER LEG** — each pinned block's columns appear in
its slot's pool leg, so a decorative pin is unrepresentable. Being read is not being forced; the
forcing claims live in the header table. ⚠ Compiler-trusted, same confession as above — the
inner `legs.any` rescan per pin is quadratic in exactly the terms the kernel cannot cache. -/
theorem finalizeAir_pinsTied :
    Dregg2.Circuit.EffectAirIR.EffectAir.pinsTied finalizeAir = true := by native_decide

#assert_compiled the_tables_cover_the_values
#assert_compiled the_ranges_cover_the_reads
#assert_compiled same_slot_ranges_are_disjoint
#assert_compiled inputs_are_live_from_the_top
#assert_compiled fs_pi_count_eq
#assert_compiled the_quotient_constants_check_in_the_ring
#assert_compiled the_endo_is_the_base_eigenvalue
#assert_compiled fs_width_eq
#assert_compiled fs_layout_eq
#assert_compiled fs_committed_width
#assert_compiled fs_constraint_count
-- ⚑ COMPILER-TRUSTED, and said out loud: the two leg-walk verdicts.
#assert_compiled finalizeAir_mainRailOk
#assert_compiled finalizeAir_pinsTied

end Dregg2.Circuit.Emit.MinaFinalizeScalars

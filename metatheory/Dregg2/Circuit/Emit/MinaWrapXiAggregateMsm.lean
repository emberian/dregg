/-
# `Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm` — the ξ-AGGREGATE, with the SCALAR MULTIPLICATION
INSIDE THE CIRCUIT.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This is Lean-authored AIR.** The emitted object is
`PastaMsmBucketed.bucketedRowDescChal NC N_PAD NBITS C GENS SCAL` — an `EffectVmDescriptor2` built
by a Lean `def` out of Lean-authored `VmConstraint2`s, whose first 42 constraints are
`PastaMsmWindowed.rowGates` verbatim (`bucketedRowDesc_extends_rowGates`), i.e. the same
`PastaCurveComplete.pallasCompleteAdd` the whole Pasta cone shares, and whose narrow form is a
PREFIX of it (`bucketedRowDescChalOn_extends_the_narrow_descriptor`). This file authors **no new
gate**: it names a curve, a window, a generator list, a scalar list and a challenge-block WIDTH, and
it proves things about the resulting artifact. Rust parses the descriptor, fills trace CELLS and
runs the deployed prover. House Law #1.

## ⚑ THE DEFECT THIS FILE CLOSES, stated as it was found

`MinaWrapCommitStages.xiAggDesc` folds 47 terms — at full term count, with the real block's
points, against o1-labs' own aggregate. But its ROM immediates are `XI_TERMS`, and

```
def XI_TERMS : List Aff :=
  (List.range 47).map (fun i => toAff (MinaWrapGroupGate.smul (qpow XI i) …))
```

is **PRE-SCALED**: `MinaWrapGroupGate.smul` is a Lean REFERENCE FUNCTION, not a gate. The scalar
multiplication — the entire content of an MSM — happened before the descriptor existed. What that
descriptor forces is *"these 47 hardcoded points, added in this order, give this hardcoded point."*
A prover that wanted a different aggregate would change the ROM, and the ROM is the thing the
verifier reads.

Here the scalars are **not** applied in advance. `SCAL` carries the 47 powers of the block's real
`ξ` as NUMBERS; `GENS` carries the 47 unscaled commitments. The descriptor's `T_COVER` permutation
forces every `(window, generator)` pair to be consumed exactly once at the sweep level equal to its
declared digit, and the fused running sum

  `Σ_i s_i·P_i = Σ_{d=1}^{D} ( Σ_{i : d_i ≥ d} P_i )`

makes the accumulation the trace's own work. **`s_i·P_i` is computed by the AIR, not handed to it.**

## ⚠ THE GAPS THIS INHERITS, and they are inherited KNOWINGLY

Nothing below repairs these; they belong to `PastaMsmBucketed` and they travel with it.

1. **The digits are DECLARED, not DERIVED BY A GATE.** `T_COVER`'s manifest carries `digit_w(s_i)`
   as a descriptor parameter, so the artifact is SCALAR-SPECIALISED: it forces the trace to compute
   `Σ s_i·P_i` for the `s` the descriptor names. ⚑ **What §3b/§2-pre DO close is where that `s`
   comes from:** since 2026-08-05 the six-value squaring basis that GENERATES all 47 scalars is on
   this descriptor's own wire, 192 public-input felts, welded elementwise to
   `dregg-mina-xi-scalar-vector::v2`'s published basis and thence to a `ξ` an emitted AIR lifted out
   of the block's Fq sponge. `MinaWrapXiBasisWeld` is that weld and its §4 is the resolution
   statement. ⚠ An emitted gate chain that re-derives each row's digit FROM the wire block is still
   not built; `PastaMsmBucketed` §7.3 prices it.
2. **The row template is `pallasCompleteAdd`.** Correct for this cone — the ξ-aggregate is a WRAP
   commitment combination over Pallas — but the Vesta swap `bucketedRowDescVesta` offers is not
   exercised here.
3. ⚑ **The rows are denominated in the UNSOUND `fpMulCore`.** `PastaMsmBucketed` §7.2 says so, and
   it must be repeated here rather than absorbed, because the cone this file joins
   (`MinaWrapCommitStages`) is emitted at `PastaFieldSound`. **That is a downgrade, and it is a
   downgrade to be STATED, not absorbed:** the ξ-aggregate now scales in-circuit at the cost of
   moving from the sound multiply to the oversized one. The 495-bit gate coefficients are why the
   Rust side must parse through `parse_vm_descriptor2_unsound_oversized`.

## The parameters, and why each is forced rather than chosen

`c = 2`, `nbits = 255`, `n = 59`. §1 proves the trace height is `8192`, a power of two, which the
deployed prover requires AND which a permutation manifest's length must equal. The 12 padding terms
carry scalar `0`; the fused identity's inner sums range over `d ≥ 1`, so a zero-digit term appears
in none of them and contributes nothing — `the_padding_contributes_nothing`.

## Axiom hygiene

General theorems are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Facts
about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06). No `sorry`/`admit`. Named theorems, not `#guard`s. NEW file; not imported by the `Dregg2` root, per
house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm`
-/
import Dregg2.Circuit.Emit.PastaMsmBucketed
import Dregg2.Circuit.Emit.MinaWrapAggregationData
import Dregg2.Circuit.Emit.PastaFieldSound

namespace Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm

open Dregg2.Circuit.DescriptorIR2 (EffectVmDescriptor2)
open Dregg2.Circuit.Emit.PastaField (pN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt smul padd msmComm)
open Dregg2.Circuit.Emit.MinaWrapAggregationGate (XI COMBINE_POINTS COMBINED_GOLD)
open Dregg2.Circuit.Emit.PastaMsmBucketed (windowsOf levelsOf fusedAdds bucketedRows termRows
  winLen scalarDigitC coverManifest srsManifest schedManifest bucketedRowDesc bucketedRowDescChal
  bucketedTables chalPinGates chalThreadGates CHB WK PI_COUNT
  SCHED_TUP COVER_TUP SRS_TUP MAX_EP_ROWS MAX_EP_CELLS MAX_EP_ARITY)
open Dregg2.Circuit.Emit.PastaFieldSound (SK limbAt)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## §1 — THE PARAMETERS, and the power-of-two height they are chosen to hit. -/

/-- The block's polyscale challenge, `q`-arithmetic. ⚑ `MinaWrapCommitStages`'s
`the_base_field_reduction_of_xi_squared_is_a_different_scalar` is the refutation that reading these
powers in the BASE field gives different scalars — the classic Pasta error, caught here once
already. -/
def qmul (x y : Nat) : Nat := (x * y) % PastaField.qN

def qpow (x : Nat) : Nat → Nat
  | 0 => 1
  | n + 1 => qmul (qpow x n) x

/-- The 47 real terms `combine_commitments` feeds the terminal MSM. -/
def N_REAL : Nat := 47

/-- The padded term count: 12 further terms at scalar `0`, so the height is a power of two. -/
def N_PAD : Nat := 59

/-- The window width. -/
def C : Nat := 2

/-- ⚑ **FULL-WIDTH Pasta scalars.** Not a reduced plane count — the ξ powers are 255-bit scalar
field elements and they enter at 255 bits. -/
def NBITS : Nat := 255

/-- The 47 powers `(ξ⁰, …, ξ⁴⁶)`, then 12 zeros. -/
def SCAL : List Nat :=
  ((List.range N_REAL).map (qpow XI)) ++ List.replicate (N_PAD - N_REAL) 0

/-- The 47 real commitments, then 12 repeats of the first — which the zero scalars annihilate. -/
def GENS : List Pt :=
  COMBINE_POINTS ++ List.replicate (N_PAD - N_REAL) (COMBINE_POINTS.getD 0 Oproj)

theorem lists_are_the_padded_length : SCAL.length = N_PAD ∧ GENS.length = N_PAD := by native_decide

/-- ⚑ **THE HEIGHT IS A POWER OF TWO**, which is what the whole padding exists for: the deployed
prover refuses a non-power-of-two base trace, AND an `exactPublicRows` manifest is a PERMUTATION,
so its length IS the trace height. `128` windows of `64` rows. -/
theorem the_height_is_eight_thousand_one_hundred_ninety_two :
    bucketedRows N_PAD NBITS C = 8192
      ∧ windowsOf NBITS C = 128 ∧ winLen N_PAD C = 64 ∧ levelsOf C = 3 := by native_decide

theorem the_height_is_a_power_of_two : bucketedRows N_PAD NBITS C = 2 ^ 13 := by native_decide

/-- ⚑ **AND THE WINDOWS COVER THE WHOLE SCALAR.** `128 · 2 = 256 ≥ 255`. This is the check that a
window count silently dropping a 255-bit scalar's top bits would fail — the digits are declared, so
nothing else would have noticed. -/
theorem the_windows_cover_the_whole_scalar : NBITS ≤ windowsOf NBITS C * C := by native_decide

/-! ## §2 — WHAT THE DESCRIPTOR DECLARES, welded to the block's own numbers. -/

/-! ### ⚑⚑ §2-pre — THE SIX-VALUE BASIS ON THE WIRE, and why SIX.

`MinaWrapXiScalarWeld.the_squaring_basis_generates_the_orbit` measured it and did not build it: at
`c⃗ = (ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)` the tensor `∏_j c_j^{bit_j(i)}` **is** `ξ^i` for every `i < 64`, so
the 47 scalars of this aggregate are generated by SIX values and not by forty-seven. Six values at
`SK = 32` eight-bit limbs is `192` public-input felts — a surface this descriptor can carry, where
`47 · 32 = 1 504` was the number that made the whole idea look like a re-architecture.

⚑ **THE ENCODING IS THE COMMIT-MACHINE'S, ON PURPOSE.** 32 limbs of 8 bits is what
`MinaWrapCommitStages.piBlock` writes and what `MinaWrapXiEndoLift` already publishes, so the weld
in `MinaWrapXiBasisWeld` is a **slice comparison and not a re-encoding**: a batch verifier compares
`aggPIs[27 … 218]` against `xiPIs[64 … 255]` felt by felt and does no arithmetic. The alternative —
this cone's own `9 × 30` coordinate limbs — would have made the tie a 255-bit recomposition in the
verifier, which is the cost the whole cone exists to remove.

⚠ **AND IT LEAVES A COST FOR THE RUNG AFTER THIS ONE, stated rather than discovered later.** The
in-circuit tensor chain reduces in `fqMulCore`, which reads `9 × 30`; consuming these felts in-row
will need an `8 → 30` bit regroup with its range certificates. That is a real cost of that rung and
it is the price of making THIS tie free for the verifier. -/

/-- The number of challenge values on the wire. -/
def NCHAL : Nat := 6

/-- The number of challenge FELTS. -/
def NC : Nat := NCHAL * SK

/-- ⚑ **THE SIX BASIS VALUES, DERIVED HERE FROM THIS FILE'S OWN ξ.** High power first, which is
`PastaMsmScalarDerive.sAt`'s convention (challenge `j` pairs with binary digit `nb−1−j`).

⚠ This list is built from `MinaWrapAggregationGate.XI` by THIS file's `qpow`; `MinaWrapCommitStages.
XI_BASIS` is built by that file's, and the emitted chain descriptor publishes what its MACHINE
computed. Three routes, and `MinaWrapXiBasisWeld` is where they are required to agree. -/
def BASIS : List Nat :=
  [qpow XI 32, qpow XI 16, qpow XI 8, qpow XI 4, qpow XI 2, qpow XI 1]

/-- ⚑ **THE 192 FELTS THIS DESCRIPTOR'S WIRE CARRIES**, slots `27 … 218`. -/
def basisPIs : List ℤ := BASIS.flatMap (fun v => (List.range SK).map (limbAt v))

theorem the_basis_is_six_values_and_one_hundred_ninety_two_felts :
    BASIS.length = NCHAL ∧ basisPIs.length = NC ∧ NC = 192
      ∧ BASIS.eraseDups.length = NCHAL := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND EACH IS THE SQUARE OF ITS SUCCESSOR, ENDING ON ξ.** The basis is FIVE squarings from the
one value this cone publishes — `the_polyscale_is_the_endo_lift_of_the_squeeze`'s ξ — and not six
independent numbers. Without this the "six wire values" claim would be six free scalars. -/
theorem the_basis_is_five_squarings_of_the_polyscale :
    ((List.range (NCHAL - 1)).all
      (fun j => decide (BASIS.getD j 0 = qmul (BASIS.getD (j + 1) 0) (BASIS.getD (j + 1) 0))))
        = true
      ∧ BASIS.getD (NCHAL - 1) 0 = XI := by
  refine ⟨?_, ?_⟩ <;> native_decide

/-- ⚑ **THE EMITTED ARTIFACT — WIDENED.** `bucketedRowDesc`'s 91 constraints verbatim, plus 192
first-row PI pins and 192 threads over the 192 fresh columns `612 … 803`.

⚠ FLAG DAY: `piCount` moves `27 → 219`, `traceWidth` `612 → 804`, and the name gains `-w192`.
`mina-xi-aggregate-msm.json` re-emits; the old artifact no longer resolves under any name this
tree emits. The three toy instances (`pasta-msm-bucketed-{c2,c3,vesta-c2}.json`) are UNTOUCHED —
they pass through `bucketedRowDesc`, which did not move. -/
def xiAggMsmDesc : EffectVmDescriptor2 := bucketedRowDescChal NC N_PAD NBITS C GENS SCAL

/-- Recompose a term's declared `c`-bit digits, MSB-first, over every window the descriptor has. -/
def recompose (i : Nat) : Nat :=
  (List.range (windowsOf NBITS C)).foldl
    (fun acc w => acc * 2 ^ C + scalarDigitC SCAL NBITS C w i) 0

/-- ⚑ **THE DECLARED DIGITS RECOMPOSE TO THE DECLARED SCALARS — ALL 59, NO TRUNCATION.**

`T_COVER`'s manifest is the only place the scalars appear in the artifact, and it carries DIGITS.
This says those digits are the base-`2^C` digits of exactly the numbers `SCAL` names, over the
window count the descriptor actually has. Without it, "the digits are declared" would also permit
"the digits are the declared scalars' LOW 254 bits", which is a different MSM with the same
descriptor shape and no green anywhere would move. -/
theorem the_declared_digits_recompose :
    ((List.range N_PAD).all (fun i => decide (recompose i = SCAL.getD i 0))) = true := by native_decide

/-- ⚑ **AND THE DECLARED SCALARS ARE THE REAL ξ POWERS.** The first 47 entries are `ξ⁰ … ξ⁴⁶` at
the block's own challenge, in `q`. -/
theorem the_declared_scalars_are_the_xi_powers :
    ((List.range N_REAL).all (fun i => decide (SCAL.getD i 0 = qpow XI i))) = true := by native_decide

/-- ⚑ **AND THE PADDING IS INERT.** Every padding term carries scalar `0`, hence digit `0` in every
window; the fused identity's inner sums range over `d ≥ 1`, so a zero-digit term is in none of them.
The 12 extra rows per window buy the power-of-two height and nothing else. -/
theorem the_padding_contributes_nothing :
    ((List.range (N_PAD - N_REAL)).all
      (fun k => decide (SCAL.getD (N_REAL + k) 0 = 0)
        && ((List.range (windowsOf NBITS C)).all
              (fun w => decide (scalarDigitC SCAL NBITS C w (N_REAL + k) = 0))))) = true := by
  native_decide

/-- ⚑ **AND THE DECLARED GENERATORS ARE THE BLOCK'S OWN COMMITMENTS.** The first 47 entries of
`GENS` are `MinaWrapAggregationGate.COMBINE_POINTS` — the 2 recursion, `public_comm`, `ft_comm`,
`Z`, 6 index, 15 witness, 15 coefficient and 6 sigma commitments of Mina devnet block 539508. -/
theorem the_declared_generators_are_the_block_commitments :
    ((List.range N_REAL).all
      (fun i => decide (GENS.getD i Oproj = COMBINE_POINTS.getD i Oproj))) = true := by native_decide

/-- Every declared generator is a real Pallas point. -/
theorem every_declared_generator_is_on_pallas :
    (GENS.all (projOnCurveM pN curveB)) = true := by native_decide

/-! ## §3 — ⚑ THE WELD TO `COMBINED_GOLD`, AS A NAMED THEOREM.

Until this section the four folds of `MinaWrapCommitStages` matched o1-labs by **two adjacent
`IO.println`s** in `EmitCommitStages.lean` — a human reading two lines of stdout and agreeing they
were the same digits. A sibling lane's verdict on exactly that shape, and the reason it fixed a
transcription it had already checked by hand: *"one wrong digit would have given a self-consistent
tree — Lean proving the program computes ITS constants, the harness pinning ITS digest, every gate
green."* The printlns are deleted; these are what replaced them. -/

/-- The MSM the descriptor NAMES: `Σ SCAL_i · GENS_i`, by `MinaWrapGroupGate.msmComm`, which is
`PolyComm::multi_scalar_mul` in shape. -/
def declaredMsm : Pt := msmComm (SCAL.zip GENS)

/-- ⚑ **THE MSM THIS DESCRIPTOR NAMES IS o1-LABS' OWN AGGREGATE.**

`COMBINED_GOLD` is `Σᵢ ξⁱ·Cᵢ` as o1-labs' `PolyComm::multi_scalar_mul` computed it on Mina devnet
block 539508. This is 47 full 255-bit RCB ladders and 59 complete adds in the Lean kernel, over the
padded lists the DESCRIPTOR carries — not over a tidied copy of them.

⚑ It is also an INDEPENDENT route to that point. `MinaWrapAggregationGate.combinedComm_reproduces_
kimchi` reaches `COMBINED_GOLD` by `chunkedComm`, a HORNER fold (`res := res·ξ + c`) that never
forms a power of ξ at all. This one forms all 47 powers explicitly and multiplies each into its own
generator. Two different computations, one point: that is a gate, where a constant checked against
its own definition would have been decoration. -/
theorem the_declared_msm_is_o1_labs_aggregate :
    projEqM pN declaredMsm COMBINED_GOLD = true := by native_decide

/-- ⚑ …and it is a FINITE point on Pallas, so `projEqM` is not agreeing about the identity. -/
theorem the_aggregate_is_a_real_finite_pallas_point :
    projOnCurveM pN curveB COMBINED_GOLD = true ∧ isInfM pN COMBINED_GOLD = false := by native_decide

/-- ⚑ **AND THE WELD IS REFUTABLE.** One added to the challenge gives a different aggregate — so
`the_declared_msm_is_o1_labs_aggregate` is a claim the block's data can falsify, not a tautology
about whatever `declaredMsm` happens to be. -/
theorem a_perturbed_challenge_misses_the_aggregate :
    projEqM pN
      (msmComm ((((List.range N_REAL).map (qpow (XI + 1)))
        ++ List.replicate (N_PAD - N_REAL) 0).zip GENS)) COMBINED_GOLD = false := by native_decide

/-- ⚑ **AND A DROPPED TERM MISSES IT TOO.** The last real commitment's scalar zeroed — the shape a
prover that quietly omitted one generator would produce. -/
theorem a_dropped_term_misses_the_aggregate :
    projEqM pN (msmComm ((SCAL.set (N_REAL - 1) 0).zip GENS)) COMBINED_GOLD = false := by native_decide

/-! ## §3b — ⚑⚑ THE WIRE SURFACE, AS FACTS ABOUT THE EMITTED ARTIFACT. -/

/-- ⚑ **THE AGGREGATE PUBLISHES 219 FELTS: THE OUTPUT POINT AND THE SIX-VALUE BASIS.**

The sentence this retires is `MinaWrapXiScalarWeld.the_aggregate_has_no_room_for_a_scalar_vector`,
which was true of `bucketedRowDesc` and is false of this artifact — the obstruction was a MISSING
SURFACE and not a property of the layout. `27 + 6·32 = 219`, and the 192 challenge felts live in
192 columns the row template never addresses. -/
theorem the_aggregate_publishes_the_basis_on_its_wire :
    xiAggMsmDesc.piCount = PI_COUNT + NC
      ∧ xiAggMsmDesc.piCount = 219
      ∧ xiAggMsmDesc.traceWidth = WK + NC
      ∧ xiAggMsmDesc.traceWidth = 804
      ∧ CHB = WK := by
  refine ⟨rfl, by native_decide, rfl, by native_decide, rfl⟩

/-- ⚑ **AND THE BLOCK IS PINNED AND THREADED, 192 OF EACH.** The pins put the basis on the wire;
the threads make it ONE vector for the whole 8 192-row trace. Without the threads a prover may pick
a fresh basis per row — the forgery `PastaMsmScalarDerive` §5d exhibits — and every PI comparison
downstream would still hold, because a PI pin only looks at row 0. -/
theorem the_wire_block_is_pinned_and_threaded :
    (chalPinGates NC).length = NC ∧ (chalThreadGates NC).length = NC
      ∧ xiAggMsmDesc.constraints.length
          = (bucketedRowDesc N_PAD NBITS C GENS SCAL).constraints.length + 2 * NC
      ∧ (bucketedRowDesc N_PAD NBITS C GENS SCAL).constraints.length = 91 := by
  refine ⟨by simp [chalPinGates], by simp [chalThreadGates], ?_, by decide⟩
  simp [xiAggMsmDesc, Dregg2.Circuit.Emit.PastaMsmBucketed.bucketedRowDescChal,
    Dregg2.Circuit.Emit.PastaMsmBucketed.bucketedRowDescChalOn, bucketedRowDesc,
    chalPinGates, chalThreadGates, Nat.two_mul]

/-- ⚑ **AND THE THREE MANIFESTS DID NOT MOVE.** The widening APPENDS: `T_SCHED`, `T_COVER` and
`T_SRS` are the same three `exactPublicRows` objects `bucketedRowDesc` declares, so every routing
theorem above — and the permutation that forces a generator to be consumed at its declared level —
holds of this artifact verbatim. -/
theorem the_widening_did_not_move_a_manifest :
    xiAggMsmDesc.tables = (bucketedRowDesc N_PAD NBITS C GENS SCAL).tables := rfl

/-- ⚑ **AND THE NAME MOVED WITH THE SHAPE.** A widened PI surface under the old key is exactly the
defect `PastaMsmBucketed` §4b renamed the family to kill: two AIRs, one identifier. -/
theorem the_widened_artifact_has_its_own_name :
    xiAggMsmDesc.name = "dregg-pasta-msm-bucketed-pallas-n59b255-c2-w192::v1"
      ∧ xiAggMsmDesc.name ≠ (bucketedRowDesc N_PAD NBITS C GENS SCAL).name := by
  refine ⟨rfl, by native_decide⟩

/-! ## §4 — WHAT STILL HOLDS A VALUE NOTHING COMPUTES, at CURRENT resolution.

Read this before citing anything above.

⚑ **`ξ` AND ITS BASIS — ON THE WIRE SINCE 2026-08-05. Read exactly which half moved.**

  * `MinaWrapXiEndoLift` emits `ScalarChallenge(v′).to_field(endo_r)` AS AN AIR and proves its
    output is o1-labs' own `ξ` on the block's own `v′` — which `MinaBlockFqTranscript`'s emitted
    2 048-row Fq sponge squeezes from Mina devnet block 539508's 91-element phase-2 tape. **`ξ` is
    computed, from the transcript, not typed.**
  * `MinaWrapCommitStages.xiChainProg` taps `ξ, ξ², ξ⁴, ξ⁸, ξ¹⁶, ξ³²` out of its own 46-multiply
    walk and its `::v2` descriptor publishes them as **192 public-input felts**.
  * ⚑ **THIS descriptor now has 192 slots to equal them in**, pinned on the first row and threaded
    down the trace, and `MinaWrapXiBasisWeld` proves the two 192-felt blocks are equal
    **elementwise, no digest, no re-encoding** — the same standard `the_endo_output_block_is_the_
    chain_input_block` met at 32.
  * And `MinaWrapXiBasisWeld` §3 proves `T_COVER`'s 7 552 declared digits are `digit_w` of the
    TENSOR IMAGE of exactly those 192 felts, over all 59 terms and all 128 windows.

⚑⚑ **AND THE CENSUS SCORES THE 192 AS DECORATIVE — 192 OF 219 PUBLIC INPUTS, 87.7%, THE LARGEST
ROW IN `scripts/descriptor-anchor-inertness-baseline.txt`.** Measured 2026-08-05 at source, not
inferred: columns `612 … 803` are each touched by EXACTLY TWO constraints — `chalPinGates`'
first-row `piBinding` and `chalThreadGates`' `nxt CH_m − CH_m` — and by nothing that relates them
to another column. `nxt c` and `loc c` are the same column, so a thread is a UNARY window gate and
the census reads it as joining nothing, **which is right**. The thread does real work (the block is
one trace-global vector, not 8 192 free ones, and `a_basis_that_varies_by_row_is_refused` measures
it firing as p3 constraint `#311` on row 4095); what it does not do is relate the basis to the MSM.

The row is minted rather than argued away, with its reason in that file, and it carries a RUNNING
TEST — `circuit/tests/pasta_msm_bucketed_prove.rs::the_published_basis_is_not_yet_bound_to_the_
declared_digits` proves and verifies this aggregate against a basis that is NOT the block's own,
reaching the same `COMBINED_GOLD` over an identical row template. ⚠ **The row goes to zero when
`T_COVER`'s digits become these felts' in-circuit image, and not before.** Recomposing the 32 limbs
of each value into a value column, or hashing the block into an anchor, would join all 192 columns
to each other and zero the census while leaving 192 free witnesses — the "absorbing them as chip
INPUTS" laundering that census file refuses by name.

⚠ **WHAT THIS IS NOT, and it must not be read as more.** The digits are still DESCRIPTOR data.
`T_COVER` is `exactPublicRows` and `PublicLookupBalanced` demands a PERMUTATION, so the deployed
prover already refuses a moved `DGT` — the digits were never forgeable and this is therefore **not a
soundness repair**. What changed is the QUANTIFIER on the challenge: it was *a constant the verifier
is told*, and it is now *a value the verifier already holds from another proof of this block's own
transcript*. The remaining half — an emitted gate chain that RE-DERIVES each row's digit from the
wire block, `PastaMsmScalarDerive`'s `PRc`/`MUc`/`QUc` in this layout — is **not built**;
`PastaMsmBucketed` §7.3 prices it at ~1 400 constraints and ~2 700 columns, plus the `8 → 30` limb
regroup §2-pre names.

⚑ **THE UNSOUND MULTIPLY.** Stated in the header and repeated because it is the kind of thing that
gets absorbed: these rows are `fpMulCore`, not `PastaFieldSound`. `PastaMsmBucketed` §6d prices the
sound row at over a hundredfold the gate count. ⚑ **And the widening does not touch it** — neither
`chalPinGates` nor `chalThreadGates` multiplies anything, so when the `EffectAir`↔gadget bridge
lands and the rows become sound, this whole wire block carries over unchanged. -/

/-- The declared cell budget, so the deployed caps are checked rather than assumed. -/
theorem the_manifests_fit_the_deployed_caps :
    bucketedRows N_PAD NBITS C ≤ MAX_EP_ROWS
      ∧ SCHED_TUP < MAX_EP_ARITY ∧ COVER_TUP < MAX_EP_ARITY ∧ SRS_TUP < MAX_EP_ARITY
      ∧ bucketedRows N_PAD NBITS C * (SCHED_TUP + COVER_TUP + SRS_TUP) ≤ MAX_EP_CELLS := by
  native_decide

/-- ⚑ **THE PRICE OF THE WIRE BLOCK, SAID OUT LOUD.** 192 columns over 8 192 rows is 1 572 864 more
committed cells — a `31.4%` rise on the row template's own 5 013 504, and FRI pays for committed
area. That is what a verifier-free basis tie costs here, and it is a number rather than an
adjective. -/
theorem the_wire_block_costs_thirty_one_percent_more_area :
    bucketedRows N_PAD NBITS C * NC = 1572864
      ∧ bucketedRows N_PAD NBITS C * WK = 5013504
      ∧ 100 * (bucketedRows N_PAD NBITS C * NC) < 32 * (bucketedRows N_PAD NBITS C * WK) := by
  refine ⟨by native_decide, by native_decide, by native_decide⟩

/-- ⚑ **THE TERM ROWS ARE 92% OF THE TRACE**, and the rest is the fused collapse — the census that
says the padding is a rounding error and the object is really doing 7 552 conditional adds. -/
theorem the_term_rows_dominate :
    termRows N_PAD NBITS C = 7552 ∧ 100 * termRows N_PAD NBITS C > 92 * bucketedRows N_PAD NBITS C
      := by native_decide

/-- ⚑ **AND THE REAL WORK IS 47/59 OF THAT.** The 12 padding terms occupy 1 536 of the 7 552 term
rows; a reader pricing this object should price the real content. -/
theorem the_real_terms_are_forty_seven_fifty_ninths :
    windowsOf NBITS C * N_REAL = 6016 ∧ windowsOf NBITS C * (N_PAD - N_REAL) = 1536 := by native_decide

#assert_compiled lists_are_the_padded_length
#assert_compiled the_height_is_eight_thousand_one_hundred_ninety_two
#assert_compiled the_height_is_a_power_of_two
#assert_compiled the_windows_cover_the_whole_scalar
#assert_compiled the_declared_digits_recompose
#assert_compiled the_declared_scalars_are_the_xi_powers
#assert_compiled the_padding_contributes_nothing
#assert_compiled the_declared_generators_are_the_block_commitments
#assert_compiled every_declared_generator_is_on_pallas
#assert_compiled the_declared_msm_is_o1_labs_aggregate
#assert_compiled the_aggregate_is_a_real_finite_pallas_point
#assert_compiled a_perturbed_challenge_misses_the_aggregate
#assert_compiled a_dropped_term_misses_the_aggregate
#assert_compiled the_basis_is_six_values_and_one_hundred_ninety_two_felts
#assert_compiled the_basis_is_five_squarings_of_the_polyscale
#assert_compiled the_aggregate_publishes_the_basis_on_its_wire
#assert_axioms the_wire_block_is_pinned_and_threaded
#assert_axioms the_widening_did_not_move_a_manifest
#assert_compiled the_widened_artifact_has_its_own_name
#assert_compiled the_manifests_fit_the_deployed_caps
#assert_compiled the_wire_block_costs_thirty_one_percent_more_area
#assert_compiled the_term_rows_dominate
#assert_compiled the_real_terms_are_forty_seven_fifty_ninths

end Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm

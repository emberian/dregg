/-
# `Dregg2.Circuit.Emit.MinaWrapXiBasisWeld` — THE AGGREGATE'S SCALARS ARE COMPUTED, AND THE
GENERATOR IS ON THE WIRE.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This file emits nothing and authors no gate.** Every object it names is emitted somewhere else —
`MinaWrapCommitStages.xiDesc` (the machine), `MinaWrapXiAggregateMsm.xiAggMsmDesc` (the bucketed
MSM), `MinaWrapXiEndoLift.endoDesc` (the lift) — and every theorem here reads one of those artifacts
as DATA and compares it with another. House Law #1 is not at risk in this file. What IS at risk is
the honesty of the comparison, and §4 is where that is priced.

## THE SENTENCE THIS RETIRES

`MinaWrapXiScalarWeld` §3, its own author, measuring the obstruction and the fix in one breath:

> ⚑ **So there is no PI slot on the aggregate for a published scalar to equal.** […] ⚑ **And for
> THIS aggregate the derivation is already the right shape**: `PastaMsmScalarDerive.sAt` computes
> `s_i = ∏_j c_j^{bit_j(i)}`, and at `c⃗ = (ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)` that IS `ξ^i` — so the
> ξ-aggregate needs a SIX-element challenge vector on the wire, not a 47-element one.
> `the_squaring_basis_generates_the_orbit` is that fact, stated here so the next lane builds the
> weld instead of rediscovering that it fits.

The obstruction was a **missing surface**, not a property of the layout, and both halves of it are
now built:

  * `MinaWrapCommitStages.xiChainProg` taps `ξ, ξ², ξ⁴, ξ⁸, ξ¹⁶, ξ³²` out of the 46-multiply walk it
    was already doing and publishes them — `dregg-mina-xi-scalar-vector::v2`, `piCount = 256`.
  * `PastaMsmBucketed.chalPinGates`/`chalThreadGates` widen the aggregate to `27 + 192` public
    inputs over 192 fresh columns — `…-c2-w192::v1`, `piCount = 219`, `traceWidth = 804`.

## ⚑⚑ THE TWO TIES, AND WHAT EACH IS WORTH

  1. **§2 — THE WIRE TIE.** The aggregate's 192 published felts and the chain's 192 published felts
     are the SAME LIST, elementwise. `47 · 32 = 1 504` was the number that made this look like a
     re-architecture; `6 · 32 = 192` is the number that fits. **No digest, no representative, no
     re-encoding** — both sides publish at `SK = 32` eight-bit limbs, so a batch verifier compares
     two slices and does no arithmetic. There is nothing to collide, hence no birthday bound:
     `a_perturbed_wire_felt_breaks_the_weld` moves ONE felt and it fails.

  2. **§3 — THE DIGIT WELD.** `T_COVER`'s 8 192 emitted rows are the base-`2^c` digits of the
     TENSOR IMAGE of exactly those 192 felts, under `PastaMsmScalarDerive`'s own `sAt` — over all 59
     terms and all 128 windows. `tensorQ_is_sNat` is the general bridge that makes "the tensor" that
     file's function and not one this file invented.

## ⚠ WHAT THIS IS NOT — read before citing any of it

**This is not a soundness repair, and it must not be described as one.** `T_COVER` is
`TableSem.exactPublicRows`, `DescriptorIR2.PublicLookupBalanced` demands a PERMUTATION of the
declared list, and the deployed prover refuses a moved `DGT` (`a_generator_folded_at_the_wrong_
level_is_refused`). The digits were never forgeable.

What moved is the QUANTIFIER on the challenge. Before: *`ξ` is a constant the descriptor names, and
the verifier is told it.* After: *`ξ`'s squaring basis is 192 felts on this proof's wire, equal to
192 felts on the wire of a proof whose AIR derived `ξ` from Mina devnet block 539508's own Fq sponge
squeeze.* That is a real change and it is a bounded one.

⚠ **AND THE REMAINING HALF IS NOT BUILT.** An emitted gate chain that RE-DERIVES each row's digit
from the wire block — `PastaMsmScalarDerive`'s `PRc`/`MUc`/`QUc` ported into this layout — is what
would make the digits an in-circuit image rather than a checked-once-per-(block, VK) one.
`PastaMsmBucketed` §7.3 prices it at ~1 400 constraints and ~2 700 columns, and
`MinaWrapXiAggregateMsm` §2-pre adds the `8 → 30` limb regroup this encoding choice hands it.

## Axiom hygiene

General theorems are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Facts
about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06). No `sorry`/`admit`. Named theorems, not `#guard`s. NEW file; not imported by the `Dregg2` root, per
house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapXiBasisWeld`
-/
import Dregg2.Circuit.Emit.MinaWrapXiScalarWeld
import Dregg2.Circuit.Emit.PastaMsmScalarBound

namespace Dregg2.Circuit.Emit.MinaWrapXiBasisWeld

open Dregg2.Circuit.Emit.PastaField (qN)
open Dregg2.Circuit.Emit.PastaFieldSound (SK)
open Dregg2.Circuit.Emit.PastaMsmBucketed
  (coverManifest scalarDigitC windowsOf bucketedRows termRows)
open Dregg2.Circuit.Emit.PastaMsmScalarBound (sAt sNat)
open Dregg2.Circuit.Emit.MinaWrapOpeningGate (Fq)
open Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm
  (N_REAL N_PAD C NBITS SCAL NCHAL NC BASIS basisPIs qpow qmul xiAggMsmDesc)
open Dregg2.Circuit.Emit.MinaWrapXiScalarWeld (xiOnTheWire coverRows)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## §1 — THE TENSOR, AS `PastaMsmScalarDerive`'s OWN FUNCTION.

`PastaMsmScalarBound.sAt` is stated over an arbitrary `CommRing`, and the deployed instance is
`Fq = ZMod qN`. Nothing in this tree evaluates a `ZMod qN` product in the KERNEL — the two places
that touch `sScalars` at a concrete challenge list do it through `#guard`, i.e. the compiled
evaluator. So the tensor is spelled here in `Nat` at `q`, and the two are joined by a GENERAL
theorem rather than by a convention this file asserts.

⚑ **`tensorQ` is `sAt`'s recursion verbatim**: the head challenge pairs with the HIGH bit, one
factor per challenge, `1` where the bit is clear. Getting that backwards gives `ξ^(bit-reversed i)`,
which agrees with `ξ^i` at `i ∈ {0, 63}` and nowhere else — `a_transposed_basis_leaves_the_digits`
is the refutation. -/

/-- `PastaMsmScalarBound.sAt`'s recursion, in `Nat` reduced at `q`. -/
def tensorQ : List Nat → Nat → Nat
  | [], _ => 1
  | c :: rest, i => qmul (if Nat.testBit i rest.length then c else 1) (tensorQ rest i)

/-- ⚑⚑ **AND IT IS `PastaMsmScalarDerive`'s TENSOR, NOT A MIRROR OF IT.**

A general theorem over every challenge list whose entries are canonical, for every index — so the
digit weld below is a statement about the function that file emits gates for, and a later rung that
builds those gates is welding to the same object. Without this, §3 would be green about a product
this file defined and named after one it never touched. -/
theorem tensorQ_is_sNat :
    ∀ (cs : List Nat), (∀ c ∈ cs, c < qN) →
      ∀ i, tensorQ cs i = sNat (cs.map (fun c => (c : Fq))) i := by
  haveI : NeZero qN := ⟨by decide⟩
  haveI : Fact (1 < qN) := ⟨by decide⟩
  intro cs
  induction cs with
  | nil =>
      intro _ i
      show (1 : Nat) = ZMod.val (1 : Fq)
      exact (ZMod.val_one qN).symm
  | cons c rest ih =>
      intro h i
      have hc : c < qN := h c (List.mem_cons_self ..)
      have hr : ∀ x ∈ rest, x < qN := fun x hx => h x (List.mem_cons_of_mem _ hx)
      have hlen : (rest.map (fun c => (c : Fq))).length = rest.length := by simp
      have hsel : ZMod.val (if Nat.testBit i rest.length then (c : Fq) else 1)
          = (if Nat.testBit i rest.length then c else 1) := by
        by_cases hb : Nat.testBit i rest.length
        · rw [if_pos hb, if_pos hb, ZMod.val_natCast, Nat.mod_eq_of_lt hc]
        · rw [if_neg hb, if_neg hb]
          exact ZMod.val_one qN
      show qmul (if Nat.testBit i rest.length then c else 1) (tensorQ rest i)
        = ZMod.val (sAt ((c : Fq) :: rest.map (fun c => (c : Fq))) i)
      rw [show sAt ((c : Fq) :: rest.map (fun c => (c : Fq))) i
            = (if Nat.testBit i (rest.map (fun c => (c : Fq))).length then (c : Fq) else 1)
                * sAt (rest.map (fun c => (c : Fq))) i from rfl, hlen, ZMod.val_mul, hsel,
        ih hr i]
      rfl

/-! ## §2 — ⚑⚑ THE WIRE TIE: 192 FELTS, ELEMENTWISE.

`MinaWrapXiEndoLift.the_endo_output_block_is_the_chain_input_block` met this standard at 32 felts
and said why it matters at exactly that width. This is the same standard at 192. -/

/-- The 192 felts the ξ-AGGREGATE publishes, slots `27 … 218` of `…-c2-w192::v1`. -/
def aggBasisBlock : List ℤ := basisPIs

/-- The 192 felts the SCALAR CHAIN publishes, slots `64 … 255` of `dregg-mina-xi-scalar-vector::v2`
— blocks 2 through 7 of its eight-block surface. -/
def chainBasisBlock : List ℤ :=
  Dregg2.Circuit.Emit.MinaWrapCommitStages.xiPIs.drop (2 * SK)

/-- ⚑⚑ **THE WELD.** The aggregate's wire block IS the chain's wire block — elementwise, all 192
felts.

Two separately emitted descriptors, two separately generated traces, one shared 192-felt boundary.
A batch that verifies both proofs and compares these two slices learns that the six values
generating the aggregate's 47 scalars are the six the machine derived, by five squarings, from a `ξ`
`MinaWrapXiEndoLift` lifted out of Mina devnet block 539508's own Fq sponge squeeze.

⚠ And the two lists are built by DIFFERENT routes: `basisPIs` from `MinaWrapXiAggregateMsm`'s own
`qpow` over `MinaWrapAggregationGate.XI`, `chainBasisBlock` off the machine's published register
file. A file that built one from the other would be checking a constant against its own
definition. -/
theorem the_aggregate_wire_block_is_the_chain_wire_block :
    aggBasisBlock = chainBasisBlock := by decide

/-- ⚑ **AND IT IS 192 FELTS OF SIX DISTINCT FULL-WIDTH VALUES.** Stated because
`the_aggregate_wire_block_is_the_chain_wire_block` would be equally green over a ONE-felt block, and
a one-felt tie between two descriptors is `2^31` — below this repo's bar and exactly the shape the
`proof_bind` seam already has. It would also be equally green over six copies of one value, which is
what a tap that aliased its register would publish. -/
theorem the_shared_block_is_six_whole_field_elements :
    aggBasisBlock.length = NC ∧ NC = 6 * SK ∧ NC = 192
      ∧ BASIS.eraseDups.length = NCHAL
      ∧ BASIS.all (fun v => decide (v < qN)) = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- One published value, decoded from its 32 felts by the inverse of the map that wrote them. -/
def decodeBlock (b : List ℤ) : Nat :=
  (List.range SK).foldr (fun i acc => acc * 256 + (b.getD i 0).toNat) 0

/-- ⚑ The felt the refutation below moves, READ rather than assumed: the most significant limb of
the head basis value `ξ³²`. It is a NON-ZERO byte, and raising it by one changes the value that
block decodes to — so the tamper moves a number and not merely a list entry.

⚑ This exists because a sibling in this cone drafted a refutation that moved a row whose digit was
ZERO into an accumulator that was also zero, and `decide` REFUTED the refutation — *a tamper that
changes nothing is not a tamper*, and nothing but reading the value would have said so. The first
draft of THIS theorem guessed the felt was `27`; `decide` refuted that too. -/
theorem the_moved_felt_is_a_nonzero_byte_and_moving_it_moves_the_value :
    0 < aggBasisBlock.getD (SK - 1) 0
      ∧ aggBasisBlock.getD (SK - 1) 0 < 255
      ∧ aggBasisBlock.length = 192
      ∧ decodeBlock ((aggBasisBlock.set (SK - 1) (aggBasisBlock.getD (SK - 1) 0 + 1)).take SK)
          ≠ decodeBlock (aggBasisBlock.take SK) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE WELD IS REFUTABLE, ONE FELT AT A TIME.** The felt above raised by one — the smallest
change a forger could make to the shared boundary — and the equality is false. This is what makes
the weld a gate rather than a restatement of how both sides were built. -/
theorem a_perturbed_wire_felt_breaks_the_weld :
    aggBasisBlock.set (SK - 1) (aggBasisBlock.getD (SK - 1) 0 + 1) ≠ chainBasisBlock := by
  native_decide

/-- ⚑ **AND THE THREE ARTIFACTS ARE THREE ARTIFACTS.** A weld between an object and itself is not a
weld; a batch cannot satisfy two halves of this with one proof. -/
theorem the_welded_descriptors_are_distinct :
    xiAggMsmDesc.name = "dregg-pasta-msm-bucketed-pallas-n59b255-c2-w192::v1"
      ∧ Dregg2.Circuit.Emit.MinaWrapCommitStages.xiDesc.name
          = "dregg-mina-xi-scalar-vector::v2"
      ∧ Dregg2.Circuit.Emit.MinaWrapXiEndoLift.endoDesc.name = "dregg-mina-xi-endo-lift::v1"
      ∧ xiAggMsmDesc.piCount = 219
      ∧ Dregg2.Circuit.Emit.MinaWrapCommitStages.xiDesc.piCount = 256 := by
  refine ⟨rfl, rfl, rfl, ?_, ?_⟩ <;> native_decide

/-! ## §3 — ⚑⚑ THE DIGIT WELD: `T_COVER`'s ROWS ARE THE TENSOR IMAGE OF THE WIRE BLOCK. -/

/-- ⚑ **THE SIX CHALLENGES AS THE WIRE CARRIES THEM** — decoded from the aggregate's own public
inputs, not read out of the `def` that produced them. -/
def wireBasis : List Nat :=
  (List.range NCHAL).map (fun j => decodeBlock ((aggBasisBlock.drop (j * SK)).take SK))

/-- ⚑⚑ **THE WIRE BLOCK CARRIES THE SQUARING ORBIT OF THE ξ THE ENDO LIFT DERIVED.**

`xiOnTheWire` is `MinaWrapXiScalarWeld`'s decode of `MinaWrapXiEndoLift.endoOutputBlock` — the 32
felts the lift's LAST-ROW pin publishes, whose value `the_polyscale_is_the_endo_lift_of_the_squeeze`
proves is `ScalarChallenge(v′).to_field(endo_r)` at Mina devnet block 539508's own `v′`.

So the six numbers the aggregate's wire carries are `ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ` **of a `ξ` that came
out of a sponge**, and not six numbers a descriptor named. -/
theorem the_wire_basis_is_the_squaring_orbit_of_the_lifted_polyscale :
    wireBasis = [qpow xiOnTheWire 32, qpow xiOnTheWire 16, qpow xiOnTheWire 8,
                 qpow xiOnTheWire 4, qpow xiOnTheWire 2, xiOnTheWire] := by
  native_decide

/-- ⚑ …and it is FIVE SQUARINGS, so the six are one value's orbit rather than six free scalars. -/
theorem the_wire_basis_is_five_squarings :
    ((List.range (NCHAL - 1)).all
      (fun j => decide (wireBasis.getD j 0
                  = qmul (wireBasis.getD (j + 1) 0) (wireBasis.getD (j + 1) 0)))) = true
      ∧ wireBasis.getD (NCHAL - 1) 0 = xiOnTheWire
      ∧ wireBasis.eraseDups.length = NCHAL := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **THE SCALAR VECTOR THE WIRE BLOCK GENERATES.** The tensor over the 47 real terms; the 12
padding terms carry `0`, which is what makes them inert (`the_padding_contributes_nothing`).

⚠ The `if` is not a convenience. `tensorQ wireBasis i` is `ξ^i` for every `i < 64`, so it is NOT
zero at `i ∈ [47, 59)`: the padding is a property of THIS descriptor's term count, not of the
tensor, and writing it as one would be a different claim. -/
def derivedScalars : List Nat :=
  (List.range N_PAD).map (fun i => if i < N_REAL then tensorQ wireBasis i else 0)

/-- ⚑⚑ **THE AGGREGATE'S DECLARED SCALARS ARE THE TENSOR IMAGE OF THE WIRE BLOCK.** All 59 of them,
at full 255-bit width, under `PastaMsmScalarDerive`'s own `sAt` (via `tensorQ_is_sNat`). -/
theorem the_declared_scalars_are_the_tensor_of_the_wire_block :
    SCAL = derivedScalars := by decide

/-- ⚑⚑ **AND THEREFORE `T_COVER`'s EMITTED ROWS ARE THE DIGITS OF THAT IMAGE.**

This is the digit weld. The table is resolved by NAME out of the emitted artifact's own table list —
the singleton on the right is what refuses a second table under the same name — and its
`exactPublicRows` manifest is `coverManifest` of the scalars the wire block GENERATES, over the
window count the descriptor actually has.

⚠ Read §4 before citing it: the digits are still descriptor data, and `T_COVER`'s permutation is
still what forces them. What this says is where they COME FROM. -/
theorem the_emitted_cover_table_is_the_tensor_image_of_the_wire_block :
    (xiAggMsmDesc.tables.filter (fun t => t.name == "pasta_msm_cover")).map
        Dregg2.Circuit.DescriptorIR2.TableDef.sem
      = [Dregg2.Circuit.DescriptorIR2.RowSemantics.exactPublicRows
          (coverManifest N_PAD NBITS C derivedScalars)] := by
  rw [← the_declared_scalars_are_the_tensor_of_the_wire_block]
  rfl

/-- ⚑ …and what that says about the GRID, since `coverManifest` is `(w+1, i+1, digit_w(s_i))` by
construction: the emitted table has one row per trace row, `128 · 59 = 7 552` of them real, each
carrying `digit_w` of the tensor image at the generator index the row itself names.

⚠ Stated as the manifest's SHAPE rather than re-derived cell by cell. A per-cell `decide` over
7 552 rows re-evaluates `derivedScalars` — 47 six-factor tensors — once per cell, and it blew a
4 000 000-heartbeat budget. The table equality above is the stronger statement anyway; this is its
census. -/
theorem the_tensor_image_fills_the_whole_grid :
    coverRows.length = bucketedRows N_PAD NBITS C
      ∧ termRows N_PAD NBITS C = windowsOf NBITS C * N_PAD
      ∧ windowsOf NBITS C * N_PAD = 7552
      ∧ derivedScalars.length = N_PAD := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ### §3b — ⚠ THE FALSIFIERS, AND THEY MOVE VALUES THAT ARE READ FIRST. -/

/-- ⚑ **A MOVED WIRE FELT LEAVES THE DIGITS.** The head basis value's top limb raised by one — the
felt `the_moved_felt_is_what_it_is_claimed_to_be` read — and `T_COVER`'s manifest is no longer the
tensor image. This is what makes §3 a gate: the digits track the wire, they do not merely coexist
with it. -/
theorem a_perturbed_wire_felt_leaves_the_digits :
    ((List.range N_PAD).map (fun i =>
        if i < N_REAL then
          tensorQ ((List.range NCHAL).map (fun j =>
            decodeBlock (((aggBasisBlock.set (SK - 1) (aggBasisBlock.getD (SK - 1) 0 + 1)).drop
              (j * SK)).take SK))) i
        else 0))
      ≠ SCAL := by
  native_decide

/-- ⚑ **AND A TRANSPOSED BASIS LEAVES THEM TOO** — the same six values, `ξ³²` and `ξ¹⁶` exchanged.
The head pairs with the HIGH index bit, so the order is load-bearing and this is the refutation that
it is: a file that read `PastaMsmScalarDerive`'s convention backwards would be green everywhere
except here. -/
theorem a_transposed_basis_leaves_the_digits :
    ((List.range N_PAD).map (fun i =>
        if i < N_REAL then tensorQ ((wireBasis.set 0 (wireBasis.getD 1 0)).set 1
          (wireBasis.getD 0 0)) i else 0))
      ≠ SCAL := by
  native_decide

/-- ⚑ **AND THE TWO TAMPERS REALLY DO MOVE A VALUE.** Both refutations above are stated against
lists; this says the thing each one perturbs actually changes, so neither is a tamper that changed
nothing. -/
theorem the_tampers_move_a_value :
    aggBasisBlock.set (SK - 1) (aggBasisBlock.getD (SK - 1) 0 + 1) ≠ aggBasisBlock
      ∧ (wireBasis.set 0 (wireBasis.getD 1 0)).set 1 (wireBasis.getD 0 0) ≠ wireBasis
      ∧ wireBasis.getD 0 0 ≠ wireBasis.getD 1 0 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## §4 — ⚑ WHAT IS COMPUTED NOW, AND WHAT IS STILL DECLARED.

Stated at CURRENT resolution, per link of the path, so a reader can cite one link without
inheriting another's claim.

| link | status |
|---|---|
| block 539508's 91-element phase-2 tape → `v′` | **COMPUTED** — 46 emitted chain links, root verified |
| `v′` → `ξ` | **COMPUTED** — `dregg-mina-xi-endo-lift::v1`, an emitted AIR, 2 048×687 |
| `ξ` crosses to the machine | **WIRE** — 32 felts, elementwise |
| `ξ` → `ξ², ξ⁴, ξ⁸, ξ¹⁶, ξ³²` | **COMPUTED** — five multiplies of `xiChainProg`, published at `::v2` |
| the basis crosses to the aggregate | ⚑ **WIRE** — 192 felts, elementwise, §2 |
| the basis → the 59 scalars | **DERIVED IN LEAN** — §3, `sAt`'s tensor, checked once per (block, VK) |
| the 59 scalars → `T_COVER`'s 7 552 digits | **DESCRIPTOR DATA**, permutation-forced |
| `T_COVER` → `Σ sᵢ·Pᵢ` | **COMPUTED IN-CIRCUIT** — the fused running sum, 8 192 rows |

⚠ **THE ONE ROW THAT IS STILL A READER'S JOB** is `the basis → the 59 scalars`. It is a Lean theorem
over two emitted artifacts, not an emitted gate, so it is checked once per (block, VK) by whoever
reads them — and it costs that reader the 282 modular multiplications a batch verifier does not do.
`PastaMsmBucketed` §7.3's derivation is what turns that row into an in-circuit one; it is not built,
it is priced, and it is the next rung.

⚑ **AND THE `fpMulCore` DOWNGRADE IS NOT LIFTED, NOT SPREAD AND NOT REPAIRED.** The aggregate's rows
are the unsound multiply; `MinaWrapCommitStages` and `MinaWrapXiEndoLift` are `PastaFieldSound`. The
blocker is a TYPE obstruction and not a cost (`swCompleteAddGadget` takes gate CONSTRUCTORS while
`PastaFieldSound`/`PastaAddSubSound` are `EffectAir`s lowered through `EffectLower.lowerAir`, so no
sound complete-add and no sound `smul` core exist in this tree at all). ⚑ **When that bridge lands,
everything in this file carries over unchanged** — §2 compares two PI vectors and §3 reads a
manifest, and **neither half mentions the row template's multiply.** `chalPinGates` and
`chalThreadGates` do not multiply anything either. -/

/-- ⚑ **THE PATH'S TWO WIRE TIES, AS ONE STATEMENT.** ξ crosses at 32 felts and its basis crosses at
192, and the aggregate's basis tail is the endo lift's output block — so the three artifacts are one
chain and not three that happen to agree. -/
theorem the_path_is_one_chain :
    Dregg2.Circuit.Emit.MinaWrapXiEndoLift.endoOutputBlock
        = Dregg2.Circuit.Emit.MinaWrapXiEndoLift.chainInputBlock
      ∧ aggBasisBlock = chainBasisBlock
      ∧ aggBasisBlock.drop (5 * SK) = Dregg2.Circuit.Emit.MinaWrapXiEndoLift.endoOutputBlock := by
  refine ⟨Dregg2.Circuit.Emit.MinaWrapXiEndoLift.the_endo_output_block_is_the_chain_input_block,
    the_aggregate_wire_block_is_the_chain_wire_block, ?_⟩
  decide

#assert_axioms tensorQ_is_sNat
#assert_axioms the_aggregate_wire_block_is_the_chain_wire_block
#assert_compiled the_shared_block_is_six_whole_field_elements
#assert_compiled the_moved_felt_is_a_nonzero_byte_and_moving_it_moves_the_value
#assert_compiled a_perturbed_wire_felt_breaks_the_weld
#assert_compiled the_welded_descriptors_are_distinct
#assert_compiled the_wire_basis_is_the_squaring_orbit_of_the_lifted_polyscale
#assert_compiled the_wire_basis_is_five_squarings
#assert_axioms the_declared_scalars_are_the_tensor_of_the_wire_block
#assert_axioms the_emitted_cover_table_is_the_tensor_image_of_the_wire_block
#assert_compiled the_tensor_image_fills_the_whole_grid
#assert_compiled a_perturbed_wire_felt_leaves_the_digits
#assert_compiled a_transposed_basis_leaves_the_digits
#assert_compiled the_tampers_move_a_value
#assert_axioms the_path_is_one_chain

end Dregg2.Circuit.Emit.MinaWrapXiBasisWeld

/-
# `Dregg2.Circuit.Emit.MinaWrapXiScalarWeld` — the ξ-AGGREGATE'S DECLARED DIGITS, READ BACK OUT OF
THE EMITTED MANIFEST AND MATCHED AGAINST THE ORBIT OF A PUBLISHED ξ.

## ⚑ SAY THE SUBSTRATE OUT LOUD

**This file emits nothing and authors no gate.** It is a WELD: every object it names is emitted
somewhere else, and every theorem here reads one of those artifacts as DATA and compares it with
another. House Law #1 is not at risk in this file; the thing at risk here is the honesty of the
comparison, and §3 is where that is priced.

## WHAT IS TIED, AND WHAT KIND OF TIE IT IS

`MinaWrapXiEndoLift` closes ξ: the block's Fq sponge squeezes `v′`, an emitted AIR lifts it to ξ,
and ξ crosses to `MinaWrapCommitStages.xiDesc` as **32 shared public-input felts**. That is a wire
equality between two proofs.

The ξ-AGGREGATE cannot be joined that way, and the reason is structural rather than a cost.
`PastaMsmBucketed` §7.4, measured by its own author:

> This descriptor's `piCount = 27` publishes only the output `C`; `u⃗` enters through `T_COVER`'s
> declared digits and is therefore a DESCRIPTOR PARAMETER, not a wire value.

⚑ **So there WAS no PI slot on the aggregate for a published scalar to equal**, and the arithmetic
that made it look structural is `the_aggregate_has_room_for_the_basis_and_not_for_the_orbit`: a
47-scalar vector needs 1 504 felts at this cone's own limb width, which fits nothing. A "PI equality"
asserted against that side would have had to be a one-felt digest, and a one-felt tie between two
descriptors is `2^31` — the shape the `proof_bind` seam already has and the shape this cone was told
not to add.

⚑ **UPDATED 2026-08-05 — THE OBSTRUCTION WAS A MISSING SURFACE, AND THE SURFACE IS BUILT.** §3's own
closing note (six wire values, not forty-seven) is what made it cheap: `…-c2-w192::v1` publishes
`27 + 192` felts, `dregg-mina-xi-scalar-vector::v2` publishes the six-value basis on 192 of its own,
and `MinaWrapXiBasisWeld` ties them elementwise with no digest. **This file's §2 is now the
FULL-ORBIT corroboration of a tie that is a wire equality on the six generators.**

What IS available is a **descriptor-to-descriptor equality at full width**, and it is what this file
proves: `T_COVER`'s emitted manifest, read in ONE ordered pass keyed by each row's own generator
index, recomposes to exactly the orbit `(ξ⁰ … ξ⁴⁶, 0¹²)` of the ξ that crosses the wire in
`MinaWrapXiEndoLift`'s shared block. **47 scalars × 255 bits, elementwise, no digest.**

## ⚑ THE HONEST DIFFERENCE BETWEEN THE TWO TIES — do not let this get absorbed

  * ξ ↔ chain is checked **per proof, by the batch**, out of two PI vectors.
  * the orbit ↔ manifest is checked **once per (block, VK), by whoever reads the two artifacts**.
    It is not free: it costs the reader 46 multiplies in `q`, which is the work the chain circuit
    exists to remove. So this tie makes the aggregate's digits *derived from a published ξ* — it
    does **not** make them cheap for a verifier, and it does not put them on a wire.

⚠ The real fix is named and it is not this: `T_COVER`'s digits must be DERIVED in-row from a
challenge on the wire, which is `PastaMsmScalarDerive.deriveRowDesc`'s `chalPinGates` welded into
`bucketedRowDesc`. `PastaMsmBucketed` §7.3 prices it at ~1 400 constraints and ~2 700 columns and
notes the redundancy factor drops 256 → 20 in this layout. ⚑ **And for THIS aggregate the derivation
is already the right shape**: `PastaMsmScalarDerive.sAt` computes `s_i = ∏_j c_j^{bit_j(i)}`, and at
`c⃗ = (ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)` that IS `ξ^i` — so the ξ-aggregate needs a SIX-element challenge
vector on the wire, not a 47-element one. `the_squaring_basis_generates_the_orbit` is that fact,
stated here so the next lane builds the weld instead of rediscovering that it fits.

## Axiom hygiene

General theorems are `#assert_axioms`-clean (⊆ {propext, Classical.choice, Quot.sound}). Facts
about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06). No `sorry`/`admit`. Named theorems, not `#guard`s. NEW file; not imported by the `Dregg2` root.
-/
import Dregg2.Circuit.Emit.MinaWrapXiEndoLift
import Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm

namespace Dregg2.Circuit.Emit.MinaWrapXiScalarWeld

open Dregg2.Circuit.Emit.PastaFieldSound (SK)
open Dregg2.Circuit.Emit.PastaMsmBucketed (coverManifest termRows bucketedRows windowsOf)
open Dregg2.Circuit.Emit.MinaWrapXiAggregateMsm
  (N_REAL N_PAD C NBITS SCAL qpow qmul xiAggMsmDesc)
open Dregg2.Circuit.Emit.MinaWrapXiEndoLift (endoOutputBlock XI)

set_option autoImplicit false
set_option maxRecDepth 4000000
set_option maxHeartbeats 4000000

/-! ## §1 — ξ, READ BACK OUT OF THE SHARED PUBLIC-INPUT BLOCK.

Not `MinaWrapAggregationGate.XI` used as a constant — the 32 felts that actually cross the boundary
between the two proofs, decoded by the inverse of the map that wrote them. If the weld's boundary
carried a different value, every theorem below would move. -/

/-- The polyscale, recomposed from the 32 shared boundary felts. -/
def xiOnTheWire : Nat :=
  (List.range SK).foldr (fun i acc => acc * 256 + (endoOutputBlock.getD i 0).toNat) 0

/-- ⚑ **THE SHARED BOUNDARY CARRIES THE POLYSCALE.** -/
theorem the_shared_boundary_decodes_to_the_polyscale : xiOnTheWire = XI := by native_decide

/-! ## §2 — `T_COVER`'s MANIFEST, READ AS DATA.

⚑ **Keyed, not positional.** The fold below routes each row by the generator index the row itself
carries in field 1 — so a manifest whose rows were permuted, or whose keys disagreed with their
position, would land its digits somewhere else and the result would move. That is the discipline a
sibling lane paid for: a display name is not a key, and a position is not one either. -/

/-- The emitted manifest of the ξ-aggregate's cover table. -/
def coverRows : List (List Nat) := coverManifest N_PAD NBITS C SCAL

/-- ⚑ **AND IT IS THE DESCRIPTOR'S OWN TABLE**, not a re-derivation that happens to agree: the
table the emitted artifact declares under the name `pasta_msm_cover` carries exactly this list —
resolved by NAME out of the descriptor's own table list, and the singleton on the right is what
refuses a second table under the same name. -/
theorem the_cover_rows_are_the_descriptors_own_table :
    (xiAggMsmDesc.tables.filter (fun t => t.name == "pasta_msm_cover")).map
        Dregg2.Circuit.DescriptorIR2.TableDef.sem
      = [Dregg2.Circuit.DescriptorIR2.RowSemantics.exactPublicRows coverRows] := rfl

/-- One step of the recomposition: route the row's digit into the accumulator its own key names,
shifting that accumulator left by one window. -/
def absorbRow (acc : List Nat) (row : List Nat) : List Nat :=
  let i := row.getD 1 0
  if i = 0 then acc
  else acc.set (i - 1) ((acc.getD (i - 1) 0) * 2 ^ C + row.getD 2 0)

/-- ⚑ **THE 59 DECLARED SCALARS, RECOMPOSED IN ONE ORDERED PASS OVER THE EMITTED ROWS.** The
manifest is window-major and its windows run most-significant first, so a left fold that shifts and
adds walks each term's digits in order. -/
def manifestScalars : List Nat :=
  coverRows.foldl absorbRow (List.replicate N_PAD 0)

/-- ⚑⚑ **THE AGGREGATE'S DECLARED DIGITS ARE THE ORBIT OF THE ξ ON THE WIRE.**

`T_COVER` is the only place the scalars appear in the artifact, and it carries DIGITS. This says
those digits recompose — over the window count the descriptor actually has, keyed by the rows' own
generator indices — to `ξ⁰ … ξ⁴⁶` followed by the twelve zeros the padding carries, where `ξ` is
**the value the endo-lift proof publishes on the boundary the scalar chain consumes**.

47 full-width scalars. No digest, no truncation, no representative. -/
theorem the_declared_digits_are_the_orbit_of_the_wire_xi :
    manifestScalars
      = (List.range N_REAL).map (qpow xiOnTheWire) ++ List.replicate (N_PAD - N_REAL) 0 := by
  native_decide

/-- ⚑ **AND THE ORBIT IS 47 DIFFERENT SCALARS.** Without this the theorem above would be equally
green over a ξ of `0` or `1`, whose orbit is constant — which is exactly what a silently-zeroed
boundary would produce. -/
theorem the_orbit_is_not_constant :
    ((List.range N_REAL).map (qpow xiOnTheWire)).eraseDups.length = N_REAL
      ∧ xiOnTheWire ≠ 0 ∧ xiOnTheWire ≠ 1 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- The two rows the refutations below move, READ rather than assumed: the first term row is
window 1, generator 1, digit 0 (the leading base-4 digit of `ξ⁰ = 1`), and the row at index
`127 · 59` is the LAST window's digit of the same scalar, which is 1.

⚑ This exists because the first refutation drafted for `a_relabelled_key_leaves_the_orbit` moved a
row whose digit was ZERO into an accumulator that was also zero, and `decide` REFUTED the
refutation — a tamper that changes nothing is not a tamper, and nothing but reading the row would
have said so. -/
theorem the_tampered_rows_are_what_they_are_claimed_to_be :
    coverRows.getD 0 [] = [1, 1, 0] ∧ coverRows.getD 7493 [] = [128, 1, 1]
      ∧ 7493 = (windowsOf NBITS C - 1) * N_PAD := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND ONE MOVED DIGIT LEAVES THE ORBIT.** The first term row's digit raised by one — the
smallest change a prover that wanted a different aggregate could make to the artifact — and the
recomposition is no longer the orbit. This is what makes the theorem above a gate rather than a
restatement of how `coverManifest` was built. -/
theorem a_perturbed_digit_leaves_the_orbit :
    (coverRows.set 0 [1, 1, 1]).foldl absorbRow (List.replicate N_PAD 0)
      ≠ (List.range N_REAL).map (qpow xiOnTheWire) ++ List.replicate (N_PAD - N_REAL) 0 := by
  native_decide

/-- ⚑ **AND A RELABELLED KEY LEAVES IT TOO.** The same digit, in the same POSITION, routed to a
different generator by its own key — the forgery a positional read would not see. -/
theorem a_relabelled_key_leaves_the_orbit :
    (coverRows.set 7493 [128, 2, (coverRows.getD 7493 []).getD 2 0]).foldl absorbRow
        (List.replicate N_PAD 0)
      ≠ (List.range N_REAL).map (qpow xiOnTheWire) ++ List.replicate (N_PAD - N_REAL) 0 := by
  native_decide

/-- The manifest's shape, so a truncated or over-long emission is a red rather than a different
still-true sentence: one row per trace row, `128 · 59` of them real. -/
theorem the_manifest_is_the_trace_height :
    coverRows.length = bucketedRows N_PAD NBITS C
      ∧ termRows N_PAD NBITS C = windowsOf NBITS C * N_PAD
      ∧ manifestScalars.length = N_PAD := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ## §3 — ⚑ WHAT THIS TIE IS AND IS NOT.

Stated as theorems where it can be, so the limit is a fact about the artifacts and not a paragraph
a later reader can decide was pessimistic. -/

/-- ⚑ **THE AGGREGATE HAS NO ROOM FOR A *47*-SCALAR VECTOR — AND IT HAS ROOM FOR THE SIX.**

⚠ **This theorem said `piCount = 27` until 2026-08-05, and it went RED at the point of the change.**
That is what it was for. The original reading — *"the wire has no slot to put it in"* — was a
statement about a MISSING SURFACE and not about the layout, and `PastaMsmBucketed.chalPinGates`
supplied the surface. What survives, and what made the fix cheap, is the ARITHMETIC: a 47-scalar
vector needs `47 · 32 = 1 504` felts and would not have fitted anything; the six-value squaring
basis needs `192`, and `the_squaring_basis_generates_the_orbit` below is why six is enough.

`MinaWrapXiBasisWeld` is the wire tie this retires the obstruction for. -/
theorem the_aggregate_has_room_for_the_basis_and_not_for_the_orbit :
    xiAggMsmDesc.piCount = 27 + 6 * SK
      ∧ xiAggMsmDesc.piCount = 219
      ∧ 6 * SK < N_REAL * SK
      ∧ N_REAL * SK = 1504
      ∧ 6 * SK = 192 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- ⚑ **AND THE DERIVATION THAT WOULD FIX IT NEEDS SIX WIRE VALUES, NOT FORTY-SEVEN.**

`PastaMsmScalarDerive`'s tensor chain computes `s_i = ∏_j c_j^{bit_j(i)}`. At
`c⃗ = (ξ³², ξ¹⁶, ξ⁸, ξ⁴, ξ², ξ)` — the head pairing with the high index bit, which is that file's own
convention — the product IS `ξ^i` for every `i < 64`. So the ξ-aggregate's digits become DERIVED
from a **six-element** challenge vector on the wire, `6 · 32 = 192` public-input felts, and the
squaring basis is five multiplies from the ξ this cone already publishes.

Stated here as a named fact rather than left in a docblock, because the next lane's cost estimate
depends on it and the difference between 6 and 47 is the difference between a weld that fits the
deployed PI budget and one that does not. -/
theorem the_squaring_basis_generates_the_orbit :
    ((List.range N_REAL).all (fun i =>
      decide (qpow xiOnTheWire i
        = (List.range 6).foldl
            (fun acc j => if (i / 2 ^ j) % 2 = 1 then qmul acc (qpow xiOnTheWire (2 ^ j)) else acc)
            1))) = true := by
  native_decide

/-- ⚑ **AND SIX IS EXACTLY ENOUGH.** Five would drop `ξ³²`, and the aggregate's term count is 47. -/
theorem six_squarings_cover_forty_seven_terms :
    N_REAL ≤ 2 ^ 6 ∧ ¬ (N_REAL ≤ 2 ^ 5) ∧ 6 * SK = 192 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-! ### §3b — ⚑ THE PRICE THIS FILE DOES NOT LIFT.

`MinaWrapXiAggregateMsm` §4's third bullet is unchanged and is repeated because it is the kind of
thing that gets absorbed by a file that only reads artifacts: **the aggregate's rows are denominated
in the unsound `fpMulCore`**, where `MinaWrapXiEndoLift` and every descriptor in
`MinaWrapCommitStages` are `PastaFieldSound`. Nothing here repairs that, nothing here spreads it,
and the weld above does not make the aggregate's arithmetic sound — it makes its SCALARS derived.

⚑ **THE BLOCKER IS RETIRED (2026-08-05), AND THIS WELD DID CARRY OVER UNCHANGED.** It read:

> *"The blocker is a TYPE obstruction and not a cost: `swCompleteAddGadget` takes gate CONSTRUCTORS
> while `PastaFieldSound`/`PastaAddSubSound` are `EffectAir`s lowered through
> `EffectLower.lowerAir`, so no sound complete-add and no sound `smul` core exist in this tree at
> all."*

The type reading was right and one bullet short of the reason. The blocking leg is not arity: it is
that five of a sound multiply's 68 legs are `AirLeg.limbs` — range LOOKUPS against a table the AIR
must DECLARE — and `swCompleteAddGadget`'s return type has no channel for a `TableDef`
(`pallasCompleteAddDesc` carries `tables := []`). So even a widened `… → List VmConstraint2` would
emit lookups against nothing, and dropping them to fit would drop the SOUNDNESS: the byte-ranges are
`felt_gates_force_congruence`'s hypotheses, not its packaging.

`Dregg2.Circuit.Emit.PastaCurveSound` is the bridge — a `SoundCore` is a leg block plus a declared
witness width, the tables are hoisted to the composed AIR, and `lowerAir` runs once. The sound
`smul` core did not exist at all and now does, at 96 constraints rather than the multiply's 189.
Both curves: `pallasCompleteAddSound_forces`, `vestaCompleteAddSound_forces`, **4 476 constraints /
3 048 columns**, `#assert_axioms`-clean, and refusing the nonzero-ℤ-body pole in release
(`circuit/tests/pasta_curve_row_felt_soundness.rs`).

⚠ **What this does NOT retire is the sentence above it**: the ξ-aggregate's own rows are still
`fpMulCore`-denominated, because nothing has re-emitted them onto the sound core. The bridge makes
that a migration rather than an impossibility, and §7.2 of `PastaMsmBucketed` records the standing
verdict on whether this cone should be migrated at all. -/

#assert_compiled the_shared_boundary_decodes_to_the_polyscale
#assert_axioms the_cover_rows_are_the_descriptors_own_table
#assert_compiled the_declared_digits_are_the_orbit_of_the_wire_xi
#assert_compiled the_orbit_is_not_constant
#assert_compiled a_perturbed_digit_leaves_the_orbit
#assert_compiled a_relabelled_key_leaves_the_orbit
#assert_compiled the_tampered_rows_are_what_they_are_claimed_to_be
#assert_compiled the_manifest_is_the_trace_height
#assert_compiled the_aggregate_has_room_for_the_basis_and_not_for_the_orbit
#assert_compiled the_squaring_basis_generates_the_orbit
#assert_compiled six_squarings_cover_forty_seven_terms

end Dregg2.Circuit.Emit.MinaWrapXiScalarWeld

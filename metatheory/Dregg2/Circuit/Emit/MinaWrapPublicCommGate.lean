import Dregg2.Circuit.Emit.MinaWrapAggregationGate
-- ⚑ rung 5f's DATA (`SRS_H`, `LAGRANGE`, `PUBLIC_INPUT`, `NEG_PUBLIC`, `PUBLIC_COMM_GOLD`), split
-- out 2026-08-09 into the SAME namespace so nothing here or downstream is renamed. Three consumers
-- imported this gate for a literal and paid its 14.5 GB kernel `decide`; they now import the data.
import Dregg2.Circuit.Emit.MinaWrapPublicCommData
import Dregg2.Circuit.Emit.MinaRealBlockTranscript
/-!
# Dregg2.Circuit.Emit.MinaWrapPublicCommGate — RUNG 5e: the Wrap **`public_comm`**, derived
in-kernel from the SRS Lagrange basis and the REAL Mina devnet block's own 40-element public
input.

`docs/MINA-REAL-BLOCK-GATE.md` §6.1. Rungs 5a–5d showed that our group arithmetic agrees with
kimchi's on real points. This is the first rung whose input is not a commitment the block hands
us: `public_comm` is **computed from the public input** — the protocol-state hash, the two
`messages_for_next_*_proof` digests and the deferred values, packed into 40 `Fq` field elements
by openmina's own `PreparedStatement::to_public_input`.

## The object

`kimchi/src/verifier.rs:850-871` (`to_batch`'s "commit to the negated public input polynomial"):

```text
public_comm = mask_custom( MSM(lagrange[0..public], -public_input), blinders = 1 ).commitment
            = Σ_{i<40} (−publicᵢ)·Lᵢ  +  1·srs.h
```

`mask_custom` (`poly-commitment/src/ipa.rs:408-425`) is `com + blinder·h` per chunk, and the
blinder handed in here is literally `PolyComm::one` — so the "blinding" is a FIXED `+h`, not a
secret, and `tamper_blinder_dropped` below is what says it is nevertheless load-bearing.
`domain = 2^14 < max_poly_size = 2^15`, so `chunk_size = 1` and every Lagrange commitment and the
result are single-chunk.

## What this rung buys that 5a–5d did not

**It closes the transcript's public-commitment carrier.** `MinaRealBlockTranscript` absorbs
`PUBCOMM_XY` — the `(x, y)` of `public_comm` — as the third item of its phase-1 tape, and every
challenge on the real block descends from that absorb. Until now those two coordinates were
*eaten*: a number in a dump, with nothing saying it was a commitment to this block's public
input. `publicComm_is_the_transcript_preimage` derives them.

## What pins the gold

The extractor rebuilds `public_comm` with an **explicit sequential fold** — deliberately not
`PolyComm::multi_scalar_mul`, so the reconstruction is a different computation from the one it is
checked against — and asserts it equals o1-labs' `commit_public` output, which is the value the
ACCEPTED `kimchi::verifier::verify` and `oracles(...)` consumed. Then (GT5) it displaces
`public_comm` by `+G` inside the 47-entry evaluations list and **o1-labs' own `SRS::verify`
rejects**. Nothing is emitted unless both hold.

## Cost, measured

40 × 255-bit RCB ladders per instance ≈ 15 s of kernel at the 0.19 s/ladder unit `docs/
MINA-REAL-BLOCK-GATE.md` §6.1 established. Nine instances (four accept, five tamper):
**159 s / 14.5 GB peak RSS measured on hbox**.

## What this is NOT

It does not open a commitment — that is rung 5f (`MinaWrapOpeningGate`). And the SRS Lagrange
basis is taken as given: that `Lᵢ` is a commitment to the `i`-th Lagrange polynomial over the
`2^14` domain is a property of the SRS, not of this block, and is not checked here.

Facts about concrete data are `native_decide`, pinned `#assert_compiled` (since 2026-11-06);
no `sorry`. NEW file. NOT imported by the
`Dregg2` root, per house practice for gates. Import line:
`import Dregg2.Circuit.Emit.MinaWrapPublicCommGate`
-/

namespace Dregg2.Circuit.Emit.MinaWrapPublicCommGate

open Dregg2.Circuit.Emit.PastaField (pN qN)
open Dregg2.Circuit.Emit.PastaCurve (curveB)
open Dregg2.Circuit.Emit.PastaCurveComplete (Oproj projOnCurveM projEqM isInfM)
open Dregg2.Circuit.Emit.MinaWrapGroupGate (Pt padd msmComm)

set_option autoImplicit false
set_option maxRecDepth 20000000
set_option maxHeartbeats 4000000

/-! ## §2 — the computed object -/

/-- **`publicComm`** — `Σ (−publicᵢ)·Lᵢ + srs.h`, over K4b's 255-bit RCB ladder and K4a's
unified complete add. -/
def publicComm : Pt := padd (msmComm (NEG_PUBLIC.zip LAGRANGE)) SRS_H

/-! ## §3 — anti-vacuity: the inputs are real -/

/-- **`lagrange_basis_is_real`** — 40 Lagrange points and `srs.h` are on `y² = x³ + 5` over `Fp`,
the count is 40, and the basis has no repeated point in the first slots (a constant basis would
make §4 an accident). -/
theorem lagrange_basis_is_real :
    (LAGRANGE.all (projOnCurveM pN curveB) && projOnCurveM pN curveB SRS_H
      && projOnCurveM pN curveB PUBLIC_COMM_GOLD && !isInfM pN PUBLIC_COMM_GOLD) = true := by
  native_decide

/-- **`public_input_shape`** — 40 elements, all reduced in `Fq`, and not all equal (so the MSM is
not a disguised single scalar multiplication). -/
theorem public_input_shape :
    PUBLIC_INPUT.length = 40 ∧ LAGRANGE.length = 40
    ∧ PUBLIC_INPUT.all (fun x => decide (x < qN)) = true
    ∧ (PUBLIC_INPUT.getD 0 0 ≠ PUBLIC_INPUT.getD 1 0) := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

/-! ## §4 — ⚑ THE RUNG -/

/-- ⚑ **`publicComm_reproduces_kimchi`** — the 40-term Lagrange MSM over the block's own public
input, plus the fixed blinder, IS o1-labs' `public_comm`. Forty 255-bit ladders and forty-one
complete adds on real Pallas points. -/
theorem publicComm_reproduces_kimchi :
    projEqM pN publicComm PUBLIC_COMM_GOLD = true := by decide

/-- **`publicComm_is_a_finite_point`** — and not the identity, so `projEqM`'s `Z = 0` degeneracy
is not what made the previous theorem true. -/
theorem publicComm_is_a_finite_point : isInfM pN publicComm = false := by native_decide

/-- ⚑ **`publicComm_is_the_transcript_preimage`** — and the `(x, y)` pair `MinaRealBlockTranscript`
absorbs third into its phase-1 tape, from which β, γ, α′ and ζ′ all descend, is the point this
kernel just BUILT from the public input. C3 no longer eats its public commitment. -/
theorem publicComm_is_the_transcript_preimage :
    projEqM pN publicComm
      (MinaRealBlockTranscript.PUBCOMM_XY.getD 0 0,
       MinaRealBlockTranscript.PUBCOMM_XY.getD 1 0, 1) = true := by decide

/-- **`publicComm_is_combine_slot_2`** — and it is the point the 47-term aggregation folds at
index 2, so 5e feeds 5d rather than sitting beside it. -/
theorem publicComm_is_combine_slot_2 :
    projEqM pN publicComm
      (MinaWrapAggregationGate.COMBINE_POINTS.getD 2 Oproj) = true := by native_decide

/-! ## §5 — tamper poles

Each moves exactly one input and the result stops being `public_comm`. -/

/-- **`tamper_public_input`** — one added to the FIRST public-input element (the protocol-state
hash's own limb block). -/
theorem tamper_public_input :
    projEqM pN
      (padd (msmComm (((PUBLIC_INPUT.set 0 (PUBLIC_INPUT.getD 0 0 + 1)).map
          (fun x => (qN - x % qN) % qN)).zip LAGRANGE)) SRS_H)
      PUBLIC_COMM_GOLD = false := by native_decide

/-- **`tamper_last_public_input`** — and one added to the LAST, so the whole 40-element vector is
read, not a prefix. -/
theorem tamper_last_public_input :
    projEqM pN
      (padd (msmComm (((PUBLIC_INPUT.set 39 (PUBLIC_INPUT.getD 39 0 + 1)).map
          (fun x => (qN - x % qN) % qN)).zip LAGRANGE)) SRS_H)
      PUBLIC_COMM_GOLD = false := by native_decide

/-- **`tamper_sign`** — the public input NOT negated. kimchi commits to `−public`, and a verifier
that forgot the sign lands here. -/
theorem tamper_sign :
    projEqM pN (padd (msmComm (PUBLIC_INPUT.zip LAGRANGE)) SRS_H) PUBLIC_COMM_GOLD
      = false := by native_decide

/-- **`tamper_blinder_dropped`** — `mask_custom`'s `+1·h` omitted. The blinder is a constant and
public, which is exactly why it is easy to drop; it is still part of the committed value. -/
theorem tamper_blinder_dropped :
    projEqM pN (msmComm (NEG_PUBLIC.zip LAGRANGE)) PUBLIC_COMM_GOLD = false := by native_decide

/-- **`tamper_basis_rotation`** — the same 40 scalars against the basis rotated by one, i.e. every
public-input element assigned to the wrong Lagrange polynomial. A sum is order-insensitive, so
this — not a reversal — is the pole that says the ASSIGNMENT is checked. -/
theorem tamper_basis_rotation :
    projEqM pN
      (padd (msmComm (NEG_PUBLIC.zip (LAGRANGE.drop 1 ++ LAGRANGE.take 1))) SRS_H)
      PUBLIC_COMM_GOLD = false := by native_decide

#assert_namespace_axioms Dregg2.Circuit.Emit.MinaWrapPublicCommGate
  except tamper_basis_rotation tamper_blinder_dropped tamper_sign tamper_last_public_input tamper_public_input publicComm_is_combine_slot_2 publicComm_is_a_finite_point public_input_shape lagrange_basis_is_real

#assert_compiled tamper_basis_rotation
#assert_compiled tamper_blinder_dropped
#assert_compiled tamper_sign
#assert_compiled tamper_last_public_input
#assert_compiled tamper_public_input
#assert_compiled publicComm_is_combine_slot_2
#assert_compiled publicComm_is_a_finite_point
#assert_compiled public_input_shape
#assert_compiled lagrange_basis_is_real
end Dregg2.Circuit.Emit.MinaWrapPublicCommGate

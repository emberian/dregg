/-
# Market.EmitSameOpeningGadget — the SameOpeningGadget EMITTED as a byte-pinned descriptor

**Substrate, said out loud: this AIR is AUTHORED IN LEAN.** This file emits the Tier-0 apex
construction `Market.DarkBazaarSameOpeningGadget.GadgetAccepts` as a real `EffectVmDescriptor2`
(the same wire IR `circuit-prove` consumes), and proves the emit-SOUNDNESS theorem tying the
emitted descriptor's `Satisfied2` denotation back to `GadgetAccepts` — the analog of
`darkBazaarPrivateN4K4_emitted_air_sound` + `..._descriptor_to_accepts` for the same-opening
relation. No Rust AIR exists or will; Rust only fills this Lean-authored layout.

## Why limbs (the load-bearing emit decision)

The deployed BFV parameters are `fheRs4096`: `q` is 109-bit, `Δ = ⌊q/t⌋` is 90-bit
(`Bfv.Δ4096_bits`), and an honest phase `Δ·packedBook w + e` is up to ~118 bits. The descriptor
field is BabyBear (`p = 2013265921 ≈ 2^31`). A single-column phase gate
`phase − (Δ·b + e) ≡ 0 [ZMOD p]` would be UNSOUND as an integer statement — the gate value can wrap
mod p, admitting forged books. So the decryption-consistency half is emitted as an exact
**base-2^12 limb system with carry columns**:

  * the public phase is 10 base-4096 limbs (covers `< 2^120`);
  * the packed book is bit-decomposed (28 bits, the same 28-bit pack the private descriptor
    commits) and multiplied by the CONSTANT limbs of `Δ` (digits `deltaDigit i`, each < 2^12,
    so every partial product stays far inside the zero-residue window);
  * the private noise is offset-encoded: `e = eShift − 2^87` with `eShift` bit-decomposed to
    88 bits, so the range check enforces `|e| ≤ 2^87` — strictly inside the deployed decrypt
    margin (`safeNoise_deployed_pow87`, kernel-checked);
  * ten carry columns (15 bits each, offset by +1 to admit the −1 borrow) localize the integer
    identity limb-by-limb; every gate value is bounded `< 2^28 ≪ p`, so each modular gate LIFTS
    to an exact integer equation, and the telescoped chain gives
    `phase = Δ·packedBook w + e` over ℤ — no wrap, no slack.

The Poseidon2 root half is NOT re-authored: this descriptor reuses the private descriptor's
`rootLookup` VERBATIM — same `TableId.poseidon2` chip, same `rootInputExprs` shape, and the SAME
column indices (`SESSION=0`, `RULE=1`, `ROOT=2..9`, `BLINDING=12..19`, `PACKED_BOOK=20`) as
`darkBazaarPrivateN4K4Descriptor`.

## The join (named precisely)

The weld to the clearing proof is STATEMENT-LEVEL: both descriptors expose
`(session, rule, root[0..8))` at public-input indices 0..9 and bind them through the same
`ChipTableSoundN`-sound Poseidon2 chip. A verifier that checks both proofs against the SAME
`(session, root)` statement gets: the clearing was computed over a book `w₁` opening that root
(private descriptor), and the ciphertext opens to a book `w₂` opening that root (this file);
`two_distinct_openings_yield_root_collision` / `RootCollision` then pins `w₁ = w₂` short of a
Poseidon2 binding break. That cross-descriptor weld theorem is NAMED, not proved here (§ residuals).

## What is proved here

  * `sameOpeningGadget_emit_sound` — **the emit-soundness keystone**: any `Satisfied2`-satisfying
    canonical trace of the emitted descriptor yields a decoded witness `w` with
    `GadgetAccepts fheRs4096 (permHash8 permOut) session cols w` at the column-read phase/noise/root.
  * `sameOpeningGadget_emit_discharges_apex` — chained through the proved `gadgetAccepts_sound`:
    the emitted descriptor discharges `SameOpening` itself.
  * `sameOpeningGadget_emitted_statement_sound` — the statement-level form: `SameOpening` at the
    PUBLIC-INPUT-read session, phase limbs, and root lanes (what a verifier actually sees).
  * The exact integer decode underneath: bit lifts, limb recompositions, the carry-chain
    telescope (`limb_identity`), the noise-margin check, and the wide-root binding.

## NAMED residuals (honest boundary — none faked)

  1. **Emitted completeness.** Soundness only, like the private descriptor: realizing every
     accepting `GadgetAccepts` instance as a satisfying trace (carry values exist in range) is
     argued by the arithmetic above but NOT proved in Lean here. Also the emitted noise family is
     `|e| ≤ 2^87`, a strict subset of the relation's full `SafeNoise` margin (≈ 2^88): honest
     instances beyond 2^87 are not representable — a named completeness gap, no soundness cost.
  2. **Phase-limb well-formedness is a statement obligation**: the theorems take
     `pis (10+k) < 4096` (and `CanonicalAssignment`), exactly as the private descriptor takes
     canonical cells. The emitted AIR does not range-check the PUBLIC phase limbs; the verifier
     checks its own statement.
  3. **RNS/CRT + collective key**: the phase limbs model the CRT-reconstructed ℤ-phase of the
     scalar `Bfv` model (named gap inherited from `Bfv.Noise`, not widened). Binding the limbs to
     the actually-posted RNS ciphertext rows under the COLLECTIVE key (no single party holds `s`)
     is the named §3.2/§3.3 residual — the host cannot honestly fill the phase limbs alone.
  4. **The poly (per-slot) emit**: this emits the SCALAR `GadgetAccepts`; `GadgetAcceptsPoly`
     (4 slots) is 4 copies of this dec-chain (per-slot 7-bit code instead of the 28-bit pack)
     sharing the one root lookup — structured by `gadgetAcceptsPoly_master`, not yet emitted.
  5. **The cross-descriptor weld theorem** (join above) — named, not proved here.

Build: `cd metatheory && lake env lean Market/EmitSameOpeningGadget.lean`
Emit:  `cd metatheory && lake env lean --run Market/EmitSameOpeningGadget.lean`
-/
import Market.DarkBazaarSameOpeningGadget

namespace Market.EmitSameOpeningGadget

open Dregg2.Circuit (Assignment)
open Dregg2.Exec.CircuitEmit (EmittedExpr)
open Dregg2.Circuit.Emit.EffectVmEmit (VmConstraint)
open Dregg2.Circuit.DescriptorIR2
  (EffectVmDescriptor2 VmConstraint2 TableId TraceFamily VmTrace Satisfied2
    ChipTableSoundN chipLookupTupleN chip_lookup_sound_N envAt emitVmJson2)
open Market.DarkBazaarPrivateDescriptor
open Market.DarkBazaarSameOpening
open Market.DarkBazaarSameOpeningGadget
open Bfv

set_option autoImplicit false

/-! ## 1. Layout.

Columns 0..20 MATCH `darkBazaarPrivateN4K4Descriptor` exactly (`SESSION=0`, `RULE=1`,
`ROOT lane = 2+lane`, `BLINDING lane = 12+lane`, `PACKED_BOOK=20`; 10/11 unused here), so the
private descriptor's `rootLookup` is reused verbatim. New columns: -/

/-- Public phase limb `k` (base 4096, little-endian), columns 21..30. -/
def PHASE_LIMB (k : Nat) : Nat := 21 + k
/-- Packed-book bit `i` (28 bits), columns 31..58. -/
def BBIT (i : Nat) : Nat := 31 + i
/-- Shifted-noise bit `i` (88 bits: `eShift = e + 2^87 < 2^88`), columns 59..146. -/
def EBIT (i : Nat) : Nat := 59 + i
/-- Carry bit `i` (10 carries × 15 bits, +1-offset encoding), columns 147..296. -/
def CBIT (i : Nat) : Nat := 147 + i
def GADGET_TRACE_WIDTH : Nat := 297

/-- `Δ` for `fheRs4096` as a pinned literal (kernel-checked below). -/
def DELTA : Int := 628790808402079651235184628

/-- The base-2^12 digits of the deployed `Δ` (little-endian; kernel-checked below). -/
def deltaDigit : Nat → Int
  | 0 => 4084 | 1 => 2707 | 2 => 1096 | 3 => 382
  | 4 => 1666 | 5 => 2592 | 6 => 2079 | 7 => 32
  | _ => 0

/-- The deployed `Δ` really is the pinned literal (kernel `decide` on the 109-bit division). -/
theorem delta_deployed : ((fheRs4096.Δ : ℕ) : ℤ) = DELTA := by decide

/-- The digits really recompose to `Δ` (kernel `decide`). -/
theorem delta_digits_recompose :
    deltaDigit 0 + 4096 * deltaDigit 1 + 4096 ^ 2 * deltaDigit 2 + 4096 ^ 3 * deltaDigit 3 +
      4096 ^ 4 * deltaDigit 4 + 4096 ^ 5 * deltaDigit 5 + 4096 ^ 6 * deltaDigit 6 +
      4096 ^ 7 * deltaDigit 7 = DELTA := by decide

theorem deltaDigit_bounds (i : Nat) : 0 ≤ deltaDigit i ∧ deltaDigit i ≤ 4095 := by
  match i with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => exact ⟨by norm_num [deltaDigit], by norm_num [deltaDigit]⟩
  | n + 8 => exact ⟨le_refl 0, by show (0 : ℤ) ≤ 4095; norm_num⟩

/-! ## 2. Bit-sum machinery (values and expressions). -/

/-- The integer denoted by `n` little-endian bit columns. -/
def bitSum (a : Assignment) (col : Nat → Nat) (n : Nat) : Int :=
  ((List.range n).map fun j => (2 : Int) ^ j * a (col j)).sum

/-- The same sum as an emitted expression. -/
def bitSumE (col : Nat → Nat) (n : Nat) : EmittedExpr :=
  sumE ((List.range n).map fun j => weighted ((2 : Int) ^ j) (v (col j)))

theorem sumE_eval (a : Assignment) (xs : List EmittedExpr) :
    (sumE xs).eval a = (xs.map (·.eval a)).sum := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    simp only [sumE, List.foldr_cons, List.map_cons, List.sum_cons] at *
    simp only [add, EmittedExpr.eval]
    rw [ih]

theorem bitSumE_eval (a : Assignment) (col : Nat → Nat) (n : Nat) :
    (bitSumE col n).eval a = bitSum a col n := by
  unfold bitSumE bitSum
  rw [sumE_eval, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  simp [Function.comp, weighted, mul, v, c, EmittedExpr.eval]

theorem bitSum_succ (a : Assignment) (col : Nat → Nat) (n : Nat) :
    bitSum a col (n + 1) = bitSum a col n + 2 ^ n * a (col n) := by
  unfold bitSum
  rw [List.range_succ, List.map_append, List.sum_append]
  simp

theorem bitSum_bounds (a : Assignment) (col : Nat → Nat) (n : Nat)
    (h : ∀ j, j < n → a (col j) = 0 ∨ a (col j) = 1) :
    0 ≤ bitSum a col n ∧ bitSum a col n < 2 ^ n := by
  induction n with
  | zero => simp [bitSum]
  | succ n ih =>
    have hn := ih (fun j hj => h j (Nat.lt_succ_of_lt hj))
    have hbit := h n (Nat.lt_succ_self n)
    have hp : (0 : ℤ) < 2 ^ n := by positivity
    have hs : (2 : ℤ) ^ (n + 1) = 2 * 2 ^ n := by ring
    rw [bitSum_succ]
    rcases hbit with hb | hb <;> rw [hb] <;> constructor <;> linarith [hn.1, hn.2]

theorem bitSum_append (a : Assignment) (col : Nat → Nat) (m n : Nat) :
    bitSum a col (m + n) =
      bitSum a col m + 2 ^ m * bitSum a (fun j => col (m + j)) n := by
  induction n with
  | zero => simp [bitSum]
  | succ n ih =>
    have h1 : m + (n + 1) = (m + n) + 1 := by omega
    rw [h1, bitSum_succ, ih, bitSum_succ]
    have h2 : (2 : ℤ) ^ (m + n) = 2 ^ m * 2 ^ n := by rw [pow_add]
    rw [h2]; ring

theorem bitSum_congr (a : Assignment) {col col' : Nat → Nat} (n : Nat)
    (h : ∀ j, j < n → col j = col' j) : bitSum a col n = bitSum a col' n := by
  unfold bitSum
  apply congrArg List.sum
  apply List.map_congr_left
  intro j hj
  rw [h j (List.mem_range.mp hj)]

/-! ## 3. The decoded values. -/

/-- The packed book read off the 28 bit columns. -/
def bVal (a : Assignment) : Int := bitSum a BBIT 28
/-- The shifted noise read off the 88 bit columns. -/
def eShiftVal (a : Assignment) : Int := bitSum a EBIT 88
/-- The (signed) noise: offset decode `e = eShift − 2^87`. -/
def noiseVal (a : Assignment) : Int := eShiftVal a - 2 ^ 87
/-- The public phase read off the ten base-4096 limbs. -/
def phaseVal (a : Assignment) : Int :=
  ((List.range 10).map fun k => (4096 : Int) ^ k * a (PHASE_LIMB k)).sum
/-- Base-4096 digit `j` of the packed book (widths 12,12,4). -/
def bDigit (a : Assignment) (j : Nat) : Int :=
  bitSum a (fun i => BBIT (12 * j + i)) (if j = 2 then 4 else 12)
/-- Base-4096 digit `k` of the shifted noise (widths 12×7, 4). -/
def eDigit (a : Assignment) (k : Nat) : Int :=
  bitSum a (fun i => EBIT (12 * k + i)) (if k = 7 then 4 else 12)
/-- Carry `k`, +1-offset decoded: value in `[−1, 2^15−2]`. -/
def carryVal (a : Assignment) (k : Nat) : Int :=
  bitSum a (fun j => CBIT (15 * k + j)) 15 - 1
/-- Base-128 order-code digit `i` of the packed book (bits `7i..7i+7`). -/
def codeVal (a : Assignment) (i : Nat) : Int :=
  bitSum a (fun j => BBIT (7 * i + j)) 7

/-- The k-th convolution term `Σ_{j≤2, j≤k, k−j<8} Δ_{k−j}·b_j` (value form). -/
def convVal (a : Assignment) (k : Nat) : Int :=
  ((List.range 3).map fun j =>
    if j ≤ k ∧ k - j < 8 then deltaDigit (k - j) * bDigit a j else 0).sum
def eTermVal (a : Assignment) (k : Nat) : Int := if k < 8 then eDigit a k else 0
def tPrevVal (a : Assignment) (k : Nat) : Int := if k = 0 then 0 else carryVal a (k - 1)
/-- The noise-offset digit: `2^87 = 8·4096^7`. -/
def offK (k : Nat) : Int := if k = 7 then 8 else 0

/-! ## 4. The gate expressions. -/

def bDigitE (j : Nat) : EmittedExpr :=
  bitSumE (fun i => BBIT (12 * j + i)) (if j = 2 then 4 else 12)
def eDigitE (k : Nat) : EmittedExpr :=
  bitSumE (fun i => EBIT (12 * k + i)) (if k = 7 then 4 else 12)
def carryE (k : Nat) : EmittedExpr :=
  sub (bitSumE (fun j => CBIT (15 * k + j)) 15) (c 1)
def convE (k : Nat) : EmittedExpr :=
  sumE ((List.range 3).map fun j =>
    if j ≤ k ∧ k - j < 8 then weighted (deltaDigit (k - j)) (bDigitE j) else c 0)
def eTermE (k : Nat) : EmittedExpr := if k < 8 then eDigitE k else c 0
def tPrevE (k : Nat) : EmittedExpr := if k = 0 then c 0 else carryE (k - 1)

/-- Carry-chain gate `k`: `conv_k + eDigit_k + t_{k−1} − (phase_k + off_k + 4096·t_k) = 0`. -/
def carryBody (k : Nat) : EmittedExpr :=
  sub (add (add (convE k) (eTermE k)) (tPrevE k))
      (add (add (v (PHASE_LIMB k)) (c (offK k))) (weighted 4096 (carryE k)))

theorem bDigitE_eval (a : Assignment) (j : Nat) : (bDigitE j).eval a = bDigit a j :=
  bitSumE_eval a _ _

theorem eDigitE_eval (a : Assignment) (k : Nat) : (eDigitE k).eval a = eDigit a k :=
  bitSumE_eval a _ _

theorem carryE_eval (a : Assignment) (k : Nat) : (carryE k).eval a = carryVal a k := by
  unfold carryE carryVal
  simp [sub, neg, add, mul, c, EmittedExpr.eval, bitSumE_eval]
  ring

theorem convE_eval (a : Assignment) (k : Nat) : (convE k).eval a = convVal a k := by
  unfold convE convVal
  rw [sumE_eval, List.map_map]
  apply congrArg List.sum
  apply List.map_congr_left
  intro j _
  by_cases hc : j ≤ k ∧ k - j < 8
  · simp [Function.comp, hc, weighted, mul, c, EmittedExpr.eval, bDigitE_eval]
  · simp [Function.comp, hc, c, EmittedExpr.eval]

theorem carryBody_eval (a : Assignment) (k : Nat) :
    (carryBody k).eval a =
      convVal a k + eTermVal a k + tPrevVal a k
        - (a (PHASE_LIMB k) + offK k + 4096 * carryVal a k) := by
  unfold carryBody eTermE tPrevE eTermVal tPrevVal
  split_ifs with h1 h2 <;>
    simp [sub, neg, add, mul, weighted, v, c, EmittedExpr.eval,
      convE_eval, carryE_eval, eDigitE_eval] <;> ring

/-! ## 5. The descriptor. -/

def gadgetBinaries : List EmittedExpr :=
  ((List.range 28).map fun i => binaryBody (BBIT i)) ++
  ((List.range 88).map fun i => binaryBody (EBIT i)) ++
  ((List.range 150).map fun i => binaryBody (CBIT i))

def gadgetBodies : List EmittedExpr :=
  [ sub (v RULE) (c RULE_ID)
  , sub (v PACKED_BOOK) (bitSumE BBIT 28) ] ++
  gadgetBinaries ++
  ((List.range 10).map carryBody) ++
  [carryE 9]

def gadgetPins : List VmConstraint2 :=
  [ .base (.piBinding .first SESSION 0)
  , .base (.piBinding .first RULE 1) ] ++
  (List.range 8).map (fun i => .base (.piBinding .first (ROOT i) (2 + i))) ++
  (List.range 10).map (fun k => .base (.piBinding .first (PHASE_LIMB k) (10 + k)))

/-- **The emitted SameOpeningGadget descriptor.** Reuses the private descriptor's `rootLookup`
(the Poseidon2 chip binding of `ROOT 0..7` to the domain-separated preimage over `SESSION`,
`RULE`, `PACKED_BOOK`, `BLINDING 0..7`) verbatim; adds the limbed decryption-consistency chain. -/
def sameOpeningGadgetDescriptor : EffectVmDescriptor2 :=
  { name := "same-opening-gadget-n4::dec-limb-v1"
  , traceWidth := GADGET_TRACE_WIDTH
  , piCount := 20
  , tables := []
  , constraints := [rootLookup] ++
      gadgetBodies.map (fun body => .base (.gate body)) ++ gadgetPins ++
      gadgetBodies.map (fun body => .base (.boundary .last body))
  , hashSites := []
  , ranges := [] }

#guard sameOpeningGadgetDescriptor.traceWidth == 297
#guard sameOpeningGadgetDescriptor.piCount == 20
#guard gadgetBodies.length == 2 + 266 + 10 + 1
#guard sameOpeningGadgetDescriptor.constraints.length == 1 + 2 * gadgetBodies.length + 20
-- Byte pins on the emitted JSON (drift gate; the full golden file is supervisor wiring):
#guard (emitVmJson2 sameOpeningGadgetDescriptor).length == 210329
#guard (emitVmJson2 sameOpeningGadgetDescriptor).contains "same-opening-gadget-n4::dec-limb-v1"
-- The top Δ digit (32·4096^7 carries the 2^87 headroom structure) really rides the wire:
#guard (emitVmJson2 sameOpeningGadgetDescriptor).contains "4084"

/-! ## 6. `Satisfied2` extraction rungs (mirroring the private descriptor). -/

theorem gadget_gate_mem {body : EmittedExpr} (hbody : body ∈ gadgetBodies) :
    VmConstraint2.base (.gate body) ∈ sameOpeningGadgetDescriptor.constraints := by
  have hmem : VmConstraint2.base (.gate body) ∈
      gadgetBodies.map (fun b => VmConstraint2.base (.gate b)) :=
    List.mem_map.mpr ⟨body, hbody, rfl⟩
  simp only [sameOpeningGadgetDescriptor, List.mem_append]
  tauto

theorem gadget_pin_mem {pin : VmConstraint2} (hpin : pin ∈ gadgetPins) :
    pin ∈ sameOpeningGadgetDescriptor.constraints := by
  simp only [sameOpeningGadgetDescriptor, List.mem_append]
  tauto

theorem gadget_root_lookup_mem :
    rootLookup ∈ sameOpeningGadgetDescriptor.constraints := by
  simp only [sameOpeningGadgetDescriptor, List.mem_append, List.mem_singleton]
  tauto

theorem gadget_gate_vanishes {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 []
      (constTrace a pis tf))
    {body : EmittedExpr} (hbody : body ∈ gadgetBodies) :
    body.eval a ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (gadget_gate_mem hbody)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem gadget_pin_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 []
      (constTrace a pis tf))
    {col pi : Nat}
    (hpin : VmConstraint2.base (.piBinding .first col pi) ∈ gadgetPins) :
    a col ≡ pis pi [ZMOD BABYBEAR_MODULUS] := by
  have h := hsat.rowConstraints 0 (by simp) _ (gadget_pin_mem hpin)
  simpa [VmConstraint2.holdsAt, VmConstraint.holdsVm, BABYBEAR_MODULUS] using h

theorem gadget_wide_root_sound {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}
    (permOut : List Int → List Int)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 []
      (constTrace a pis tf)) :
    rootDigestCols.map a = permOut (rootInputExprs.map (·.eval a)) := by
  have hrow := hsat.rowConstraints 0 (by simp) rootLookup gadget_root_lookup_mem
  have hlookup :
      (chipLookupTupleN rootInputExprs rootDigestCols).map (·.eval a) ∈ tf TableId.poseidon2 := by
    simpa [Market.DarkBazaarPrivateDescriptor.rootLookup, VmConstraint2.holdsAt,
      Dregg2.Circuit.DescriptorIR2.Lookup.holdsAt] using hrow
  exact chip_lookup_sound_N permOut (tf TableId.poseidon2) hChip a
    rootInputExprs rootDigestCols (by decide) hlookup

/-! ## 7. Bit families and exact column decodes. -/

section Decode

variable {hash : List Int → Int} {a pis : Assignment} {tf : TraceFamily}

theorem bbit_body_mem {i : Nat} (hi : i < 28) : binaryBody (BBIT i) ∈ gadgetBodies := by
  have h : binaryBody (BBIT i) ∈ (List.range 28).map fun i => binaryBody (BBIT i) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [gadgetBodies, gadgetBinaries, List.mem_append]
  tauto

theorem ebit_body_mem {i : Nat} (hi : i < 88) : binaryBody (EBIT i) ∈ gadgetBodies := by
  have h : binaryBody (EBIT i) ∈ (List.range 88).map fun i => binaryBody (EBIT i) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [gadgetBodies, gadgetBinaries, List.mem_append]
  tauto

theorem cbit_body_mem {i : Nat} (hi : i < 150) : binaryBody (CBIT i) ∈ gadgetBodies := by
  have h : binaryBody (CBIT i) ∈ (List.range 150).map fun i => binaryBody (CBIT i) :=
    List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩
  simp only [gadgetBodies, gadgetBinaries, List.mem_append]
  tauto

theorem carry_body_mem {k : Nat} (hk : k < 10) : carryBody k ∈ gadgetBodies := by
  have h : carryBody k ∈ (List.range 10).map carryBody :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  simp only [gadgetBodies, List.mem_append]
  tauto

theorem top_carry_body_mem : carryE 9 ∈ gadgetBodies := by
  simp [gadgetBodies]

theorem rule_body_mem' : sub (v RULE) (c RULE_ID) ∈ gadgetBodies := by
  simp [gadgetBodies]

theorem pb_body_mem : sub (v PACKED_BOOK) (bitSumE BBIT 28) ∈ gadgetBodies := by
  simp [gadgetBodies]

theorem bbits (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    ∀ i, i < 28 → a (BBIT i) = 0 ∨ a (BBIT i) = 1 := fun _ hi =>
  binary_of_modular_gate hcanon (gadget_gate_vanishes hsat (bbit_body_mem hi))

theorem ebits (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    ∀ i, i < 88 → a (EBIT i) = 0 ∨ a (EBIT i) = 1 := fun _ hi =>
  binary_of_modular_gate hcanon (gadget_gate_vanishes hsat (ebit_body_mem hi))

theorem cbits (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    ∀ i, i < 150 → a (CBIT i) = 0 ∨ a (CBIT i) = 1 := fun _ hi =>
  binary_of_modular_gate hcanon (gadget_gate_vanishes hsat (cbit_body_mem hi))

theorem bDigit_bounds (hb : ∀ i, i < 28 → a (BBIT i) = 0 ∨ a (BBIT i) = 1)
    {j : Nat} (hj : j < 3) : 0 ≤ bDigit a j ∧ bDigit a j ≤ 4095 := by
  unfold bDigit
  have hw : ∀ i, i < (if j = 2 then 4 else 12) → 12 * j + i < 28 := by
    intro i hi
    by_cases h2 : j = 2 <;> simp [h2] at hi ⊢ <;> omega
  have hbs := bitSum_bounds a (fun i => BBIT (12 * j + i)) _ (fun i hi => hb _ (hw i hi))
  have h4 : (2 : ℤ) ^ (4 : ℕ) = 16 := by norm_num
  have h12 : (2 : ℤ) ^ (12 : ℕ) = 4096 := by norm_num
  by_cases h2 : j = 2 <;> simp only [h2, if_true, if_false] at hbs ⊢ <;> omega

theorem eDigit_bounds (hb : ∀ i, i < 88 → a (EBIT i) = 0 ∨ a (EBIT i) = 1)
    {k : Nat} (hk : k < 8) : 0 ≤ eDigit a k ∧ eDigit a k ≤ 4095 := by
  unfold eDigit
  have hw : ∀ i, i < (if k = 7 then 4 else 12) → 12 * k + i < 88 := by
    intro i hi
    by_cases h2 : k = 7 <;> simp [h2] at hi ⊢ <;> omega
  have hbs := bitSum_bounds a (fun i => EBIT (12 * k + i)) _ (fun i hi => hb _ (hw i hi))
  have h4 : (2 : ℤ) ^ (4 : ℕ) = 16 := by norm_num
  have h12 : (2 : ℤ) ^ (12 : ℕ) = 4096 := by norm_num
  by_cases h2 : k = 7 <;> simp only [h2, if_true, if_false] at hbs ⊢ <;> omega

theorem carry_bounds (hc : ∀ i, i < 150 → a (CBIT i) = 0 ∨ a (CBIT i) = 1)
    {k : Nat} (hk : k < 10) : -1 ≤ carryVal a k ∧ carryVal a k ≤ 32766 := by
  unfold carryVal
  have hbs := bitSum_bounds a (fun j => CBIT (15 * k + j)) 15
    (fun j hj => hc _ (by omega))
  have h15 : (2 : ℤ) ^ (15 : ℕ) = 32768 := by norm_num
  omega

theorem convVal_bounds (hb : ∀ i, i < 28 → a (BBIT i) = 0 ∨ a (BBIT i) = 1) (k : Nat) :
    0 ≤ convVal a k ∧ convVal a k ≤ 50307075 := by
  have h0 := bDigit_bounds hb (j := 0) (by omega)
  have h1 := bDigit_bounds hb (j := 1) (by omega)
  have h2 := bDigit_bounds hb (j := 2) (by omega)
  have d0 := deltaDigit_bounds k
  have d1 := deltaDigit_bounds (k - 1)
  have d2 := deltaDigit_bounds (k - 2)
  have m0l : 0 ≤ deltaDigit k * bDigit a 0 := mul_nonneg d0.1 h0.1
  have m1l : 0 ≤ deltaDigit (k - 1) * bDigit a 1 := mul_nonneg d1.1 h1.1
  have m2l : 0 ≤ deltaDigit (k - 2) * bDigit a 2 := mul_nonneg d2.1 h2.1
  have m0u : deltaDigit k * bDigit a 0 ≤ 4095 * 4095 :=
    mul_le_mul d0.2 h0.2 h0.1 (by norm_num)
  have m1u : deltaDigit (k - 1) * bDigit a 1 ≤ 4095 * 4095 :=
    mul_le_mul d1.2 h1.2 h1.1 (by norm_num)
  have m2u : deltaDigit (k - 2) * bDigit a 2 ≤ 4095 * 4095 :=
    mul_le_mul d2.2 h2.2 h2.1 (by norm_num)
  unfold convVal
  norm_num [List.range_succ]
  split_ifs <;> constructor <;> linarith

theorem rule_column_exact' (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    a RULE = RULE_ID := by
  have hgate := gadget_gate_vanishes hsat rule_body_mem'
  have hres : a RULE - RULE_ID ≡ 0 [ZMOD BABYBEAR_MODULUS] := by
    simpa [sub, neg, mul, add, v, c, EmittedExpr.eval, ← sub_eq_add_neg] using hgate
  have hcong : a RULE ≡ RULE_ID [ZMOD BABYBEAR_MODULUS] := by
    simpa using hres.add_right RULE_ID
  exact eq_of_modEq_of_canonical hcong (hcanon RULE) (by
    norm_num [RULE_ID, BABYBEAR_MODULUS])

theorem packed_book_bits_exact (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    a PACKED_BOOK = bVal a := by
  have hb := bbits hcanon hsat
  have hbounds := bitSum_bounds a BBIT 28 hb
  have hgate := gadget_gate_vanishes hsat pb_body_mem
  have hev : (sub (v PACKED_BOOK) (bitSumE BBIT 28)).eval a = a PACKED_BOOK - bVal a := by
    simp [sub, neg, mul, add, v, c, EmittedExpr.eval, bitSumE_eval, bVal]
    ring
  rw [hev] at hgate
  have hcong : a PACKED_BOOK ≡ bVal a [ZMOD BABYBEAR_MODULUS] := by
    simpa using hgate.add_right (bVal a)
  apply eq_of_modEq_of_canonical hcong (hcanon PACKED_BOOK)
  have h28 : (2 : ℤ) ^ (28 : ℕ) = 268435456 := by norm_num
  unfold bVal at *
  simp only [BABYBEAR_MODULUS]
  omega

/-! ## 8. The carry-chain lift and telescope. -/

theorem carry_gate_exact (hcanon : CanonicalAssignment a)
    (hphase : ∀ k, k < 10 → a (PHASE_LIMB k) < 4096)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf))
    {k : Nat} (hk : k < 10) :
    convVal a k + eTermVal a k + tPrevVal a k
      = a (PHASE_LIMB k) + offK k + 4096 * carryVal a k := by
  have hb := bbits hcanon hsat
  have he := ebits hcanon hsat
  have hc := cbits hcanon hsat
  have hmod := gadget_gate_vanishes hsat (carry_body_mem hk)
  rw [carryBody_eval] at hmod
  have hcv := convVal_bounds hb k
  have het : 0 ≤ eTermVal a k ∧ eTermVal a k ≤ 4095 := by
    unfold eTermVal
    split_ifs with h
    · exact eDigit_bounds he h
    · norm_num
  have htp : -1 ≤ tPrevVal a k ∧ tPrevVal a k ≤ 32766 := by
    unfold tPrevVal
    split_ifs with h
    · norm_num
    · exact carry_bounds hc (by omega)
  have hcy := carry_bounds hc hk
  have hph := hphase k hk
  have hph0 := (hcanon (PHASE_LIMB k)).1
  have hoff : 0 ≤ offK k ∧ offK k ≤ 8 := by
    unfold offK; split_ifs <;> norm_num
  have hzero := eq_zero_of_modEq_zero_of_window hmod (by
    unfold InZeroResidueWindow
    simp only [BABYBEAR_MODULUS]
    constructor <;> omega)
  linarith [hzero]

theorem top_carry_zero (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    carryVal a 9 = 0 := by
  have hc := cbits hcanon hsat
  have hmod := gadget_gate_vanishes hsat top_carry_body_mem
  rw [carryE_eval] at hmod
  have hcy := carry_bounds hc (k := 9) (by omega)
  exact eq_zero_of_modEq_zero_of_window hmod (by
    unfold InZeroResidueWindow
    simp only [BABYBEAR_MODULUS]
    constructor <;> omega)

/-- The packed book regrouped into its three base-4096 digits. -/
theorem bVal_digits : bVal a = bDigit a 0 + 4096 * bDigit a 1 + 4096 ^ 2 * bDigit a 2 := by
  have e0 : bitSum a BBIT 12 = bDigit a 0 := by
    unfold bDigit
    exact (bitSum_congr a _ (fun j hj => by simp only [BBIT]; try omega)).symm
  have e1 : bitSum a (fun j => BBIT (12 + j)) 12 = bDigit a 1 := by
    unfold bDigit
    exact bitSum_congr a _ (fun j hj => by simp only [BBIT]; try omega)
  have e2 : bitSum a (fun j => BBIT (12 + (12 + j))) 4 = bDigit a 2 := by
    unfold bDigit
    exact bitSum_congr a _ (fun j hj => by simp only [BBIT]; try omega)
  unfold bVal
  rw [show (28 : Nat) = 12 + 16 from rfl, bitSum_append,
      show (16 : Nat) = 12 + 4 from rfl, bitSum_append]
  simp only [e0, e1, e2]
  ring

/-- The shifted noise regrouped into its eight base-4096 digits. -/
theorem eShiftVal_digits :
    eShiftVal a =
      eDigit a 0 + 4096 * eDigit a 1 + 4096 ^ 2 * eDigit a 2 + 4096 ^ 3 * eDigit a 3 +
        4096 ^ 4 * eDigit a 4 + 4096 ^ 5 * eDigit a 5 + 4096 ^ 6 * eDigit a 6 +
        4096 ^ 7 * eDigit a 7 := by
  have e0 : bitSum a EBIT 12 = eDigit a 0 := by
    unfold eDigit
    exact (bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)).symm
  have e1 : bitSum a (fun j => EBIT (12 + j)) 12 = eDigit a 1 := by
    unfold eDigit
    exact bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)
  have e2 : bitSum a (fun j => EBIT (12 + (12 + j))) 12 = eDigit a 2 := by
    unfold eDigit
    exact bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)
  have e3 : bitSum a (fun j => EBIT (12 + (12 + (12 + j)))) 12 = eDigit a 3 := by
    unfold eDigit
    exact bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)
  have e4 : bitSum a (fun j => EBIT (12 + (12 + (12 + (12 + j))))) 12 = eDigit a 4 := by
    unfold eDigit
    exact bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)
  have e5 : bitSum a (fun j => EBIT (12 + (12 + (12 + (12 + (12 + j)))))) 12 = eDigit a 5 := by
    unfold eDigit
    exact bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)
  have e6 : bitSum a (fun j => EBIT (12 + (12 + (12 + (12 + (12 + (12 + j))))))) 12
      = eDigit a 6 := by
    unfold eDigit
    exact bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)
  have e7 : bitSum a (fun j => EBIT (12 + (12 + (12 + (12 + (12 + (12 + (12 + j)))))))) 4
      = eDigit a 7 := by
    unfold eDigit
    exact bitSum_congr a _ (fun j hj => by simp only [EBIT]; try omega)
  unfold eShiftVal
  rw [show (88 : Nat) = 12 + 76 from rfl, bitSum_append,
      show (76 : Nat) = 12 + 64 from rfl, bitSum_append,
      show (64 : Nat) = 12 + 52 from rfl, bitSum_append,
      show (52 : Nat) = 12 + 40 from rfl, bitSum_append,
      show (40 : Nat) = 12 + 28 from rfl, bitSum_append,
      show (28 : Nat) = 12 + 16 from rfl, bitSum_append,
      show (16 : Nat) = 12 + 4 from rfl, bitSum_append]
  simp only [e0, e1, e2, e3, e4, e5, e6, e7]
  ring

theorem phaseVal_expand :
    phaseVal a =
      a (PHASE_LIMB 0) + 4096 * a (PHASE_LIMB 1) + 4096 ^ 2 * a (PHASE_LIMB 2) +
        4096 ^ 3 * a (PHASE_LIMB 3) + 4096 ^ 4 * a (PHASE_LIMB 4) +
        4096 ^ 5 * a (PHASE_LIMB 5) + 4096 ^ 6 * a (PHASE_LIMB 6) +
        4096 ^ 7 * a (PHASE_LIMB 7) + 4096 ^ 8 * a (PHASE_LIMB 8) +
        4096 ^ 9 * a (PHASE_LIMB 9) := by
  unfold phaseVal
  norm_num [List.range_succ]
  ring

/-- **The telescoped limb identity**: an accepting trace forces the EXACT integer relation
`phase = Δ·b + e` — no mod-p wrap survives the window-lifted carry chain. -/
theorem limb_identity (hcanon : CanonicalAssignment a)
    (hphase : ∀ k, k < 10 → a (PHASE_LIMB k) < 4096)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    phaseVal a = DELTA * bVal a + noiseVal a := by
  have h0 := carry_gate_exact hcanon hphase hsat (k := 0) (by omega)
  have h1 := carry_gate_exact hcanon hphase hsat (k := 1) (by omega)
  have h2 := carry_gate_exact hcanon hphase hsat (k := 2) (by omega)
  have h3 := carry_gate_exact hcanon hphase hsat (k := 3) (by omega)
  have h4 := carry_gate_exact hcanon hphase hsat (k := 4) (by omega)
  have h5 := carry_gate_exact hcanon hphase hsat (k := 5) (by omega)
  have h6 := carry_gate_exact hcanon hphase hsat (k := 6) (by omega)
  have h7 := carry_gate_exact hcanon hphase hsat (k := 7) (by omega)
  have h8 := carry_gate_exact hcanon hphase hsat (k := 8) (by omega)
  have h9 := carry_gate_exact hcanon hphase hsat (k := 9) (by omega)
  have ht := top_carry_zero hcanon hsat
  simp only [convVal, eTermVal, tPrevVal, offK, deltaDigit] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  norm_num [List.range_succ] at h0 h1 h2 h3 h4 h5 h6 h7 h8 h9
  rw [phaseVal_expand, bVal_digits]
  unfold noiseVal
  rw [eShiftVal_digits]
  unfold DELTA
  linear_combination (-1 : ℤ) * h0 - 4096 * h1 - 4096 ^ 2 * h2 - 4096 ^ 3 * h3 -
    4096 ^ 4 * h4 - 4096 ^ 5 * h5 - 4096 ^ 6 * h6 - 4096 ^ 7 * h7 - 4096 ^ 8 * h8 -
    4096 ^ 9 * h9 - 4096 ^ 10 * ht

/-! ## 9. The noise margin (kernel-checked on the deployed 109-bit numbers). -/

/-- `SafeNoise` is downward closed in the budget. -/
theorem safeNoise_mono {P : Params} {B B' : ℤ} (hB : B ≤ B') (h : SafeNoise P B') :
    SafeNoise P B := by
  unfold SafeNoise at *
  have ht : (0 : ℤ) ≤ 2 * (P.t : ℤ) := by positivity
  have := mul_le_mul_of_nonneg_left hB ht
  linarith

/-- The emitted noise bound `2^87` is inside the deployed decrypt margin (kernel `decide`). -/
theorem safeNoise_deployed_pow87 : SafeNoise fheRs4096 (2 ^ 87) := by
  unfold SafeNoise
  decide

theorem noise_in_margin (he : ∀ i, i < 88 → a (EBIT i) = 0 ∨ a (EBIT i) = 1) :
    SafeNoise fheRs4096 |noiseVal a| := by
  have hbs := bitSum_bounds a EBIT 88 he
  have h88 : (2 : ℤ) ^ (88 : ℕ) = 2 * 2 ^ (87 : ℕ) := by ring
  have habs : |noiseVal a| ≤ 2 ^ 87 := by
    unfold noiseVal eShiftVal
    rw [abs_le]
    constructor <;> linarith [hbs.1, hbs.2]
  exact safeNoise_mono habs safeNoise_deployed_pow87

/-! ## 10. The decoded witness and the root binding. -/

/-- The private witness decoded off the trace: order `i`'s 7-bit code from bits `7i..7i+7`,
blinding from the (shared-index) `BLINDING` columns. -/
def decodedW (a : Assignment) : PrivateWitness where
  orders := fun i =>
    ⟨⟨(codeVal a i.val).toNat % 8, Nat.mod_lt _ (by decide)⟩,
     ⟨(codeVal a i.val).toNat / 8 % 16, Nat.mod_lt _ (by decide)⟩⟩
  blinding := fun lane => a (BLINDING lane.val)

theorem codeVal_bounds (hb : ∀ i, i < 28 → a (BBIT i) = 0 ∨ a (BBIT i) = 1)
    {i : Nat} (hi : i < 4) : 0 ≤ codeVal a i ∧ codeVal a i < 128 := by
  unfold codeVal
  have hbs := bitSum_bounds a (fun j => BBIT (7 * i + j)) 7 (fun j hj => hb _ (by omega))
  have h7 : (2 : ℤ) ^ (7 : ℕ) = 128 := by norm_num
  omega

theorem decoded_code (hb : ∀ i, i < 28 → a (BBIT i) = 0 ∨ a (BBIT i) = 1) (i : Fin 4) :
    orderCode ((decodedW a).orders i) = codeVal a i.val := by
  have hc := codeVal_bounds hb i.isLt
  simp only [decodedW, orderCode]
  push_cast
  omega

/-- The decoded book's 28-bit pack IS the bit-column value: the base-128 order digits and the
base-2 bits regroup to the same integer. -/
theorem packedBook_decoded_bits (hb : ∀ i, i < 28 → a (BBIT i) = 0 ∨ a (BBIT i) = 1) :
    packedBook (decodedW a) = bVal a := by
  have c0 : bitSum a BBIT 7 = codeVal a 0 := by
    unfold codeVal
    exact (bitSum_congr a _ (fun j hj => by simp only [BBIT]; try omega)).symm
  have c1 : bitSum a (fun j => BBIT (7 + j)) 7 = codeVal a 1 := by
    unfold codeVal
    exact bitSum_congr a _ (fun j hj => by simp only [BBIT]; try omega)
  have c2 : bitSum a (fun j => BBIT (7 + (7 + j))) 7 = codeVal a 2 := by
    unfold codeVal
    exact bitSum_congr a _ (fun j hj => by simp only [BBIT]; try omega)
  have c3 : bitSum a (fun j => BBIT (7 + (7 + (7 + j)))) 7 = codeVal a 3 := by
    unfold codeVal
    exact bitSum_congr a _ (fun j hj => by simp only [BBIT]; try omega)
  have hsplit : bVal a =
      codeVal a 0 + 128 * codeVal a 1 + 16384 * codeVal a 2 + 2097152 * codeVal a 3 := by
    unfold bVal
    rw [show (28 : Nat) = 7 + 21 from rfl, bitSum_append,
        show (21 : Nat) = 7 + 14 from rfl, bitSum_append,
        show (14 : Nat) = 7 + 7 from rfl, bitSum_append]
    simp only [c0, c1, c2, c3]
    ring
  have h0 := decoded_code hb 0
  have h1 := decoded_code hb 1
  have h2 := decoded_code hb 2
  have h3 := decoded_code hb 3
  rw [hsplit]
  simp only [packedBook, List.ofFn_succ, List.ofFn_zero, List.sum_cons, List.sum_nil]
  simp [h0, h1, h2, h3]
  ring

theorem gadget_root_input_decoded (hcanon : CanonicalAssignment a)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    rootInputExprs.map (·.eval a) = rootPreimage (a SESSION) (decodedW a) := by
  have hb := bbits hcanon hsat
  have hr := rule_column_exact' hcanon hsat
  have hp : a PACKED_BOOK = packedBook (decodedW a) := by
    rw [packed_book_bits_exact hcanon hsat, packedBook_decoded_bits hb]
  simp only [rootInputExprs, rootPreimage, decodedW, BLINDING, ROOT_DOMAIN_TAG,
    List.ofFn_succ, v, c, DIGEST_WIDTH, BLINDING_BASE]
  norm_num [List.range_succ, Function.comp_apply, EmittedExpr.eval]
  exact ⟨hr, by simpa [decodedW, BLINDING, BLINDING_BASE] using hp⟩

theorem gadget_root_semantic (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    ∀ lane : Fin 8,
      a (ROOT lane.val) = orderRoot (permHash8 permOut) (a SESSION) (decodedW a) lane := by
  have hwide := gadget_wide_root_sound permOut hChip hsat
  rw [gadget_root_input_decoded hcanon hsat] at hwide
  intro lane
  have h := congrArg (fun xs : List Int => xs.getD lane.val 0) hwide
  fin_cases lane <;>
    simpa [orderRoot, permHash8, rootDigestCols, DIGEST_WIDTH, ROOT, List.range_succ] using h

/-! ## 11. THE EMIT-SOUNDNESS KEYSTONES. -/

/-- The gadget-column view read off an accepting trace. -/
def gadgetColumnsOf (a : Assignment) : GadgetColumns where
  phase := phaseVal a
  noise := noiseVal a
  root := fun lane => a (ROOT lane.val)

/-- **KEYSTONE (emit soundness): `Satisfied2` of the EMITTED descriptor implies `GadgetAccepts`.**
Any satisfying canonical trace (with digit-canonical public phase limbs — the statement
well-formedness obligation) decodes to a witness `w` accepted by the PROVED gadget relation, at
the deployed parameters, with the column-read phase/noise/root. This is the analog of
`certFDescriptor_emit_sound` / `darkBazaarPrivateN4K4_emitted_air_sound` for the same-opening
apex: the emitted AIR enforces exactly the Lean relation. -/
theorem sameOpeningGadget_emit_sound (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hphase : ∀ k, k < 10 → a (PHASE_LIMB k) < 4096)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    GadgetAccepts fheRs4096 (permHash8 permOut) (a SESSION)
      (gadgetColumnsOf a) (decodedW a) := by
  have hb := bbits hcanon hsat
  have he := ebits hcanon hsat
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · show decGate fheRs4096 (gadgetColumnsOf a) (decodedW a) = 0
    unfold decGate gadgetColumnsOf
    have hid := limb_identity hcanon hphase hsat
    have hpb := packedBook_decoded_bits hb
    simp only
    rw [delta_deployed, hpb]
    linarith [hid]
  · exact noise_in_margin he
  · intro lane
    exact gadget_root_semantic permOut hcanon hChip hsat lane

/-- Chained through the PROVED `gadgetAccepts_sound`: the emitted descriptor discharges the
Tier-0 apex relation `SameOpening` itself. -/
theorem sameOpeningGadget_emit_discharges_apex (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hphase : ∀ k, k < 10 → a (PHASE_LIMB k) < 4096)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    SameOpening fheRs4096 (permHash8 permOut) (a SESSION)
      ⟨phaseVal a⟩ (fun lane => a (ROOT lane.val)) (decodedW a) :=
  gadgetAccepts_sound (sameOpeningGadget_emit_sound permOut hcanon hphase hChip hsat)

/-! ## 12. The statement-level form (what the verifier reads: the public inputs). -/

theorem session_pin_mem :
    VmConstraint2.base (.piBinding .first SESSION 0) ∈ gadgetPins := by
  simp [gadgetPins]

theorem root_pin_mem (lane : Fin 8) :
    VmConstraint2.base (.piBinding .first (ROOT lane.val) (2 + lane.val)) ∈ gadgetPins := by
  have h : VmConstraint2.base (.piBinding .first (ROOT lane.val) (2 + lane.val)) ∈
      (List.range 8).map (fun i => VmConstraint2.base (.piBinding .first (ROOT i) (2 + i))) :=
    List.mem_map.mpr ⟨lane.val, List.mem_range.mpr lane.isLt, rfl⟩
  simp only [gadgetPins, List.mem_append]
  tauto

theorem phase_pin_mem {k : Nat} (hk : k < 10) :
    VmConstraint2.base (.piBinding .first (PHASE_LIMB k) (10 + k)) ∈ gadgetPins := by
  have h : VmConstraint2.base (.piBinding .first (PHASE_LIMB k) (10 + k)) ∈
      (List.range 10).map
        (fun k => VmConstraint2.base (.piBinding .first (PHASE_LIMB k) (10 + k))) :=
    List.mem_map.mpr ⟨k, List.mem_range.mpr hk, rfl⟩
  simp only [gadgetPins, List.mem_append]
  tauto

theorem session_pin_exact (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    a SESSION = pis 0 :=
  eq_of_modEq_of_canonical (gadget_pin_sound hsat session_pin_mem)
    (hcanon SESSION) (hcanonPis 0)

theorem root_pin_exact (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf))
    (lane : Fin 8) : a (ROOT lane.val) = pis (2 + lane.val) :=
  eq_of_modEq_of_canonical (gadget_pin_sound hsat (root_pin_mem lane))
    (hcanon (ROOT lane.val)) (hcanonPis (2 + lane.val))

theorem phase_pin_exact (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf))
    {k : Nat} (hk : k < 10) : a (PHASE_LIMB k) = pis (10 + k) :=
  eq_of_modEq_of_canonical (gadget_pin_sound hsat (phase_pin_mem hk))
    (hcanon (PHASE_LIMB k)) (hcanonPis (10 + k))

/-- The statement's phase: the ten public limbs recombined. -/
def piPhase (pis : Assignment) : Int :=
  ((List.range 10).map fun k => (4096 : Int) ^ k * pis (10 + k)).sum

/-- **KEYSTONE (statement level): the emitted descriptor proves `SameOpening` at the
PUBLIC-INPUT-read objects** — session `pis 0`, phase `piPhase pis` (limbs `pis 10..19`), root
lanes `pis 2..9`. The two well-formedness obligations on the STATEMENT (canonical cells,
digit-canonical phase limbs) are exactly the verifier's own input checks. -/
theorem sameOpeningGadget_emitted_statement_sound (permOut : List Int → List Int)
    (hcanon : CanonicalAssignment a)
    (hcanonPis : CanonicalAssignment pis)
    (hphasePis : ∀ k, k < 10 → pis (10 + k) < 4096)
    (hChip : ChipTableSoundN permOut (tf TableId.poseidon2))
    (hsat : Satisfied2 hash sameOpeningGadgetDescriptor dbM0 dbF0 [] (constTrace a pis tf)) :
    SameOpening fheRs4096 (permHash8 permOut) (pis 0)
      ⟨piPhase pis⟩ (fun lane => pis (2 + lane.val)) (decodedW a) := by
  have hpl : ∀ k, k < 10 → a (PHASE_LIMB k) = pis (10 + k) :=
    fun k hk => phase_pin_exact hcanon hcanonPis hsat hk
  have hphase : ∀ k, k < 10 → a (PHASE_LIMB k) < 4096 :=
    fun k hk => (hpl k hk) ▸ hphasePis k hk
  have hmain := sameOpeningGadget_emit_discharges_apex permOut hcanon hphase hChip hsat
  have hsess := session_pin_exact hcanon hcanonPis hsat
  have hphaseEq : phaseVal a = piPhase pis := by
    unfold phaseVal piPhase
    apply congrArg List.sum
    apply List.map_congr_left
    intro k hk
    rw [hpl k (List.mem_range.mp hk)]
  have hrootEq : (fun lane : Fin 8 => a (ROOT lane.val)) =
      fun lane : Fin 8 => pis (2 + lane.val) := by
    funext lane
    exact root_pin_exact hcanon hcanonPis hsat lane
  rw [← hsess, ← hphaseEq, ← hrootEq]
  exact hmain

end Decode

#assert_all_clean [Market.EmitSameOpeningGadget.delta_deployed,
  Market.EmitSameOpeningGadget.delta_digits_recompose,
  Market.EmitSameOpeningGadget.safeNoise_deployed_pow87,
  Market.EmitSameOpeningGadget.limb_identity,
  Market.EmitSameOpeningGadget.carry_gate_exact,
  Market.EmitSameOpeningGadget.top_carry_zero,
  Market.EmitSameOpeningGadget.packed_book_bits_exact,
  Market.EmitSameOpeningGadget.packedBook_decoded_bits,
  Market.EmitSameOpeningGadget.noise_in_margin,
  Market.EmitSameOpeningGadget.gadget_wide_root_sound,
  Market.EmitSameOpeningGadget.gadget_root_semantic,
  Market.EmitSameOpeningGadget.sameOpeningGadget_emit_sound,
  Market.EmitSameOpeningGadget.sameOpeningGadget_emit_discharges_apex,
  Market.EmitSameOpeningGadget.sameOpeningGadget_emitted_statement_sound]

end Market.EmitSameOpeningGadget

/-! ## 13. The emitter: prints the byte-pinned descriptor JSON.

⚑ NAMESPACED, deliberately. This module is IMPORTED (`Market.lean:44` → `Dregg2.lean`), so a
root-level `def main` here collides with the one in `Dregg2/Apps/AgentOrchestration.lean:450` and
reds the ROOT aggregate ("environment already contains 'main'") even though the file elaborates
green in isolation — the per-file-green-hides-a-red-umbrella trap. The tree's `lake env lean --run`
runners (`metatheory/Emit*.lean`) live at the metatheory ROOT and are deliberately NOT imported,
which is why they may own the root `main`. To run this emitter, add a thin non-imported root runner
that calls `Market.EmitSameOpeningGadget.emitMain`. -/

def emitMain : IO Unit :=
  IO.println (Dregg2.Circuit.DescriptorIR2.emitVmJson2
    Market.EmitSameOpeningGadget.sameOpeningGadgetDescriptor)

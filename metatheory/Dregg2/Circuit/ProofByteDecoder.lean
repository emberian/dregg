/-
# Dregg2.Circuit.ProofByteDecoder — a REAL byte→field-view decoder for the deployed
public-input wire, discharging one leg of `CircuitSoundness.cfgView`'s opacity.

## What `cfgView` is (the opacity this file bites)

`CircuitSoundness.cfgView : BatchPublicInputs → BatchProof → (BatchProofData ℤ × WrapPublics ℤ)`
is declared `opaque` — the byte-deserialization of a proof's `(pi, π)` bytes into the
structured field-element views the verifier walks. Its ONLY specification was the
docstring KAT claim; nothing in Lean actually PARSED the deployed byte layout.

This module builds a concrete, executable byte→field decoder for the ONE piece of the
`cfgView` output that IS a plain base-field-element stream on the deployed wire: the
**public-input segment** — `WrapPublics.segment` (the IVC root's carried
`[genesis_root…, final_root…, num_turns, chain_digest…]`, `ivc_turn_chain.rs:1296`) and,
by the tooth-3 identity `exposedSegment = WrapPublics`, `BatchProofData.exposedSegment`.

## The deployed byte layout (the anchor — NOT invented)

The wire is the canonical fixed-width layout the deployed prover emits for a field
public-input vector, read directly from the deployed Rust:

  * `turn/src/binding_proof.rs:70` `public_inputs_babybear`: the PI vector is
    `Vec<u32>` mapped to field elements via `BabyBear::new(v)`;
  * `circuit/src/field.rs:114` `BabyBear::new(v) = Self(v % BABYBEAR_P)` — reduce mod
    `p = 2^31 − 2^27 + 1 = 2013265921` (the canonical, malleability-closing decode, the
    SAME reduction the serde `Deserialize` impl at `field.rs:82` performs);
  * `turn/src/binding_proof.rs:81-89` `hash_into`: the canonical byte encoding is a
    `u64`-LE length prefix (`(len as u64).to_le_bytes()`) followed by each element as a
    4-byte `u32`-LE limb (`v.to_le_bytes()`). This is the layout folded into `Turn::hash`
    (blake3) — load-bearing, not decorative.

So the decoder here is byte-EXACT with the deployed `hash_into` public-input sub-layout
and the `BabyBear::new` field reduction, and its golden vector is the deployed test
vector `vec![0xDEAD_BEEF, 0xCAFE_F00D]` (`binding_proof.rs:191`).

## What this discharges vs. the NAMED residual

DISCHARGES: `cfgView`'s opacity for the `(pi/π bytes) → WrapPublics.segment /
BatchProofData.exposedSegment` leg — a real `parse ∘ encode = id` roundtrip + a golden
vector pinned to the deployed serializer, replacing the docstring-only KAT claim on that
leg with executable, kernel-checked bytes.

The second half of this file now parses the exact leading `BatchProof` field of the
postcard-serialized
`p3_circuit_prover::BatchStarkProof<DreggRecursionConfig>`.  Serde emits struct fields
in declaration order and postcard emits unsigned integers and sequence lengths in
base-128 varint form.  The parser follows the deployed nested types all the way through
`BatchCommitments`, `BatchOpenedValues`, `FriProof`, every `QueryProof`/Merkle opening,
global lookup data, and `degree_bits`.  It therefore extracts the trace and quotient
caps, flattened OOD openings, FRI caps, final polynomial, query-PoW witness, and the
per-query `log_arity` schedule from real proof bytes.

RECONSTRUCTION STATUS: postcard does NOT serialize query indices, FRI betas,
fold-domain points, the OOD point ζ, AIR constraint evaluations, vanishing inverses,
or recomposed table openings.  Query indices/betas/ζ and domain points are now derived
inside `verifyAlgoUnifiedFaithfulExt`, never supplied by `cfgExtView`.  This decoder
also retains each FRI round's grouped quartic sibling values and Merkle path;
`reconstructExtQueriesFromWire` inserts the verifier-carried value at the derived query
position, so complete rows are no longer KAT-reconstructed.  What remains KAT is the
initial reduced PCS evaluation, AIR constraint/chunk-selector evaluation, and the
BabyBear generator/hash/arithmetic calibration.  The enclosing `BatchStarkProof` metadata
(`table_packing` through `stark_common`, including its optional preprocessed cap) is
also the unconsumed suffix, returned explicitly rather than silently accepted.  These
are the named `InnerProofReconstructionResidual` and `BatchStarkMetadataTailResidual`.
`readVarNat_encodeVarNat` proves the general postcard scalar/length roundtrip and
`readBatchProofCore_golden` pins the complete nested cursor.  A whole-core
encode/decode theorem is the named `CoreProjectionRoundtripResidual`: this decoder
intentionally consumes but does not retain authentication paths and lookup names, so
its `BatchProofData` projection is not injective and cannot honestly be re-encoded.

## Axiom hygiene

Every theorem is `#assert_axioms`-clean (omega + structural induction only). No `sorry`,
no `native_decide`, no new axiom. `#guard`s kernel-reduce over concrete deployed bytes;
`#eval`s exhibit non-vacuity. NEW file; imports read-only.
-/
import Dregg2.Circuit.CircuitSoundness

namespace Dregg2.Circuit.ProofByteDecoder

open Dregg2.Circuit

set_option autoImplicit false

/-! ## §1 — the BabyBear modulus (the deployed `BabyBear::new` reduction). -/

/-- The BabyBear prime `p = 2^31 − 2^27 + 1 = 2013265921` (`circuit/src/field.rs:12`,
`BABYBEAR_P`). `BabyBear::new(v) = v % p`. -/
def babybearP : Nat := 2013265921

/-- The deployed modulus really is `2^31 − 2^27 + 1`. -/
theorem babybearP_val : babybearP = 2 ^ 31 - 2 ^ 27 + 1 := by decide

/-! ## §2 — little-endian byte primitives (byte-exact with `to_le_bytes`).

Bytes are modelled as `Nat` (each intended `< 256`, as produced by `to_le_bytes`). The
readers reconstruct the integer with the identical positional weights; the writers are
`u32::to_le_bytes` / `u64::to_le_bytes` verbatim. -/

/-- `u32::to_le_bytes` — the four little-endian bytes of a `u32`. -/
def u32le (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256]

/-- Read one little-endian `u32` off the front of a byte list (the inverse of
`u32le`). -/
def readU32le : List Nat → Option (Nat × List Nat)
  | b0 :: b1 :: b2 :: b3 :: rest =>
      some (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3, rest)
  | _ => none

/-- `u64::to_le_bytes` — the eight little-endian bytes of a `u64` (the length prefix). -/
def u64le (n : Nat) : List Nat :=
  [n % 256, (n / 256) % 256, (n / 65536) % 256, (n / 16777216) % 256,
   (n / 4294967296) % 256, (n / 1099511627776) % 256,
   (n / 281474976710656) % 256, (n / 72057594037927936) % 256]

/-- Read one little-endian `u64` length prefix off the front of a byte list. -/
def readU64le : List Nat → Option (Nat × List Nat)
  | b0 :: b1 :: b2 :: b3 :: b4 :: b5 :: b6 :: b7 :: rest =>
      some (b0 + 256 * b1 + 65536 * b2 + 16777216 * b3 + 4294967296 * b4
              + 1099511627776 * b5 + 281474976710656 * b6 + 72057594037927936 * b7, rest)
  | _ => none

/-- `readU32le` inverts `u32le` on any in-range `u32` (leftover bytes preserved). -/
theorem readU32le_u32le (n : Nat) (h : n < 4294967296) (rest : List Nat) :
    readU32le (u32le n ++ rest) = some (n, rest) := by
  simp only [u32le, readU32le, List.cons_append, List.nil_append]
  have hn : n % 256 + 256 * ((n / 256) % 256) + 65536 * ((n / 65536) % 256)
      + 16777216 * ((n / 16777216) % 256) = n := by omega
  rw [hn]

/-- `readU64le` inverts `u64le` on any in-range `u64` (leftover bytes preserved). -/
theorem readU64le_u64le (n : Nat) (h : n < 18446744073709551616) (rest : List Nat) :
    readU64le (u64le n ++ rest) = some (n, rest) := by
  simp only [u64le, readU64le, List.cons_append, List.nil_append]
  have hn : n % 256 + 256 * ((n / 256) % 256) + 65536 * ((n / 65536) % 256)
      + 16777216 * ((n / 16777216) % 256) + 4294967296 * ((n / 4294967296) % 256)
      + 1099511627776 * ((n / 1099511627776) % 256)
      + 281474976710656 * ((n / 281474976710656) % 256)
      + 72057594037927936 * ((n / 72057594037927936) % 256) = n := by omega
  rw [hn]

/-! ## §3 — the field-element stream codec (the deployed `hash_into` PI layout).

A field stream is a `u64`-LE count followed by `count` `u32`-LE limbs; each limb decodes
to a canonical field element via `% babybearP` (the deployed `BabyBear::new`). -/

/-- Encode a list of field values as contiguous `u32`-LE limbs. -/
def encodeFieldElems : List Nat → List Nat
  | [] => []
  | x :: xs => u32le x ++ encodeFieldElems xs

/-- Decode `k` field limbs, reducing each mod `babybearP` (the deployed `BabyBear::new`
malleability-closing reduction). Returns the decoded elements and the unconsumed tail;
`none` if the bytes run out. -/
def decodeFieldElems : Nat → List Nat → Option (List Nat × List Nat)
  | 0, bs => some ([], bs)
  | (k + 1), bs =>
      match readU32le bs with
      | none => none
      | some (v, rest) =>
          match decodeFieldElems k rest with
          | none => none
          | some (vs, rest') => some ((v % babybearP) :: vs, rest')

/-- Encode a field stream: `u64`-LE length prefix + the limbs. -/
def encodeFieldStream (xs : List Nat) : List Nat :=
  u64le xs.length ++ encodeFieldElems xs

/-- Decode a field stream: read the length prefix, then that many limbs. Returns the
elements and the unconsumed tail. -/
def decodeFieldStream (bs : List Nat) : Option (List Nat × List Nat) :=
  match readU64le bs with
  | none => none
  | some (count, rest) => decodeFieldElems count rest

/-- Decode a field stream requiring EVERY byte consumed (a well-formed single-stream
proof view — trailing garbage is a REJECT, not silently ignored). -/
def decodeFieldStreamExact (bs : List Nat) : Option (List Nat) :=
  match decodeFieldStream bs with
  | some (vs, []) => some vs
  | _ => none

/-! ## §4 — the roundtrip laws (`parse ∘ encode = id`). -/

/-- **Limb roundtrip.** Decoding the encoding of `xs` (elements canonical, `< p`) yields
`xs` back with the trailing bytes intact. -/
theorem decodeFieldElems_encode :
    ∀ (xs : List Nat), (∀ x ∈ xs, x < babybearP) → ∀ (rest : List Nat),
      decodeFieldElems xs.length (encodeFieldElems xs ++ rest) = some (xs, rest)
  | [], _, rest => by simp [decodeFieldElems, encodeFieldElems]
  | a :: as, hx, rest => by
      have ha : a < babybearP := hx a (by simp)
      have has : ∀ x ∈ as, x < babybearP := fun x hxin => hx x (by simp [hxin])
      have ha32 : a < 4294967296 := by
        have hp : babybearP = 2013265921 := rfl
        omega
      simp only [encodeFieldElems, List.append_assoc, List.length_cons, decodeFieldElems,
        readU32le_u32le a ha32, decodeFieldElems_encode as has rest]
      rw [Nat.mod_eq_of_lt ha]

/-- **Stream roundtrip.** Decoding the encoding of a canonical field vector `xs` yields
`xs` back with the trailing bytes intact. -/
theorem decodeFieldStream_encode (xs : List Nat) (hx : ∀ x ∈ xs, x < babybearP)
    (rest : List Nat) (hlen : xs.length < 18446744073709551616) :
    decodeFieldStream (encodeFieldStream xs ++ rest) = some (xs, rest) := by
  simp only [decodeFieldStream, encodeFieldStream, List.append_assoc,
    readU64le_u64le xs.length hlen]
  exact decodeFieldElems_encode xs hx rest

/-- **Exact-stream roundtrip.** With no trailing bytes, the exact decoder recovers the
canonical field vector. -/
theorem decodeFieldStreamExact_encode (xs : List Nat) (hx : ∀ x ∈ xs, x < babybearP)
    (hlen : xs.length < 18446744073709551616) :
    decodeFieldStreamExact (encodeFieldStream xs) = some xs := by
  have h := decodeFieldStream_encode xs hx [] hlen
  simp only [List.append_nil] at h
  simp only [decodeFieldStreamExact, h]

/-! ## §5 — assembling the `cfgView` field views.

The decoded PI segment populates BOTH `WrapPublics.segment` (the carried claim) and, by
the deployed tooth-3 identity `exposedSegment = WrapPublics`
(`ivc_turn_chain.rs:133`), `BatchProofData.exposedSegment`. The remaining
`BatchProofData` fields are the NAMED residual (see the module header) — set empty here
because they are NOT on the public-input wire. -/

/-- Cast decoded canonical field limbs into the model field `ℤ`. -/
def toFieldZ (vs : List Nat) : List ℤ := vs.map (fun n => (n : ℤ))

/-- The `cfgView` output view built from a public-input byte stream: the decoded segment
lands in both `WrapPublics.segment` and `BatchProofData.exposedSegment` (tooth 3). -/
def decodeView (bs : List Nat) :
    Option (FriVerifier.BatchProofData ℤ × FriVerifier.WrapPublics ℤ) :=
  match decodeFieldStreamExact bs with
  | none => none
  | some vs =>
      let seg := toFieldZ vs
      some ({ traceCommit := [], friCommitments := [], finalPoly := [], queries := [],
              exposedSegment := seg }, { segment := seg })

/-- Encode a canonical field segment to its public-input wire bytes. -/
def encodeView (vs : List Nat) : List Nat := encodeFieldStream vs

/-- The `cfgView` output-input type bridge: consume the SAME `BatchProof.bytes` the
opaque `cfgView` takes (`List ℤ`), truncating each byte back to `Nat`. This pins the
decoder to the actual `cfgView` proof argument, not a bespoke input. -/
def decodeViewFromProof (π : CircuitSoundness.BatchProof) :
    Option (FriVerifier.BatchProofData ℤ × FriVerifier.WrapPublics ℤ) :=
  decodeView (π.bytes.map Int.toNat)

/-- **The view roundtrip.** Parsing the encoding of a canonical field segment `vs`
reconstructs the exact `WrapPublics.segment` and `BatchProofData.exposedSegment` — the
`parse ∘ encode = id` law on the fields `cfgView` produces. -/
theorem decodeView_encode (vs : List Nat) (hx : ∀ x ∈ vs, x < babybearP)
    (hlen : vs.length < 18446744073709551616) :
    decodeView (encodeView vs)
      = some ({ traceCommit := [], friCommitments := [], finalPoly := [], queries := [],
                exposedSegment := toFieldZ vs }, { segment := toFieldZ vs }) := by
  simp only [decodeView, encodeView, decodeFieldStreamExact_encode vs hx hlen]

/-- The two views agree on the exposed segment — the deployed tooth-3 identity
`exposedSegment = WrapPublics.segment`, now a THEOREM about the decoder output rather
than a docstring claim. -/
theorem decodeView_tooth3 (vs : List Nat) (hx : ∀ x ∈ vs, x < babybearP)
    (hlen : vs.length < 18446744073709551616) :
    ∃ bpd wp, decodeView (encodeView vs) = some (bpd, wp)
      ∧ bpd.exposedSegment = wp.segment := by
  refine ⟨_, _, decodeView_encode vs hx hlen, ?_⟩
  rfl

#assert_axioms readU32le_u32le
#assert_axioms readU64le_u64le
#assert_axioms decodeFieldElems_encode
#assert_axioms decodeFieldStream_encode
#assert_axioms decodeFieldStreamExact_encode
#assert_axioms decodeView_encode
#assert_axioms decodeView_tooth3

/-! ## §6 — golden vectors (kernel-checked, pinned to the deployed serializer).

The deployed test vector is `public_inputs = vec![0xDEAD_BEEF, 0xCAFE_F00D]`
(`turn/src/binding_proof.rs:191`). Its `hash_into` byte layout is:

  * count `2` as `u64`-LE: `[2,0,0,0,0,0,0,0]`;
  * `0xDEADBEEF` as `u32`-LE: `[239,190,173,222]` (0xEF,0xBE,0xAD,0xDE);
  * `0xCAFEF00D` as `u32`-LE: `[13,240,254,202]` (0x0D,0xF0,0xFE,0xCA).

Decoding reduces each mod `p` (the deployed `BabyBear::new`):
`0xDEADBEEF % p = 1722662638`, `0xCAFEF00D % p = 1392439308` — matching
`assert_eq!(bb[0], BabyBear::new(0xDEAD_BEEF))` in the deployed test. -/

-- GOLDEN: the deployed `[0xDEADBEEF, 0xCAFEF00D]` PI wire decodes to the two reduced
-- BabyBear field elements.
#guard decodeFieldStreamExact
    [2, 0, 0, 0, 0, 0, 0, 0, 239, 190, 173, 222, 13, 240, 254, 202]
  = some [1722662638, 1392439308]

-- The decoded value equals the deployed `BabyBear::new(0xDEADBEEF) = 0xDEADBEEF % p`.
#guard (3735928559 % babybearP) = 1722662638
#guard (3405705229 % babybearP) = 1392439308

-- GOLDEN (malleability leg): a wire limb carrying the RAW value `p` itself
-- (`0x78000001 = [1,0,0,120]`) decodes to `0` — exactly `BabyBear::new(p) = p % p = 0`,
-- the canonical reduction the deployed decode enforces.
#guard decodeFieldStreamExact [1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 120] = some [0]

-- The full `cfgView` field views on the deployed golden bytes: exposed segment and
-- carried publics both hold the two reduced elements, and they AGREE (tooth 3).
#guard
    (match decodeView
        [2, 0, 0, 0, 0, 0, 0, 0, 239, 190, 173, 222, 13, 240, 254, 202] with
     | some (bpd, wp) =>
         bpd.exposedSegment == wp.segment
           && wp.segment == ([1722662638, 1392439308] : List ℤ)
     | none => false)

-- Roundtrip on a canonical segment (including the max element `p − 1`).
#guard decodeFieldStreamExact (encodeFieldStream [1, 2, 2013265920])
  = some [1, 2, 2013265920]

-- Empty PI segment: length-prefix `0`, zero limbs — a valid empty view.
#guard decodeFieldStreamExact [0, 0, 0, 0, 0, 0, 0, 0] = some ([] : List Nat)

-- Truncated wire (claims 1 limb, supplies 3 bytes) is REJECTED, not silently accepted.
#guard decodeFieldStreamExact [1, 0, 0, 0, 0, 0, 0, 0, 5, 6, 7] = (none : Option (List Nat))

-- Trailing garbage after a complete stream is REJECTED (exact-consumption).
#guard decodeFieldStreamExact [0, 0, 0, 0, 0, 0, 0, 0, 99] = (none : Option (List Nat))

-- Non-vacuity: the assembled view is genuinely inhabited on the golden bytes.
#eval (decodeView
    [2, 0, 0, 0, 0, 0, 0, 0, 239, 190, 173, 222, 13, 240, 254, 202]).map
  (fun r => (r.1.exposedSegment, r.2.segment))

-- Non-vacuity: the roundtrip hypotheses are satisfiable (a concrete canonical vector).
#eval (decodeView (encodeView [7, 11, 2013265920])).map
  (fun r => (r.1.exposedSegment, r.2.segment))

/-! ## §7 — postcard primitives used by the inner `BatchStarkProof` blob.

Postcard 1.1.3 serializes every unsigned integer (including every `Vec` length and
64-bit-host `usize`) as a little-endian base-128 varint.  Serde tuples/structs add no
tags; `Option` is one byte (`0`/`1`); arrays have no length prefix.  These executable
primitives are therefore the deployed codec, not a bespoke sidecar format. -/

/-- Canonical postcard base-128 encoding of a natural number. -/
def encodeVarNat (n : Nat) : List Nat :=
  if n < 128 then [n]
  else (n % 128 + 128) :: encodeVarNat (n / 128)
termination_by n
decreasing_by omega

/-- Parse one postcard base-128 unsigned varint.  The recursive result is the
higher-order tail, so `(low + 128 * high)` exactly mirrors postcard's shift loop.
Bytes outside `u8` are rejected. -/
def readVarNat : List Nat → Option (Nat × List Nat)
  | [] => none
  | b :: bs =>
      if b < 128 then some (b, bs)
      else if b < 256 then
        match readVarNat bs with
        | some (hi, rest) => some (b - 128 + 128 * hi, rest)
        | none => none
      else none

/-- Postcard varint roundtrip, with an arbitrary following byte suffix preserved. -/
theorem readVarNat_encodeVarNat (n : Nat) (rest : List Nat) :
    readVarNat (encodeVarNat n ++ rest) = some (n, rest) := by
  revert rest
  induction n using Nat.strong_induction_on with
  | h n ih =>
      intro rest
      by_cases hn : n < 128
      · simp [encodeVarNat, hn, readVarNat]
      · have hn128 : 128 ≤ n := by omega
        have hdiv : n / 128 < n := Nat.div_lt_self (by omega) (by omega)
        have hmod : n % 128 < 128 := Nat.mod_lt _ (by omega)
        have hbyte : ¬n % 128 + 128 < 128 := by omega
        have hbyte256 : n % 128 + 128 < 256 := by omega
        rw [encodeVarNat]
        simp only [hn, ↓reduceIte, List.cons_append, readVarNat, hbyte, hbyte256,
          ih (n / 128) hdiv rest]
        congr 2
        have hdecomp := Nat.mod_add_div n 128
        omega

#assert_axioms readVarNat_encodeVarNat

/-- Postcard's width-bounded varint loop (`varint_max<T>()` iterations). -/
def readVarNatBounded : Nat → List Nat → Option (Nat × List Nat)
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, b :: bs =>
      if b < 128 then some (b, bs)
      else if b < 256 then
        match readVarNatBounded fuel bs with
        | some (hi, rest) => some (b - 128 + 128 * hi, rest)
        | none => none
      else none

/-- Deployed 64-bit-host `usize`/`u64` postcard decoder: at most ten bytes and the
decoded value must fit below `2^64`, matching `try_take_varint_u64`. -/
def readVarU64 : List Nat → Option (Nat × List Nat) := fun bs =>
  match readVarNatBounded 10 bs with
  | some (n, rest) => if n < 18446744073709551616 then some (n, rest) else none
  | none => none

/-- Deployed `u32` postcard decoder: at most five bytes and value below `2^32`. -/
def readVarU32 : List Nat → Option (Nat × List Nat) := fun bs =>
  match readVarNatBounded 5 bs with
  | some (n, rest) => if n < 4294967296 then some (n, rest) else none
  | none => none

/-- A small state-free parser type: parsed value plus the unconsumed byte suffix. -/
abbrev ByteParser (α : Type) := List Nat → Option (α × List Nat)

/-- Parse exactly `n` repetitions of `p`. -/
def readN {α : Type} (p : ByteParser α) : Nat → ByteParser (List α)
  | 0, bs => some ([], bs)
  | n + 1, bs =>
      match p bs with
      | none => none
      | some (x, rest) =>
          match readN p n rest with
          | none => none
          | some (xs, rest') => some (x :: xs, rest')

/-- Parse a postcard `Vec<T>`: varint length followed by that many `T`s. -/
def readVec {α : Type} (p : ByteParser α) : ByteParser (List α) := fun bs =>
  match readVarU64 bs with
  | none => none
  | some (n, rest) => readN p n rest

/-- Parse a raw serde `u8`. -/
def readByte : ByteParser Nat
  | [] => none
  | b :: bs => if b < 256 then some (b, bs) else none

/-- Parse a postcard `Option<T>` (`0 = None`, `1 = Some`; all other tags reject). -/
def readOption {α : Type} (p : ByteParser α) : ByteParser (Option α) := fun bs =>
  match readByte bs with
  | some (0, rest) => some (none, rest)
  | some (1, rest) =>
      match p rest with
      | some (x, rest') => some (some x, rest')
      | none => none
  | _ => none

/-! ### BabyBear's proof-wire representation.

The p3 `MontyField31` serde implementation writes its *Montgomery-form* `u32` as a
postcard varint and rejects values `≥ p` on decode.  `R = 2^32 mod p = 268435454` and
`R⁻¹ mod p = 943718400`; multiplying by the latter converts the wire word back to the
canonical field representative consumed by the Lean challenger. -/

def montyRInv : Nat := 943718400

def fromBabyBearMonty (raw : Nat) : Nat := (raw * montyRInv) % babybearP

/-- Parse one deployed p3 BabyBear proof element, rejecting non-canonical Montgomery
words exactly as `MontyField31::deserialize` does. -/
def readBabyBear : ByteParser Nat := fun bs =>
  match readVarU32 bs with
  | some (raw, rest) =>
      if raw < babybearP then some (fromBabyBearMonty raw, rest) else none
  | none => none

/-- Quartic `BinomialExtensionField<BabyBear, 4>`: serde array, exactly four base
coefficients and no length prefix. -/
def readExt4 : ByteParser (List Nat) := readN readBabyBear 4

/-- Poseidon2 Merkle digest: exactly eight BabyBear words. -/
def readDigest8 : ByteParser (List Nat) := readN readBabyBear 8

/-- A deployed cap is `MerkleCap { cap : Vec<[BabyBear; 8]>, phantom }`; the phantom
emits no bytes.  Flattening is the transcript's elementwise observation order. -/
def readCap : ByteParser (List Nat) := fun bs =>
  match readVec readDigest8 bs with
  | some (ds, rest) => some (ds.flatten, rest)
  | none => none

/-! ## §8 — exact parser for the serialized `p3_batch_stark::BatchProof` prefix.

The following helpers deliberately parse even the material not retained in
`BatchProofData` (Merkle authentication paths and lookup names).  That is what makes
the byte cursor land at the real end of `BatchProof`, instead of guessing offsets. -/

/-- Parse one `OpenedValuesWithLookups<Challenge>` and retain the extension values in
serde declaration order. -/
def readOpenedInstance : ByteParser (List Nat) := fun bs =>
  match readVec readExt4 bs with
  | none => none
  | some (traceLocal, bs) =>
    match readOption (readVec readExt4) bs with
    | none => none
    | some (traceNext, bs) =>
      match readOption (readVec readExt4) bs with
      | none => none
      | some (preLocal, bs) =>
        match readOption (readVec readExt4) bs with
        | none => none
        | some (preNext, bs) =>
          match readVec (readVec readExt4) bs with
          | none => none
          | some (quotient, bs) =>
            match readOption (readVec readExt4) bs with
            | none => none
            | some (random, bs) =>
              match readVec readExt4 bs with
              | none => none
              | some (permLocal, bs) =>
                match readVec readExt4 bs with
                | none => none
                | some (permNext, bs) =>
                  some (traceLocal.flatten ++ (traceNext.getD []).flatten
                    ++ (preLocal.getD []).flatten ++ (preNext.getD []).flatten
                    ++ quotient.flatten.flatten ++ (random.getD []).flatten
                    ++ permLocal.flatten ++ permNext.flatten, bs)

/-- Parse `BatchOpenedValues { instances : Vec<_> }`. -/
def readBatchOpenedValues : ByteParser (List Nat) := fun bs =>
  match readVec readOpenedInstance bs with
  | some (xs, rest) => some (xs.flatten, rest)
  | none => none

/-- Parse one input-MMCS `BatchOpening`: opened base rows followed by its Merkle path.
The retained list is the literal base-field opening stream; the authentication path is
consumed but not confused with opened evaluations. -/
def readBatchOpening : ByteParser (List Nat) := fun bs =>
  match readVec (readVec readBabyBear) bs with
  | none => none
  | some (opened, bs) =>
    match readVec readDigest8 bs with
    | none => none
    | some (_, bs) => some (opened.flatten, bs)

/-- Literal wire data for one FRI commit-phase step.  Unlike the old projection, this
retains extension siblings as separate quartic values and the complete Merkle path,
so the apex row can be reconstructed rather than supplied by `cfgExtView`. -/
structure DecodedCommitStepWire where
  logArity : Nat
  siblingValues : List (List Nat)
  openingProof : List (List Nat)
  deriving Repr, DecidableEq

/-- Parse one FRI commit-phase step and retain its `log_arity`, sibling extension
values, and extension-MMCS authentication path. -/
def readCommitPhaseStep : ByteParser DecodedCommitStepWire := fun bs =>
  match readByte bs with
  | none => none
  | some (logArity, bs) =>
    match readVec readExt4 bs with
    | none => none
    | some (siblings, bs) =>
      match readVec readDigest8 bs with
      | none => none
      | some (openingProof, bs) =>
          some ({ logArity, siblingValues := siblings, openingProof }, bs)

/-- The serialized portion of one FRI query that is available without replaying the
transcript/domain: input opened rows, per-round arities, and sibling values. -/
structure DecodedQueryWire where
  inputOpened : List Nat
  logArities : List Nat
  siblingValues : List Nat
  /-- Exact per-round grouping retained for verifier-side row reconstruction. -/
  commitSteps : List DecodedCommitStepWire := []
  deriving Repr, DecidableEq

def readFriQuery : ByteParser DecodedQueryWire := fun bs =>
  match readVec readBatchOpening bs with
  | none => none
  | some (inputs, bs) =>
    match readVec readCommitPhaseStep bs with
    | none => none
    | some (steps, bs) =>
      some ({ inputOpened := inputs.flatten,
              logArities := steps.map (·.logArity),
              siblingValues := (steps.map fun s => s.siblingValues.flatten).flatten,
              commitSteps := steps }, bs)

/-- Literal wire projection of the nested `FriProof`. -/
structure DecodedFriWire where
  commitments : List (List Nat)
  commitPowWitnesses : List Nat
  queries : List DecodedQueryWire
  finalPoly : List Nat
  queryPowWitness : Nat
  deriving Repr, DecidableEq

def readFriProof : ByteParser DecodedFriWire := fun bs =>
  match readVec readCap bs with
  | none => none
  | some (commitments, bs) =>
    match readVec readBabyBear bs with
    | none => none
    | some (commitPowWitnesses, bs) =>
      match readVec readFriQuery bs with
      | none => none
      | some (queries, bs) =>
        match readVec readExt4 bs with
        | none => none
        | some (finalPoly, bs) =>
          match readBabyBear bs with
          | none => none
          | some (queryPowWitness, bs) =>
            some ({ commitments, commitPowWitnesses, queries,
                    finalPoly := finalPoly.flatten, queryPowWitness }, bs)

/-- Consume one UTF-8/string byte payload.  UTF-8 validity is not needed to find the
next postcard field; every byte is nevertheless checked to be a `u8`. -/
def readRawString : ByteParser Unit := fun bs =>
  match readVec readByte bs with
  | some (_, rest) => some ((), rest)
  | none => none

/-- Consume one `LookupData<Challenge>` (`name`, `aux_column`, `cumulative_sum`). -/
def readLookupData : ByteParser Unit := fun bs =>
  match readRawString bs with
  | none => none
  | some (_, bs) =>
    match readVarU64 bs with
    | none => none
    | some (_, bs) =>
      match readExt4 bs with
      | none => none
      | some (_, bs) => some ((), bs)

/-- The exact data available in the leading serialized `BatchProof` field. -/
structure DecodedBatchProofCore where
  traceCommit : List Nat
  permutationCommit : Option (List Nat)
  quotientCommit : List Nat
  randomCommit : Option (List Nat)
  openedEvaluations : List Nat
  fri : DecodedFriWire
  degreeBits : List Nat
  deriving Repr, DecidableEq

/-- Parse the complete leading `p3_batch_stark::BatchProof` field of a deployed
`BatchStarkProof`.  The returned suffix begins exactly at `table_packing`. -/
def readBatchProofCore : ByteParser DecodedBatchProofCore := fun bs =>
  match readCap bs with
  | none => none
  | some (traceCommit, bs) =>
    match readOption readCap bs with
    | none => none
    | some (permutationCommit, bs) =>
      match readCap bs with
      | none => none
      | some (quotientCommit, bs) =>
        match readOption readCap bs with
        | none => none
        | some (randomCommit, bs) =>
          match readBatchOpenedValues bs with
          | none => none
          | some (openedEvaluations, bs) =>
            match readFriProof bs with
            | none => none
            | some (fri, bs) =>
              match readVec (readVec readLookupData) bs with
              | none => none
              | some (_, bs) =>
                match readVec readVarU64 bs with
                | none => none
                | some (degreeBits, bs) =>
                  some ({ traceCommit, permutationCommit, quotientCommit, randomCommit,
                          openedEvaluations, fri, degreeBits }, bs)

/-- Require every serialized query to carry the same deployed FRI arity schedule.
The empty-query case has the empty schedule; a mismatch rejects instead of selecting a
prover-favourable query. -/
def commonLogArities : List DecodedQueryWire → Option (List Nat)
  | [] => some []
  | q :: qs => if qs.all (fun r => decide (r.logArities = q.logArities))
      then some q.logArities else none

/-- Canonical field cast for the parsed proof projection. -/
private def innerToFieldZ (xs : List Nat) : List ℤ := xs.map (fun n => (n : ℤ))

/-- Map the literal serialized core fields into `BatchProofData`.  The result includes
the unconsumed `BatchStarkProof` metadata tail.  Fields which do not exist on the wire
are intentionally empty (the named reconstruction residual in the module header). -/
def decodeInnerProofCorePrefix (bs : List Nat) :
    Option (FriVerifier.BatchProofData ℤ × List Nat) :=
  match readBatchProofCore bs with
  | none => none
  | some (core, metadataTail) =>
    match commonLogArities core.fri.queries with
    | none => none
    | some logArities =>
      some ({ traceCommit := innerToFieldZ core.traceCommit,
              friCommitments := core.fri.commitments.map innerToFieldZ,
              finalPoly := innerToFieldZ core.fri.finalPoly,
              queries := [], exposedSegment := [],
              powWitness := [(core.fri.queryPowWitness : ℤ)],
              quotientCommit := innerToFieldZ core.quotientCommit,
              openedEvaluations := innerToFieldZ core.openedEvaluations,
              friLogArities := innerToFieldZ logArities }, metadataTail)

/-- `proof_bytes` has the same signed-list carrier as the apex's abstract proof. -/
def decodeInnerProofCoreFromProof (π : CircuitSoundness.BatchProof) :
    Option (FriVerifier.BatchProofData ℤ × List Nat) :=
  decodeInnerProofCorePrefix (π.bytes.map Int.toNat)

/-! ## §8.1 — reconstruct the extension query view from literal wire data.

The serialized query omits exactly one evaluation per round: the value already
carried by the verifier.  We retain the other `2^log_arity-1` values and the Merkle
path here.  `friChainGoExtAny` inserts the carried value at `qidx % arity`, hashes the
resulting row, verifies the path, folds it with the transcript beta, and repeats. -/

open Dregg2.Circuit.ExtFieldChallenge

/-- Convert one decoded commit step into the compact apex layer.  No beta, domain
point, full row, or leaf is fabricated; all four are verifier-derived/reconstructed. -/
def decodedStepToExtLayer (s : DecodedCommitStepWire) : ExtLayerOpening ℤ :=
  { beta := ⟨[]⟩, x := ⟨[]⟩, e0 := ⟨[]⟩, e1 := ⟨[]⟩,
    siblingValues := s.siblingValues.map (fun e => ⟨innerToFieldZ e⟩),
    leaf := [], siblings := s.openingProof.map innerToFieldZ }

/-- One query needs only its transcript-derived index and the reduced PCS evaluation
that enters FRI.  Every commit-phase row/path comes literally from postcard bytes. -/
def decodedQueryToExt (index : Nat) (initialEval : ExtElem ℤ)
    (q : DecodedQueryWire) : ExtQueryOpening ℤ :=
  { index, initialEval, layers := q.commitSteps.map decodedStepToExtLayer }

/-- Exact three-way zipper; count mismatch rejects rather than truncating queries. -/
def reconstructExtQueriesFromWire :
    List DecodedQueryWire → List Nat → List (ExtElem ℤ) → Option (List (ExtQueryOpening ℤ))
  | [], [], [] => some []
  | q :: qs, i :: is, e :: es =>
      match reconstructExtQueriesFromWire qs is es with
      | some rest => some (decodedQueryToExt i e q :: rest)
      | none => none
  | _, _, _ => none

/-- Assemble the remaining apex extension view.  `qidx` is passed directly from
`deriveTranscript`; `initialEvals` and AIR openings are the precisely named KAT tail. -/
def reconstructExtVerifierView (core : DecodedBatchProofCore) (qidx : List Nat)
    (initialEvals : List (ExtElem ℤ)) (airs : List (ExtSingleAirOpening ℤ)) :
    Option (ExtVerifierView ℤ) :=
  match reconstructExtQueriesFromWire core.fri.queries qidx initialEvals with
  | some queries => some { queries, singleAirOpenings := airs }
  | none => none

/-! ## §9 — inner-proof roundtrip/golden pins.

The general varint roundtrip above covers every unsigned scalar and length in the
schema.  This compact complete `BatchProof` core fixture exercises every nesting level
needed to reach the metadata boundary: three caps, one FRI query/commit step, final
quartic polynomial, PoW witness, lookup outer vector, and degree bits. -/

private def zeroCapWire : List Nat := [1, 0, 0, 0, 0, 0, 0, 0, 0]

private def innerCoreGolden : List Nat :=
  -- BatchCommitments: main cap, no permutation, quotient cap, no random.
  zeroCapWire ++ [0] ++ zeroCapWire ++ [0]
  -- opened_values.instances = [].
  ++ [0]
  -- FriProof: one commit cap; no commit-PoW witnesses; one query.
  ++ [1] ++ zeroCapWire ++ [0] ++ [1]
  -- query.input_proof = []; one commit step: arity 1, no siblings, empty Merkle path.
  ++ [0] ++ [1, 1, 0, 0]
  -- final_poly = one quartic zero; query PoW witness = zero.
  ++ [1, 0, 0, 0, 0] ++ [0]
  -- global_lookup_data = []; degree_bits = [3].
  ++ [0] ++ [1, 3]
  -- First byte of the enclosing BatchStarkProof.table_packing metadata tail.
  ++ [99]

private def goldenQueryWire : DecodedQueryWire :=
  { inputOpened := [], logArities := [1], siblingValues := [],
    commitSteps := [{ logArity := 1, siblingValues := [], openingProof := [] }] }

private def goldenFriView : DecodedFriWire :=
  { commitments := [List.replicate 8 0]
    commitPowWitnesses := []
    queries := [goldenQueryWire]
    finalPoly := [0, 0, 0, 0]
    queryPowWitness := 0 }

private def goldenCoreView : DecodedBatchProofCore :=
  { traceCommit := List.replicate 8 0, permutationCommit := none,
    quotientCommit := List.replicate 8 0, randomCommit := none,
    openedEvaluations := [],
    fri := goldenFriView,
    degreeBits := [3] }

private def reconstructionEval : ExtElem ℤ := ⟨[11, 12, 13, 14]⟩

private def goldenExtLayer : ExtLayerOpening ℤ :=
  { beta := ⟨[]⟩, x := ⟨[]⟩, e0 := ⟨[]⟩, e1 := ⟨[]⟩,
    siblingValues := [], leaf := [], siblings := [] }

private def goldenExtView : ExtVerifierView ℤ :=
  { queries := [{ index := 7, initialEval := reconstructionEval,
                  layers := [goldenExtLayer] }],
    singleAirOpenings := [] }

/-- The literal query grouping reaches the apex view with the transcript-derived
index and supplied PCS reduction, while beta/x/leaf remain absent as intended. -/
theorem reconstructExtVerifierView_golden :
    reconstructExtVerifierView goldenCoreView [7] [reconstructionEval] [] =
      some goldenExtView := by decide

#assert_axioms reconstructExtVerifierView_golden

private def richStep : DecodedCommitStepWire :=
  { logArity := 2, siblingValues := [[1,2,3,4], [5,6,7,8], [9,10,11,12]],
    openingProof := [[21,22,23,24,25,26,27,28]] }

-- Grouping and Merkle authentication material survive decoding into the verifier view.
#guard (decodedStepToExtLayer richStep).siblingValues.map (·.lanes) =
  richStep.siblingValues.map innerToFieldZ
#guard (decodedStepToExtLayer richStep).siblings = richStep.openingProof.map innerToFieldZ

/-- Golden parse theorem: the complete core lands exactly at the metadata suffix. -/
theorem readBatchProofCore_golden :
    readBatchProofCore innerCoreGolden = some (goldenCoreView, [99]) := by decide

#assert_axioms readBatchProofCore_golden

#guard readVarNat (encodeVarNat 18446744073709551615 ++ [7]) =
  some (18446744073709551615, [7])

#guard readVarU64 (encodeVarNat 18446744073709551615 ++ [7]) =
  some (18446744073709551615, [7])

-- The 65-bit value and an eleven-byte continuation are postcard-bad varints.
#guard readVarU64 (encodeVarNat 18446744073709551616) = none
#guard readVarU64 [128, 128, 128, 128, 128, 128, 128, 128, 128, 128, 0] = none

#guard readBatchProofCore innerCoreGolden = some (goldenCoreView, [99])

/-- Prefix copied from the committed deployed artifact
`ugc-dregg/tests/fixtures/whole_history_proof.bin`: after the version-3 envelope,
64-byte VK fingerprint, and root-blob length, these are the first 80 root-proof bytes.
This is a real `BatchStarkProof<DreggRecursionConfig>` cap, not the compact schema
fixture above. -/
private def deployedRootPrefix : List Nat :=
  [1, 161, 245, 242, 179, 6, 158, 228, 178, 21, 224, 146, 128, 172, 2,
   224, 241, 253, 179, 5, 227, 157, 253, 160, 1, 193, 164, 215, 162, 6,
   231, 161, 222, 152, 2, 213, 199, 216, 237, 4, 1, 1, 175, 246, 213,
   177, 1, 136, 167, 198, 142, 1, 147, 209, 158, 251, 1, 191, 164, 131,
   232, 4, 153, 140, 222, 23, 180, 166, 178, 46, 245, 172, 252, 184, 4,
   139, 218, 191, 197, 5]

-- REAL golden: postcard/Montgomery-decode the committed proof's trace cap.
#guard
  (readCap deployedRootPrefix).map Prod.fst = some
    [137726085, 104795266, 1718352796, 1333018456,
     659641094, 154649970, 290255892, 1087545141]

-- The projection contains every literal transcript/FRI wire field and preserves the
-- metadata boundary.  It does not fabricate query indices, ζ, or AIR-derived tables.
#guard
  (match decodeInnerProofCorePrefix innerCoreGolden with
   | some (p, tail) =>
       p.traceCommit.length = 8
         && p.quotientCommit.length = 8
         && p.friCommitments.length = 1
         && p.finalPoly = ([0, 0, 0, 0] : List ℤ)
         && p.powWitness = ([0] : List ℤ)
         && p.friLogArities = ([1] : List ℤ)
         && p.queries = [] && p.oodPoint = [] && p.tableOpenings = []
         && tail = [99]
   | none => false)

-- Malformed/noncanonical Montgomery field words are rejected by the real inner codec.
#guard readBabyBear (encodeVarNat babybearP) = (none : Option (Nat × List Nat))

-- A mismatched per-query arity schedule is rejected, not silently normalized.
#guard commonLogArities
  [{ inputOpened := [], logArities := [1], siblingValues := [] },
   { inputOpened := [], logArities := [2], siblingValues := [] }] = none

end Dregg2.Circuit.ProofByteDecoder

/-
# The payload-length ladder (RFC 6455 §5.2)

A WebSocket frame carries its payload length in a three-rung ladder: the 7-bit
field in byte 1 encodes the length inline when it is `≤ 125`; the marker `126`
introduces a 16-bit big-endian extended length; the marker `127` introduces a
64-bit big-endian extended length. RFC 6455 §5.2 requires the **minimal**
number of bytes: a length that fits a shorter rung MUST use it.

This file models the ladder and proves it canonical:

* `decodeLenField_encodeLenField` — **decode inverts encode**: the length read
  back from an encoded field is the original length (for any `n < 2⁶⁴`).
* `encodeLenField_canonical` — encode always lands on the minimal rung
  (`LenFieldCanonical`), which is exactly the §5.2 shortest-encoding rule.
* `canonical_marker_forced` — the rung of any canonical field is exactly the
  one the encoder picks for the length it denotes: the shortest rung that fits a
  length is forced by that length, so a length has no second canonical rung.

Big-endian is modeled in Horner form (`fromBEAux`) so the round-trips reduce to
`omega` over concrete byte digits, with no symbolic powers.
-/
import Ws.Basic

namespace Ws

/-! ## Big-endian byte helpers (Horner form) -/

/-- Big-endian decode, Horner form: fold bytes most-significant first into an
accumulator, `acc ↦ acc·256 + byte`. -/
def fromBEAux : Nat → Bytes → Nat
  | acc, [] => acc
  | acc, b :: bs => fromBEAux (acc * 256 + b.toNat) bs

/-- Big-endian decode of a byte list. -/
def fromBE (l : Bytes) : Nat := fromBEAux 0 l

/-- The 16-bit big-endian encoding of `n` (its low two bytes, most significant
first). -/
def toBE16 (n : Nat) : Bytes := [UInt8.ofNat (n / 256), UInt8.ofNat n]

/-- The 64-bit big-endian encoding of `n` (its low eight bytes, most
significant first). The divisors are the literal powers `256^7 … 256^1`. -/
def toBE64 (n : Nat) : Bytes :=
  [ UInt8.ofNat (n / 72057594037927936), UInt8.ofNat (n / 281474976710656),
    UInt8.ofNat (n / 1099511627776),     UInt8.ofNat (n / 4294967296),
    UInt8.ofNat (n / 16777216),          UInt8.ofNat (n / 65536),
    UInt8.ofNat (n / 256),               UInt8.ofNat n ]

theorem toBE16_length (n : Nat) : (toBE16 n).length = 2 := rfl
theorem toBE64_length (n : Nat) : (toBE64 n).length = 8 := rfl

/-- `UInt8.ofNat` reduces modulo 256. -/
theorem toNat_ofNat (n : Nat) : (UInt8.ofNat n).toNat = n % 256 := by
  simp [UInt8.toNat_ofNat]

/-- **16-bit round trip**: a length below `2¹⁶` survives big-endian encode then
decode. -/
theorem fromBE_toBE16 (n : Nat) (h : n < 2 ^ 16) : fromBE (toBE16 n) = n := by
  simp only [toBE16, fromBE, fromBEAux, toNat_ofNat]
  omega

/-- **64-bit round trip**: a length below `2⁶⁴` survives big-endian encode then
decode. -/
theorem fromBE_toBE64 (n : Nat) (h : n < 2 ^ 64) : fromBE (toBE64 n) = n := by
  simp only [toBE64, fromBE, fromBEAux, toNat_ofNat]
  omega

/-! ## The length field -/

/-- The marker (the 7-bit field value in byte 1) the encoder picks for a
payload of length `n`: inline when `≤ 125`, else `126` (16-bit rung) when it
fits `2¹⁶`, else `127` (64-bit rung). -/
def lenMarker (n : Nat) : Nat :=
  if n < 126 then n else if n < 2 ^ 16 then 126 else 127

/-- The extended-length bytes the encoder appends for a payload of length `n`:
none inline, two on the 16-bit rung, eight on the 64-bit rung. -/
def lenExt (n : Nat) : Bytes :=
  if n < 126 then [] else if n < 2 ^ 16 then toBE16 n else toBE64 n

/-- The full length field: `(marker, extended bytes)`. -/
def encodeLenField (n : Nat) : Nat × Bytes := (lenMarker n, lenExt n)

/-- Decode a length field: the payload length denoted by a `(marker, extended
bytes)` pair. Inline for a marker `≤ 125`, otherwise the big-endian extended
value. -/
def decodeLenField (marker : Nat) (ext : Bytes) : Nat :=
  if marker ≤ 125 then marker else fromBE ext

/-- A length field is **canonical** (RFC 6455 §5.2 minimal encoding) when the
marker sits on the shortest rung that fits the payload length it denotes: an
inline marker carries no extended bytes; the 16-bit rung is used only for
lengths that do not fit inline; the 64-bit rung only for lengths that do not
fit sixteen bits. The lower bounds `126 ≤ …` and `2¹⁶ ≤ …` are exactly the
§5.2 "minimal number of bytes" rule. -/
def LenFieldCanonical (marker : Nat) (ext : Bytes) : Prop :=
  (marker ≤ 125 ∧ ext = []) ∨
  (marker = 126 ∧ ext.length = 2 ∧ 126 ≤ fromBE ext ∧ fromBE ext < 2 ^ 16) ∨
  (marker = 127 ∧ ext.length = 8 ∧ 2 ^ 16 ≤ fromBE ext ∧ fromBE ext < 2 ^ 64)

/-! ## Canonicity -/

/-- **Decode inverts encode**: the length recovered from an encoded field is the
original length, for every `n < 2⁶⁴`. -/
theorem decodeLenField_encodeLenField (n : Nat) (h : n < 2 ^ 64) :
    decodeLenField (lenMarker n) (lenExt n) = n := by
  by_cases h126 : n < 126
  · have hm : lenMarker n = n := by simp [lenMarker, h126]
    have he : lenExt n = [] := by simp [lenExt, h126]
    rw [hm, he, decodeLenField, if_pos (show n ≤ 125 by omega)]
  · by_cases h16 : n < 2 ^ 16
    · have hm : lenMarker n = 126 := by simp [lenMarker, h126, h16]
      have he : lenExt n = toBE16 n := by simp [lenExt, h126, h16]
      rw [hm, he, decodeLenField, if_neg (by decide)]
      exact fromBE_toBE16 n h16
    · have hm : lenMarker n = 127 := by simp [lenMarker, h126, h16]
      have he : lenExt n = toBE64 n := by simp [lenExt, h126, h16]
      rw [hm, he, decodeLenField, if_neg (by decide)]
      exact fromBE_toBE64 n h

/-- **Encode lands on the minimal rung**: `encodeLenField` always produces a
canonical field — this is precisely the RFC 6455 §5.2 shortest-encoding rule
(a length always uses the shortest rung that fits it). -/
theorem encodeLenField_canonical (n : Nat) (h : n < 2 ^ 64) :
    LenFieldCanonical (lenMarker n) (lenExt n) := by
  unfold LenFieldCanonical lenMarker lenExt
  by_cases h126 : n < 126
  · left
    rw [if_pos h126, if_pos h126]
    exact ⟨by omega, rfl⟩
  · by_cases h16 : n < 2 ^ 16
    · right; left
      rw [if_neg h126, if_pos h16, if_neg h126, if_pos h16]
      refine ⟨rfl, toBE16_length n, ?_, ?_⟩
      · rw [fromBE_toBE16 n h16]; omega
      · rw [fromBE_toBE16 n h16]; exact h16
    · right; right
      rw [if_neg h126, if_neg h16, if_neg h126, if_neg h16]
      refine ⟨rfl, toBE64_length n, ?_, ?_⟩
      · rw [fromBE_toBE64 n h]; omega
      · rw [fromBE_toBE64 n h]; exact h

/-- **The rung is forced by the length**: the marker of any canonical field is
exactly the marker the encoder picks for the length it denotes. So a length
sits on a single canonical rung — there is no second minimal encoding, and the
shortest rung that fits is forced. Together with `decodeLenField_encodeLenField`
and `encodeLenField_canonical`, this is the canonicity of the ladder. -/
theorem canonical_marker_forced (marker : Nat) (ext : Bytes)
    (h : LenFieldCanonical marker ext) :
    marker = lenMarker (decodeLenField marker ext) := by
  rcases h with ⟨hm, _⟩ | ⟨hm, _, hlo, hhi⟩ | ⟨hm, _, hlo, hhi⟩
  · have hd : decodeLenField marker ext = marker := by simp [decodeLenField, hm]
    rw [hd]
    simp [lenMarker, show marker < 126 by omega]
  · subst hm
    have hd : decodeLenField 126 ext = fromBE ext := by simp [decodeLenField]
    rw [hd]
    simp only [lenMarker, if_neg (show ¬ fromBE ext < 126 by omega), if_pos hhi]
  · subst hm
    have hd : decodeLenField 127 ext = fromBE ext := by simp [decodeLenField]
    rw [hd]
    simp only [lenMarker, if_neg (show ¬ fromBE ext < 126 by omega),
      if_neg (show ¬ fromBE ext < 2 ^ 16 by omega)]

end Ws

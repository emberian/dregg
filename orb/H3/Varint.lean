import H3.Basic

/-!
# QUIC variable-length integers (RFC 9000 §16)

The two most significant bits of the first byte give the total length of the
integer; the remaining bits are the big-endian value:

| 2-bit prefix | length | usable bits | maximum value          |
|--------------|--------|-------------|------------------------|
| `00`         | 1      | 6           | `2^6  - 1`             |
| `01`         | 2      | 14          | `2^14 - 1`             |
| `10`         | 4      | 30          | `2^30 - 1`             |
| `11`         | 8      | 62          | `2^62 - 1` (`maxVarint`) |

Headline theorems:

* `decVarint_encVarint` — **round-trip**: decoding an encoding (under any
  byte suffix) recovers the value and consumes exactly the encoding.
* `encVarint_length` / `encVarint_isSome_iff` — **length bounds**: the
  encoder emits exactly `encLen v ∈ {1,2,4,8}` bytes and succeeds exactly on
  `v ≤ maxVarint`; dually `decVarint_consumed` bounds what the decoder eats.
* `encVarint_canonical` — **canonical form**: the encoder's output is
  minimal-length among all encodings the decoder accepts for that value.
-/

namespace H3
namespace Varint

/-- Maximum value representable in a QUIC varint: `2^62 - 1`. -/
def maxVarint : Nat := 2 ^ 62 - 1

/-- Truncate a natural number to one byte. -/
def byte (n : Nat) : UInt8 := UInt8.ofNat n

theorem byte_toNat (n : Nat) : (byte n).toNat = n % 256 := rfl

theorem u8_toNat_lt (x : UInt8) : x.toNat < 256 := x.toBitVec.isLt

/-- Encode a value as a QUIC varint (shortest form). `none` iff
`maxVarint < v`. `byte` truncates, so each digit is written mod 256; the
guards keep every leading digit in range. -/
def encVarint (v : Nat) : Option Bytes :=
  if v < 2 ^ 6 then
    some [byte v]
  else if v < 2 ^ 14 then
    some [byte (0x40 + v / 2 ^ 8), byte v]
  else if v < 2 ^ 30 then
    some [byte (0x80 + v / 2 ^ 24), byte (v / 2 ^ 16), byte (v / 2 ^ 8), byte v]
  else if v ≤ maxVarint then
    some [byte (0xC0 + v / 2 ^ 56), byte (v / 2 ^ 48), byte (v / 2 ^ 40),
          byte (v / 2 ^ 32), byte (v / 2 ^ 24), byte (v / 2 ^ 16),
          byte (v / 2 ^ 8), byte v]
  else none

/-- The number of bytes `encVarint` emits for `v` (when it succeeds). -/
def encLen (v : Nat) : Nat :=
  if v < 2 ^ 6 then 1 else if v < 2 ^ 14 then 2 else if v < 2 ^ 30 then 4 else 8

/-- Decode a QUIC varint from the head of `bs`. Returns
`(value, bytesConsumed)`; `none` iff fewer bytes are present than the
first byte's 2-bit prefix demands. -/
def decVarint (bs : Bytes) : Option (Nat × Nat) :=
  match bs with
  | [] => none
  | b :: rest =>
    match b.toNat / 64 with
    | 0 => some (b.toNat % 64, 1)
    | 1 =>
      if 1 ≤ rest.length then
        some (b.toNat % 64 * 2 ^ 8 + (rest.getD 0 0).toNat, 2)
      else none
    | 2 =>
      if 3 ≤ rest.length then
        some (b.toNat % 64 * 2 ^ 24 + (rest.getD 0 0).toNat * 2 ^ 16 +
              (rest.getD 1 0).toNat * 2 ^ 8 + (rest.getD 2 0).toNat, 4)
      else none
    | _ =>
      if 7 ≤ rest.length then
        some (b.toNat % 64 * 2 ^ 56 + (rest.getD 0 0).toNat * 2 ^ 48 +
              (rest.getD 1 0).toNat * 2 ^ 40 + (rest.getD 2 0).toNat * 2 ^ 32 +
              (rest.getD 3 0).toNat * 2 ^ 24 + (rest.getD 4 0).toNat * 2 ^ 16 +
              (rest.getD 5 0).toNat * 2 ^ 8 + (rest.getD 6 0).toNat, 8)
      else none

/-! ## Reduction lemmas for `decVarint` (one per length class) -/

theorem decVarint_case0 (b : UInt8) (rest : Bytes) (h : b.toNat / 64 = 0) :
    decVarint (b :: rest) = some (b.toNat % 64, 1) := by
  simp only [decVarint, h]

theorem decVarint_case1 (b : UInt8) (rest : Bytes) (h : b.toNat / 64 = 1)
    (hl : 1 ≤ rest.length) :
    decVarint (b :: rest) =
      some (b.toNat % 64 * 2 ^ 8 + (rest.getD 0 0).toNat, 2) := by
  simp only [decVarint, h, if_pos hl]

theorem decVarint_case2 (b : UInt8) (rest : Bytes) (h : b.toNat / 64 = 2)
    (hl : 3 ≤ rest.length) :
    decVarint (b :: rest) =
      some (b.toNat % 64 * 2 ^ 24 + (rest.getD 0 0).toNat * 2 ^ 16 +
            (rest.getD 1 0).toNat * 2 ^ 8 + (rest.getD 2 0).toNat, 4) := by
  simp only [decVarint, h, if_pos hl]

theorem decVarint_case3 (b : UInt8) (rest : Bytes) (h : b.toNat / 64 = 3)
    (hl : 7 ≤ rest.length) :
    decVarint (b :: rest) =
      some (b.toNat % 64 * 2 ^ 56 + (rest.getD 0 0).toNat * 2 ^ 48 +
            (rest.getD 1 0).toNat * 2 ^ 40 + (rest.getD 2 0).toNat * 2 ^ 32 +
            (rest.getD 3 0).toNat * 2 ^ 24 + (rest.getD 4 0).toNat * 2 ^ 16 +
            (rest.getD 5 0).toNat * 2 ^ 8 + (rest.getD 6 0).toNat, 8) := by
  simp only [decVarint, h, if_pos hl]

/-! ## Round-trip -/

/-- **Round-trip under any suffix**: decoding an encoding followed by
arbitrary further bytes recovers the value and consumes exactly the
encoding's length. -/
theorem decVarint_encVarint (v : Nat) (bs tail : Bytes)
    (h : encVarint v = some bs) :
    decVarint (bs ++ tail) = some (v, bs.length) := by
  unfold encVarint at h
  by_cases h1 : v < 2 ^ 6
  · rw [if_pos h1] at h
    injection h with h
    subst h
    simp only [List.cons_append, List.nil_append, List.length_cons,
      List.length_nil]
    rw [decVarint_case0 _ _ (by rw [byte_toNat]; omega), byte_toNat]
    have : v % 256 % 64 = v := by omega
    rw [this]
  · rw [if_neg h1] at h
    by_cases h2 : v < 2 ^ 14
    · rw [if_pos h2] at h
      injection h with h
      subst h
      simp only [List.cons_append, List.nil_append, List.length_cons,
        List.length_nil]
      rw [decVarint_case1 _ _ (by rw [byte_toNat]; omega) (by simp)]
      simp only [List.getD_cons_zero, byte_toNat]
      have : (64 + v / 2 ^ 8) % 256 % 64 * 2 ^ 8 + v % 256 = v := by omega
      rw [this]
    · rw [if_neg h2] at h
      by_cases h3 : v < 2 ^ 30
      · rw [if_pos h3] at h
        injection h with h
        subst h
        simp only [List.cons_append, List.nil_append, List.length_cons,
          List.length_nil]
        rw [decVarint_case2 _ _ (by rw [byte_toNat]; omega) (by simp)]
        simp only [List.getD_cons_zero, List.getD_cons_succ, byte_toNat]
        have : (128 + v / 2 ^ 24) % 256 % 64 * 2 ^ 24 +
            v / 2 ^ 16 % 256 * 2 ^ 16 + v / 2 ^ 8 % 256 * 2 ^ 8 + v % 256
            = v := by omega
        rw [this]
      · rw [if_neg h3] at h
        by_cases h4 : v ≤ maxVarint
        · rw [if_pos h4] at h
          injection h with h
          subst h
          unfold maxVarint at h4
          simp only [List.cons_append, List.nil_append, List.length_cons,
            List.length_nil]
          rw [decVarint_case3 _ _ (by rw [byte_toNat]; omega) (by simp)]
          simp only [List.getD_cons_zero, List.getD_cons_succ, byte_toNat]
          have : (192 + v / 2 ^ 56) % 256 % 64 * 2 ^ 56 +
              v / 2 ^ 48 % 256 * 2 ^ 48 + v / 2 ^ 40 % 256 * 2 ^ 40 +
              v / 2 ^ 32 % 256 * 2 ^ 32 + v / 2 ^ 24 % 256 * 2 ^ 24 +
              v / 2 ^ 16 % 256 * 2 ^ 16 + v / 2 ^ 8 % 256 * 2 ^ 8 + v % 256
              = v := by omega
          rw [this]
        · rw [if_neg h4] at h
          exact absurd h (by simp)

/-- Round-trip, no suffix. -/
theorem decVarint_encVarint' (v : Nat) (bs : Bytes) (h : encVarint v = some bs) :
    decVarint bs = some (v, bs.length) := by
  have := decVarint_encVarint v bs [] h
  simpa using this

/-! ## Length bounds -/

/-- The encoder succeeds exactly on the representable range. -/
theorem encVarint_isSome_iff (v : Nat) :
    (encVarint v).isSome ↔ v ≤ maxVarint := by
  unfold encVarint maxVarint
  repeat' split
  all_goals simp
  all_goals omega

/-- **Length bound**: a successful encoding has exactly `encLen v` bytes. -/
theorem encVarint_length (v : Nat) (bs : Bytes) (h : encVarint v = some bs) :
    bs.length = encLen v := by
  unfold encVarint at h
  unfold encLen
  repeat' split at h
  all_goals first
    | (injection h with h; subst h
       simp only [List.length_cons, List.length_nil]
       repeat' split
       all_goals omega)
    | exact absurd h (by simp)

theorem encLen_mem (v : Nat) :
    encLen v = 1 ∨ encLen v = 2 ∨ encLen v = 4 ∨ encLen v = 8 := by
  unfold encLen
  repeat' split
  all_goals simp

/-- **Decoder consumption bounds**: a successful decode consumes 1, 2, 4, or
8 bytes, at least one, and never more than the input holds; the decoded value
is representable. -/
theorem decVarint_consumed (bs : Bytes) (v n : Nat)
    (h : decVarint bs = some (v, n)) :
    (n = 1 ∨ n = 2 ∨ n = 4 ∨ n = 8) ∧ 1 ≤ n ∧ n ≤ bs.length := by
  unfold decVarint at h
  split at h
  · exact absurd h (by simp)
  · rename_i b rest
    split at h
    · injection h with h
      injection h with h₁ h₂
      simp [← h₂]
    · split at h
      · injection h with h
        injection h with h₁ h₂
        rename_i hl
        simp [← h₂]
        omega
      · exact absurd h (by simp)
    · split at h
      · injection h with h
        injection h with h₁ h₂
        rename_i hl
        simp [← h₂]
        omega
      · exact absurd h (by simp)
    · split at h
      · injection h with h
        injection h with h₁ h₂
        rename_i hl
        simp [← h₂]
        omega
      · exact absurd h (by simp)

theorem decVarint_consumed_pos (bs : Bytes) (v n : Nat)
    (h : decVarint bs = some (v, n)) : 1 ≤ n :=
  (decVarint_consumed bs v n h).2.1

theorem decVarint_consumed_le (bs : Bytes) (v n : Nat)
    (h : decVarint bs = some (v, n)) : n ≤ bs.length :=
  (decVarint_consumed bs v n h).2.2

/-- Every decoded value is representable (`≤ maxVarint`), and is bounded by
the usable bits of its length class. -/
theorem decVarint_value_lt (bs : Bytes) (v n : Nat)
    (h : decVarint bs = some (v, n)) :
    (n = 1 → v < 2 ^ 6) ∧ (n = 2 → v < 2 ^ 14) ∧ (n = 4 → v < 2 ^ 30) ∧
      v < 2 ^ 62 := by
  unfold decVarint at h
  split at h
  · exact absurd h (by simp)
  · rename_i b rest
    have hb := u8_toNat_lt b
    split at h
    · injection h with h
      injection h with h₁ h₂
      omega
    · split at h
      · injection h with h
        injection h with h₁ h₂
        have h0 := u8_toNat_lt (rest.getD 0 0)
        omega
      · exact absurd h (by simp)
    · split at h
      · injection h with h
        injection h with h₁ h₂
        have h0 := u8_toNat_lt (rest.getD 0 0)
        have h1 := u8_toNat_lt (rest.getD 1 0)
        have h2 := u8_toNat_lt (rest.getD 2 0)
        omega
      · exact absurd h (by simp)
    · split at h
      · injection h with h
        injection h with h₁ h₂
        have h0 := u8_toNat_lt (rest.getD 0 0)
        have h1 := u8_toNat_lt (rest.getD 1 0)
        have h2 := u8_toNat_lt (rest.getD 2 0)
        have h3 := u8_toNat_lt (rest.getD 3 0)
        have h4 := u8_toNat_lt (rest.getD 4 0)
        have h5 := u8_toNat_lt (rest.getD 5 0)
        have h6 := u8_toNat_lt (rest.getD 6 0)
        omega
      · exact absurd h (by simp)

theorem decVarint_value_le (bs : Bytes) (v n : Nat)
    (h : decVarint bs = some (v, n)) : v ≤ maxVarint := by
  have := (decVarint_value_lt bs v n h).2.2.2
  unfold maxVarint
  omega

/-! ## Canonical form -/

/-- **Canonical form**: whatever encoding the decoder accepted for `v`, the
encoder's own output for `v` exists and is no longer — `encVarint` emits the
canonical (minimal-length) form. -/
theorem encVarint_canonical (bs : Bytes) (v n : Nat)
    (h : decVarint bs = some (v, n)) :
    ∃ ebs, encVarint v = some ebs ∧ ebs.length ≤ n := by
  have hv := decVarint_value_le bs v n h
  have hsome : (encVarint v).isSome := (encVarint_isSome_iff v).mpr hv
  match hebs : encVarint v with
  | none => rw [hebs] at hsome; simp at hsome
  | some ebs =>
    refine ⟨ebs, rfl, ?_⟩
    have hlen := encVarint_length v ebs hebs
    have hmem := decVarint_consumed bs v n h
    have hval := decVarint_value_lt bs v n h
    unfold encLen at hlen
    rcases hmem.1 with h1 | h2 | h4 | h8
    · have := hval.1 h1
      rw [if_pos this] at hlen
      omega
    · have := hval.2.1 h2
      rw [hlen]
      repeat' split
      all_goals omega
    · have := hval.2.2.1 h4
      rw [hlen]
      repeat' split
      all_goals omega
    · rw [hlen]
      repeat' split
      all_goals omega

/-! ## Wire vectors (RFC 9000 §A.1), checker-verified -/

example : decVarint [0x25] = some (37, 1) := rfl
example : decVarint [0x7b, 0xbd] = some (15293, 2) := rfl
example : decVarint [0x9d, 0x7f, 0x3e, 0x7d] = some (494878333, 4) := rfl
example : decVarint [0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c]
    = some (151288809941952652, 8) := rfl
example : encVarint 37 = some [0x25] := rfl
example : encVarint 15293 = some [0x7b, 0xbd] := rfl
example : encVarint 494878333 = some [0x9d, 0x7f, 0x3e, 0x7d] := rfl
example : encVarint 151288809941952652
    = some [0xc2, 0x19, 0x7c, 0x5e, 0xff, 0x14, 0xe8, 0x8c] := rfl
/-- A truncated two-byte varint is rejected. -/
example : decVarint [0x40] = none := rfl
/-- `2^62` overflows. -/
example : encVarint (2 ^ 62) = none := rfl

end Varint
end H3

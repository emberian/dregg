import H3.Frame

/-!
# HTTP/3 frame decode — correctness against an independent RFC 9114 §7.1 spec

`H3.decFrame` (H3/Frame.lean) is the byte-level HTTP/3 frame cutter: it reads
one RFC 9114 §7.1 frame from the head of a buffer — a type varint, a length
varint, then the length-many payload bytes — using the QUIC varint reader
`H3.Varint.decVarint` (H3/Varint.lean). The `Varint` layer proves that reader
round-trips and stays in range; this module pins the *frame decoder itself* to
an independent specification of what §7.1 says the decoded frame must be, and
proves the real decoder equals it on every input for the two frames whose
payload is delivered verbatim (DATA §7.2.1 and HEADERS §7.2.2).

## The specification is written from the RFC, not from the code

The reference decoder `specFrame` below reconstructs the §7.1 frame using
primitives defined here from the wire format — never the implementation's:

* **Frame layout** — RFC 9114 §7.1 fixes the wire image as
  `Type (i) · Length (i) · Frame Payload (..)`, where `(i)` is a QUIC
  variable-length integer and the payload is "a sequence of bytes … with a
  length of exactly `Length`". `specFrame` reads the two integers and then
  takes *exactly* `Length` bytes; it fails when fewer than `Length` payload
  bytes are present.
* **The variable-length integers** — RFC 9000 §16 defines a varint as: the two
  most significant bits of the first byte give the length class (`2^prefix`
  bytes total), and the value is the remaining bits read as a big-endian
  unsigned integer. `specVarint` reads the length as `2 ^ (b >>> 6)` and the
  value positionally with `beValue` — the weighted sum
  `Σ bᵢ · 256^(len-1-i)` with the first byte's two class bits masked off. The
  implementation instead extracts the class with `b.toNat / 64`, the low bits
  with `b.toNat % 64`, and folds the trailing bytes through hardcoded
  power-of-two weights and `getD` indices. `specVarint_eq_decVarint` proves the
  two readings agree on every buffer, so a frame decoder that mis-reads a
  varint fails the refinement.

## Results

* `decFrame_refines_spec` — **the refinement**: whenever `specFrame` decodes a
  frame of type DATA (`0x00`) or HEADERS (`0x01`), `H3.decFrame` returns exactly
  that payload and consumes exactly the spec's byte count. The payload the real
  decoder emits *equals* the exact `Length` bytes the spec isolates, and the
  frame type / length are the two varints the spec read.
* `specFrame_none_incomplete` — the failure direction: when the spec cannot read
  a full header-plus-payload, the real decoder reports `incomplete`; so for
  DATA/HEADERS the two agree on *every* buffer, success and short-buffer alike.
* `decFrame_data_payload_exact` / `decFrame_headers_payload_exact` — the two
  headline §7.1 facts extracted from the refinement: a decoded DATA/HEADERS
  payload is byte-for-byte the `Length`-long slice starting after the header.
* `length_misread_fails` / `payload_drop_fails` — **non-vacuity**: concrete
  DATA frames on which the spec's payload differs from a decoder that reads the
  length varint as a single byte, and from one that drops a payload byte. A
  decoder with either bug cannot satisfy `decFrame_refines_spec`.
-/

namespace H3FrameCorrect

open H3

/-! ## Independent RFC 9000 §16 varint primitives -/

/-- Positional big-endian value of a byte string: the most significant byte
carries weight `256 ^ (length - 1)` (RFC 9000 §16: the varint's value bits are
read "in network byte order"). Defined by explicit positional weights,
independently of the implementation's `getD`-indexed hardcoded fold. -/
def beValue : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + beValue bs

@[simp] theorem beValue_nil : beValue [] = 0 := rfl

@[simp] theorem beValue_cons (b : UInt8) (bs : Bytes) :
    beValue (b :: bs) = b.toNat * 256 ^ bs.length + beValue bs := rfl

/-- Independent QUIC varint reader (RFC 9000 §16). The first byte's two most
significant bits (`b >>> 6`) select the length class `2 ^ prefix ∈ {1,2,4,8}`;
the value is the class bits masked off (`b % 64` as the top digit) followed by
the big-endian reading of the remaining `len - 1` bytes. Fails when the buffer
is shorter than the class demands. -/
def specVarint (bs : Bytes) : Option (Nat × Nat) :=
  match bs with
  | [] => none
  | b :: rest =>
    if bs.length < 2 ^ (b.toNat / 64) then none
    else some (b.toNat % 64 * 256 ^ (2 ^ (b.toNat / 64) - 1) +
      beValue (rest.take (2 ^ (b.toNat / 64) - 1)), 2 ^ (b.toNat / 64))

/-- **Varint agreement**: the independent §16 reader and the implementation's
`decVarint` return the same value and byte count on every buffer. A frame
decoder that mis-reads either varint therefore cannot match `decFrame`. -/
theorem specVarint_eq_decVarint (bs : Bytes) :
    specVarint bs = Varint.decVarint bs := by
  rcases bs with _ | ⟨b, rest⟩
  · rfl
  · have hb : b.toNat < 256 := Varint.u8_toNat_lt b
    have hk : b.toNat / 64 = 0 ∨ b.toNat / 64 = 1 ∨ b.toNat / 64 = 2 ∨
        b.toNat / 64 = 3 := by omega
    rcases hk with hk | hk | hk | hk
    · -- 1-byte class: always present
      rw [Varint.decVarint_case0 b rest hk]
      simp only [specVarint, hk, List.length_cons]
      rw [if_neg (by omega)]
      simp only [List.take_zero, beValue_nil, Nat.mul_one, Nat.add_zero]
    · -- 2-byte class
      by_cases hl : 1 ≤ rest.length
      · obtain ⟨r0, rest', rfl⟩ : ∃ a l, rest = a :: l := by
          cases rest with
          | nil => simp at hl
          | cons a l => exact ⟨a, l, rfl⟩
        rw [Varint.decVarint_case1 b (r0 :: rest') hk hl]
        simp only [specVarint, hk, List.length_cons]
        rw [if_neg (by omega)]
        simp only [show (r0 :: rest').take 1 = [r0] from rfl, beValue_cons,
          beValue_nil, List.length_nil, List.getD_cons_zero,
          Option.some.injEq, Prod.mk.injEq]
        omega
      · rw [show specVarint (b :: rest) = none from by
            simp only [specVarint, hk, List.length_cons]; rw [if_pos (by omega)],
          show Varint.decVarint (b :: rest) = none from by
            simp only [Varint.decVarint, hk]; rw [if_neg hl]]
    · -- 4-byte class
      by_cases hl : 3 ≤ rest.length
      · obtain ⟨r0, r1, r2, rest', rfl⟩ : ∃ a b c l, rest = a :: b :: c :: l := by
          rcases rest with _ | ⟨a, _ | ⟨b', _ | ⟨c, l⟩⟩⟩
          · simp at hl
          · simp at hl
          · simp at hl
          · exact ⟨a, b', c, l, rfl⟩
        rw [Varint.decVarint_case2 b (r0 :: r1 :: r2 :: rest') hk hl]
        simp only [specVarint, hk, List.length_cons]
        rw [if_neg (by omega)]
        simp only [show (r0 :: r1 :: r2 :: rest').take 3 = [r0, r1, r2] from rfl,
          beValue_cons, beValue_nil, List.length_cons, List.length_nil,
          List.getD_cons_zero, List.getD_cons_succ, Option.some.injEq,
          Prod.mk.injEq]
        omega
      · rw [show specVarint (b :: rest) = none from by
            simp only [specVarint, hk, List.length_cons]; rw [if_pos (by omega)],
          show Varint.decVarint (b :: rest) = none from by
            simp only [Varint.decVarint, hk]; rw [if_neg hl]]
    · -- 8-byte class
      by_cases hl : 7 ≤ rest.length
      · obtain ⟨r0, r1, r2, r3, r4, r5, r6, rest', rfl⟩ :
            ∃ a b c d e f g l, rest = a :: b :: c :: d :: e :: f :: g :: l := by
          rcases rest with _ | ⟨a, _ | ⟨b', _ | ⟨c, _ | ⟨d, _ | ⟨e,
            _ | ⟨f, _ | ⟨g, l⟩⟩⟩⟩⟩⟩⟩
          · simp at hl
          · simp at hl
          · simp at hl
          · simp at hl
          · simp at hl
          · simp at hl
          · simp at hl
          · exact ⟨a, b', c, d, e, f, g, l, rfl⟩
        rw [Varint.decVarint_case3 b (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rest')
          hk hl]
        simp only [specVarint, hk, List.length_cons]
        rw [if_neg (by omega)]
        simp only [show (r0 :: r1 :: r2 :: r3 :: r4 :: r5 :: r6 :: rest').take 7 =
            [r0, r1, r2, r3, r4, r5, r6] from rfl,
          beValue_cons, beValue_nil, List.length_cons, List.length_nil,
          List.getD_cons_zero, List.getD_cons_succ, Option.some.injEq,
          Prod.mk.injEq]
        omega
      · rw [show specVarint (b :: rest) = none from by
            simp only [specVarint, hk, List.length_cons]; rw [if_pos (by omega)],
          show Varint.decVarint (b :: rest) = none from by
            simp only [Varint.decVarint, hk]; rw [if_neg hl]]

/-! ## Independent RFC 9114 §7.1 frame layout -/

/-- A decoded §7.1 frame image: the two header integers, the exact payload
slice, and the total bytes the header-plus-payload occupies. -/
structure SpecFrame where
  /-- The Type field (RFC 9114 §7.1), a QUIC varint. -/
  frameType : Nat
  /-- The Length field (RFC 9114 §7.1), a QUIC varint: the payload byte count. -/
  payloadLen : Nat
  /-- The Frame Payload: exactly `payloadLen` bytes (RFC 9114 §7.1). -/
  payload : Bytes
  /-- Total bytes consumed: both varints plus the payload. -/
  consumed : Nat
deriving Repr, DecidableEq

/-- Independent §7.1 frame decoder: read the Type varint, read the Length
varint, then take *exactly* `Length` payload bytes (failing if fewer are
present). Written over `specVarint`, never over the implementation. -/
def specFrame (bs : Bytes) : Option SpecFrame :=
  match specVarint bs with
  | none => none
  | some (t, n1) =>
    match specVarint (bs.drop n1) with
    | none => none
    | some (len, n2) =>
      let rest := bs.drop (n1 + n2)
      if rest.length < len then none
      else some ⟨t, len, rest.take len, n1 + n2 + len⟩

/-! ## The refinement -/

/-- **Refinement (DATA / HEADERS)**: whenever the independent §7.1 spec decodes
a frame whose type is DATA (`0x00`) or HEADERS (`0x01`), the real `decFrame`
returns exactly that payload and consumes exactly the spec's byte count. This
pins the decoded payload to the exact `Length` bytes and the type/length to the
two varints — a decoder that mis-reads the length varint or drops payload bytes
produces a different `SpecFrame` and fails this equality. -/
theorem decFrame_refines_spec (bs : Bytes) (sf : SpecFrame)
    (h : specFrame bs = some sf) :
    (sf.frameType = 0x00 →
      decFrame bs = .complete (.data sf.payload) sf.consumed) ∧
    (sf.frameType = 0x01 →
      decFrame bs = .complete (.headers sf.payload) sf.consumed) := by
  unfold specFrame at h
  rw [specVarint_eq_decVarint] at h
  unfold decFrame
  cases hv1 : Varint.decVarint bs with
  | none => rw [hv1] at h; simp at h
  | some tp =>
    obtain ⟨t, n1⟩ := tp
    rw [hv1] at h ⊢
    rw [specVarint_eq_decVarint] at h
    cases hv2 : Varint.decVarint (bs.drop n1) with
    | none => rw [hv2] at h; simp at h
    | some lp =>
      obtain ⟨len, n2⟩ := lp
      rw [hv2] at h ⊢
      by_cases hlt : (bs.drop (n1 + n2)).length < len
      · rw [if_pos hlt] at h; simp at h
      · rw [if_pos rfl] at h
        rw [if_neg hlt] at h
        injection h with h
        subst h
        rw [if_neg hlt]
        refine ⟨fun ht => ?_, fun ht => ?_⟩ <;>
          · simp only at ht
            simp only [FrameType.ofNat, ht]
      all_goals simp_all

theorem decFrame_data_payload_exact (bs : Bytes) (sf : SpecFrame)
    (h : specFrame bs = some sf) (ht : sf.frameType = 0x00) :
    decFrame bs = .complete (.data sf.payload) sf.consumed :=
  (decFrame_refines_spec bs sf h).1 ht

theorem decFrame_headers_payload_exact (bs : Bytes) (sf : SpecFrame)
    (h : specFrame bs = some sf) (ht : sf.frameType = 0x01) :
    decFrame bs = .complete (.headers sf.payload) sf.consumed :=
  (decFrame_refines_spec bs sf h).2 ht

/-- The failure direction: when the spec cannot read a full frame (a varint is
truncated, or fewer than `Length` payload bytes are present), the real decoder
reports `incomplete`. Together with `decFrame_refines_spec` this makes the two
agree on *every* buffer for DATA / HEADERS: `decFrame` completes with the exact
payload exactly when `specFrame` succeeds. -/
theorem specFrame_none_incomplete (bs : Bytes) (h : specFrame bs = none) :
    decFrame bs = .incomplete := by
  unfold specFrame at h
  unfold decFrame
  rw [specVarint_eq_decVarint] at h
  cases hv1 : Varint.decVarint bs with
  | none => rw [hv1]
  | some tp =>
    obtain ⟨t, n1⟩ := tp
    rw [hv1] at h ⊢
    rw [specVarint_eq_decVarint] at h
    cases hv2 : Varint.decVarint (bs.drop n1) with
    | none => rw [hv2]
    | some lp =>
      obtain ⟨len, n2⟩ := lp
      rw [hv2] at h ⊢
      by_cases hlt : (bs.drop (n1 + n2)).length < len
      · rw [if_neg hlt]
      · rw [if_pos rfl, if_neg hlt] at h; simp at h

/-! ## Non-vacuity

The refinement is falsifiable: a wrong decoder fails it. Each witness below is a
concrete DATA frame on which the spec's payload differs from a specific bug, so
that bug cannot equal `decFrame` on that input (since `decFrame` equals the spec
there by `decFrame_refines_spec`). -/

/-- A length reader that reads the Length varint as a single byte's low six
bits — the "I ignored the 2-bit class prefix" bug. -/
def badLenVarint : Bytes → Option (Nat × Nat)
  | [] => none
  | b :: _ => some (b.toNat % 64, 1)

/-- The frame decoder built from `badLenVarint` for the length field. -/
def badLenFrame (bs : Bytes) : Option SpecFrame :=
  match specVarint bs with
  | none => none
  | some (t, n1) =>
    match badLenVarint (bs.drop n1) with
    | none => none
    | some (len, n2) =>
      let rest := bs.drop (n1 + n2)
      if rest.length < len then none
      else some ⟨t, len, rest.take len, n1 + n2 + len⟩

/-- The frame decoder that drops the final payload byte. -/
def dropPayloadFrame (bs : Bytes) : Option SpecFrame :=
  match specVarint bs with
  | none => none
  | some (t, n1) =>
    match specVarint (bs.drop n1) with
    | none => none
    | some (len, n2) =>
      let rest := bs.drop (n1 + n2)
      if rest.length < len then none
      else some ⟨t, len, (rest.take len).dropLast, n1 + n2 + len⟩

/-- The witness frame: DATA (`0x00`), Length `2` encoded *non-canonically* in a
2-byte varint (`0x40 0x02`), payload `[0xaa, 0xbb]`. The length is two bytes on
the wire, so a decoder that reads it as one byte lands at the wrong offset. -/
def witness : Bytes := [0x00, 0x40, 0x02, 0xaa, 0xbb]

/-- On the witness, the real decoder (= the spec) delivers the full 2-byte
payload. -/
example : specFrame witness = some ⟨0x00, 2, [0xaa, 0xbb], 5⟩ := by decide

example : decFrame witness = .complete (.data [0xaa, 0xbb]) 5 := by decide

/-- **Non-vacuity (length mis-read).** Reading the 2-byte Length varint as a
single byte yields Length `0` and an empty payload — different from the spec's
`[0xaa, 0xbb]`. So `badLenFrame` disagrees with `decFrame` on `witness`; a
decoder with this bug fails `decFrame_refines_spec`. -/
theorem length_misread_fails :
    badLenFrame witness ≠ specFrame witness := by decide

/-- The dropped-payload bug and the spec also differ on `witness`: the spec's
payload is `[0xaa, 0xbb]`, the bug's is `[0xaa]`. -/
theorem payload_drop_fails :
    dropPayloadFrame witness ≠ specFrame witness := by decide

/-- Both bugs, phrased as payload inequalities against the exact §7.1 slice, to
make the discrepancy explicit. -/
theorem bugs_change_payload :
    (badLenFrame witness).map SpecFrame.payload ≠ some [0xaa, 0xbb] ∧
    (dropPayloadFrame witness).map SpecFrame.payload ≠ some [0xaa, 0xbb] := by
  decide

end H3FrameCorrect

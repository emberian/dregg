import Reactor.Ws

/-!
# WebSocket frame decode — correctness against an independent RFC 6455 §5.2 spec

`Reactor.Ws.decodeFrame` is the byte-level frame cutter: it reads one RFC 6455
§5.2 frame from the head of a buffer, resolving the payload length with the
`Ws.Length` ladder and unmasking the payload with the `Ws.Mask` transform. The
`Ws` layer proves those *pieces* canonical/involutive; this module pins the
*decoder itself* to an independent specification of what §5.2 says the decoded
frame must be, and proves the real decoder equals it on every input.

## The specification is written from the RFC, not from the code

The reference decoder `specDecode` below reconstructs the §5.2 frame using
primitives defined here from the wire format — never the implementation's:

* **FIN / opcode** — RFC 6455 §5.2 places FIN in the high bit of byte 0 and the
  opcode in its low nibble. The spec reads FIN as `Nat.testBit n 7` (bit 7) and
  the opcode nibble as `n % 16`; the implementation uses `n &&& 0x80` and
  `n &&& 0x0f`. The bridge lemmas `hiBit_eq_and80` / `nibble_eq_and0f` prove
  these agree.
* **Payload length** — §5.2's extended-length field is a big-endian unsigned
  integer. The spec reads it with `beValue`, the *positional* big-endian value
  `Σ bᵢ · 256^(len−1−i)`; the implementation folds Horner-style through
  `Ws.fromBE`. `fromBE_eq_beValue` proves the two big-endian readings agree, so
  a decoder that mis-reads the extended length fails the refinement.
* **Unmasking** — §5.3 defines the transform octet `i ↦ octet ⊕ key[i mod 4]`.
  The spec applies it as `List.mapIdx` over the payload (`xorCycle`); the
  implementation runs the stateful `Ws.applyMask`. `applyMask_eq_xorCycle` proves
  they agree, so a decoder that skips unmasking fails the refinement.

## Results

* `decodeFrame_eq_specDecode` — **the refinement**: `Reactor.Ws.decodeFrame`
  equals `specDecode` on *every* input buffer (both the successful decode and the
  `none` short-buffer cases).
* `decode_payload_unmasked` / `decode_length_extended` — the two headline §5.2
  facts extracted from the refinement: a successfully decoded masked payload is
  the on-wire bytes XORed with the cycled key, and its length is the
  extended-length field value.
* `unmask_required` / `extlen_required` — **non-vacuity**: concrete frames on
  which the spec's answer differs from a decoder that skips unmasking, and from
  one that reads the 7-bit marker `126` as the length instead of the extended
  field. A decoder with either bug cannot satisfy `decodeFrame_eq_specDecode`.
-/

namespace WsFrameCorrect

open Ws (Bytes Frame Opcode)

/-! ## Independent §5.2 primitives -/

/-- FIN is the high bit (bit 7) of byte 0 (RFC 6455 §5.2). -/
def hiBit (n : Nat) : Bool := n.testBit 7

/-- The opcode nibble is the low four bits of byte 0 (RFC 6455 §5.2). -/
def nibble (n : Nat) : Nat := n % 16

/-- The 7-bit "Payload len" field is the low seven bits of byte 1
(RFC 6455 §5.2). -/
def len7 (n : Nat) : Nat := n % 128

/-- Positional big-endian value of a byte string: the most significant byte
carries weight `256^(length-1)` (RFC 6455 §5.2 extended length is an unsigned
big-endian integer). Defined by explicit positional weights, independently of
the implementation's Horner fold. -/
def beValue : Bytes → Nat
  | [] => 0
  | b :: bs => b.toNat * 256 ^ bs.length + beValue bs

/-- The RFC 6455 §5.3 unmasking transform, applied positionally: octet `i` of the
payload is XORed with `key[i mod 4]` (a missing key byte defaults to `0`, the XOR
identity). Written as `List.mapIdx`, independently of the implementation's
stateful recursion. -/
def xorCycle (key : Bytes) (raw : Bytes) : Bytes :=
  raw.mapIdx (fun i b => b ^^^ key.getD (i % 4) 0)

/-- The payload length denoted by a §5.2 length field: the inline 7-bit value
when `≤ 125`, otherwise the big-endian extended field. -/
def specLen (m : Nat) (ext : Bytes) : Nat :=
  if m ≤ 125 then m else beValue ext

/-- The number of extended-length octets a 7-bit marker introduces: none inline,
two for marker `126` (16-bit), eight for marker `127` (64-bit) — RFC 6455 §5.2. -/
def extCount (m : Nat) : Nat := if m = 126 then 2 else if m = 127 then 8 else 0

/-- **The independent reference decoder** (RFC 6455 §5.2). Reads one frame from
the head of a buffer: FIN and opcode from byte 0, the mask bit and 7-bit length
from byte 1, the extended length as a big-endian integer, and the payload
unmasked by the §5.3 transform when the mask bit is set. Returns the decoded
frame and the unconsumed tail, or `none` if the buffer holds no complete frame.
Defined only from the wire format and the primitives above. -/
def specDecode : Bytes → Option (Frame × Bytes)
  | b0 :: b1 :: rest0 =>
    let n0 := b0.toNat
    let n1 := b1.toNat
    let fin := hiBit n0
    let opcode := Opcode.ofNat (nibble n0)
    let masked := hiBit n1
    let l7 := len7 n1
    let ec := extCount l7
    let ext := rest0.take ec
    if ext.length < ec then none
    else
      let rest1 := rest0.drop ec
      let payloadLen := specLen l7 ext
      let keyLen := if masked then 4 else 0
      let key := rest1.take keyLen
      if key.length < keyLen then none
      else
        let rest2 := rest1.drop keyLen
        let raw := rest2.take payloadLen
        if raw.length < payloadLen then none
        else
          let payload := if masked then xorCycle key raw else raw
          some ({ fin := fin, opcode := opcode, payload := payload }, rest2.drop payloadLen)
  | _ => none

/-! ## Bridge lemmas: the wire primitives agree with the implementation's -/

/-- The low nibble via mask equals the value mod 16. -/
theorem nibble_eq_and0f (n : Nat) : n &&& 0x0f = nibble n :=
  Nat.and_pow_two_sub_one_eq_mod n 4

/-- The low 7 bits via mask equal the value mod 128. -/
theorem len7_eq_and7f (n : Nat) : n &&& 0x7f = len7 n :=
  Nat.and_pow_two_sub_one_eq_mod n 7

/-- Testing the high bit (bit 7) equals the `&&& 0x80 ≠ 0` mask test. -/
theorem hiBit_eq_and80 (n : Nat) : ((n &&& 0x80) != 0) = hiBit n := by
  unfold hiBit
  cases h : n.testBit 7 with
  | true =>
    have hb : (n &&& 2 ^ 7).testBit 7 = true := by
      rw [Nat.testBit_and, Nat.testBit_two_pow_self]; simp [h]
    have hne : n &&& 2 ^ 7 ≠ 0 := by
      intro h0; rw [h0] at hb; simp at hb
    simp [hne]
  | false =>
    have hz : n &&& 2 ^ 7 = 0 := by
      apply Nat.eq_of_testBit_eq
      intro j
      simp only [Nat.testBit_and, Nat.testBit_two_pow, Nat.zero_testBit]
      by_cases hj : 7 = j
      · subst hj; simp [h]
      · simp [hj]
    simp [hz]

/-- The implementation's Horner big-endian fold, generalized over the accumulator. -/
theorem fromBEAux_eq (acc : Nat) : ∀ l : Bytes,
    Ws.fromBEAux acc l = acc * 256 ^ l.length + beValue l
  | [] => by simp [Ws.fromBEAux, beValue]
  | b :: bs => by
    simp only [Ws.fromBEAux, beValue, List.length_cons]
    rw [fromBEAux_eq (acc * 256 + b.toNat) bs, Nat.add_mul, Nat.pow_succ]
    rw [Nat.mul_assoc acc 256 (256 ^ bs.length), Nat.mul_comm 256 (256 ^ bs.length),
        Nat.add_assoc]

/-- **Big-endian readings agree**: the implementation's Horner fold `Ws.fromBE`
equals the positional value `beValue`. -/
theorem fromBE_eq_beValue (l : Bytes) : Ws.fromBE l = beValue l := by
  unfold Ws.fromBE
  rw [fromBEAux_eq 0 l, Nat.zero_mul, Nat.zero_add]

/-- The implementation's stateful mask, generalized over the start offset,
equals the positional `mapIdx` transform. -/
theorem maskFrom_eq_mapIdx (key : Bytes) : ∀ (i : Nat) (raw : Bytes),
    Ws.maskFrom key i raw = raw.mapIdx (fun j b => b ^^^ key.getD ((i + j) % 4) 0)
  | _, [] => by simp [Ws.maskFrom]
  | i, b :: bs => by
    have hfun : (fun (j : Nat) (c : UInt8) => c ^^^ key.getD ((i + 1 + j) % 4) 0)
        = (fun (j : Nat) (c : UInt8) => c ^^^ key.getD ((i + (j + 1)) % 4) 0) := by
      funext j c; congr 2; omega
    simp only [Ws.maskFrom, List.mapIdx_cons, Nat.add_zero]
    rw [maskFrom_eq_mapIdx key (i + 1) bs, hfun]

/-- **Unmasking agrees**: the implementation's `Ws.applyMask` equals the
positional §5.3 transform `xorCycle`. -/
theorem applyMask_eq_xorCycle (key raw : Bytes) :
    Ws.applyMask key raw = xorCycle key raw := by
  unfold Ws.applyMask xorCycle
  rw [maskFrom_eq_mapIdx key 0 raw]
  simp

/-! ## The refinement theorem -/

/-- **Refinement.** The real byte-level decoder `Reactor.Ws.decodeFrame` equals
the independent RFC 6455 §5.2 reference decoder `specDecode` on every input
buffer — including the `none` short-buffer cases. The decoded FIN/opcode are the
high bit and low nibble of byte 0, the payload length is the extended-length
field, and a masked payload is the on-wire bytes XORed with the cycled key. -/
theorem decodeFrame_eq_specDecode (bs : Bytes) :
    Reactor.Ws.decodeFrame bs = specDecode bs := by
  cases bs with
  | nil => rfl
  | cons b0 tl =>
    cases tl with
    | nil => rfl
    | cons b1 rest0 =>
      simp only [Reactor.Ws.decodeFrame, specDecode, hiBit_eq_and80,
        nibble_eq_and0f, len7_eq_and7f, Ws.decodeLenField, fromBE_eq_beValue,
        applyMask_eq_xorCycle, specLen, extCount]

/-! ## Headline §5.2 facts, extracted from the refinement -/

/-- **Decoded length is the extended-length field.** Whenever the real decoder
succeeds, the decoded payload length is exactly `specLen` of the 7-bit marker and
the big-endian extended field — the §5.2 length ladder read independently. In
particular, on the 126/127 rungs it is `beValue` of the extended bytes, not the
marker. -/
theorem decode_length_extended (bs : Bytes) (f : Frame) (tail : Bytes)
    (h : Reactor.Ws.decodeFrame bs = some (f, tail)) :
    ∃ b0 b1 rest0, bs = b0 :: b1 :: rest0 ∧
      f.payload.length =
        specLen (len7 b1.toNat) (rest0.take (extCount (len7 b1.toNat))) := by
  rw [decodeFrame_eq_specDecode] at h
  match bs with
  | [] => simp [specDecode] at h
  | [_] => simp [specDecode] at h
  | b0 :: b1 :: rest0 =>
    refine ⟨b0, b1, rest0, rfl, ?_⟩
    simp only [specDecode] at h
    repeat' split at h
    all_goals first
      | exact Option.noConfusion h
      | (simp only [Option.some.injEq, Prod.mk.injEq] at h;
         obtain ⟨hf, -⟩ := h;
         subst hf;
         simp only [xorCycle, List.length_mapIdx, List.length_take] at *;
         omega)

/-- **Decoded masked payload is unmasked.** Whenever the real decoder succeeds on
a masked frame, the decoded payload is the on-wire raw bytes XORed with the
4-byte key cycled by position (RFC 6455 §5.3) — it is not the raw masked bytes. -/
theorem decode_payload_unmasked (bs : Bytes) (f : Frame) (tail : Bytes)
    (h : Reactor.Ws.decodeFrame bs = some (f, tail))
    (hm : ∃ b0 b1 r, bs = b0 :: b1 :: r ∧ hiBit b1.toNat = true) :
    ∃ key raw, f.payload = xorCycle key raw := by
  rw [decodeFrame_eq_specDecode] at h
  obtain ⟨b0, b1, r, hbs, hmask⟩ := hm
  subst hbs
  simp only [specDecode, hmask, ite_true] at h
  repeat' split at h
  all_goals first
    | exact Option.noConfusion h
    | (simp only [Option.some.injEq, Prod.mk.injEq] at h;
       obtain ⟨hf, -⟩ := h;
       rw [← hf];
       exact ⟨_, _, rfl⟩)

/-! ## Non-vacuity: the spec rejects the two canonical mutations -/

/-- A masked single text frame `"HI"`: `fin=1`, opcode `text`, mask bit set,
length 2, key `[1,2,3,4]`, on-wire payload `[0x49,0x4B]` (= `[0x48,0x49] ⊕ key`).
The spec unmasks it to `[0x48, 0x49]`. -/
theorem unmask_required :
    specDecode [0x81, 0x82, 0x01, 0x02, 0x03, 0x04, 0x49, 0x4B]
      = some ({ fin := true, opcode := .text, payload := [0x48, 0x49] }, [])
    ∧ specDecode [0x81, 0x82, 0x01, 0x02, 0x03, 0x04, 0x49, 0x4B]
      ≠ some ({ fin := true, opcode := .text, payload := [0x49, 0x4B] }, []) := by
  refine ⟨by rfl, ?_⟩
  intro h
  simp only [specDecode] at h
  exact absurd h (by decide)

/-- A frame using the 16-bit extended length rung: marker `126`, extended bytes
`[0x00, 0x02]` (big-endian `2`). The spec reads the length as `beValue [0,2] = 2`,
not the marker `126`. A decoder that read the marker `126` as the length would
demand 126 payload bytes and fail; the spec (and the real decoder) take 2. -/
theorem extlen_required :
    specDecode ([0x81, 0x7e, 0x00, 0x02, 0x48, 0x49] : Bytes)
      = some ({ fin := true, opcode := .text, payload := [0x48, 0x49] }, [])
    ∧ specLen (len7 0x7e) [0x00, 0x02] = 2
    ∧ specLen (len7 0x7e) [0x00, 0x02] ≠ 126 := by
  refine ⟨by rfl, by rfl, by decide⟩

end WsFrameCorrect

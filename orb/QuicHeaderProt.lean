/-
# QuicHeaderProt — QUIC header protection (RFC 9001 §5.4) over verified EverCrypt

QUIC does NOT send the packet's first byte or its packet number in the clear. On
top of the AEAD packet protection (RFC 9001 §5.3), a second, lighter masking step
— *header protection* (§5.4) — hides the packet-number length (low bits of the
first byte) and the packet-number bytes themselves. A receiver must remove it
BEFORE it can even know how many packet-number bytes there are, so this is the
first thing that touches a real off-the-shelf client's Initial packet.

The mask is 5 bytes derived from a 16-byte *sample* of the protected payload by
running the cipher suite's keystream generator (§5.4.3/§5.4.4). Two suites matter:

  * **AES** (§5.4.3) — the generator is a single raw AES block, `AES-ECB(hp_key,
    sample)`. Every real QUIC v1 Initial packet uses this suite (RFC 9001 §5.2
    mandates AES-128-GCM for Initials), so it is the one that removes an
    off-the-shelf client's header protection.
  * **ChaCha20** (§5.4.4) — the generator is the ChaCha20 block function with
    `counter = sample[0..4]` (little-endian) and `nonce = sample[4..16]`.

The verified `Crypto` seam exposes only the AEADs, not the bare block ciphers, so
header protection was previously out of reach (see the old QUIC-SOCKET-README scope
note). This module adds the two missing crossings: `chacha20Raw`, bound by
`@[extern]` to EverCrypt's verified ChaCha20 block (`EverCrypt_Cipher_chacha20` —
the SAME portable HACL* ChaCha20 the AEAD itself is built from), and (in `Crypto`)
`aesEcbBlock`, the single-block AES permutation (verified-preferred, portable
aws-lc-rs off-x86, matching the AES-GCM dispatch). With them, `IoQuic` removes real
header protection for both suites and decodes the truncated packet number.

RFC 9001 §5.4.1 mask application:
  * long-header first byte: XOR the low 4 bits with `mask[0]` (`& 0x0f`);
  * packet number (1–4 bytes): XOR byte `i` with `mask[1+i]`.
The mask is a keystream XOR, so protect and unprotect are the SAME operation
(`xor_mask_involutive`), and the sample lives strictly AFTER the masked bytes
(RFC fixes the sample offset at `pn_offset + 4`, past the ≤4 packet-number bytes),
so masking never perturbs its own sample.

For the AES cipher suites (RFC 9001 §5.4.3 — the suite a real off-the-shelf
client's Initial uses) the keystream generator is instead `AES-ECB(hp_key,
sample)`, a raw single-block AES permutation. That primitive is the one new
`Crypto` crossing `Crypto.aesEcbBlock` (→ `drorb_aes_ecb_block`); the mask
derivation, the mask application, and the round-trip are otherwise identical (an
XOR against 5 keystream bytes), so both suites share the masking core below and
the same `xor_mask_involutive` round-trip.
-/

import Crypto

namespace QuicHeaderProt

/-! ## (0) The one new verified crossing: the raw ChaCha20 block. -/

/-- EverCrypt's verified ChaCha20 block, `dst = keystream(key,iv,ctr) ⊕ src`
(RFC 8439). Bound to `drorb_chacha20` (ffi/mac_udp.c → `EverCrypt_Cipher_chacha20`,
the portable HACL* ChaCha20). `none` on a bad key(32)/iv(12) size. Feeding a
zero `src` yields the raw keystream — the header-protection mask. -/
@[extern "drorb_chacha20"]
opaque chacha20Raw (key iv : ByteArray) (ctr : UInt32) (src : ByteArray) :
    Option ByteArray

/-- **Assumed property of the verified ChaCha20 block.** On valid key/iv sizes it
is total and length-preserving — it is a keystream XOR (`|out| = |src|`). This is
the functional shadow of the HACL* `Hacl.Impl.Chacha20` spec; it is all header
protection needs (the mask is well-defined and 5 bytes long). No secrecy property
is asserted here — header protection's security is the AEAD's, not this XOR's. -/
axiom chacha20Raw_valid :
  ∀ (key iv : ByteArray) (ctr : UInt32) (src : ByteArray),
    key.size = 32 → iv.size = 12 →
    ∃ ks, chacha20Raw key iv ctr src = some ks ∧ ks.size = src.size

/-! ## (1) The header-protection mask (RFC 9001 §5.4.4, ChaCha20). -/

/-- Little-endian `UInt32` from four bytes (the ChaCha20 header-protection block
counter is `sample[0..4]` little-endian, RFC 9001 §5.4.4). -/
def leU32 (b0 b1 b2 b3 : UInt8) : UInt32 :=
  b0.toUInt32 ||| (b1.toUInt32 <<< 8) ||| (b2.toUInt32 <<< 16) ||| (b3.toUInt32 <<< 24)

/-- Five zero bytes — the plaintext whose ChaCha20 encryption IS the keystream. -/
def zero5 : ByteArray := ByteArray.mk #[0, 0, 0, 0, 0]

/-- The 5-byte ChaCha20 header-protection mask for a 16-byte `sample` (RFC 9001
§5.4.4): `counter = sample[0..4]` (LE), `nonce = sample[4..16]`, `mask =
ChaCha20(hpKey, counter, nonce)[0..5]`. `none` if the sample is short. -/
def chachaHpMask (hpKey sample : ByteArray) : Option ByteArray :=
  let s := sample.toList
  if s.length < 16 then none else
  let ctr := leU32 (s.getD 0 0) (s.getD 1 0) (s.getD 2 0) (s.getD 3 0)
  let nonce : ByteArray := ⟨((s.drop 4).take 12).toArray⟩
  chacha20Raw hpKey nonce ctr zero5

/-- The 5-byte **AES** header-protection mask for a 16-byte `sample` (RFC 9001
§5.4.3): `mask = AES-ECB(hpKey, sample)[0..5]`. The AES suites (which every real
QUIC v1 Initial uses) compute the keystream with a single raw AES block over the
sample, via the verified-preferred / portable-fallback `Crypto.aesEcbBlock`.
`none` if the sample is short or the block cannot be computed. -/
def aesHpMask (hpKey sample : ByteArray) : Option ByteArray :=
  let s := sample.toList
  if s.length < 16 then none else
  (Crypto.aesEcbBlock hpKey ⟨(s.take 16).toArray⟩).map
    (fun blk => ⟨(blk.toList.take 5).toArray⟩)

/-! ## (2) Truncated packet-number decoding (RFC 9000 §A.3). -/

/-- Reconstruct the full packet number from the `pnLenBytes`-byte truncated value
on the wire and the largest expected packet number (RFC 9000 §A.3). For a fresh
Initial (`expected = 0`) this returns the truncated value unchanged. -/
def decodePacketNumber (truncated pnLenBytes expected : Nat) : Nat :=
  let pnWin := 1 <<< (pnLenBytes * 8)
  let pnHwin := pnWin / 2
  let candidate := (expected - expected % pnWin) + truncated
  if candidate + pnHwin ≤ expected ∧ candidate + pnWin < (1 <<< 62) then
    candidate + pnWin
  else if expected + pnHwin < candidate ∧ pnWin ≤ candidate then
    candidate - pnWin
  else
    candidate

/-! ## (3) Applying / removing header protection. -/

/-- A header-protection mask derivation: the cipher-suite keystream generator that
maps a 16-byte ciphertext `sample` to its ≥5-byte mask. `chachaHpMask hpKey` (RFC
9001 §5.4.4) and `aesHpMask hpKey` (§5.4.3) are the two instances; the masking
core below is identical for both — it is only an XOR against the first 5 bytes. -/
abbrev MaskFn := ByteArray → Option ByteArray

/-- XOR the header-protected bytes of `full` in place under a suite-specific mask
derivation `mk`: the low 4 bits of the first byte (long header) and the `pnLen`
packet-number bytes at `pnOff`, against `mk sample`. Protect and unprotect are this
same function (XOR). `none` if the sample (16 bytes at `pnOff + 4`) is short or the
mask cannot be derived. -/
def maskHeaderWith (full : List UInt8) (pnOff pnLen : Nat) (mk : MaskFn) :
    Option (List UInt8) :=
  let sample := (full.drop (pnOff + 4)).take 16
  match mk ⟨sample.toArray⟩ with
  | none => none
  | some mask =>
    let m := mask.toList
    let fb := (full.getD 0 0) ^^^ ((m.getD 0 0) &&& 0x0f)
    let full1 := full.set 0 fb
    let full2 := (List.range pnLen).foldl
      (fun acc i => acc.set (pnOff + i) ((acc.getD (pnOff + i) 0) ^^^ (m.getD (1 + i) 0)))
      full1
    some full2

/-- Apply/remove ChaCha20 header protection (RFC 9001 §5.4.4). -/
def maskHeader (full : List UInt8) (pnOff pnLen : Nat) (hpKey : ByteArray) :
    Option (List UInt8) :=
  maskHeaderWith full pnOff pnLen (chachaHpMask hpKey)

/-- Apply/remove **AES** header protection (RFC 9001 §5.4.3) — the suite every
real QUIC v1 Initial packet uses. Identical masking core, `AES-ECB` keystream. -/
def maskHeaderAes (full : List UInt8) (pnOff pnLen : Nat) (hpKey : ByteArray) :
    Option (List UInt8) :=
  maskHeaderWith full pnOff pnLen (aesHpMask hpKey)

/-- What removing header protection recovers: the unmasked first byte, the
packet-number length it now reveals, the decoded full packet number, and the
reconstructed unprotected header (AAD) through the packet number. -/
structure Unprotected where
  firstByte : UInt8
  pnLen : Nat
  pn : Nat
  header : ByteArray

/-- Remove header protection from a received packet `pkt` whose packet-number
field starts at `pnOff` (RFC 9001 §5.4.1) under a suite-specific mask derivation
`mk`: derive the mask, unmask the first byte to learn `pnLen`, unmask and decode
the packet number, and rebuild the unprotected header (the AEAD additional data).
`expectedPn` seeds the truncated-PN decode. -/
def removeHpWith (pkt : List UInt8) (pnOff : Nat) (mk : MaskFn) (expectedPn : Nat) :
    Option Unprotected :=
  let sample := (pkt.drop (pnOff + 4)).take 16
  match mk ⟨sample.toArray⟩ with
  | none => none
  | some mask =>
    let m := mask.toList
    let fb := (pkt.getD 0 0) ^^^ ((m.getD 0 0) &&& 0x0f)
    let pnLen := (fb &&& 0x03).toNat + 1
    let rawPn := (pkt.drop pnOff).take pnLen
    if rawPn.length ≠ pnLen then none else
    let unPn := (List.range pnLen).map (fun i => (rawPn.getD i 0) ^^^ (m.getD (1 + i) 0))
    let truncated := unPn.foldl (fun a x => a * 256 + x.toNat) 0
    let pn := decodePacketNumber truncated pnLen expectedPn
    let hdr := ((pkt.take pnOff).set 0 fb) ++ unPn
    some { firstByte := fb, pnLen := pnLen, pn := pn, header := ⟨hdr.toArray⟩ }

/-- Remove **ChaCha20** header protection (RFC 9001 §5.4.4). -/
def removeHp (pkt : List UInt8) (pnOff : Nat) (hpKey : ByteArray) (expectedPn : Nat) :
    Option Unprotected :=
  removeHpWith pkt pnOff (chachaHpMask hpKey) expectedPn

/-- Remove **AES** header protection (RFC 9001 §5.4.3) — the suite a real
off-the-shelf client's Initial packet arrives under. Same removal core, `AES-ECB`
keystream (`Crypto.aesEcbBlock`). -/
def removeHpAes (pkt : List UInt8) (pnOff : Nat) (hpKey : ByteArray) (expectedPn : Nat) :
    Option Unprotected :=
  removeHpWith pkt pnOff (aesHpMask hpKey) expectedPn

/-! ## (4) Header protection is self-inverse (protect ∘ unprotect = id). -/

/-- A byte XORed with the same mask twice is unchanged — the algebraic heart of
"apply and remove header protection are the same XOR". -/
theorem xor_mask_involutive (b m : UInt8) : (b ^^^ m) ^^^ m = b := by
  have h : ∀ x y : UInt8, (x ^^^ y).toBitVec = x.toBitVec ^^^ y.toBitVec := fun _ _ => rfl
  apply UInt8.toBitVec_inj.mp
  rw [h, h]
  simp [BitVec.xor_assoc, BitVec.xor_self, BitVec.xor_zero]

/-- Masking the low 4 bits of the first byte is self-inverse: this is the
first-byte case of header protection round-tripping. -/
theorem xor_lowbits_involutive (b m : UInt8) :
    (b ^^^ (m &&& 0x0f)) ^^^ (m &&& 0x0f) = b :=
  xor_mask_involutive b (m &&& 0x0f)

end QuicHeaderProt

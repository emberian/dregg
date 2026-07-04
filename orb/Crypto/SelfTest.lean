/-
Crypto.SelfTest — exercises the crypto FFI seam against published test vectors.

This is NOT part of the trusted core. It is a runnable check that the C shim,
as linked (HACL*/EverCrypt — verified crypto), actually implements the primitives `Crypto.lean`
axiomatizes. Run: `lake exe crypto-selftest`. Exit code 0 = all vectors passed.

Vectors: RFC 8439 style AEAD roundtrip, RFC 7748 §5.2 X25519, RFC 8032 §7.1
Ed25519 test 1, RFC 5869 §A.1 HKDF-SHA256 test 1, FIPS-180 SHA-256/384 of "abc".
-/
import Crypto

namespace Crypto.SelfTest

/-- Parse a hex string into a `ByteArray`. Returns `#[]` on any bad nibble; the
vectors below are all well-formed so this stays total and simple. -/
def ofHex (s : String) : ByteArray := Id.run do
  let cs := s.toList.filter (· ≠ ' ')
  let hexVal : Char → Option UInt8 := fun c =>
    if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat).toUInt8
    else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10).toUInt8
    else if 'A' ≤ c ∧ c ≤ 'F' then some (c.toNat - 'A'.toNat + 10).toUInt8
    else none
  let rec go : List Char → ByteArray → ByteArray
    | hi :: lo :: rest, acc =>
      match hexVal hi, hexVal lo with
      | some h, some l => go rest (acc.push (h * 16 + l))
      | _, _ => acc
    | _, acc => acc
  go cs (ByteArray.mk #[])

def toHex (b : ByteArray) : String :=
  let d := "0123456789abcdef".toList.toArray
  b.toList.foldl (fun s x =>
    s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

/-- A single named check. -/
structure Check where
  name : String
  ok   : Bool

def eqBA (a b : ByteArray) : Bool := a.toList == b.toList

/-- `ByteArray` carries no `BEq`, so compare `Option ByteArray` structurally. -/
def optEq (a b : Option ByteArray) : Bool :=
  match a, b with
  | some x, some y => eqBA x y
  | none, none => true
  | _, _ => false

open Crypto

def checks : List Check := Id.run do
  let mut cs : List Check := []

  -- 1. ChaCha20-Poly1305 seal/open roundtrip + tamper rejection.
  let key   := ofHex (String.join (List.replicate 32 "01"))
  let nonce := ofHex "000000000000000000000000"
  let ad    := ofHex "50515253c0c1c2c3c4c5c6c7"
  let msg   := "Ladies and Gentlemen of the class of '99".toUTF8
  let ct := chachaSeal key nonce ad msg
  let round := match ct with
    | some c => optEq (chachaOpen key nonce ad c) (some msg)
    | none => false
  cs := cs ++ [⟨"chacha20poly1305 roundtrip", round⟩]
  let tamperRejected := match ct with
    | some c =>
      let bad := (c.toList.set 0 (c.toList.headD 0 ^^^ 0xff))
      optEq (chachaOpen key nonce ad (ByteArray.mk bad.toArray)) none
    | none => false
  cs := cs ++ [⟨"chacha20poly1305 tamper→none", tamperRejected⟩]

  -- 2. X25519, RFC 7748 §5.2 vector 1.
  let sc  := ofHex "a546e36bf0527c9d3b16154b82465edd62144c0ac1fc5a18506a2244ba449ac4"
  let u   := ofHex "e6db6867583030db3594c1a424b15f7c726624ec26b3353b10a903a6d0ab1c4c"
  let exp := ofHex "c3da55379de9c6908e94ea4df28d084f32eccf03491c71f754b4075577a28552"
  cs := cs ++ [⟨"x25519 RFC7748 §5.2", optEq (x25519 sc u) (some exp)⟩]

  -- 3. Ed25519 verify, RFC 8032 §7.1 test 1 (empty message).
  let pub := ofHex "d75a980182b10ab7d54bfed3c964073a0ee172f3daa62325af021a68f707511a"
  let sig := ofHex ("e5564300c360ac729086e2cc806e828a84877f1eb8e5d974d873e065224901555f"
                   ++ "b8821590a33bacc61e39701cf9b46bd25bf5f0595bbe24655141438e7a100b")
  cs := cs ++ [⟨"ed25519 verify RFC8032 §7.1", ed25519Verify pub ByteArray.empty sig⟩]
  let badSig := ByteArray.mk ((sig.toList.set 0 (sig.toList.headD 0 ^^^ 0x01)).toArray)
  cs := cs ++ [⟨"ed25519 bad-sig→false", ed25519Verify pub ByteArray.empty badSig == false⟩]

  -- 4. HKDF-SHA256, RFC 5869 §A.1 test 1.
  let ikm  := ofHex (String.join (List.replicate 22 "0b"))
  let salt := ofHex "000102030405060708090a0b0c"
  let info := ofHex "f0f1f2f3f4f5f6f7f8f9"
  let prkE := ofHex "077709362c2e32df0ddc3f0dc47bba6390b6c73bb50f9c3122ec844ad7c2b3e5"
  let okmE := ofHex ("3cb25f25faacd57a90434f64d0362f2a2d2d0a90cf1a5a4c5db02d56ecc4c5bf3"
                   ++ "4007208d5b887185865")
  let prk := hkdfExtract salt ikm
  cs := cs ++ [⟨"hkdf-sha256 extract RFC5869", optEq prk (some prkE)⟩]
  let okm := match prk with
    | some p => hkdfExpand p info 42
    | none => none
  cs := cs ++ [⟨"hkdf-sha256 expand RFC5869", optEq okm (some okmE)⟩]

  -- 5. SHA-256 / SHA-384 of "abc" (FIPS-180).
  let abc := "abc".toUTF8
  cs := cs ++ [⟨"sha256(abc)",
    eqBA (sha256 abc)
      (ofHex "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad")⟩]
  cs := cs ++ [⟨"sha384(abc)",
    eqBA (sha384 abc)
      (ofHex ("cb00753f45a35e8bb5a03d699ac65007272c32ab0eded1631a8b605a43ff5bed"
            ++ "8086072ba1e7cc2358baeca134c825a7"))⟩]

  -- 6. AES-256-GCM roundtrip + tamper (verified EverCrypt where AES-NI is
  -- present, portable aws-lc-rs fallback otherwise — either way, must hold).
  let ak := ofHex (String.join (List.replicate 32 "02"))
  let an := ofHex "000000000000000000000001"
  let am := "aes-gcm probe".toUTF8
  match aesGcmSeal ak an ad am with
  | some c =>
      cs := cs ++ [⟨"aes256gcm roundtrip", optEq (aesGcmOpen ak an ad c) (some am)⟩]
      let bad := ByteArray.mk ((c.toList.set 0 (c.toList.headD 0 ^^^ 0xff)).toArray)
      cs := cs ++ [⟨"aes256gcm tamper→none", optEq (aesGcmOpen ak an ad bad) none⟩]
  | none => cs := cs ++ [⟨"aes256gcm seal produced ciphertext", false⟩]

  -- 7. AES-128-GCM — the RFC 9001 §5.2 QUIC Initial cipher (16-byte key selects
  -- AES-128). Roundtrip + tamper, plus the NIST GCM case-1 known-answer (all-zero
  -- key/IV, empty plaintext/AAD ⇒ tag 58e2fccefa7e3061367f1d57a4e7455a).
  let ak128 := ofHex (String.join (List.replicate 16 "02"))
  let am128 := "aes-128-gcm quic initial".toUTF8
  match aesGcmSeal ak128 an ad am128 with
  | some c =>
      cs := cs ++ [⟨"aes128gcm roundtrip", optEq (aesGcmOpen ak128 an ad c) (some am128)⟩]
      let bad := ByteArray.mk ((c.toList.set 0 (c.toList.headD 0 ^^^ 0xff)).toArray)
      cs := cs ++ [⟨"aes128gcm tamper→none", optEq (aesGcmOpen ak128 an ad bad) none⟩]
  | none => cs := cs ++ [⟨"aes128gcm seal produced ciphertext", false⟩]
  let zk := ofHex (String.join (List.replicate 16 "00"))
  let zn := ofHex "000000000000000000000000"
  cs := cs ++ [⟨"aes128gcm NIST GCM case-1 tag",
    optEq (aesGcmSeal zk zn ByteArray.empty ByteArray.empty)
      (some (ofHex "58e2fccefa7e3061367f1d57a4e7455a"))⟩]

  return cs

def main : IO UInt32 := do
  let cs := checks
  for c in cs do
    IO.println s!"[{if c.ok then "PASS" else "FAIL"}] {c.name}"
  let failed := cs.filter (!·.ok)
  if failed.isEmpty then
    IO.println s!"\nall {cs.length} crypto-FFI vectors passed"
    return 0
  else
    IO.eprintln s!"\n{failed.length} of {cs.length} FAILED"
    return 1

end Crypto.SelfTest

def main : IO UInt32 := Crypto.SelfTest.main

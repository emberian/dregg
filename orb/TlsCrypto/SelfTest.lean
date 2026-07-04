/-
TlsCrypto.SelfTest — the TLS 1.3 key schedule against RFC 8448 vectors.

Runs the key schedule of `TlsCrypto` on the *linked* EverCrypt and checks it
against the RFC 8448 §3 "Simple 1-RTT Handshake" trace. These values are
cipher-suite-independent for any SHA-256 suite: they exercise HKDF-Extract,
HKDF-Expand-Label, and the transcript hash. Also runs a real ChaCha20-Poly1305
record roundtrip through `recordSeal`/`recordOpen`.

Run: `lake exe tls-keyschedule-selftest`. Exit code 0 = all vectors passed.
-/
import TlsCrypto

namespace TlsCrypto.SelfTest

open Crypto TlsCrypto

/-- Parse a hex string (spaces ignored) into a `ByteArray`. -/
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
  b.toList.foldl (fun s x => s ++ s!"{d[(x.toNat / 16)]!}{d[(x.toNat % 16)]!}") ""

def eqBA (a b : ByteArray) : Bool := a.toList == b.toList

def optEq (a : Option ByteArray) (b : ByteArray) : Bool :=
  match a with
  | some x => eqBA x b
  | none => false

structure Check where
  name : String
  ok : Bool

def checks : List Check := Id.run do
  let mut cs : List Check := []

  -- Transcript hash of the empty message list, SHA-256("").
  let emptyHashE := ofHex
    "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855"
  cs := cs ++ [⟨"SHA-256(\"\") empty transcript hash", eqBA emptyHash emptyHashE⟩]

  -- RFC 8448 §3: the "early" extract secret (no PSK).
  let earlyE := ofHex
    "33ad0a1c607ec03b09e6cd9893680ce210adf300aa1f2660e1b22e10f170f92a"
  cs := cs ++ [⟨"RFC8448 early secret", optEq earlySecretNoPsk earlyE⟩]

  -- RFC 8448 §3: Derive-Secret(early, "derived", "").
  let derivedE := ofHex
    "6f2615a108c702c5678f54fc9dbab69716c076189c48250cebeac3576c3611ba"
  let derived := match earlySecretNoPsk with
    | some es => deriveSecret es "derived".toUTF8 emptyHash
    | none => none
  cs := cs ++ [⟨"RFC8448 Derive-Secret(early,\"derived\",\"\")",
    match derived with | some d => eqBA d derivedE | none => false⟩]

  -- A real ChaCha20-Poly1305 record roundtrip through the record layer:
  -- derive keys from a nonzero secret, seal, then open at the same sequence.
  let secret := ofHex (String.join (List.replicate 32 "2a"))
  match trafficKeys secret with
  | some rk =>
    let msg := "hello tls 1.3 record layer".toUTF8
    let ad := recordAD (msg.size + 16)
    match recordSeal rk 0 ad msg with
    | some ct =>
      cs := cs ++ [⟨"record seal→open roundtrip (seq 0)",
        optEq (recordOpen rk 0 ad ct) msg⟩]
      -- Opening at the wrong sequence must fail (nonce mismatch → bad tag).
      cs := cs ++ [⟨"record open at wrong seq → none",
        (recordOpen rk 1 ad ct).isNone⟩]
      -- A one-byte tamper must fail to open.
      let bad := ByteArray.mk (ct.toList.set 0 (ct.toList.headD 0 ^^^ 0xff)).toArray
      cs := cs ++ [⟨"record tamper → none", (recordOpen rk 0 ad bad).isNone⟩]
    | none => cs := cs ++ [⟨"record seal produced none (unexpected)", false⟩]
  | none => cs := cs ++ [⟨"trafficKeys produced none (unexpected)", false⟩]

  return cs

def main : IO UInt32 := do
  let cs := checks
  for c in cs do
    IO.println s!"[{if c.ok then "PASS" else "FAIL"}] {c.name}"
  let failed := cs.filter (!·.ok)
  if failed.isEmpty then
    IO.println s!"\nall {cs.length} TLS key-schedule / record vectors passed"
    return 0
  else
    IO.eprintln s!"\n{failed.length} of {cs.length} FAILED"
    return 1

end TlsCrypto.SelfTest

def main : IO UInt32 := TlsCrypto.SelfTest.main

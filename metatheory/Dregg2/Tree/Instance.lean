/-
# Dregg2.Tree.Instance: the executable instance (hashes, wire formats of certificates)

Fixes the three hashes every theorem in `Dregg2.Tree` leaves abstract:

    node  H(x)   = SHAKE256("dregg.tree.node.v1" ‖ 0x00 ‖ x, 32)      (Merkle.shakeH)
    flat  F(x)   = SHAKE256("dregg.tree.flat.v1" ‖ 0x00 ‖ x, 32)      (schemas, tables)
    mmr   h(l)   = int_be(SHAKE256("dregg.tree.mmr.v1" ‖ 0x00 ‖ enc(arr(map intItem l)), 32))

The MMR hash frames its integer list with the same canonical CBOR (`intItem`, `Cbor.enc`), which
`canon_injective` makes injective, so a collision of `h` at distinct lists is a SHAKE256 collision
at distinct inputs (`Spec.mmrHash_coll`, for lists of 256-bit naturals: the MMR hashes only
digests and leaves). The deployed leaf hash is cSHAKE256 (minidregg); the
statements do not change when these do.

Wire formats (JSON envelope; every value inside is canonical CBOR in hex, read by the proved
`ofCanonicalBytes`; digests and keys are hex): see `docs/automata/tree/FORMAT.md`.
-/
import Dregg2.Tree.Cert
import Lean.Data.Json

namespace Dregg2.Tree.Instance

open Lean (Json)
open Cbor

def flatF (x : List UInt8) : Digest :=
  fix32 (Dregg2.Crypto.Keccak.shake256 ("dregg.tree.flat.v1".toUTF8.toList ++ [0] ++ x) 32)

/-- The MMR's input framing: canonical CBOR of the integer list. -/
def mmrInput (l : List Int) : List UInt8 :=
  "dregg.tree.mmr.v1".toUTF8.toList ++ [0] ++ enc (.arr (l.map intItem))

def mmrHash (l : List Int) : Int :=
  (ofBE (fix32 (Dregg2.Crypto.Keccak.shake256 (mmrInput l) 32)) : Int)

/-! ## Hex -/

def hexDigit (n : Nat) : Char := "0123456789abcdef".toList.getD n '0'

def toHex (b : List UInt8) : String :=
  String.ofList (b.flatMap fun x => [hexDigit (x.toNat / 16), hexDigit (x.toNat % 16)])

def nibble (c : Char) : Option Nat :=
  if '0' ≤ c ∧ c ≤ '9' then some (c.toNat - '0'.toNat)
  else if 'a' ≤ c ∧ c ≤ 'f' then some (c.toNat - 'a'.toNat + 10)
  else none

def ofHexChars : List Char → Option (List UInt8)
  | [] => some []
  | a :: b :: r => do
    let x ← nibble a
    let y ← nibble b
    let rest ← ofHexChars r
    pure (UInt8.ofNat (16 * x + y) :: rest)
  | [_] => none

def ofHex (s : String) : Option (List UInt8) := ofHexChars s.toList

/-- Digests as 32-byte big-endian hex (the MMR root is an `Int` below `2^256`). -/
def intToHex32 (n : Int) : String := toHex (be 32 n.toNat)

#guard toHex [0x00, 0xab, 0xff] == "00abff"
#guard ofHex "00abff" == some [0x00, 0xab, 0xff]
#guard ofHex "0g" == none

/-! ## Reading certificates -/

abbrev R := Except String

def getStr (j : Json) (k : String) : R String := do (← j.getObjVal? k).getStr?
def getHex (j : Json) (k : String) : R (List UInt8) := do
  match ofHex (← getStr j k) with
  | some b => pure b
  | none => throw s!"field {k}: not lowercase hex"
def hexOf (j : Json) : R (List UInt8) := do
  match ofHex (← j.getStr?) with
  | some b => pure b
  | none => throw "not lowercase hex"
def getNat (j : Json) (k : String) : R Nat := do (← j.getObjVal? k).getNat?
def getArr (j : Json) (k : String) : R (Array Json) := do (← j.getObjVal? k).getArr?

/-- A canonical value from CBOR hex, through the proved reader. -/
def valueOfHex (s : String) : R JVal := do
  match ofHex s with
  | none => throw "value: not hex"
  | some b => match ofCanonicalBytes b with
    | some v => pure v
    | none => throw "value: not canonical CBOR of the model"

def stepOfJson (j : Json) : R Step :=
  match j.getObjVal? "key", j.getObjVal? "idx" with
  | .ok k, _ => do .key <$> hexOf k
  | _, .ok i => do .idx <$> i.getNat?
  | _, _ => throw "path step: want {key} or {idx}"

def pathOfJson (j : Json) : R Path := do (← j.getArr?).toList.mapM stepOfJson

def entriesOfJson (j : Json) : R (List (List UInt8 × Digest)) := do
  (← j.getArr?).toList.mapM fun e => do
    let a ← e.getArr?
    if a.size != 2 then throw "obj entry: want [key, digest]"
    pure (← hexOf a[0]!, ← hexOf a[1]!)

partial def openingOfJson (j : Json) : R Opening := do
  if let .ok v := j.getObjVal? "here" then return .here (← valueOfHex (← v.getStr?))
  if let .ok ds := j.getObjVal? "arr" then
    return .arr (← (← ds.getArr?).toList.mapM hexOf) (← openingOfJson (← j.getObjVal? "rest"))
  if let .ok es := j.getObjVal? "obj" then
    return .obj (← entriesOfJson es) (← openingOfJson (← j.getObjVal? "rest"))
  if let .ok ds := j.getObjVal? "absent_arr" then
    return .absentArr (← (← ds.getArr?).toList.mapM hexOf)
  if let .ok es := j.getObjVal? "absent_obj" then
    return .absentObj (← entriesOfJson es)
  throw "opening: want here/arr/obj/absent_arr/absent_obj"

def bitsOfStr (s : String) : R (List Bool) :=
  s.toList.mapM fun c => if c = '1' then pure true else if c = '0' then pure false
    else throw "run label: want a string of 0/1"

partial def runOfJson (j : Json) : R (Run (List Bool)) := do
  let q ← bitsOfStr (← getStr j "q")
  match j.getObjVal? "kids" with
  | .ok ks => return .node q (← (← ks.getArr?).toList.mapM runOfJson)
  | .error _ => return .leaf q

def verdictOfStr : String → R FieldVerdict
  | "absent" => pure .absent
  | "non_string" => pure .nonString
  | "accept" => pure .accept
  | "reject" => pure .reject
  | s => throw s!"verdict {s}"

def verdictStr : FieldVerdict → String
  | .absent => "absent" | .nonString => "non_string" | .accept => "accept" | .reject => "reject"

def evidenceOfJson (j : Json) : R RecEvidence := do
  let root ← getHex j "root"
  if let .ok rf := j.getObjVal? "refute" then
    return .refute root (← getNat rf "j") (← openingOfJson (← rf.getObjVal? "opening"))
  if let .ok fl := j.getObjVal? "full" then
    return .full root (← (← fl.getArr?).toList.mapM openingOfJson)
  throw "record: want refute or full"

end Dregg2.Tree.Instance

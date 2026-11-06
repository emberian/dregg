/-
# Dregg2.Tree.Value: the JSON value model, its canonical CBOR encoding, and `canon_injective`

`JVal` is a JSON value after projection (`Dregg2.Tree.Json`): strings are their decoded UTF-8
bytes (escapes resolved, so `"p"` and `"p"` are one leaf), numbers are exact decimals with
one representative per value, and objects are lists of `(key, value)` entries.

**Numbers.** `int n` is an integer value; `dec m e` is the non-integer `m · 10^e` with `e < 0` and
`10 ∤ m` (`decCanon`; the exponent is also at least `-2^64`, `expOk`). Every finite decimal has exactly one such form: integers (including `1.0`,
`10e-1`, `1e400`, `-0`) are `int`, the rest are `dec` (`Json.mkNum`). There are no floats: RFC 8785
(JCS) canonicalizes IEEE doubles and so aliases `9007199254740993` with `9007199254740992` (pinned
in `Json`); this model does not.

**Wire form: deterministic CBOR, RFC 8949 §4.2.1.** `null`/`false`/`true` are simple 22/20/21;
integers are major 0/1 when they fit 64 bits and bignums (tags 2/3, minimal big-endian bytes)
otherwise; `dec m e` is tag 4 `[e, m]` (decimal fraction, §3.4.4); strings are major 3; arrays
major 4; objects major 5. `WF` is the canonical-form predicate: admitted, every string valid UTF-8,
`dec` canonical, and object keys strictly increasing in the bytewise order of their encodings
(§4.2.1 rule 3), which also refuses duplicate keys.

**Theorems.** `toItem_injective` (the model → items map), `canon_injective` (encoding is injective
on admitted values; no ordering hypothesis needed), and `ofCanonicalBytes_sound`: the checkers'
byte reader returns `some v` only when `v` is `WF` and the bytes are exactly `encode v`. With
`canon_injective` that makes canonical bytes and canonical trees the same object, which is the
morphism the tree root and a byte commitment need to name one record.
-/
import Dregg2.Tree.Cbor

namespace Dregg2.Tree

open Cbor

/-- A JSON value in the projected model. -/
inductive JVal where
  | null
  | bool (b : Bool)
  | int (n : Int)
  | dec (m : Int) (e : Int)
  | str (s : List UInt8)
  | arr (xs : List JVal)
  | obj (kvs : List (List UInt8 × JVal))
  deriving Repr, Inhabited

namespace JVal

/-- A scalar (a leaf of the tree). -/
def isScalar : JVal → Bool
  | .arr _ | .obj _ => false
  | _ => true

mutual
/-- Structural equality, executable. -/
def beq : JVal → JVal → Bool
  | .null, .null => true
  | .bool a, .bool b => a == b
  | .int a, .int b => a == b
  | .dec m e, .dec m' e' => m == m' && e == e'
  | .str a, .str b => a == b
  | .arr xs, .arr ys => beqList xs ys
  | .obj a, .obj b => beqKVs a b
  | _, _ => false
def beqList : List JVal → List JVal → Bool
  | [], [] => true
  | x :: xs, y :: ys => beq x y && beqList xs ys
  | _, _ => false
def beqKVs : List (List UInt8 × JVal) → List (List UInt8 × JVal) → Bool
  | [], [] => true
  | (k, x) :: xs, (k', y) :: ys => k == k' && beq x y && beqKVs xs ys
  | _, _ => false
end

mutual
theorem beq_iff : ∀ a b : JVal, beq a b = true ↔ a = b
  | .null, b => by cases b <;> simp [beq]
  | .bool x, b => by cases b <;> simp [beq]
  | .int x, b => by cases b <;> simp [beq]
  | .dec m e, b => by cases b <;> simp [beq]
  | .str x, b => by cases b <;> simp [beq]
  | .arr xs, b => by cases b <;> simp [beq, beqList_iff xs]
  | .obj kvs, b => by cases b <;> simp [beq, beqKVs_iff kvs]
theorem beqList_iff : ∀ xs ys : List JVal, beqList xs ys = true ↔ xs = ys
  | [], ys => by cases ys <;> simp [beqList]
  | x :: xs, ys => by cases ys <;> simp [beqList, beq_iff x, beqList_iff xs]
theorem beqKVs_iff : ∀ a b : List (List UInt8 × JVal), beqKVs a b = true ↔ a = b
  | [], b => by cases b <;> simp [beqKVs]
  | (k, x) :: xs, b => by
    cases b with
    | nil => simp [beqKVs]
    | cons p ys =>
      obtain ⟨k', y⟩ := p
      simp [beqKVs, beq_iff x, beqKVs_iff xs, and_assoc]
end

instance : DecidableEq JVal := fun a b => decidable_of_iff _ (beq_iff a b)
instance : BEq JVal := ⟨beq⟩

end JVal

/-! ## Numbers in CBOR -/

/-- Minimal big-endian bytes of a natural (empty for 0). -/
def natBytes (n : Nat) : List UInt8 :=
  if h : n = 0 then [] else natBytes (n / 256) ++ [UInt8.ofNat (n % 256)]
termination_by n
decreasing_by omega

theorem ofBE_natBytes (n : Nat) : ofBE (natBytes n) = n := by
  induction n using Nat.strongRecOn with
  | _ n ih =>
    unfold natBytes
    by_cases h : n = 0
    · simp [h, ofBE]
    · simp only [h, dite_false, ofBE_append_single]
      rw [ih (n / 256) (by omega)]
      have : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
        simp [UInt8.toNat_ofNat'] <;> omega
      rw [this]; omega

/-- An integer as a CBOR item: major 0/1 within 64 bits, bignum tag 2/3 beyond (RFC 8949 §3.4.3). -/
def intItem (n : Int) : Item :=
  if 0 ≤ n then
    if n.toNat < 2 ^ 64 then .uint n.toNat else .tag 2 (.bytes (natBytes n.toNat))
  else
    if (-1 - n).toNat < 2 ^ 64 then .nint (-1 - n).toNat else .tag 3 (.bytes (natBytes (-1 - n).toNat))

/-! ## The model as items -/

mutual
/-- The CBOR item of a value. -/
def toItem : JVal → Item
  | .null => .simple 22
  | .bool false => .simple 20
  | .bool true => .simple 21
  | .int n => intItem n
  | .dec m e => .tag 4 (.arr [intItem e, intItem m])
  | .str s => .text s
  | .arr xs => .arr (toItems xs)
  | .obj kvs => .map (toPairs kvs)
def toItems : List JVal → List Item
  | [] => []
  | x :: xs => toItem x :: toItems xs
def toPairs : List (List UInt8 × JVal) → List (Item × Item)
  | [] => []
  | (k, v) :: kvs => (.text k, toItem v) :: toPairs kvs
end

theorem toItems_length : ∀ xs : List JVal, (toItems xs).length = xs.length
  | [] => rfl
  | _ :: xs => by simp [toItems, toItems_length xs]

theorem toPairs_length : ∀ kvs : List (List UInt8 × JVal), (toPairs kvs).length = kvs.length
  | [] => rfl
  | _ :: kvs => by simp [toPairs, toPairs_length kvs]

/-- The canonical encoding of a value. -/
def encode (v : JVal) : List UInt8 := enc (toItem v)

/-- The admitted domain of a value: its item is admitted. -/
def Admitted (v : JVal) : Prop := Adm (toItem v)

/-! ## Canonical form -/

/-- RFC 3629 UTF-8 well-formedness (shortest forms, no surrogates, at most U+10FFFF). -/
def utf8Valid : List UInt8 → Bool
  | [] => true
  | b :: r =>
    let x := b.toNat
    if x < 0x80 then utf8Valid r
    else
      let cont (c : UInt8) := 0x80 ≤ c.toNat ∧ c.toNat < 0xC0
      match r with
      | c1 :: r1 =>
        if 0xC2 ≤ x ∧ x < 0xE0 then cont c1 && utf8Valid r1
        else
          match r1 with
          | c2 :: r2 =>
            if x = 0xE0 then (0xA0 ≤ c1.toNat ∧ c1.toNat < 0xC0) && cont c2 && utf8Valid r2
            else if (0xE1 ≤ x ∧ x < 0xED) ∨ (0xEE ≤ x ∧ x < 0xF0) then
              cont c1 && cont c2 && utf8Valid r2
            else if x = 0xED then (0x80 ≤ c1.toNat ∧ c1.toNat < 0xA0) && cont c2 && utf8Valid r2
            else
              match r2 with
              | c3 :: r3 =>
                if x = 0xF0 then (0x90 ≤ c1.toNat ∧ c1.toNat < 0xC0) && cont c2 && cont c3 && utf8Valid r3
                else if 0xF1 ≤ x ∧ x < 0xF4 then cont c1 && cont c2 && cont c3 && utf8Valid r3
                else if x = 0xF4 then (0x80 ≤ c1.toNat ∧ c1.toNat < 0x90) && cont c2 && cont c3 && utf8Valid r3
                else false
              | [] => false
          | [] => false
      | [] => false

/-- Bytewise lexicographic strict order. -/
def lexLt : List UInt8 → List UInt8 → Bool
  | [], [] => false
  | [], _ :: _ => true
  | _ :: _, [] => false
  | a :: as, b :: bs => a < b || (a == b && lexLt as bs)

/-- The map-key order of RFC 8949 §4.2.1: bytewise lexicographic on the encoded keys. -/
def keyLt (a b : List UInt8) : Bool := lexLt (enc (.text a)) (enc (.text b))

/-- Strictly increasing keys (no duplicates). -/
def keysSorted : List (List UInt8 × JVal) → Bool
  | [] => true
  | [_] => true
  | (a, _) :: (b, v) :: r => keyLt a b && keysSorted ((b, v) :: r)

/-- A canonical decimal: a non-integer value. -/
def decCanon (m e : Int) : Bool := e < 0 && m % 10 != 0

/-- RFC 8949 §3.4.4: a decimal fraction's exponent is major type 0/1, never a bignum, so a
canonical exponent lies in `[-2^64, 0)` (codex round 1, finding 3). -/
def expOk (e : Int) : Bool := decide (-(2 ^ 64 : Int) ≤ e)

mutual
/-- **`WF`**, the canonical form, decidable. -/
def wf : JVal → Bool
  | .dec m e => decCanon m e && expOk e
  | .str s => utf8Valid s
  | .arr xs => wfList xs
  | .obj kvs => keysSorted kvs && wfKVs kvs
  | _ => true
def wfList : List JVal → Bool
  | [] => true
  | x :: xs => wf x && wfList xs
def wfKVs : List (List UInt8 × JVal) → Bool
  | [] => true
  | (k, v) :: kvs => utf8Valid k && wf v && wfKVs kvs
end

/-- Canonical and admitted: what the checkers accept. -/
def WF (v : JVal) : Prop := wf v = true ∧ Admitted v

instance (v : JVal) : Decidable (WF v) := by
  unfold WF Admitted; rw [← adm_iff]; infer_instance

/-! ## Reading canonical bytes -/

mutual
/-- Items back to values (partial: refuses items outside the model's image). -/
def ofItem : Item → Option JVal
  | .simple 22 => some .null
  | .simple 20 => some (.bool false)
  | .simple 21 => some (.bool true)
  | .uint n => some (.int n)
  | .nint n => some (.int (-1 - (n : Int)))
  | .tag 2 (.bytes b) => some (.int (ofBE b))
  | .tag 3 (.bytes b) => some (.int (-1 - (ofBE b : Int)))
  | .tag 4 (.arr [e, m]) =>
    match ofItem e, ofItem m with
    | some (.int e), some (.int m) => some (.dec m e)
    | _, _ => none
  | .text s => some (.str s)
  | .arr xs => (ofItems xs).map .arr
  | .map kvs => (ofPairs kvs).map .obj
  | _ => none
def ofItems : List Item → Option (List JVal)
  | [] => some []
  | x :: xs =>
    match ofItem x, ofItems xs with
    | some v, some vs => some (v :: vs)
    | _, _ => none
def ofPairs : List (Item × Item) → Option (List (List UInt8 × JVal))
  | [] => some []
  | (.text k, x) :: xs =>
    match ofItem x, ofPairs xs with
    | some v, some vs => some ((k, v) :: vs)
    | _, _ => none
  | _ => none
end

theorem ofItem_intItem (n : Int) : ofItem (intItem n) = some (.int n) := by
  unfold intItem
  by_cases h0 : 0 ≤ n
  · by_cases h1 : n.toNat < 2 ^ 64
    · simp only [h0, h1, if_true, ofItem, Option.some.injEq, JVal.int.injEq]; omega
    · simp only [h0, h1, if_true, if_false, ofItem, ofBE_natBytes, Option.some.injEq,
        JVal.int.injEq]; omega
  · by_cases h1 : (-1 - n).toNat < 2 ^ 64
    · simp only [h0, h1, if_true, if_false, ofItem, Option.some.injEq, JVal.int.injEq]; omega
    · simp only [h0, h1, if_false, ofItem, ofBE_natBytes, Option.some.injEq, JVal.int.injEq]
      omega

mutual
/-- The model's items read back: `ofItem` is a left inverse of `toItem`. -/
theorem ofItem_toItem : ∀ v : JVal, ofItem (toItem v) = some v
  | .null => by simp [toItem, ofItem]
  | .bool false => by simp [toItem, ofItem]
  | .bool true => by simp [toItem, ofItem]
  | .int n => by simp only [toItem, ofItem_intItem]
  | .dec m e => by simp [toItem, ofItem, ofItem_intItem]
  | .str s => by simp [toItem, ofItem]
  | .arr xs => by simp [toItem, ofItem, ofItems_toItems xs]
  | .obj kvs => by simp [toItem, ofItem, ofPairs_toPairs kvs]
theorem ofItems_toItems : ∀ xs : List JVal, ofItems (toItems xs) = some xs
  | [] => by simp [toItems, ofItems]
  | x :: xs => by simp [toItems, ofItems, ofItem_toItem x, ofItems_toItems xs]
theorem ofPairs_toPairs : ∀ kvs : List (List UInt8 × JVal), ofPairs (toPairs kvs) = some kvs
  | [] => by simp [toPairs, ofPairs]
  | (k, v) :: kvs => by simp [toPairs, ofPairs, ofItem_toItem v, ofPairs_toPairs kvs]
end

theorem toItem_injective {a b : JVal} (h : toItem a = toItem b) : a = b := by
  have := ofItem_toItem a
  rw [h, ofItem_toItem b] at this
  exact (Option.some.inj this).symm

instance (v : JVal) : Decidable (Admitted v) := by
  unfold Admitted; rw [← adm_iff]; infer_instance

/-- ⚑ **`canon_injective`** — canonical encoding is injective on the model: two admitted values
with one encoding are the same value. Holds without `WF`. What is proved, and what is not (codex
round 1, finding 5): each tree has one byte string and each byte string at most one tree (this
theorem, `ofCanonicalBytes_sound`); two `WF` objects whose entry lists are permutations of each
other are equal (`Spec.wf_unique_obj`, one level, identical entries). That `Json.parse` maps two
spellings of one JSON value to one tree (recursive key-order and number-spelling equivalence) is
NOT a theorem; it is pinned by `#guard`s in `Json.lean`. -/
theorem canon_injective {a b : JVal} (ha : Admitted a) (hb : Admitted b)
    (h : encode a = encode b) : a = b :=
  toItem_injective (enc_injective ha hb h)

/-- Prefix-free form (what the Merkle frames use). -/
theorem canon_prefix_injective {a b : JVal} (ha : Admitted a) (hb : Admitted b) {r s : List UInt8}
    (h : encode a ++ r = encode b ++ s) : a = b ∧ r = s := by
  obtain ⟨h1, h2⟩ := enc_prefix_injective ha hb h
  exact ⟨toItem_injective h1, h2⟩

/-- **The checkers' byte reader.** Decode one item, map it into the model, and accept only if
the value is `WF` and re-encodes to exactly the input bytes. -/
def ofCanonicalBytes (b : List UInt8) : Option JVal :=
  match decodeAll b with
  | none => none
  | some i =>
    match ofItem i with
    | none => none
    | some v => if decide (WF v) && encode v == b then some v else none

/-- ⚑ What the reader returns is canonical and IS the input's canonical value. -/
theorem ofCanonicalBytes_sound {b : List UInt8} {v : JVal} (h : ofCanonicalBytes b = some v) :
    WF v ∧ encode v = b := by
  unfold ofCanonicalBytes at h
  split at h
  · cases h
  · split at h
    · cases h
    · rename_i v' _
      by_cases hc : (decide (WF v') && encode v' == b) = true
      · rw [if_pos hc] at h
        cases h
        simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hc
        exact hc
      · rw [if_neg hc] at h; cases h

/-- Canonical bytes name at most one value, and a value at most one byte string. -/
theorem ofCanonicalBytes_unique {b b' : List UInt8} {v : JVal}
    (h : ofCanonicalBytes b = some v) (h' : ofCanonicalBytes b' = some v) : b = b' := by
  rw [← (ofCanonicalBytes_sound h).2, ← (ofCanonicalBytes_sound h').2]

/-! ## Paths -/

/-- One step of a path: an object key or an array index. -/
inductive Step where
  | key (k : List UInt8)
  | idx (i : Nat)
  deriving Repr, DecidableEq, Inhabited

abbrev Path := List Step

/-- The first entry with key `k` (a `WF` object has at most one). -/
def findKey (k : List UInt8) : List (List UInt8 × JVal) → Option JVal
  | [] => none
  | (k', v) :: r => if k' = k then some v else findKey k r

/-- The value at a path, if present. -/
def lookup : JVal → Path → Option JVal
  | v, [] => some v
  | .arr xs, .idx i :: p => match xs[i]? with
    | some x => lookup x p
    | none => none
  | .obj kvs, .key k :: p => match findKey k kvs with
    | some x => lookup x p
    | none => none
  | _, _ :: _ => none

/-! ## Pins -/

#guard encode .null == [0xf6] && encode (.bool true) == [0xf5]
#guard encode (.int 0) == [0x00] && encode (.int (-1)) == [0x20]
#guard encode (.int 18446744073709551616) == [0xc2, 0x49, 1, 0, 0, 0, 0, 0, 0, 0, 0]  -- RFC 8949 App. A
#guard encode (.int (-18446744073709551617)) == [0xc3, 0x49, 1, 0, 0, 0, 0, 0, 0, 0, 0]
#guard encode (.dec 27315 (-2)) == [0xc4, 0x82, 0x21, 0x19, 0x6a, 0xb3]               -- 273.15, §3.4.4
#guard ofCanonicalBytes (encode (.dec 27315 (-2))) |>.isSome
-- a non-shortest head is refused by the reader (the decoder alone would accept it)
#guard (ofCanonicalBytes [0x18, 0x05]).isNone && (ofCanonicalBytes [0x05]).isSome
-- a decimal whose exponent would need a bignum is refused (RFC 8949 §3.4.4)
#guard (ofCanonicalBytes (encode (.dec 1 (-18446744073709551617)))).isNone
#guard (ofCanonicalBytes (encode (.dec 1 (-18446744073709551616)))).isSome
-- a non-canonical decimal (an integer written as tag 4) is refused
#guard (ofCanonicalBytes (encode (.dec 10 (-1)))).isNone
-- duplicate keys are refused, and so are unsorted keys
#guard (ofCanonicalBytes (encode (.obj [("a".toUTF8.toList, .null), ("a".toUTF8.toList, .null)]))).isNone
#guard (ofCanonicalBytes (encode (.obj [("b".toUTF8.toList, .null), ("a".toUTF8.toList, .null)]))).isNone
#guard (ofCanonicalBytes (encode (.obj [("a".toUTF8.toList, .null), ("b".toUTF8.toList, .null)]))).isSome
-- §4.2.1 order is on the ENCODED key: "b" (0x61 0x62) sorts before "aa" (0x62 0x61 0x61)
#guard keyLt "b".toUTF8.toList "aa".toUTF8.toList
-- invalid UTF-8 (a lone surrogate's bytes, an overlong slash) is refused
#guard !utf8Valid [0xED, 0xA0, 0x80] && !utf8Valid [0xC0, 0xAF] && utf8Valid "é€𝄞".toUTF8.toList
-- the empty array and the empty object are different values with different bytes
#guard encode (.arr []) == [0x80] && encode (.obj []) == [0xa0]

/-- info: 'Dregg2.Tree.canon_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms canon_injective

/-- info: 'Dregg2.Tree.toItem_injective' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms toItem_injective

/-- info: 'Dregg2.Tree.ofCanonicalBytes_sound' depends on axioms: [propext, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms ofCanonicalBytes_sound

end Dregg2.Tree

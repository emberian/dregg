/-
# Dregg2.Tree.Cbor: definite-length CBOR items, the encoder, a fuelled decoder, and injectivity

The wire form of the tree model (`Dregg2.Tree.Value`) is deterministic CBOR (RFC 8949 §4.2.1).
This module is the format layer: an `Item` type for the definite-length subset (major types 0-7,
no indefinite lengths, no floats), the encoder `enc` with shortest-form heads (§4.2.1 rule 1), a
fuelled decoder `dec`, and the round trip `dec_enc`. Injectivity and prefix-freedom of `enc` on the
admitted domain (`Adm`: every head argument below `2^64`) follow from the round trip
(`enc_prefix_injective`, `enc_injective`).

The decoder accepts non-shortest heads; the checkers never trust it alone. They decode, re-encode
and compare bytes (`Value.ofCanonicalBytes`), so an accepted byte string IS `enc` of its item, and
the non-shortest spelling `[0x18, 0x05]` of `5` is refused there (`#guard` below).

Lean core only: the `tree-check` executable links this module without compiling Mathlib.
-/

namespace Dregg2.Tree.Cbor

/-- A definite-length CBOR data item (RFC 8949 §3.1). `simple v` is major type 7 with `v < 24`
(false = 20, true = 21, null = 22). Floats (major 7, ai 25-27) are not in the model. -/
inductive Item where
  | uint (n : Nat)
  | nint (n : Nat)
  | bytes (b : List UInt8)
  | text (b : List UInt8)
  | arr (xs : List Item)
  | map (kvs : List (Item × Item))
  | tag (t : Nat) (x : Item)
  | simple (v : Nat)
  deriving Repr, Inhabited

/-! ## Big-endian byte strings -/

/-- `k` big-endian bytes of `n` (the low `8k` bits). -/
def be : Nat → Nat → List UInt8
  | 0, _ => []
  | k + 1, n => be k (n / 256) ++ [UInt8.ofNat (n % 256)]

/-- Read bytes big-endian. -/
def ofBE (l : List UInt8) : Nat := l.foldl (fun a b => a * 256 + b.toNat) 0

theorem be_length : ∀ k n, (be k n).length = k
  | 0, _ => rfl
  | k + 1, n => by simp [be, be_length k]

theorem ofBE_append_single (l : List UInt8) (b : UInt8) :
    ofBE (l ++ [b]) = ofBE l * 256 + b.toNat := by
  simp [ofBE, List.foldl_append]

theorem ofBE_be : ∀ k n, ofBE (be k n) = n % 256 ^ k
  | 0, n => by simp [be, ofBE, Nat.mod_one]
  | k + 1, n => by
    rw [be, ofBE_append_single, ofBE_be k]
    have h1 : (UInt8.ofNat (n % 256)).toNat = n % 256 := by
      simp [UInt8.toNat_ofNat'] <;> omega
    rw [h1, Nat.pow_succ, Nat.mul_comm (256 ^ k) 256, Nat.mod_mul]
    omega

/-! ## Heads -/

/-- The first byte of a head: major type `m` in the top three bits, additional info `ai`. -/
def ib (m ai : Nat) : UInt8 := UInt8.ofNat (m * 32 + ai)

/-- The shortest head for major type `m` and argument `n` (§4.2.1: "preferred serialization").
Arguments at or above `2^64` have no head; `Adm` keeps them out. -/
def head (m n : Nat) : List UInt8 :=
  if n < 24 then [ib m n]
  else if n < 2 ^ 8 then ib m 24 :: be 1 n
  else if n < 2 ^ 16 then ib m 25 :: be 2 n
  else if n < 2 ^ 32 then ib m 26 :: be 4 n
  else ib m 27 :: be 8 n

/-- Read `k` big-endian bytes off the front. -/
def takeBE (k : Nat) (r : List UInt8) : Option (Nat × List UInt8) :=
  if k ≤ r.length then some (ofBE (r.take k), r.drop k) else none

/-- Decode a head: `(major, argument, rest)`. Accepts non-shortest arguments (see header). -/
def decHead : List UInt8 → Option (Nat × Nat × List UInt8)
  | [] => none
  | x :: r =>
    let m := x.toNat / 32
    let ai := x.toNat % 32
    if ai < 24 then some (m, ai, r)
    else if ai = 24 then (takeBE 1 r).map fun p => (m, p.1, p.2)
    else if ai = 25 then (takeBE 2 r).map fun p => (m, p.1, p.2)
    else if ai = 26 then (takeBE 4 r).map fun p => (m, p.1, p.2)
    else if ai = 27 then (takeBE 8 r).map fun p => (m, p.1, p.2)
    else none

theorem ib_toNat {m ai : Nat} (hm : m < 8) (hai : ai < 32) : (ib m ai).toNat = m * 32 + ai := by
  simp [ib, UInt8.toNat_ofNat'] <;> omega

theorem takeBE_be (k n : Nat) (hn : n < 256 ^ k) (r : List UInt8) :
    takeBE k (be k n ++ r) = some (n, r) := by
  simp [takeBE, be_length, List.take_left', List.drop_left', ofBE_be, Nat.mod_eq_of_lt hn]

theorem decHead_head {m n : Nat} (hm : m < 8) (hn : n < 2 ^ 64) (r : List UInt8) :
    decHead (head m n ++ r) = some (m, n, r) := by
  unfold head
  by_cases h0 : n < 24
  · simp only [h0, if_true, List.cons_append, List.nil_append, decHead]
    rw [ib_toNat hm (by omega)]
    have e1 : (m * 32 + n) / 32 = m := by omega
    have e2 : (m * 32 + n) % 32 = n := by omega
    simp [e1, e2, h0]
  · by_cases h1 : n < 2 ^ 8
    · simp only [h0, h1, if_true, if_false, List.cons_append, decHead]
      rw [ib_toNat hm (by omega)]
      have e1 : (m * 32 + 24) / 32 = m := by omega
      have e2 : (m * 32 + 24) % 32 = 24 := by omega
      simp [e1, e2, takeBE_be 1 n (by omega)]
    · by_cases h2 : n < 2 ^ 16
      · simp only [h0, h1, h2, if_true, if_false, List.cons_append, decHead]
        rw [ib_toNat hm (by omega)]
        have e1 : (m * 32 + 25) / 32 = m := by omega
        have e2 : (m * 32 + 25) % 32 = 25 := by omega
        simp [e1, e2, takeBE_be 2 n (by omega)]
      · by_cases h3 : n < 2 ^ 32
        · simp only [h0, h1, h2, h3, if_true, if_false, List.cons_append, decHead]
          rw [ib_toNat hm (by omega)]
          have e1 : (m * 32 + 26) / 32 = m := by omega
          have e2 : (m * 32 + 26) % 32 = 26 := by omega
          simp [e1, e2, takeBE_be 4 n (by omega)]
        · simp only [h0, h1, h2, h3, if_false, List.cons_append, decHead]
          rw [ib_toNat hm (by omega)]
          have e1 : (m * 32 + 27) / 32 = m := by omega
          have e2 : (m * 32 + 27) % 32 = 27 := by omega
          simp [e1, e2, takeBE_be 8 n (by omega)]

/-! ## The encoder -/

mutual
/-- The CBOR encoding of an item (definite lengths, shortest heads). -/
def enc : Item → List UInt8
  | .uint n => head 0 n
  | .nint n => head 1 n
  | .bytes b => head 2 b.length ++ b
  | .text b => head 3 b.length ++ b
  | .arr xs => head 4 xs.length ++ encList xs
  | .map kvs => head 5 kvs.length ++ encPairs kvs
  | .tag t x => head 6 t ++ enc x
  | .simple v => head 7 v
def encList : List Item → List UInt8
  | [] => []
  | x :: xs => enc x ++ encList xs
def encPairs : List (Item × Item) → List UInt8
  | [] => []
  | (k, v) :: kvs => enc k ++ enc v ++ encPairs kvs
end

mutual
/-- The admitted domain: every head argument fits the 64-bit head; simple values below 24. -/
def Adm : Item → Prop
  | .uint n => n < 2 ^ 64
  | .nint n => n < 2 ^ 64
  | .bytes b => b.length < 2 ^ 64
  | .text b => b.length < 2 ^ 64
  | .arr xs => xs.length < 2 ^ 64 ∧ AdmList xs
  | .map kvs => kvs.length < 2 ^ 64 ∧ AdmPairs kvs
  | .tag t x => t < 2 ^ 64 ∧ Adm x
  | .simple v => v < 24
def AdmList : List Item → Prop
  | [] => True
  | x :: xs => Adm x ∧ AdmList xs
def AdmPairs : List (Item × Item) → Prop
  | [] => True
  | (k, v) :: kvs => Adm k ∧ Adm v ∧ AdmPairs kvs
end

mutual
/-- Decidable form of `Adm` (what the checkers run). -/
def adm : Item → Bool
  | .uint n => n < 2 ^ 64
  | .nint n => n < 2 ^ 64
  | .bytes b => b.length < 2 ^ 64
  | .text b => b.length < 2 ^ 64
  | .arr xs => xs.length < 2 ^ 64 && admList xs
  | .map kvs => kvs.length < 2 ^ 64 && admPairs kvs
  | .tag t x => t < 2 ^ 64 && adm x
  | .simple v => v < 24
def admList : List Item → Bool
  | [] => true
  | x :: xs => adm x && admList xs
def admPairs : List (Item × Item) → Bool
  | [] => true
  | (k, v) :: kvs => adm k && adm v && admPairs kvs
end

mutual
theorem adm_iff : ∀ i : Item, adm i = true ↔ Adm i
  | .uint n => by simp [adm, Adm]
  | .nint n => by simp [adm, Adm]
  | .bytes b => by simp [adm, Adm]
  | .text b => by simp [adm, Adm]
  | .arr xs => by simp [adm, Adm, admList_iff xs]
  | .map kvs => by simp [adm, Adm, admPairs_iff kvs]
  | .tag t x => by simp [adm, Adm, adm_iff x]
  | .simple v => by simp [adm, Adm]
theorem admList_iff : ∀ xs : List Item, admList xs = true ↔ AdmList xs
  | [] => by simp [admList, AdmList]
  | x :: xs => by simp [admList, AdmList, adm_iff x, admList_iff xs]
theorem admPairs_iff : ∀ kvs : List (Item × Item), admPairs kvs = true ↔ AdmPairs kvs
  | [] => by simp [admPairs, AdmPairs]
  | (k, v) :: kvs => by simp [admPairs, AdmPairs, adm_iff k, adm_iff v, admPairs_iff kvs, and_assoc]
end

/-! ## The decoder -/

/-- Decode `k` consecutive things with `d`. -/
def decN {α : Type} (d : List UInt8 → Option (α × List UInt8)) :
    Nat → List UInt8 → Option (List α × List UInt8)
  | 0, r => some ([], r)
  | k + 1, r =>
    match d r with
    | none => none
    | some (x, r1) =>
      match decN d k r1 with
      | none => none
      | some (xs, r2) => some (x :: xs, r2)

/-- Decode a pair with `d` twice. -/
def decPair {α : Type} (d : List UInt8 → Option (α × List UInt8)) (r : List UInt8) :
    Option ((α × α) × List UInt8) :=
  match d r with
  | none => none
  | some (k, r1) =>
    match d r1 with
    | none => none
    | some (v, r2) => some ((k, v), r2)

/-- Read `n` raw bytes. -/
def takeN (n : Nat) (r : List UInt8) : Option (List UInt8 × List UInt8) :=
  if n ≤ r.length then some (r.take n, r.drop n) else none

/-- The fuelled decoder: fuel bounds the nesting depth. -/
def dec : Nat → List UInt8 → Option (Item × List UInt8)
  | 0, _ => none
  | fuel + 1, bs =>
    match decHead bs with
    | none => none
    | some (m, n, r) =>
      if m = 0 then some (.uint n, r)
      else if m = 1 then some (.nint n, r)
      else if m = 2 then (takeN n r).map fun p => (.bytes p.1, p.2)
      else if m = 3 then (takeN n r).map fun p => (.text p.1, p.2)
      else if m = 4 then (decN (dec fuel) n r).map fun p => (.arr p.1, p.2)
      else if m = 5 then (decN (decPair (dec fuel)) n r).map fun p => (.map p.1, p.2)
      else if m = 6 then (dec fuel r).map fun p => (.tag n p.1, p.2)
      else if m = 7 ∧ n < 24 then some (.simple n, r)
      else none

mutual
/-- Nesting depth (the fuel the decoder needs is `depth + 1`). -/
def depth : Item → Nat
  | .arr xs => depthList xs + 1
  | .map kvs => depthPairs kvs + 1
  | .tag _ x => depth x + 1
  | _ => 0
def depthList : List Item → Nat
  | [] => 0
  | x :: xs => max (depth x) (depthList xs)
def depthPairs : List (Item × Item) → Nat
  | [] => 0
  | (k, v) :: kvs => max (max (depth k) (depth v)) (depthPairs kvs)
end

theorem takeN_append (b r : List UInt8) : takeN b.length (b ++ r) = some (b, r) := by
  simp [takeN, List.take_left', List.drop_left']

/-! ### The round trip -/

mutual
theorem dec_enc : ∀ (i : Item), Adm i → ∀ (fuel : Nat), depth i < fuel → ∀ (r : List UInt8),
    dec fuel (enc i ++ r) = some (i, r)
  | .uint n, h, fuel + 1, _, r => by
    simp only [enc, dec, decHead_head (m := 0) (by decide) h r]; simp
  | .nint n, h, fuel + 1, _, r => by
    simp only [enc, dec, decHead_head (m := 1) (by decide) h r]; simp
  | .bytes b, h, fuel + 1, _, r => by
    simp only [enc, dec, List.append_assoc, decHead_head (m := 2) (by decide) h, takeN_append]
    simp
  | .text b, h, fuel + 1, _, r => by
    simp only [enc, dec, List.append_assoc, decHead_head (m := 3) (by decide) h, takeN_append]
    simp
  | .arr xs, h, fuel + 1, hd, r => by
    simp only [depth] at hd
    have e := decN_encList xs h.2 fuel (by omega) r
    simp only [enc, dec, List.append_assoc, decHead_head (m := 4) (by decide) h.1]
    simp [e]
  | .map kvs, h, fuel + 1, hd, r => by
    simp only [depth] at hd
    have e := decN_encPairs kvs h.2 fuel (by omega) r
    simp only [enc, dec, List.append_assoc, decHead_head (m := 5) (by decide) h.1]
    simp [e]
  | .tag t x, h, fuel + 1, hd, r => by
    simp only [depth] at hd
    have e := dec_enc x h.2 fuel (by omega) r
    simp only [enc, dec, List.append_assoc, decHead_head (m := 6) (by decide) h.1]
    simp [e]
  | .simple v, h, fuel + 1, _, r => by
    simp only [Adm] at h
    simp only [enc, dec, decHead_head (m := 7) (n := v) (by decide) (by omega) r]
    simp [h]
theorem decN_encList : ∀ (xs : List Item), AdmList xs → ∀ (fuel : Nat), depthList xs < fuel →
    ∀ (r : List UInt8), decN (dec fuel) xs.length (encList xs ++ r) = some (xs, r)
  | [], _, _, _, r => rfl
  | x :: xs, h, fuel, hd, r => by
    simp only [depthList] at hd
    simp only [encList, List.append_assoc, List.length_cons, decN]
    simp [dec_enc x h.1 fuel (by omega), decN_encList xs h.2 fuel (by omega)]
theorem decN_encPairs : ∀ (kvs : List (Item × Item)), AdmPairs kvs → ∀ (fuel : Nat),
    depthPairs kvs < fuel → ∀ (r : List UInt8),
    decN (decPair (dec fuel)) kvs.length (encPairs kvs ++ r) = some (kvs, r)
  | [], _, _, _, r => rfl
  | (k, v) :: kvs, h, fuel, hd, r => by
    simp only [depthPairs] at hd
    simp only [encPairs, List.append_assoc, List.length_cons, decN, decPair]
    simp [dec_enc k h.1 fuel (by omega), dec_enc v h.2.1 fuel (by omega),
      decN_encPairs kvs h.2.2 fuel (by omega)]
end

/-- **Prefix-free injectivity.** Two admitted items whose encodings agree up to a suffix are the
same item, and the suffixes agree. -/
theorem enc_prefix_injective {i j : Item} (hi : Adm i) (hj : Adm j) {r s : List UInt8}
    (h : enc i ++ r = enc j ++ s) : i = j ∧ r = s := by
  have e1 := dec_enc i hi (max (depth i) (depth j) + 1) (by omega) r
  have e2 := dec_enc j hj (max (depth i) (depth j) + 1) (by omega) s
  rw [h, e2] at e1
  cases e1
  exact ⟨rfl, rfl⟩

/-- **`enc` is injective on the admitted domain.** -/
theorem enc_injective {i j : Item} (hi : Adm i) (hj : Adm j) (h : enc i = enc j) : i = j :=
  (enc_prefix_injective hi hj (r := []) (s := []) (by simpa using h)).1

/-- Encodings of admitted item lists of one length, prefix-free. -/
theorem encList_prefix_injective {xs ys : List Item} (hx : AdmList xs) (hy : AdmList ys)
    (hl : xs.length = ys.length) {r s : List UInt8} (h : encList xs ++ r = encList ys ++ s) :
    xs = ys ∧ r = s := by
  have e1 := decN_encList xs hx (max (depthList xs) (depthList ys) + 1) (by omega) r
  have e2 := decN_encList ys hy (max (depthList xs) (depthList ys) + 1) (by omega) s
  rw [h, hl, e2] at e1
  cases e1
  exact ⟨rfl, rfl⟩

/-! ## Pins -/

/-- Decode exactly one item and nothing after it. -/
def decodeAll (b : List UInt8) : Option Item :=
  match dec (b.length + 1) b with
  | some (i, []) => some i
  | _ => none

#guard enc (.uint 5) == [0x05]
#guard enc (.uint 24) == [0x18, 0x18]
#guard enc (.uint 1000000) == [0x1a, 0x00, 0x0f, 0x42, 0x40]   -- RFC 8949 Appendix A
#guard enc (.nint 0) == [0x20]                                   -- -1
#guard enc (.text "a".toUTF8.toList) == [0x61, 0x61]
#guard enc (.arr [.uint 1, .arr [.uint 2, .uint 3]]) == [0x82, 0x01, 0x82, 0x02, 0x03]
#guard enc (.map [(.text [0x61], .uint 1)]) == [0xa1, 0x61, 0x61, 0x01]
#guard enc (.simple 20) == [0xf4] && enc (.simple 21) == [0xf5] && enc (.simple 22) == [0xf6]
-- the non-shortest spelling of 5 decodes to the same item as the shortest one: the decoder alone
-- is malleable; `Value.ofCanonicalBytes` refuses it by re-encoding (pinned there)
#guard (decodeAll [0x18, 0x05]).map enc == some [0x05]
#guard (decodeAll [0x05]).map enc == some [0x05]
-- an empty array and an empty map are different bytes
#guard enc (.arr []) == [0x80] && enc (.map []) == [0xa0]

/-- info: 'Dregg2.Tree.Cbor.enc_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enc_injective

/-- info: 'Dregg2.Tree.Cbor.enc_prefix_injective' depends on axioms: [propext, Classical.choice, Quot.sound] -/
#guard_msgs (whitespace := lax) in #print axioms enc_prefix_injective

end Dregg2.Tree.Cbor

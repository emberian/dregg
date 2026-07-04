import Body.Basic

/-!
# Hexadecimal chunk-size codec (RFC 7230 §4.1)

A chunked-transfer `chunk-size` is a run of ASCII hex digits (big-endian, most
significant first). This file gives an encoder `toHex` and a decoder `parseHex`
and proves:

* `parseHex_toHex` — **round trip**: `parseHex (toHex n) = some n` for every
  natural `n`. The size read back from an encoded chunk-size is the original.
* `toHex_ne_nil` — the encoding of any size is a non-empty digit run (a chunk
  header always carries at least one size digit).
* `toHex_no_cr` / `toHex_no_crlf` — a hex-digit run never contains a CR or LF
  octet, so the CRLF that terminates the chunk-size line is unambiguous: the
  first CRLF after the size digits is exactly the line terminator.

The encoder uses `toHexFuel`, a structurally-recursive form with an explicit
fuel bound (`n + 1` digits always suffice), so every equation reduces without
well-founded-recursion unfolding. The decoder is a big-endian Horner fold.
-/

namespace Body
namespace Hex

/-- Encode a single hex digit value `d < 16` as its ASCII byte (lowercase for
`a`–`f`, matching the RFC's preferred form). -/
def hexDigit (d : Nat) : UInt8 :=
  if d < 10 then UInt8.ofNat (48 + d) else UInt8.ofNat (97 + (d - 10))

/-- Decode an ASCII byte to its hex-digit value, accepting `0`–`9`, `a`–`f`, and
`A`–`F`. Any other byte is not a hex digit. -/
def hexVal (b : UInt8) : Option Nat :=
  let n := b.toNat
  if 48 ≤ n ∧ n ≤ 57 then some (n - 48)
  else if 97 ≤ n ∧ n ≤ 102 then some (n - 87)
  else if 65 ≤ n ∧ n ≤ 70 then some (n - 55)
  else none

/-- The sixteen digit values, from a `< 16` bound. -/
theorem lt_sixteen_cases (d : Nat) (h : d < 16) :
    d = 0 ∨ d = 1 ∨ d = 2 ∨ d = 3 ∨ d = 4 ∨ d = 5 ∨ d = 6 ∨ d = 7 ∨ d = 8 ∨ d = 9 ∨
    d = 10 ∨ d = 11 ∨ d = 12 ∨ d = 13 ∨ d = 14 ∨ d = 15 := by omega

/-- The digit-value round trip: decoding an encoded digit recovers it. -/
theorem hexVal_hexDigit (d : Nat) (h : d < 16) : hexVal (hexDigit d) = some d := by
  rcases lt_sixteen_cases d h with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- A hex-digit byte is never a CR or LF framing octet. -/
theorem hexDigit_ne_crlf (d : Nat) (h : d < 16) : hexDigit d ≠ CR ∧ hexDigit d ≠ LF := by
  rcases lt_sixteen_cases d h with
    rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl <;> decide

/-- Fueled big-endian hex encoder: `fuel` bounds the digit count. -/
def toHexFuel : Nat → Nat → Bytes
  | 0, _ => []
  | fuel + 1, n =>
    if n < 16 then [hexDigit n]
    else toHexFuel fuel (n / 16) ++ [hexDigit (n % 16)]

/-- Big-endian hex encoding of a size. `n + 1` fuel always suffices. -/
def toHex (n : Nat) : Bytes := toHexFuel (n + 1) n

/-- Big-endian Horner decoder over a digit run: fold `acc ↦ acc·16 + digit`,
short-circuiting to `none` on the first non-hex byte. -/
def parseHexAux (acc : Nat) : Bytes → Option Nat
  | [] => some acc
  | b :: bs => (hexVal b).bind (fun d => parseHexAux (acc * 16 + d) bs)

/-- Decode a (non-empty) hex-digit run to the size it denotes. An empty run is
not a valid `chunk-size`. -/
def parseHex (bs : Bytes) : Option Nat :=
  if bs.isEmpty then none else parseHexAux 0 bs

/-- The Horner fold distributes over concatenation. -/
theorem parseHexAux_append (acc : Nat) (xs ys : Bytes) :
    parseHexAux acc (xs ++ ys)
      = (parseHexAux acc xs).bind (fun v => parseHexAux v ys) := by
  induction xs generalizing acc with
  | nil => simp [parseHexAux]
  | cons b bs ih =>
    simp only [List.cons_append, parseHexAux]
    cases hb : hexVal b with
    | none => simp
    | some d => simp [ih]

/-- Decoding a single encoded digit onto an accumulator. -/
theorem parseHexAux_singleton (acc d : Nat) (h : d < 16) :
    parseHexAux acc [hexDigit d] = some (acc * 16 + d) := by
  simp [parseHexAux, hexVal_hexDigit d h]

/-- `toHexFuel` produces a non-empty run whenever it has fuel to spare. -/
theorem toHexFuel_ne_nil (fuel n : Nat) (h : n < fuel) : toHexFuel fuel n ≠ [] := by
  cases fuel with
  | zero => omega
  | succ f =>
    simp only [toHexFuel]
    split <;> simp

/-- **Horner round trip with accumulator.** Decoding the fueled encoding of `n`
onto `acc` yields `acc` shifted left past `n`'s digits, plus `n`. -/
theorem parseHexAux_toHexFuel :
    ∀ (fuel n acc : Nat), n < fuel →
      parseHexAux acc (toHexFuel fuel n)
        = some (acc * 16 ^ (toHexFuel fuel n).length + n) := by
  intro fuel
  induction fuel with
  | zero => intro n acc h; omega
  | succ f ih =>
    intro n acc h
    simp only [toHexFuel]
    split
    · -- n < 16: a single digit
      rename_i hlt
      rw [parseHexAux_singleton acc n hlt]
      simp [Nat.pow_one]
    · -- n ≥ 16: recurse on n / 16, append the low digit
      rename_i hge
      have hlt16 : ¬ n < 16 := hge
      have hn16 : 16 ≤ n := by omega
      have hdiv : n / 16 < f := by
        have : n / 16 < n := Nat.div_lt_self (by omega) (by omega)
        omega
      have hmod : n % 16 < 16 := Nat.mod_lt _ (by omega)
      rw [parseHexAux_append, ih (n / 16) acc hdiv]
      simp only [Option.some_bind]
      rw [parseHexAux_singleton _ _ hmod]
      congr 1
      rw [List.length_append, List.length_singleton, Nat.pow_succ, ← Nat.mul_assoc]
      -- (A + n/16) * 16 + n % 16 = A * 16 + n, with A := acc * 16 ^ L
      generalize acc * 16 ^ (toHexFuel f (n / 16)).length = A
      omega

/-- The encoding of any size is non-empty. -/
theorem toHex_ne_nil (n : Nat) : toHex n ≠ [] :=
  toHexFuel_ne_nil (n + 1) n (Nat.lt_succ_self n)

/-- **Chunk-size round trip.** `parseHex (toHex n) = some n`: the size read back
from an encoded chunk-size is exactly the original size. -/
theorem parseHex_toHex (n : Nat) : parseHex (toHex n) = some n := by
  have hne : toHex n ≠ [] := toHex_ne_nil n
  have hemp : (toHex n).isEmpty = false := by
    cases htoh : toHex n with
    | nil => exact absurd htoh hne
    | cons _ _ => rfl
  unfold parseHex
  rw [hemp]
  simp only [Bool.false_eq_true, if_false]
  have := parseHexAux_toHexFuel (n + 1) n 0 (Nat.lt_succ_self n)
  simpa [toHex] using this

/-- Every byte of a fueled hex run is a hex digit, hence never CR or LF. -/
theorem toHexFuel_no_crlf (fuel n : Nat) :
    ∀ b ∈ toHexFuel fuel n, b ≠ CR ∧ b ≠ LF := by
  induction fuel generalizing n with
  | zero => intro b hb; simp [toHexFuel] at hb
  | succ f ih =>
    intro b hb
    simp only [toHexFuel] at hb
    split at hb
    · rename_i hlt
      simp only [List.mem_singleton] at hb
      subst hb
      exact hexDigit_ne_crlf n hlt
    · rw [List.mem_append] at hb
      rcases hb with hb | hb
      · exact ih (n / 16) b hb
      · simp only [List.mem_singleton] at hb
        subst hb
        exact hexDigit_ne_crlf (n % 16) (Nat.mod_lt _ (by omega))

/-- A hex encoding contains no CR or LF octet. -/
theorem toHex_no_crlf (n : Nat) : ∀ b ∈ toHex n, b ≠ CR ∧ b ≠ LF :=
  toHexFuel_no_crlf (n + 1) n

/-- A hex encoding contains no CR octet — so the first CRLF after the size digits
is exactly the chunk-size line terminator, not an accident inside the digits. -/
theorem toHex_no_cr (n : Nat) : ∀ b ∈ toHex n, b ≠ CR :=
  fun b hb => (toHex_no_crlf n b hb).1

end Hex
end Body

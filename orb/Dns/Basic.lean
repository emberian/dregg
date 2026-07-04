/-!
# DNS message parsing — shared vocabulary (RFC 1035)

This library models the parse side of a DNS message: the 12-octet header, the
question and resource-record sections, and — the headline — domain-name
decoding with compression pointers (RFC 1035 §4.1.4).

Compression pointers can form loops in adversarial input. Every function here
is a *total* Lean definition: name decoding terminates on every input, loops
included. The termination argument is structural, not a timeout — a followed
pointer must jump to a strictly smaller offset, so the sequence of run-start
offsets strictly decreases and is bounded below by zero.

Scope: wire-format parse only. EDNS(0) OPT records, DNSSEC RRs, and SVCB/HTTPS
RDATA shapes are out of scope; they are ordinary resource records to the
section parser (opaque RDATA) and do not affect any theorem here.

Byte strings are modeled as `List UInt8`, matching the other libraries in this
package.
-/

namespace Dns

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

def version : String := "0.1.0"

/-! ## RFC 1035 limits -/

/-- Maximum octet length of a domain name in wire form, including every length
octet and the terminating root octet (RFC 1035 §2.3.4). -/
def maxName : Nat := 255

/-- Maximum octet length of a single label (RFC 1035 §2.3.4): the label length
lives in the low 6 bits of the length octet, so it is `< 64`. -/
def maxLabel : Nat := 63

/-! ## Name length accounting

A decoded name is a list of labels (each a `List UInt8`). Its wire length is
the sum, over labels, of `1 + label.length` (a length octet plus the label
bytes), plus one octet for the terminating root label. -/

/-- Wire octets contributed by the labels themselves (length octet + bytes),
excluding the terminating root octet. -/
def labelsLen : List (List UInt8) → Nat
  | [] => 0
  | l :: ls => (l.length + 1) + labelsLen ls

/-- Full wire length of a decoded name: `labelsLen` plus the root octet. -/
def wireLen (ls : List (List UInt8)) : Nat := labelsLen ls + 1

theorem labelsLen_append (ls : List (List UInt8)) (l : List UInt8) :
    labelsLen (ls ++ [l]) = labelsLen ls + (l.length + 1) := by
  induction ls with
  | nil => simp [labelsLen]
  | cons a t ih => simp only [List.cons_append, labelsLen, ih]; omega

theorem wireLen_append (ls : List (List UInt8)) (l : List UInt8) :
    wireLen (ls ++ [l]) = wireLen ls + (l.length + 1) := by
  simp only [wireLen, labelsLen_append]; omega

theorem wireLen_nil : wireLen [] = 1 := rfl

/-! ## Big-endian field readers -/

/-- Big-endian 16-bit integer from two octets. -/
def be16 (hi lo : UInt8) : Nat := hi.toNat * 256 + lo.toNat

/-- Big-endian 32-bit integer from four octets. -/
def be32 (a b c d : UInt8) : Nat :=
  a.toNat * 2 ^ 24 + b.toNat * 2 ^ 16 + c.toNat * 2 ^ 8 + d.toNat

theorem u8_lt (x : UInt8) : x.toNat < 256 := x.toBitVec.isLt

/-- Every 16-bit field is `< 2^16`. -/
theorem be16_lt (hi lo : UInt8) : be16 hi lo < 65536 := by
  have h1 := u8_lt hi; have h2 := u8_lt lo; unfold be16; omega

/-! ## Parse errors -/

inductive ParseError where
  /-- The message ended before the parser had all the octets a field needs. -/
  | truncated
  /-- A label length octet used a reserved 2-bit prefix (`01` or `10`). -/
  | reservedLabel
  /-- A compression pointer did not jump strictly backward — the anti-loop
  guard fired. -/
  | loopPointer
  /-- The decoded name would exceed `maxName` octets. -/
  | nameTooLong
  /-- The forward label reader ran out of fuel (unreachable for well-formed
  input; fuel is seeded from the message length). -/
  | fuelExhausted
  deriving Repr, DecidableEq

end Dns

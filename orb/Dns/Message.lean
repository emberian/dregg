import Dns.Basic
import Dns.Name

/-!
# DNS message: header and section parsing (RFC 1035 §4.1)

A message is a 12-octet header followed by four sections — question, answer,
authority, additional — whose entry counts the header carries. This file parses
the header and one entry of each section kind, and proves each parser total and
*consumed-monotone*: a successful parse advances the message cursor by a
positive amount, so a fold over a section count strictly advances.

Record types beyond the generic name/type/class/ttl/rdata frame (EDNS OPT,
DNSSEC, SVCB/HTTPS) are out of scope; their RDATA is opaque bytes here.
-/

namespace Dns

/-- The 12-octet DNS header (RFC 1035 §4.1.1). Flags are kept as a raw 16-bit
field; the section counts drive parsing. -/
structure Header where
  id : Nat
  flags : Nat
  qdCount : Nat
  anCount : Nat
  nsCount : Nat
  arCount : Nat
  deriving Repr, DecidableEq

/-- Parse the fixed 12-octet header. Returns the header and the octets consumed
(always 12). `none` exactly when fewer than 12 octets are present. -/
def parseHeader (msg : Bytes) : Option (Header × Nat) :=
  if 12 ≤ msg.length then
    some
      ({ id := be16 (msg.getD 0 0) (msg.getD 1 0)
         flags := be16 (msg.getD 2 0) (msg.getD 3 0)
         qdCount := be16 (msg.getD 4 0) (msg.getD 5 0)
         anCount := be16 (msg.getD 6 0) (msg.getD 7 0)
         nsCount := be16 (msg.getD 8 0) (msg.getD 9 0)
         arCount := be16 (msg.getD 10 0) (msg.getD 11 0) }, 12)
  else none

/-- The header parser consumes exactly 12 octets. -/
theorem parseHeader_consumed (msg : Bytes) (h : Header) (n : Nat)
    (hp : parseHeader msg = some (h, n)) : n = 12 := by
  unfold parseHeader at hp
  split at hp
  · injection hp with hp; injection hp with _ hn; omega
  · exact absurd hp (by simp)

/-- The header parser needs 12 octets: it fails on any shorter message. -/
theorem parseHeader_needs (msg : Bytes) (h : msg.length < 12) :
    parseHeader msg = none := by
  unfold parseHeader
  rw [if_neg (by omega)]

/-- Header parsing succeeds exactly when at least 12 octets are present. -/
theorem parseHeader_isSome (msg : Bytes) :
    (parseHeader msg).isSome ↔ 12 ≤ msg.length := by
  unfold parseHeader
  by_cases h : 12 ≤ msg.length
  · rw [if_pos h]; simp [h]
  · rw [if_neg h]; simp; omega

/-- Every count field is a 16-bit number. -/
theorem parseHeader_counts_lt (msg : Bytes) (h : Header) (n : Nat)
    (hp : parseHeader msg = some (h, n)) :
    h.qdCount < 65536 ∧ h.anCount < 65536 ∧ h.nsCount < 65536 ∧ h.arCount < 65536 := by
  unfold parseHeader at hp
  split at hp
  · injection hp with hp; injection hp with hh _; subst hh
    exact ⟨be16_lt _ _, be16_lt _ _, be16_lt _ _, be16_lt _ _⟩
  · exact absurd hp (by simp)

/-! ## Question section (RFC 1035 §4.1.2)

A question is a QNAME followed by a 16-bit QTYPE and 16-bit QCLASS. -/

structure Question where
  qname : List (List UInt8)
  qtype : Nat
  qclass : Nat
  deriving Repr, DecidableEq

/-- Parse one question at offset `off`. Consumes the name plus the 4 fixed
octets. -/
def parseQuestion (msg : Bytes) (off : Nat) : Option (Question × Nat) :=
  match decodeName msg off with
  | .error _ => none
  | .ok d =>
    if off + d.consumed + 4 ≤ msg.length then
      some
        ({ qname := d.labels
           qtype := be16 (msg.getD (off + d.consumed) 0) (msg.getD (off + d.consumed + 1) 0)
           qclass := be16 (msg.getD (off + d.consumed + 2) 0)
                          (msg.getD (off + d.consumed + 3) 0) },
         d.consumed + 4)
    else none

/-- **Consumed-monotone.** A parsed question advances the cursor by at least 5
octets (a one-octet root name plus the 4 fixed octets), so it strictly
advances. -/
theorem parseQuestion_consumed_ge (msg : Bytes) (off : Nat) (q : Question) (n : Nat)
    (hp : parseQuestion msg off = some (q, n)) : 5 ≤ n := by
  unfold parseQuestion at hp
  split at hp
  · exact absurd hp (by simp)
  · rename_i d hd
    split at hp
    · injection hp with hp; injection hp with _ hn
      have := decodeName_consumed_pos msg off d hd
      omega
    · exact absurd hp (by simp)

/-! ## Resource records (RFC 1035 §4.1.3)

An RR is a NAME, 16-bit TYPE, 16-bit CLASS, 32-bit TTL, 16-bit RDLENGTH, then
RDLENGTH octets of RDATA. -/

structure RR where
  name : List (List UInt8)
  rrType : Nat
  rrClass : Nat
  ttl : Nat
  rdata : List UInt8
  deriving Repr, DecidableEq

/-- Parse one resource record at offset `off`. Consumes the name, the 10 fixed
octets (type, class, ttl, rdlength), then the RDATA. -/
def parseRR (msg : Bytes) (off : Nat) : Option (RR × Nat) :=
  match decodeName msg off with
  | .error _ => none
  | .ok d =>
    if off + d.consumed + 10 ≤ msg.length then
      if off + d.consumed + 10
          + be16 (msg.getD (off + d.consumed + 8) 0) (msg.getD (off + d.consumed + 9) 0)
          ≤ msg.length then
        some
          ({ name := d.labels
             rrType := be16 (msg.getD (off + d.consumed) 0)
                           (msg.getD (off + d.consumed + 1) 0)
             rrClass := be16 (msg.getD (off + d.consumed + 2) 0)
                            (msg.getD (off + d.consumed + 3) 0)
             ttl := be32 (msg.getD (off + d.consumed + 4) 0)
                         (msg.getD (off + d.consumed + 5) 0)
                         (msg.getD (off + d.consumed + 6) 0)
                         (msg.getD (off + d.consumed + 7) 0)
             rdata := (msg.drop (off + d.consumed + 10)).take
                        (be16 (msg.getD (off + d.consumed + 8) 0)
                              (msg.getD (off + d.consumed + 9) 0)) },
           d.consumed + 10
             + be16 (msg.getD (off + d.consumed + 8) 0) (msg.getD (off + d.consumed + 9) 0))
      else none
    else none

/-- **Consumed-monotone.** A parsed resource record advances the cursor by at
least 11 octets (a one-octet root name plus the 10 fixed octets), so it strictly
advances. -/
theorem parseRR_consumed_ge (msg : Bytes) (off : Nat) (r : RR) (n : Nat)
    (hp : parseRR msg off = some (r, n)) : 11 ≤ n := by
  unfold parseRR at hp
  split at hp
  · exact absurd hp (by simp)
  · rename_i d hd
    split at hp
    · split at hp
      · injection hp with hp; injection hp with _ hn
        have := decodeName_consumed_pos msg off d hd
        omega
      · exact absurd hp (by simp)
    · exact absurd hp (by simp)

/-! ## Worked vectors, checker-verified -/

/-- A minimal header: id 0x1234, flags 0x0100 (RD), QDCOUNT 1, others 0. -/
example :
    parseHeader [0x12, 0x34, 0x01, 0x00, 0x00, 0x01, 0x00, 0x00, 0x00, 0x00, 0x00, 0x00]
      = some ({ id := 0x1234, flags := 0x0100, qdCount := 1,
                anCount := 0, nsCount := 0, arCount := 0 }, 12) := by decide

/-- A short message has no header. -/
example : parseHeader [0x12, 0x34] = none := by decide

/-- One question `www.example.com IN A` at offset 0. Consumes 17 (name) + 4. -/
example :
    parseQuestion
      [3, 119, 119, 119, 7, 101, 120, 97, 109, 112, 108, 101, 3, 99, 111, 109, 0,
       0x00, 0x01, 0x00, 0x01] 0
      = some ({ qname := [[119, 119, 119], [101, 120, 97, 109, 112, 108, 101],
                          [99, 111, 109]], qtype := 1, qclass := 1 }, 21) := by
  decide

end Dns

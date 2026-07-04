import Socks.Basic

/-!
# The SOCKS5 address field (RFC 1928 §4/§6)

A SOCKS5 request and reply both carry a target as `ATYP(1) ADDR(variable)
PORT(2)`, where `ATYP` selects the address family:

* `0x01` — IPv4: 4 address bytes, then 2 port bytes (7 bytes total).
* `0x04` — IPv6: 16 address bytes, then 2 port bytes (19 bytes total).
* `0x03` — domain: 1 length byte `dlen`, `dlen` name bytes, then 2 port bytes
  (`4 + dlen` bytes total).

`parseAddr` decodes this field from the front of a buffer. It is a total
function returning `Res Target`, and the theorems establish:

* `parseAddr_total` — every buffer classifies as complete / incomplete / error
  (the parser is never stuck).
* `parseAddr_consumed_pos` / `parseAddr_consumed_le` — **consumed-monotone**:
  on a complete parse the read cursor strictly advances (`0 < consumed`) and
  never over-reads (`consumed ≤ buf.length`), across all three families.
* `parseAddr_consumed_exact` — the exact field width per family.
-/

namespace Socks

/-- A SOCKS host: an IPv4 quad, an IPv6 octet string, or a domain label. -/
inductive Host where
  | ipv4 (a b c d : UInt8)
  | ipv6 (octets : Bytes)
  | domain (label : Bytes)
deriving Repr, DecidableEq

/-- A target: host plus 16-bit port (modeled as `Nat`). -/
structure Target where
  host : Host
  port : Nat
deriving Repr, DecidableEq

/-- Parse a SOCKS5 address field from the front of `buf`. Total: an unknown
ATYP is an `error`, a short buffer is `incomplete`, everything else decodes to
`complete`. -/
def parseAddr (buf : Bytes) : Res Target :=
  match buf with
  | [] => .incomplete
  | atyp :: _ =>
    if atyp = 0x01 then
      if buf.length < 7 then .incomplete
      else .complete
        ⟨Host.ipv4 (buf.getD 1 0) (buf.getD 2 0) (buf.getD 3 0) (buf.getD 4 0),
         readU16 buf 5⟩ 7
    else if atyp = 0x03 then
      if buf.length < 2 then .incomplete
      else if buf.length < 4 + (buf.getD 1 0).toNat then .incomplete
      else .complete
        ⟨Host.domain ((buf.drop 2).take (buf.getD 1 0).toNat),
         readU16 buf (2 + (buf.getD 1 0).toNat)⟩ (4 + (buf.getD 1 0).toNat)
    else if atyp = 0x04 then
      if buf.length < 19 then .incomplete
      else .complete
        ⟨Host.ipv6 ((buf.drop 1).take 16), readU16 buf 17⟩ 19
    else .error

/-- **Totality.** Every buffer maps to exactly one of the three outcomes: the
address parser is never stuck. -/
theorem parseAddr_total (buf : Bytes) :
    (∃ t c, parseAddr buf = .complete t c)
      ∨ parseAddr buf = .incomplete
      ∨ parseAddr buf = .error := by
  cases buf with
  | nil => exact Or.inr (Or.inl rfl)
  | cons atyp tail =>
    simp only [parseAddr]
    by_cases h1 : atyp = 0x01
    · rw [if_pos h1]
      split
      · exact Or.inr (Or.inl rfl)
      · exact Or.inl ⟨_, _, rfl⟩
    · rw [if_neg h1]
      by_cases h3 : atyp = 0x03
      · rw [if_pos h3]
        split
        · exact Or.inr (Or.inl rfl)
        · split
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl ⟨_, _, rfl⟩
      · rw [if_neg h3]
        by_cases h4 : atyp = 0x04
        · rw [if_pos h4]
          split
          · exact Or.inr (Or.inl rfl)
          · exact Or.inl ⟨_, _, rfl⟩
        · rw [if_neg h4]
          exact Or.inr (Or.inr rfl)

/-- **Consumed is exact per family.** A complete parse consumes exactly the
family's field width: 7 (IPv4), 19 (IPv6), or `4 + dlen` (domain). -/
theorem parseAddr_consumed_exact {buf : Bytes} {t : Target} {c : Nat}
    (h : parseAddr buf = .complete t c) :
    c = 7 ∨ c = 19 ∨ c = 4 + (buf.getD 1 0).toNat := by
  cases buf with
  | nil => simp [parseAddr] at h
  | cons atyp tail =>
    simp only [parseAddr] at h
    by_cases h1 : atyp = 0x01
    · rw [if_pos h1] at h
      split at h
      · exact absurd h (by simp)
      · obtain ⟨-, hc⟩ := Res.complete.inj h; exact Or.inl hc.symm
    · rw [if_neg h1] at h
      by_cases h3 : atyp = 0x03
      · rw [if_pos h3] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · obtain ⟨-, hc⟩ := Res.complete.inj h; exact Or.inr (Or.inr hc.symm)
      · rw [if_neg h3] at h
        by_cases h4 : atyp = 0x04
        · rw [if_pos h4] at h
          split at h
          · exact absurd h (by simp)
          · obtain ⟨-, hc⟩ := Res.complete.inj h; exact Or.inr (Or.inl hc.symm)
        · rw [if_neg h4] at h
          exact absurd h (by simp)

/-- **Consumed makes progress.** A complete parse consumes at least one byte,
so the read cursor strictly advances (no zero-width accept). -/
theorem parseAddr_consumed_pos {buf : Bytes} {t : Target} {c : Nat}
    (h : parseAddr buf = .complete t c) : 0 < c := by
  rcases parseAddr_consumed_exact h with rfl | rfl | rfl <;> omega

/-- **Consumed does not over-read.** A complete parse never reports more bytes
consumed than the buffer holds, across all three families. -/
theorem parseAddr_consumed_le {buf : Bytes} {t : Target} {c : Nat}
    (h : parseAddr buf = .complete t c) : c ≤ buf.length := by
  cases buf with
  | nil => simp [parseAddr] at h
  | cons atyp tail =>
    simp only [parseAddr] at h
    by_cases h1 : atyp = 0x01
    · rw [if_pos h1] at h
      split at h
      · exact absurd h (by simp)
      · obtain ⟨-, hc⟩ := Res.complete.inj h; omega
    · rw [if_neg h1] at h
      by_cases h3 : atyp = 0x03
      · rw [if_pos h3] at h
        split at h
        · exact absurd h (by simp)
        · split at h
          · exact absurd h (by simp)
          · obtain ⟨-, hc⟩ := Res.complete.inj h; omega
      · rw [if_neg h3] at h
        by_cases h4 : atyp = 0x04
        · rw [if_pos h4] at h
          split at h
          · exact absurd h (by simp)
          · obtain ⟨-, hc⟩ := Res.complete.inj h; omega
        · rw [if_neg h4] at h
          exact absurd h (by simp)

end Socks

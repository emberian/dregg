/-!
# CIDR IP filtering (IPv4 + IPv6) with deny-precedence

An allow/deny access filter over CIDR blocks.  An address is a bit-string
tagged with its family (IPv4 = 32 bits, IPv6 = 128 bits; the model is
width-agnostic and the family tag keeps the two spaces disjoint).  A CIDR
block is a network bit-string with a prefix length: an address is *in* the
block iff it has the same family and its first `len` bits equal the network's
first `len` bits (RFC 4632 CIDR prefix matching, generalized to v6).

A ruleset is an ordered list of `(CIDR, allow | deny)` rules plus a
`defaultDeny` toggle.  The decision follows **deny-precedence**: if any deny
rule matches, the address is rejected regardless of any allow rule; else if
any allow rule matches, it is permitted; else the default applies.

## What is proved

* `ip_in_cidr_correct` — an address matches a CIDR iff (same family and) its
  `len`-bit prefix equals the network's `len`-bit prefix.
* `ip_deny_precedence` — a matching deny rule forces rejection, whatever the
  allow rules say.
* `ip_default_applies` — with no matching rule, the verdict is exactly the
  `defaultDeny` toggle.
* `ip_allow_grants` — a matching allow rule with no matching deny permits.
* `ip_family_mismatch` — an address never matches a CIDR of a different
  family (v4 traffic can't match a v6 block, and vice-versa).
* `ip_default_deny_empty` — an empty default-deny ruleset rejects everything.

## Boundary / UNCLOSED

* Textual address/CIDR parsing (dotted-quad, `::` compression, `/len`) is
  not modeled; addresses enter as bit-strings.
* Well-formedness `len ≤ bit-width` and canonical (host-bits-zero) networks
  are not enforced; `take len` is total and truncates gracefully, so the
  theorems hold regardless, but ill-formed inputs are a boundary.
-/

namespace IpFilter

/-- Address family. -/
inductive Family where
  | v4
  | v6
deriving DecidableEq, Repr

/-- An IP address: a family tag and its bits, most-significant first
(length 32 for v4, 128 for v6, though the model does not enforce this). -/
structure Addr where
  family : Family
  bits : List Bool
deriving DecidableEq, Repr

/-- A CIDR block: a family, a network bit-string, and a prefix length. -/
structure Cidr where
  family : Family
  net : List Bool
  len : Nat
deriving DecidableEq, Repr

/-- Rule action. -/
inductive Action where
  | allow
  | deny
deriving DecidableEq, Repr

/-- Does address `a` fall inside CIDR `c`?  Same family, and the first
`len` bits agree. -/
def matchCidr (c : Cidr) (a : Addr) : Bool :=
  decide (c.family = a.family ∧ a.bits.take c.len = c.net.take c.len)

/-- An ordered access ruleset with a default verdict. -/
structure Ruleset where
  rules : List (Cidr × Action)
  /-- When no rule matches: `true` rejects, `false` permits. -/
  defaultDeny : Bool

/-- Does any deny rule match `a`? -/
def matchesDeny (rs : Ruleset) (a : Addr) : Bool :=
  rs.rules.any (fun r => decide (r.2 = Action.deny) && matchCidr r.1 a)

/-- Does any allow rule match `a`? -/
def matchesAllow (rs : Ruleset) (a : Addr) : Bool :=
  rs.rules.any (fun r => decide (r.2 = Action.allow) && matchCidr r.1 a)

/-- The access decision.  `true` = permit.  Deny rules take precedence over
allow rules; with no match the `defaultDeny` toggle decides. -/
def permits (rs : Ruleset) (a : Addr) : Bool :=
  if matchesDeny rs a then false
  else if matchesAllow rs a then true
  else !rs.defaultDeny

/-! ### Theorems -/

/-- **CIDR membership is prefix equality.** An address matches a CIDR iff it
shares the family and its `len`-bit prefix equals the network prefix. -/
theorem ip_in_cidr_correct (c : Cidr) (a : Addr) :
    matchCidr c a = true ↔
      (c.family = a.family ∧ a.bits.take c.len = c.net.take c.len) := by
  simp [matchCidr]

/-- **Deny-precedence.** A matching deny rule forces rejection regardless of
the allow rules. -/
theorem ip_deny_precedence (rs : Ruleset) (a : Addr)
    (h : matchesDeny rs a = true) : permits rs a = false := by
  simp [permits, h]

/-- **Default toggle.** With neither a deny nor an allow match, the verdict
is exactly the negation of `defaultDeny`. -/
theorem ip_default_applies (rs : Ruleset) (a : Addr)
    (hd : matchesDeny rs a = false) (ha : matchesAllow rs a = false) :
    permits rs a = !rs.defaultDeny := by
  simp [permits, hd, ha]

/-- **Allow grants.** A matching allow rule with no matching deny permits. -/
theorem ip_allow_grants (rs : Ruleset) (a : Addr)
    (hd : matchesDeny rs a = false) (ha : matchesAllow rs a = true) :
    permits rs a = true := by
  simp [permits, hd, ha]

/-- **Family separation.** An address never matches a CIDR of a different
family. -/
theorem ip_family_mismatch (c : Cidr) (a : Addr) (h : c.family ≠ a.family) :
    matchCidr c a = false := by
  simp [matchCidr, h]

/-- **Empty default-deny rejects everything.** -/
theorem ip_default_deny_empty (a : Addr) :
    permits ⟨[], true⟩ a = false := by
  simp [permits, matchesDeny, matchesAllow]

end IpFilter

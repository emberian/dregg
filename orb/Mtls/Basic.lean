/-
Mtls — mutual-TLS client-certificate authentication: core types.

A sans-crypto model of X.509-style certificate-path validation for the
server-side of a mutual-TLS handshake.  The client presents a certificate
*chain* (leaf first); the server decides whether that chain authenticates
a single client identity against a fixed set of trust anchors, at a given
check time.

The model is deliberately split along one boundary: **all cryptography is
an uninterpreted named interface.**  Signature verification enters as a
single total function `verifySig` carried in `Env`; the machine never looks
inside it.  Every theorem here therefore holds uniformly over every possible
signature-checking behaviour — the results are about path validation and
identity extraction, not about the cipher.  This is the same named
crypto-axiom boundary the `Tls` record machine uses for AEAD/KDF.

Structure:

  * `Cert`   — one certificate: an opaque subject and issuer name, a
               `[notBefore, notAfter]` validity window, and the CA basic
               constraint (`isCA`).  Concrete distinguished names and key
               bytes are irrelevant to the accounting, so names are opaque
               `Nat` identities.

  * `Chain`  — the presented certificate chain, ordered **leaf first**: the
               head is the client (leaf) certificate — the identity source —
               each cert is signed by its successor, and the top of the chain
               must be a member of the trust-anchor set.  This is the
               client certificate surfaced by the TLS layer as an *input*
               (the `Tls` lib is a sibling, not a dependency).

  * `Env`    — the static verification context: the named `verifySig`
               predicate (the crypto boundary) and the trust-anchor set.

  * time     — the check time `now` is an explicit input to verification, so
               the same chain can pass at one instant and fail (expired) at
               another; validity windows are enforced against it at every link.
-/

namespace Mtls

/-- Wall-clock instant, as a monotone tick count.  Validity windows and the
check time are all `Time`. -/
abbrev Time := Nat

/-- An opaque distinguished-name / identity.  Concrete subject and issuer
strings are irrelevant to path validation and identity extraction, so a name
is an opaque `Nat` identity (equality is all the model needs). -/
abbrev Name := Nat

/-- One certificate.

`subject` is the name this certificate speaks for (the client identity, for a
leaf).  `issuer` is the name that signed it.  `notBefore`/`notAfter` bound the
inclusive validity window.  `isCA` is the CA basic constraint: only a cert with
`isCA = true` may sign another certificate in a valid path. -/
structure Cert where
  subject   : Name
  issuer    : Name
  notBefore : Time
  notAfter  : Time
  isCA      : Bool
deriving DecidableEq, Repr

/-- A presented certificate chain, **leaf first**: `head` is the client (leaf)
certificate, each element is signed by the next, and the last element must be a
trusted anchor. -/
abbrev Chain := List Cert

/-- The static verification context.

`verifySig issuer child = true` means: `child`'s signature verifies under
`issuer`'s public key.  It is an **uninterpreted total function** — the named
crypto boundary.  `anchors` is the trust-anchor set: the certificates the server
trusts directly, by identity. -/
structure Env where
  /-- The named signature-verification interface (crypto boundary):
  `verifySig issuer child` is `true` iff `child` is validly signed by `issuer`. -/
  verifySig : Cert → Cert → Bool
  /-- The trust-anchor set: certificates trusted directly. -/
  anchors   : List Cert

/-- `c` is inside its validity window at time `now` (inclusive on both ends). -/
def Cert.validAt (c : Cert) (now : Time) : Bool :=
  decide (c.notBefore ≤ now ∧ now ≤ c.notAfter)

/-- `validAt` decides the validity-window predicate. -/
theorem validAt_iff {c : Cert} {now : Time} :
    c.validAt now = true ↔ c.notBefore ≤ now ∧ now ≤ c.notAfter := by
  simp [Cert.validAt]

/-- A certificate whose window has closed (expired: the check time is strictly
past `notAfter`) is not valid at that time. -/
theorem validAt_false_of_expired {c : Cert} {now : Time}
    (h : c.notAfter < now) : c.validAt now = false := by
  unfold Cert.validAt
  exact decide_eq_false_iff_not.mpr
    (fun ⟨_, h2⟩ => absurd (Nat.lt_of_lt_of_le h h2) (Nat.lt_irrefl _))

/-- A certificate whose window has not yet opened is not valid at that time. -/
theorem validAt_false_of_notYet {c : Cert} {now : Time}
    (h : now < c.notBefore) : c.validAt now = false := by
  unfold Cert.validAt
  exact decide_eq_false_iff_not.mpr
    (fun ⟨h1, _⟩ => absurd (Nat.lt_of_lt_of_le h h1) (Nat.lt_irrefl _))

end Mtls

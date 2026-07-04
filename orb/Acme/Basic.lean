/-
Acme.Basic — the shared vocabulary of the ACME issuance model (RFC 8555).

This module holds the status alphabets that the order lifecycle, the
authorization lifecycle, and the challenge lifecycle all speak, plus the one
bridge that couples them: an authorization's status is a function of the
status of the challenge that discharges it.

Nothing here does I/O or cryptography. The order/challenge step functions
live in `Acme.Order` and `Acme.Challenge`; the cryptographic and network
*validation* that decides a challenge's fate is a named abstract interface —
a `Bool`-valued result the environment injects, never a Lean `axiom` — so the
whole development discharges against the standard core axioms only.
-/

namespace Acme

def version : String := "0.1.0"

/-- Byte-ish identifiers: tokens, thumbprints, domains, paths, TXT values are
all modelled as `List Char` so that concatenation is exact and left-cancellable
(the property behind HTTP-01 path correctness). They render to the obvious
`String` via `String.mk`. -/
abbrev Bytes := List Char

/-- The two challenge types this model covers (RFC 8555 §8.3, §8.4). -/
inductive ChallengeType where
  /-- Serve the key authorization at a well-known HTTP path. -/
  | http01
  /-- Publish the key-authorization digest as a DNS TXT record. -/
  | dns01
deriving DecidableEq, Repr

/-- Challenge status (RFC 8555 §7.1.6, §8): `pending → processing →
{valid, invalid}`, the last two absorbing. -/
inductive ChalStatus where
  | pending
  | processing
  | valid
  | invalid
deriving DecidableEq, Repr

/-- Authorization status (RFC 8555 §7.1.6). The `deactivated/expired/revoked`
statuses are administrative exits outside the issuance path and are a scope
cut; the issuance-relevant core is `pending → {valid, invalid}`. -/
inductive AuthzStatus where
  | pending
  | valid
  | invalid
deriving DecidableEq, Repr

/-- Order status (RFC 8555 §7.1.6, order state machine):
`pending → ready → processing → valid`, with `invalid` an absorbing failure
reachable from `pending` (an authorization failed) or from `processing`
(issuance failed). -/
inductive OrderStatus where
  | pending
  | ready
  | processing
  | valid
  | invalid
deriving DecidableEq, Repr

/-! ### Authorization-status predicates (Bool, so `List.all/any` compute) -/

def AuthzStatus.isValid : AuthzStatus → Bool
  | .valid => true
  | _ => false

def AuthzStatus.isInvalid : AuthzStatus → Bool
  | .invalid => true
  | _ => false

@[simp] theorem AuthzStatus.isValid_eq (s : AuthzStatus) :
    s.isValid = true ↔ s = .valid := by
  cases s <;> simp [AuthzStatus.isValid]

@[simp] theorem AuthzStatus.isInvalid_eq (s : AuthzStatus) :
    s.isInvalid = true ↔ s = .invalid := by
  cases s <;> simp [AuthzStatus.isInvalid]

/-- Every authorization in the list is `valid`. This is the gate the order
must pass to leave `pending` for `ready`. -/
def allValid (as : List AuthzStatus) : Bool := as.all AuthzStatus.isValid

/-- Some authorization has failed. -/
def anyInvalid (as : List AuthzStatus) : Bool := as.any AuthzStatus.isInvalid

/-! ### The challenge → authorization bridge

An authorization is validated *by a challenge*: it turns `valid` exactly when
one of its challenges turns `valid`, and `invalid` when the attempted
challenge fails (RFC 8555 §7.1.6). Modelling one active challenge per
authorization, the authorization status is a pure function of the challenge
status. -/

def authzOfChalStatus : ChalStatus → AuthzStatus
  | .valid => .valid
  | .invalid => .invalid
  | _ => .pending

/-- **An authorization is valid iff its challenge is valid.** There is no path
to a valid authorization that does not route through a valid challenge. -/
theorem authzOfChalStatus_valid {s : ChalStatus} :
    authzOfChalStatus s = .valid ↔ s = .valid := by
  cases s <;> simp [authzOfChalStatus]

/-- Dually, a valid authorization never arises from a pending/processing
challenge. -/
theorem authzOfChalStatus_not_valid {s : ChalStatus}
    (h : s ≠ .valid) : authzOfChalStatus s ≠ .valid := by
  cases s <;> simp_all [authzOfChalStatus]

end Acme

/-
Captp.Basic — core types for the capability-transport integration seam.

The seam carries capability references between two peers over a byte transport.
Objects (kernel-side capabilities) are named on the wire by *descriptors*: a
descriptor is a small tag plus a table position, or a third-party-handoff
token.  A descriptor is meaningless without the *session* that assigns the
positions (see `Captp.Session`); this file fixes only the vocabulary shared by
the frame layer (`Captp.Frame`) and the session layer.

`Obj` abstracts the kernel object identity (a content hash in the concrete
system) to `Nat`; only `DecidableEq` is used, so the abstraction is faithful
for every table/resolution property here.  `Byte` abstracts an octet to `Nat`;
the frame decoder never inspects an octet's magnitude, so the abstraction is
exact for the structural (consumed-monotonicity) theorems.
-/

namespace Captp

/-- Kernel object identity, abstracted to a decidable-equality atom. -/
abbrev Obj := Nat

/-- A wire octet, abstracted to `Nat`. -/
abbrev Byte := Nat

/-- Position in a peer's export / import / answer table. -/
abbrev Position := Nat

/-- How an object or promise is referenced on the wire.

* `Export p` — an object *we* export to the peer, at our export position `p`.
* `ImportObject p` — an object we imported from the peer, at import position `p`.
* `ImportPromise p` — a promise we imported from the peer.
* `Answer p` — the (as-yet-unresolved) result of a pending delivery, at answer
  position `p`; the vehicle of promise pipelining.
* `HandoffGive …` / `HandoffReceive …` — third-party handoff tokens: they name
  an object living on a *third* peer and are resolved by the handoff protocol,
  not by this session's local tables.

The three-part shape (kind, position, and — for handoffs — opaque key material)
mirrors the OCapN descriptor taxonomy. -/
inductive Descriptor where
  | Export (pos : Position)
  | ImportObject (pos : Position)
  | ImportPromise (pos : Position)
  | Answer (pos : Position)
  | HandoffGive (receiverKey exporterLocation session : List Byte)
  | HandoffReceive (receivingSession receivingSide : List Byte)
deriving DecidableEq, Repr

namespace Descriptor

/-- A descriptor that this session resolves against its *local* tables (an
export/import/answer position) as opposed to one routed to the handoff
protocol.  Well-formedness of a delivered descriptor is exactly this
dichotomy: every descriptor is either local-resolvable or a handoff token,
never ambiguous. -/
def isLocal : Descriptor → Bool
  | Export _ | ImportObject _ | ImportPromise _ | Answer _ => true
  | HandoffGive .. | HandoffReceive .. => false

/-- The handoff tokens are precisely the non-local descriptors. -/
def isHandoff : Descriptor → Bool
  | HandoffGive .. | HandoffReceive .. => true
  | _ => false

end Descriptor

/-- Every descriptor is classified exactly once: local xor handoff.  This is
the well-formedness backbone the frame decoder inherits — a decoded target is
never both routable locally and a handoff, and never neither. -/
theorem Descriptor.local_xor_handoff (d : Descriptor) :
    d.isLocal = !d.isHandoff := by
  cases d <;> rfl

end Captp

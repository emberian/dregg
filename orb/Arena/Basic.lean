/-
Arena — the immutable byte-arena request model.

A parsed request is represented as two immutable byte arenas plus a list of
view entries. Each entry is a `(tag, offset, length)` triple. The 32-bit
offset space is a discriminated union: offsets below `sidecarBase`
(`0x8000_0000`) address the *main* arena (the wire bytes) directly; offsets at
or above it address the *sidecar* arena (synthesized bytes, e.g. canonicalized
header names) at `offset - sidecarBase`. The high bit of the offset is exactly
the discriminant.

Well-formedness (`Store.Wf`) says every referenced range is in-bounds of the
arena it addresses. UTF-8 validity of the referenced ranges is a SEPARATE,
explicit hypothesis (`Store.WfUtf8`) — it is never folded into `Wf` and never
assumed; the executable checker discharges it per range at run time.
-/

namespace Arena

/-- The sidecar address-space base: `0x8000_0000`. An offset `≥ sidecarBase`
addresses the sidecar arena at `offset - sidecarBase`; an offset below it
addresses the main arena directly. Equivalently (see
`isSidecarAddr_iff_testBit`): bit 31 of the offset is the discriminant. -/
def sidecarBase : UInt32 := 0x80000000

/-- `sidecarBase` as a natural number; all address arithmetic in the theory is
carried out in `Nat` via `UInt32.toNat`. -/
def sidecarBaseNat : Nat := 0x80000000

theorem sidecarBase_toNat : sidecarBase.toNat = sidecarBaseNat := rfl

/-- An offset (as `Nat`) addressing the main arena. -/
def isMainAddr (off : Nat) : Prop := off < sidecarBaseNat

/-- An offset (as `Nat`) addressing the sidecar arena. -/
def isSidecarAddr (off : Nat) : Prop := sidecarBaseNat ≤ off

instance (off : Nat) : Decidable (isMainAddr off) := by
  unfold isMainAddr; infer_instance

instance (off : Nat) : Decidable (isSidecarAddr off) := by
  unfold isSidecarAddr; infer_instance

/-- The tag naming what a view entry denotes. -/
inductive NameTag where
  /-- The request method. -/
  | method
  /-- The request target. -/
  | target
  /-- The protocol version. -/
  | version
  /-- A header field name (canonical, lowercase). -/
  | headerName
  /-- A header field value (OWS-trimmed). -/
  | headerValue
  deriving Repr, DecidableEq, Inhabited

/-- One view entry: a `(tag, offset, length)` triple into the discriminated
two-arena address space. -/
structure Entry where
  tag : NameTag
  off : UInt32
  len : UInt32
  deriving Repr, DecidableEq, Inhabited

namespace Entry

/-- `true` iff the entry's offset addresses the sidecar arena. -/
def inSidecar (e : Entry) : Bool := decide (isSidecarAddr e.off.toNat)

/-- The physical offset of the entry within the arena it addresses. -/
def physOff (e : Entry) : Nat :=
  if e.inSidecar then e.off.toNat - sidecarBaseNat else e.off.toNat

end Entry

/-- The two-arena store: the immutable main arena (wire bytes), the sidecar
arena (synthesized bytes), and the view entries referencing both. -/
structure Store where
  main : Array UInt8
  sidecar : Array UInt8
  entries : List Entry
  deriving Repr, Inhabited

namespace Store

/-- The arena an entry addresses, per the offset discriminant. -/
def arenaOf (s : Store) (e : Entry) : Array UInt8 :=
  if e.inSidecar then s.sidecar else s.main

/-- The entry's referenced range lies inside its arena. -/
def InBounds (s : Store) (e : Entry) : Prop :=
  e.physOff + e.len.toNat ≤ (s.arenaOf e).size

instance (s : Store) (e : Entry) : Decidable (s.InBounds e) := by
  unfold InBounds; infer_instance

/-- Well-formedness: every entry's referenced range is in-bounds of the arena
it addresses. (UTF-8 validity is `WfUtf8`, a separate explicit hypothesis.) -/
def Wf (s : Store) : Prop := ∀ e ∈ s.entries, s.InBounds e

/-- The executable well-formedness check — the run-time discharge of `Wf`
(see `wfCheck_iff_Wf`). -/
def wfCheck (s : Store) : Bool := s.entries.all fun e => decide (s.InBounds e)

/-- Total resolve: an entry either denotes exactly the bytes of its range
(`some`), or is out of bounds (`none`). Under `Wf` the `none` case is
unreachable for stored entries (`resolve_total`). -/
def resolve (s : Store) (e : Entry) : Option (Array UInt8) :=
  let src := s.arenaOf e
  let start := e.physOff
  let stop := start + e.len.toNat
  if stop ≤ src.size then some (src.extract start stop) else none

/-- Register an entry in the view. -/
def pushEntry (s : Store) (e : Entry) : Store :=
  { s with entries := e :: s.entries }

/-- Append bytes to the sidecar arena (the canonicalization path). -/
def appendSidecar (s : Store) (bs : Array UInt8) : Store :=
  { s with sidecar := s.sidecar ++ bs }

end Store

/-- UTF-8 validity of a byte range — the model's one open hypothesis about
the *content* of ranges. It is carried explicitly wherever needed and
discharged per range by the executable checker; no theorem in this theory
assumes it. -/
def Utf8Valid (bs : Array UInt8) : Prop :=
  String.validateUTF8 (ByteArray.mk bs) = true

instance (bs : Array UInt8) : Decidable (Utf8Valid bs) := by
  unfold Utf8Valid; infer_instance

/-- The explicit UTF-8 hypothesis for a store: every resolvable range is
valid UTF-8. Deliberately separate from `Store.Wf`. -/
def Store.WfUtf8 (s : Store) : Prop :=
  ∀ e ∈ s.entries, ∀ b, s.resolve e = some b → Utf8Valid b

end Arena

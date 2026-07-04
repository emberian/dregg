/-
# Server-Sent Events — shared vocabulary

Definitions shared by the `Sse` library: the byte-string type, the SSE field
taxonomy (`event` / `data` / `id` / `retry`, plus comment and unrecognized
lines), the logical event a frame dispatches, and the small byte constants the
line format is built from.

The library is layered:

* `Sse.Basic` — this file: `Bytes`, the `Field` taxonomy, the `Event` record,
  the field/frame step functions.
* `Sse.Frame` — the wire format (`name: value` field lines, blank-line frame
  terminator): the single-field byte round-trip, and the frame parser's
  totality + consumed-monotonicity + encode/decode inversion.
* `Sse.Broadcast` — the broadcaster: a dynamic nodup subscriber set and a
  monotone published-event sequence, with the fan-out delivery accounting.
* `Sse.Resume` — `Last-Event-ID` resumption: the replay suffix is exactly the
  events after the given id (no replay, no skip).

Byte strings are `List UInt8`, matching the other libraries in this package.
Newline line-framing (splitting a byte stream into lines on `LF`/`CRLF`, and the
UTF-8 decode the SSE spec prepends) is the transport layer below this model; a
"line" here is already an `LF`-free byte string. The intra-line byte format —
the `name: value` shape with its one-space-after-colon rule — is modeled and
its round-trip proven at the byte level in `Sse.Frame`.
-/

namespace Sse

/-- Raw byte strings, modeled as lists (as elsewhere in this package). -/
abbrev Bytes := List UInt8

/-- A single logical line of an event stream: an `LF`-free byte string. -/
abbrev Line := Bytes

/-- A subscriber identity. -/
abbrev SubId := Nat

/-! ## Byte constants of the line format -/

/-- Line feed (`\n`, `0x0A`) — the transport line delimiter (below this model). -/
def LF : UInt8 := 10
/-- Colon (`:`, `0x3A`) — the field name/value separator. -/
def COLON : UInt8 := 58
/-- Space (` `, `0x20`) — the single optional pad after the field colon. -/
def SP : UInt8 := 32

/-- The `event` field name, as bytes. -/
def nameEvent : Bytes := [101, 118, 101, 110, 116]
/-- The `data` field name, as bytes. -/
def nameData : Bytes := [100, 97, 116, 97]
/-- The `id` field name, as bytes. -/
def nameId : Bytes := [105, 100]
/-- The `retry` field name, as bytes. -/
def nameRetry : Bytes := [114, 101, 116, 114, 121]

/-! ## The field taxonomy (SSE §9.2.5–§9.2.6) -/

/-- One parsed SSE field line. The four structured fields carry their value
bytes; a `comment` is a line beginning with a colon (ignored on dispatch); an
`other` retains an unrecognized field name and its value (also ignored). The
taxonomy is total over every possible line. -/
inductive Field where
  /-- `event: <value>` — sets the dispatched event type. -/
  | event (value : Bytes)
  /-- `data: <value>` — one data line; multiple accumulate in order. -/
  | data (value : Bytes)
  /-- `id: <value>` — sets the last-event-id. -/
  | id (value : Bytes)
  /-- `retry: <value>` — sets the reconnection time (only if all-digits). -/
  | retry (value : Bytes)
  /-- A comment line (began with a colon); its bytes are ignored. -/
  | comment (value : Bytes)
  /-- An unrecognized field name and its value; ignored on dispatch. -/
  | other (name value : Bytes)
deriving Repr, DecidableEq

/-! ## The dispatched event -/

/-- The logical event a complete frame dispatches: an optional event type
(`none` ⇒ the default `message`), an optional last-event-id, an optional retry
value, and the ordered list of `data` lines. Doubles as the parser's field
accumulator. -/
structure Event where
  /-- Event type set by the last `event:` field, if any. -/
  event : Option Bytes := none
  /-- Last-event-id set by the last `id:` field, if any. -/
  id : Option Bytes := none
  /-- Reconnection time set by the last valid `retry:` field, if any. -/
  retry : Option Bytes := none
  /-- The `data:` lines, in arrival order. -/
  data : List Bytes := []
deriving Repr, DecidableEq

/-- The empty accumulator (no fields seen yet). -/
def Event.empty : Event := ⟨none, none, none, []⟩

/-- `true` iff `b` is an ASCII digit (`0`–`9`). -/
def isDigit (b : UInt8) : Bool := decide (48 ≤ b.toNat ∧ b.toNat ≤ 57)

/-- `true` iff every byte of `v` is an ASCII digit. A `retry:` value is honoured
only when this holds (SSE §9.2.6); otherwise the field is ignored. -/
def isDigits (v : Bytes) : Bool := v.all isDigit

/-- Fold one parsed field into the accumulator (the SSE event-dispatch rules,
§9.2.6): `event`/`id` overwrite, `data` appends a line, `retry` is honoured only
when all-digits, comments and unrecognized fields are ignored. -/
def stepField (a : Event) : Field → Event
  | .event v => { a with event := some v }
  | .id v => { a with id := some v }
  | .retry v => if isDigits v then { a with retry := some v } else a
  | .data v => { a with data := a.data ++ [v] }
  | .comment _ => a
  | .other _ _ => a

/-- Well-formedness of a logical event for the encode/decode round-trip: a
`retry` value, if present, must be all-digits (else the parser would drop it on
dispatch, per §9.2.6). Every other field round-trips unconditionally. -/
def Event.Wf (e : Event) : Prop :=
  match e.retry with
  | none => True
  | some v => isDigits v = true

def version : String := "0.1.0"

end Sse

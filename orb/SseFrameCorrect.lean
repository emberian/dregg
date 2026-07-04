/-
# SseFrameCorrect — the event-stream wire format as *exact bytes*

`Sse.Frame` proves round-trip facts about the frame *parser*: an encoded event
parses back to itself (`Sse.parseFrame_encodeFrame`), the parser is total on
blank-terminated input, and it is consumed-monotone. Those pin down the
*decoder*, but they do not, on their own, say the *encoder* lays down the byte
sequence the event-stream format mandates: an encoder that dropped the
terminating blank line, or merged a multi-line `data` payload onto one line,
would still admit a matching (equally wrong) parser and pass a round-trip test.

This file closes that gap for the serializer. It defines, *without any reference
to* `Sse.encodeFrame` / `Sse.encodeFieldLine`, the exact wire bytes an event
must serialize to, straight from the event-stream format (WHATWG HTML §9.2 "Server-sent
events", the field grammar of §9.2.5 and the dispatch rules of §9.2.6), and
proves the real serializer emits exactly those bytes.

## The specified framing (WHATWG HTML §9.2)

A stream is a sequence of lines; each line is terminated by a line terminator
(the format admits CRLF, a lone CR, or a lone LF — §9.2; this spec fixes the
canonical CRLF). A field line is `name` `:` ` ` `value` — the single space after
the colon is the pad the parser strips (§9.2.5). An event is dispatched by a
blank line (§9.2.6), so a serialized event is its field lines followed by one
empty line, i.e. a trailing *double* CRLF.

`wireSpec` writes, in canonical serialization order:

  * an `event:` line iff an event type is set;
  * an `id:` line iff a last-event-id is set;
  * a `retry:` line iff a reconnection time is set;
  * **one `data:` line per data value** (§9.2.6: each `data` buffer line is a
    separate `data` field — a multi-line payload is *not* collapsed); then
  * the terminating blank line (the dispatch trigger).

## The refinement

`implWire e = renderCRLF (Sse.encodeFrame e)` is the wire rendering of the real
serializer: the canonical field lines `Sse.encodeFrame` produces, each closed by
CRLF (the empty dispatch line becomes the final blank line — the closing double
CRLF). `implWire_eq_wireSpec` proves `implWire e = wireSpec e` for **every**
event: the bytes on the wire are exactly the specified framing.

## Non-vacuity

The refinement is not the encoder renamed: `wireSpec` is built by direct byte
concatenation and never mentions the encoder. Two deliberately-wrong
serializers are shown to *disagree* with the spec on concrete events —
`noBlankWire` (drops the terminating blank line) and `mergedWire` (collapses a
multi-line `data` payload onto one line) — while the real serializer agrees. A
proof that admitted either would be false.
-/
import Sse.Frame

namespace SseFrameCorrect

open Sse

/-! ## Line terminator -/

/-- Carriage return (`\r`, `0x0D`). -/
def CR : UInt8 := 13

/-- The canonical line terminator of the event-stream format (WHATWG HTML §9.2):
`CR` `LF`. -/
def CRLF : Bytes := [CR, LF]

/-! ## The independent wire specification (WHATWG HTML §9.2.5–§9.2.6) -/

/-- One field line's specified bytes: `name` `:` ` ` `value` then the line
terminator (the `": "` pad is the space §9.2.5 strips on parse). Written
directly — no reference to the serializer. -/
def fieldWire (name value : Bytes) : Bytes := name ++ COLON :: SP :: value ++ CRLF

/-- The specified `data` section: **one `data:` line per value**, in order
(§9.2.6 — each buffered `data` line is its own field; a multi-line payload is
never merged). -/
def dataLines (ds : List Bytes) : Bytes := (ds.map (fieldWire nameData)).flatten

/-- The exact wire bytes an event must serialize to (WHATWG HTML §9.2): the
present field lines in canonical order, one `data:` line per data value, then the
terminating blank line (the trailing CRLF that, with the previous line's CRLF,
forms the dispatch-triggering empty line). -/
def wireSpec (e : Event) : Bytes :=
  (match e.event with | some v => fieldWire nameEvent v | none => []) ++
  (match e.id    with | some v => fieldWire nameId    v | none => []) ++
  (match e.retry with | some v => fieldWire nameRetry v | none => []) ++
  dataLines e.data ++
  CRLF

/-! ## The serializer's wire rendering -/

/-- Render a list of `LF`-free lines to wire bytes: each line closed by CRLF.
The transport layer below `Sse.encodeFrame`, fixed to the canonical terminator. -/
def renderCRLF (lines : List Line) : Bytes := (lines.map (· ++ CRLF)).flatten

/-- The wire bytes of the **real** serializer `Sse.encodeFrame`: its canonical
field lines plus the blank dispatch line, each closed by CRLF. -/
def implWire (e : Event) : Bytes := renderCRLF (Sse.encodeFrame e)

/-! ## `renderCRLF` structure -/

@[simp] theorem renderCRLF_nil : renderCRLF [] = [] := rfl

theorem renderCRLF_cons (x : Line) (xs : List Line) :
    renderCRLF (x :: xs) = (x ++ CRLF) ++ renderCRLF xs := by
  simp [renderCRLF]

theorem renderCRLF_append (a b : List Line) :
    renderCRLF (a ++ b) = renderCRLF a ++ renderCRLF b := by
  simp [renderCRLF, List.map_append, List.flatten_append]

/-- The blank dispatch line renders to a lone terminator — the closing half of
the double CRLF. -/
theorem renderCRLF_blank : renderCRLF [([] : Line)] = CRLF := by
  simp [renderCRLF_cons]

/-! ## Field-line agreement: `encodeFieldLine · ++ CRLF = fieldWire` -/

theorem enc_event (v : Bytes) :
    encodeFieldLine (.event v) ++ CRLF = fieldWire nameEvent v := by
  simp [encodeFieldLine, fieldWire, List.append_assoc]

theorem enc_id (v : Bytes) :
    encodeFieldLine (.id v) ++ CRLF = fieldWire nameId v := by
  simp [encodeFieldLine, fieldWire, List.append_assoc]

theorem enc_retry (v : Bytes) :
    encodeFieldLine (.retry v) ++ CRLF = fieldWire nameRetry v := by
  simp [encodeFieldLine, fieldWire, List.append_assoc]

theorem enc_data (v : Bytes) :
    encodeFieldLine (.data v) ++ CRLF = fieldWire nameData v := by
  simp [encodeFieldLine, fieldWire, List.append_assoc]

/-- The `data` section: rendering the serializer's `data` field lines yields
exactly one specified `data:` line per value. -/
theorem renderCRLF_dataMap (dat : List Bytes) :
    renderCRLF ((dat.map Field.data).map encodeFieldLine) = dataLines dat := by
  induction dat with
  | nil => rfl
  | cons d ds ih =>
    simp only [List.map_cons, renderCRLF_cons, ih, enc_data, dataLines,
      List.flatten_cons]

/-! ## The refinement theorem -/

/-- **Wire-format correctness.** The bytes the real serializer `Sse.encodeFrame`
lays on the wire are *exactly* the independently specified event-stream framing
(WHATWG HTML §9.2): the present field lines in canonical order, one `data:` line
per data value, terminated by the blank dispatch line. Holds for every event. -/
theorem implWire_eq_wireSpec (e : Event) : implWire e = wireSpec e := by
  obtain ⟨ev, iv, rv, dat⟩ := e
  unfold implWire Sse.encodeFrame Sse.eventFields wireSpec
  cases ev <;> cases iv <;> cases rv <;>
    simp only [List.map_append, List.map_cons, List.map_nil, List.nil_append,
      renderCRLF_append, renderCRLF_cons, renderCRLF_nil, renderCRLF_blank,
      renderCRLF_dataMap, enc_event, enc_id, enc_retry,
      List.append_nil, List.append_assoc]

/-! ## Non-vacuity: wrong serializers disagree with the spec -/

/-- A two-line `data` event: `data: a` / `data: b`. -/
def eg2 : Event := ⟨none, none, none, [[97], [98]]⟩

/-- A single-`data` event: `data: hi`. -/
def eg1 : Event := ⟨none, none, none, [[104, 105]]⟩

/-- A broken serializer that **drops the terminating blank line** (no closing
CRLF — no dispatch trigger). -/
def noBlankWire (e : Event) : Bytes :=
  renderCRLF ((Sse.eventFields e).map encodeFieldLine)

/-- A broken serializer that **merges a multi-line `data` payload onto one
line** (all data bytes concatenated into a single `data:` field). -/
def mergedWire (e : Event) : Bytes :=
  (match e.event with | some v => fieldWire nameEvent v | none => []) ++
  (match e.id    with | some v => fieldWire nameId    v | none => []) ++
  (match e.retry with | some v => fieldWire nameRetry v | none => []) ++
  fieldWire nameData e.data.flatten ++
  CRLF

/-- The real serializer meets the spec on the multi-line event. -/
theorem impl_ok_eg2 : implWire eg2 = wireSpec eg2 := implWire_eq_wireSpec eg2

/-- **Dropping the blank line fails**: without the terminating CRLF the bytes
are not the specified framing. -/
theorem noBlank_differs : noBlankWire eg2 ≠ wireSpec eg2 := by decide

/-- **Merging multi-line data fails**: one `data:` line for two values is not the
specified framing (which mandates one line per value). -/
theorem merged_differs : mergedWire eg2 ≠ wireSpec eg2 := by decide

/-- On a single-line payload the merging bug is invisible — it is precisely the
multi-line case that exposes it, matching §9.2.6. -/
theorem merged_agrees_single : mergedWire eg1 = wireSpec eg1 := by decide

/-- The spec is sensitive to content: distinct events have distinct wire bytes,
so the refinement equation carries real information. -/
theorem wireSpec_injective_witness : wireSpec eg1 ≠ wireSpec eg2 := by decide

#print axioms implWire_eq_wireSpec
#print axioms noBlank_differs
#print axioms merged_differs

end SseFrameCorrect

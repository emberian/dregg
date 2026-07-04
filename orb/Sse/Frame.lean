/-
# The SSE wire format — field lines and frames

A field line is `name` `:` ` ` `value` (a single optional space after the colon
is stripped on parse, SSE §9.2.5). A frame is a run of field lines terminated by
a blank line; the blank line triggers event dispatch (§9.2.6).

This file establishes:

* `parseFieldLine_encode…` — the byte-level **field round-trip**: parsing an
  encoded `event`/`data`/`id`/`retry` line recovers the exact field, for every
  value (the leading-space strip is inverted because the encoder always writes
  `": "`).
* `parseFrame` — the frame parser over a list of lines. It is **total** and
  **consumed-monotone**: a complete parse consumes `0 < n ≤ #lines` lines and
  the remainder is exactly `lines.drop n` (`parseFrame_consumed`); it reports
  `complete` for any input containing a blank line
  (`parseFrame_complete_of_blank`).
* `parseFrame_encodeFrame` — the frame-level **encode/decode inversion**: a
  well-formed event, encoded and re-parsed (before any trailing bytes),
  dispatches back to itself, consuming exactly its own length.

Line-framing over raw bytes (the `LF` split, `CR` handling) is the transport
layer below `Line`; see `Sse.Basic`.
-/
import Sse.Basic

namespace Sse

/-! ## Field line encode / parse (byte level) -/

/-- Encode one field as its `LF`-free line. Structured fields write
`name` `:` ` ` `value`; a comment writes `:` `value`; an `other` writes its raw
name then `: value`. -/
def encodeFieldLine : Field → Line
  | .event v => nameEvent ++ COLON :: SP :: v
  | .data v => nameData ++ COLON :: SP :: v
  | .id v => nameId ++ COLON :: SP :: v
  | .retry v => nameRetry ++ COLON :: SP :: v
  | .comment v => COLON :: v
  | .other name v => name ++ COLON :: SP :: v

/-- Split a line at its **first** colon into `(name, rawValue)`; `none` when the
line has no colon. -/
def splitColon : Bytes → Option (Bytes × Bytes)
  | [] => none
  | b :: bs =>
    if b = COLON then some ([], bs)
    else match splitColon bs with
      | none => none
      | some (n, v) => some (b :: n, v)

/-- Strip a single leading space (SSE §9.2.5: exactly one optional space after
the field colon is removed). -/
def dropOneSpace : Bytes → Bytes
  | (32 : UInt8) :: rest => rest
  | l => l

/-- Classify a `(name, value)` pair into the field taxonomy. -/
def classify (name value : Bytes) : Field :=
  if name = nameEvent then .event value
  else if name = nameData then .data value
  else if name = nameId then .id value
  else if name = nameRetry then .retry value
  else .other name value

/-- Parse one line into a `Field` (total). Split at the first colon: no colon ⇒
the whole line is the name with an empty value; an empty name (the line began
with a colon) ⇒ a comment; otherwise a single space after the colon is stripped
and the name is classified. -/
def parseFieldLine (line : Line) : Field :=
  match splitColon line with
  | none => classify line []
  | some ([], rawVal) => .comment rawVal
  | some (name, rawVal) => classify name (dropOneSpace rawVal)

/-- On a colon-free name, `splitColon` peels the whole name and returns the
bytes after the first colon unchanged. -/
theorem splitColon_prefix :
    ∀ (name : Bytes), (∀ b ∈ name, b ≠ COLON) → ∀ rest : Bytes,
      splitColon (name ++ COLON :: rest) = some (name, rest)
  | [], _, rest => by simp [splitColon, COLON]
  | b :: bs, h, rest => by
    have hb : b ≠ COLON := h b (List.mem_cons_self _ _)
    have ih := splitColon_prefix bs (fun x hx => h x (List.mem_cons_of_mem _ hx)) rest
    simp only [List.cons_append, splitColon, if_neg hb, ih]

theorem dropOneSpace_cons_sp (v : Bytes) : dropOneSpace (SP :: v) = v := by
  simp [dropOneSpace, SP]

/-- The name-byte lists contain no colon. -/
theorem nameEvent_no_colon : ∀ b ∈ nameEvent, b ≠ COLON := by decide
theorem nameData_no_colon : ∀ b ∈ nameData, b ≠ COLON := by decide
theorem nameId_no_colon : ∀ b ∈ nameId, b ≠ COLON := by decide
theorem nameRetry_no_colon : ∀ b ∈ nameRetry, b ≠ COLON := by decide

/-! ### Field round-trip: parse inverts encode -/

/-- Parsing an encoded structured field line (non-empty, colon-free name, the
canonical `": "` pad) recovers `classify name value` — the single space is
stripped, and any colons in `value` are preserved (`splitColon` cuts at the
first colon, which is the encoder's). -/
theorem parseFieldLine_field (name value : Bytes) (hne : name ≠ [])
    (hnc : ∀ b ∈ name, b ≠ COLON) :
    parseFieldLine (name ++ COLON :: SP :: value) = classify name value := by
  unfold parseFieldLine
  rw [splitColon_prefix name hnc (SP :: value)]
  cases name with
  | nil => exact absurd rfl hne
  | cons a as => rfl

theorem parseFieldLine_event (v : Bytes) :
    parseFieldLine (encodeFieldLine (.event v)) = .event v := by
  show parseFieldLine (nameEvent ++ COLON :: SP :: v) = .event v
  rw [parseFieldLine_field nameEvent v (by decide) nameEvent_no_colon]; rfl

theorem parseFieldLine_data (v : Bytes) :
    parseFieldLine (encodeFieldLine (.data v)) = .data v := by
  show parseFieldLine (nameData ++ COLON :: SP :: v) = .data v
  rw [parseFieldLine_field nameData v (by decide) nameData_no_colon]; rfl

theorem parseFieldLine_id (v : Bytes) :
    parseFieldLine (encodeFieldLine (.id v)) = .id v := by
  show parseFieldLine (nameId ++ COLON :: SP :: v) = .id v
  rw [parseFieldLine_field nameId v (by decide) nameId_no_colon]; rfl

theorem parseFieldLine_retry (v : Bytes) :
    parseFieldLine (encodeFieldLine (.retry v)) = .retry v := by
  show parseFieldLine (nameRetry ++ COLON :: SP :: v) = .retry v
  rw [parseFieldLine_field nameRetry v (by decide) nameRetry_no_colon]; rfl

/-! ## The frame parser (over lines) -/

/-- Outcome of parsing a frame from the head of a line list. `complete` carries
the dispatched event, the number of lines consumed (through the terminating
blank line), and the unconsumed remainder. `incomplete` means no blank-line
terminator is present yet — the caller waits for more lines. -/
inductive FrameResult where
  | complete (event : Event) (consumed : Nat) (rest : List Line)
  | incomplete
deriving Repr, DecidableEq

/-- Parse a frame, accumulating fields into `a`, until the first blank line. -/
def parseFrameAux (a : Event) : List Line → FrameResult
  | [] => .incomplete
  | line :: rest =>
    if line = [] then
      .complete a 1 rest
    else
      match parseFrameAux (stepField a (parseFieldLine line)) rest with
      | .complete e n r => .complete e (n + 1) r
      | .incomplete => .incomplete

/-- Parse a frame from the head of a line list, starting from the empty
accumulator. -/
def parseFrame (lines : List Line) : FrameResult := parseFrameAux Event.empty lines

/-! ### Totality and consumed-monotonicity -/

/-- **Consumed-monotone.** Whenever the parser completes, it consumed at least
one line (the terminator — progress) and no more than the input holds
(boundedness), and the remainder is exactly the dropped suffix. -/
theorem parseFrameAux_consumed (a : Event) (lines : List Line)
    {e : Event} {n : Nat} {r : List Line}
    (h : parseFrameAux a lines = .complete e n r) :
    0 < n ∧ n ≤ lines.length ∧ r = lines.drop n := by
  induction lines generalizing a e n r with
  | nil => simp [parseFrameAux] at h
  | cons line rest ih =>
    simp only [parseFrameAux] at h
    by_cases hb : line = []
    · rw [if_pos hb] at h
      cases h
      refine ⟨Nat.one_pos, ?_, rfl⟩
      simp [List.length_cons]
    · rw [if_neg hb] at h
      cases hrec : parseFrameAux (stepField a (parseFieldLine line)) rest with
      | incomplete => rw [hrec] at h; simp at h
      | complete e' n' r' =>
        rw [hrec] at h
        cases h
        obtain ⟨hpos, hle, hdrop⟩ := ih (stepField a (parseFieldLine line)) hrec
        refine ⟨Nat.succ_pos _, ?_, ?_⟩
        · simp only [List.length_cons]; omega
        · simp only [List.drop_succ_cons]; exact hdrop

/-- Consumed-monotone, from the empty accumulator. -/
theorem parseFrame_consumed (lines : List Line)
    {e : Event} {n : Nat} {r : List Line}
    (h : parseFrame lines = .complete e n r) :
    0 < n ∧ n ≤ lines.length ∧ r = lines.drop n :=
  parseFrameAux_consumed Event.empty lines h

/-- **Totality / progress.** Any input containing a blank line parses to
`complete` — the parser never diverges or gets stuck on a well-terminated
frame. -/
theorem parseFrameAux_complete_of_blank (a : Event) (lines : List Line)
    (hmem : [] ∈ lines) :
    ∃ e n r, parseFrameAux a lines = .complete e n r := by
  induction lines generalizing a with
  | nil => simp at hmem
  | cons line rest ih =>
    simp only [parseFrameAux]
    by_cases hb : line = []
    · rw [if_pos hb]; exact ⟨a, 1, rest, rfl⟩
    · rw [if_neg hb]
      have hmem' : [] ∈ rest := by
        rcases List.mem_cons.mp hmem with h | h
        · exact absurd h.symm hb
        · exact h
      obtain ⟨e, n, r, hrec⟩ := ih (stepField a (parseFieldLine line)) hmem'
      rw [hrec]; exact ⟨e, n + 1, r, rfl⟩

theorem parseFrame_complete_of_blank (lines : List Line) (hmem : [] ∈ lines) :
    ∃ e n r, parseFrame lines = .complete e n r :=
  parseFrameAux_complete_of_blank Event.empty lines hmem

/-! ## Frame encode / decode inversion -/

/-- The field lines an event encodes to (before the terminating blank line), in
canonical order: `event`, `id`, `retry`, then the `data` lines. -/
def eventFields (e : Event) : List Field :=
  (match e.event with | some v => [Field.event v] | none => []) ++
  (match e.id with | some v => [Field.id v] | none => []) ++
  (match e.retry with | some v => [Field.retry v] | none => []) ++
  e.data.map Field.data

/-- Encode a whole frame: the field lines, then a blank line. -/
def encodeFrame (e : Event) : List Line :=
  (eventFields e).map encodeFieldLine ++ [[]]

/-- Every encoded field line is non-empty (each begins with a name byte or a
colon), so the blank line an encoder appends is the first blank line a parser
meets. -/
theorem encodeFieldLine_ne_nil (f : Field) : encodeFieldLine f ≠ [] := by
  cases f <;> simp [encodeFieldLine, nameEvent, nameData, nameId, nameRetry]

/-- Folding the parser over encoded field lines followed by a blank line
recovers exactly the fold of `stepField`, consuming `#fields + 1` lines. -/
theorem parseFrameAux_fields (a : Event) (fs : List Field) (rest : List Line)
    (hrt : ∀ f ∈ fs, parseFieldLine (encodeFieldLine f) = f) :
    parseFrameAux a (fs.map encodeFieldLine ++ [] :: rest)
      = .complete (fs.foldl stepField a) (fs.length + 1) rest := by
  induction fs generalizing a with
  | nil => simp [parseFrameAux, List.foldl]
  | cons f fs ih =>
    have hf : parseFieldLine (encodeFieldLine f) = f := hrt f (List.mem_cons_self _ _)
    have hne : encodeFieldLine f ≠ [] := encodeFieldLine_ne_nil f
    simp only [List.map_cons, List.cons_append, parseFrameAux, if_neg hne, hf]
    rw [ih (stepField a f) (fun g hg => hrt g (List.mem_cons_of_mem _ hg))]
    simp [List.length_cons, List.foldl, Nat.add_right_comm]

/-! ### `stepField` reductions -/

@[simp] theorem stepField_event (a : Event) (v : Bytes) :
    stepField a (Field.event v) = { a with event := some v } := rfl
@[simp] theorem stepField_id (a : Event) (v : Bytes) :
    stepField a (Field.id v) = { a with id := some v } := rfl
@[simp] theorem stepField_data (a : Event) (v : Bytes) :
    stepField a (Field.data v) = { a with data := a.data ++ [v] } := rfl

/-- A `retry` field with an all-digit value sets the retry slot (SSE §9.2.6). -/
theorem stepField_retry_of_digits {a : Event} {v : Bytes} (h : isDigits v = true) :
    stepField a (Field.retry v) = { a with retry := some v } := by
  unfold stepField; exact if_pos h

/-- Folding `stepField` over the append of `data` fields appends the data
values to the accumulator's data list. -/
theorem foldl_stepField_data (ev id rt : Option Bytes) (acc ds : List Bytes) :
    (ds.map Field.data).foldl stepField ⟨ev, id, rt, acc⟩
      = ⟨ev, id, rt, acc ++ ds⟩ := by
  induction ds generalizing acc with
  | nil => simp
  | cons d ds ih =>
    simp only [List.map_cons, List.foldl_cons, stepField_data]
    rw [ih (acc ++ [d])]
    simp [List.append_assoc]

/-- Folding `stepField` over an event's canonical field list reconstructs the
event — provided any `retry` value is all-digits (`Event.Wf`). -/
theorem foldl_stepField_eventFields (e : Event) (hwf : e.Wf) :
    (eventFields e).foldl stepField Event.empty = e := by
  obtain ⟨ev, iv, rv, dat⟩ := e
  simp only [eventFields, Event.empty, List.foldl_append]
  cases rv with
  | none =>
    cases ev <;> cases iv <;>
      simp only [List.foldl_nil, List.foldl_cons, stepField_event, stepField_id,
        List.nil_append, foldl_stepField_data]
  | some rvv =>
    simp only [Event.Wf] at hwf
    cases ev <;> cases iv <;>
      simp only [List.foldl_nil, List.foldl_cons, stepField_event, stepField_id,
        stepField_retry_of_digits hwf, List.nil_append, foldl_stepField_data]

/-- Each field an event encodes to round-trips at the line level. -/
theorem eventFields_roundtrip (e : Event) :
    ∀ f ∈ eventFields e, parseFieldLine (encodeFieldLine f) = f := by
  intro f hf
  unfold eventFields at hf
  simp only [List.mem_append, List.mem_map] at hf
  rcases hf with ((hev | hid) | hrt) | hdata
  · cases he : e.event with
    | none => rw [he] at hev; simp at hev
    | some v => rw [he] at hev; simp at hev; subst hev; exact parseFieldLine_event v
  · cases hi : e.id with
    | none => rw [hi] at hid; simp at hid
    | some v => rw [hi] at hid; simp at hid; subst hid; exact parseFieldLine_id v
  · cases hr : e.retry with
    | none => rw [hr] at hrt; simp at hrt
    | some v => rw [hr] at hrt; simp at hrt; subst hrt; exact parseFieldLine_retry v
  · obtain ⟨v, _, hfe⟩ := hdata; subst hfe; exact parseFieldLine_data v

/-- **Frame encode/decode inversion.** A well-formed event, encoded and parsed
back (before any trailing lines `rest`), dispatches to itself, consuming exactly
its own encoded length. This is the round-trip: `parseFrame ∘ (encodeFrame · ++
rest)` recovers the event and reports the correct consumption. -/
theorem parseFrame_encodeFrame (e : Event) (rest : List Line) (hwf : e.Wf) :
    parseFrame (encodeFrame e ++ rest) = .complete e (encodeFrame e).length rest := by
  unfold parseFrame encodeFrame
  rw [List.append_assoc]
  have hstep :
      parseFrameAux Event.empty ((eventFields e).map encodeFieldLine ++ [] :: rest)
        = .complete ((eventFields e).foldl stepField Event.empty)
            ((eventFields e).length + 1) rest :=
    parseFrameAux_fields Event.empty (eventFields e) rest (eventFields_roundtrip e)
  have hcons : ([[]] : List Line) ++ rest = [] :: rest := rfl
  rw [hcons, hstep, foldl_stepField_eventFields e hwf]
  congr 1
  simp [List.length_append]

/-! ## Wire vectors, checker-verified -/

/-- A `data`-only event with two data lines: `data: a` / `data: b` / blank. -/
example :
    parseFrame (encodeFrame ⟨none, none, none, [[97], [98]]⟩ ++ [])
      = .complete ⟨none, none, none, [[97], [98]]⟩ 3 [] := by
  rw [parseFrame_encodeFrame _ _ (by simp [Event.Wf])]; rfl

/-- A typed event with an id: `event: x` / `id: 1` / `data: hi` / blank. -/
example :
    parseFrame (encodeFrame ⟨some [120], some [49], none, [[104, 105]]⟩ ++ [])
      = .complete ⟨some [120], some [49], none, [[104, 105]]⟩ 4 [] := by
  rw [parseFrame_encodeFrame _ _ (by simp [Event.Wf])]; rfl

/-- Field round-trip on a value that itself contains a colon: `id: a:b`. -/
example : parseFieldLine (encodeFieldLine (.id [97, 58, 98])) = .id [97, 58, 98] :=
  parseFieldLine_id _

end Sse

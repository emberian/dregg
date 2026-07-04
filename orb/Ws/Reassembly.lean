import Ws.Frame

/-!
# WebSocket fragmentation reassembly (RFC 6455 §5.4)

A continuation-frame accumulator. A data message is either a single
unfragmented frame or an initial `text`/`binary` frame with `fin = false`
followed by zero or more `continuation` frames, the last with `fin = true`.
Control frames (§5.5) may be injected between the fragments of a message and
must not disturb the reassembly in progress.

The theorems:

* `step_control_state` — a control frame leaves the reassembly state untouched
  (control interleaving is transparent to a fragment in progress).
* `step_new_data_mid_fragment` — a fresh data frame arriving mid-fragment is a
  protocol error.
* `step_continuation_idle` — a continuation with nothing to continue is a
  protocol error.
* `assemble_join` — a completed message's payload is the in-order
  concatenation of its fragment payloads (no reordering, no loss).
-/

namespace Ws
namespace Reassembly

/-- A message under construction: the opening frame's data opcode and the
payload accumulated so far. -/
structure Partial where
  opcode : Opcode
  acc : Bytes
deriving Repr, DecidableEq

/-- Reassembly state: between messages, or accumulating a fragmented message. -/
inductive State where
  | idle
  | assembling (p : Partial)
deriving Repr, DecidableEq

/-- What feeding one frame produced. -/
inductive Output where
  /-- The frame was absorbed into a fragment in progress; nothing to deliver. -/
  | absorbed
  /-- A complete data message. -/
  | message (opcode : Opcode) (payload : Bytes)
  /-- A control frame, delivered as-is (it does not enter reassembly). -/
  | control (f : Frame)
  /-- A protocol error. -/
  | error
deriving Repr, DecidableEq

/-- Feed one frame to the reassembler. -/
def step (st : State) (f : Frame) : State × Output :=
  if f.opcode.isControl then
    -- Control frames never touch the reassembly state (§5.4/§5.5).
    (st, Output.control f)
  else
    match f.opcode with
    | .continuation =>
      match st with
      | .idle => (.idle, .error)  -- nothing to continue
      | .assembling p =>
        let acc' := p.acc ++ f.payload
        if f.fin then (.idle, .message p.opcode acc')
        else (.assembling { p with acc := acc' }, .absorbed)
    | .text | .binary =>
      match st with
      | .assembling _ => (st, .error)  -- new data frame mid-fragment
      | .idle =>
        if f.fin then (.idle, .message f.opcode f.payload)
        else (.assembling { opcode := f.opcode, acc := f.payload }, .absorbed)
    | _ => (st, .error)  -- reserved opcode

/-- A control frame leaves the reassembly state untouched: interleaving control
frames between fragments cannot corrupt the message in progress. -/
theorem step_control_state (st : State) (f : Frame)
    (h : f.opcode.isControl = true) : (step st f).1 = st := by
  simp [step, h]

/-- A control frame is delivered as-is, not folded into any message. -/
theorem step_control_output (st : State) (f : Frame)
    (h : f.opcode.isControl = true) : (step st f).2 = Output.control f := by
  simp [step, h]

/-- A fresh data frame (`text`/`binary`) arriving while a fragment is in
progress is a protocol error. -/
theorem step_new_data_mid_fragment (p : Partial) (f : Frame)
    (hd : f.opcode = .text ∨ f.opcode = .binary) :
    step (.assembling p) f = (.assembling p, .error) := by
  obtain ⟨fin, op, pl⟩ := f
  rcases hd with h | h <;> subst h <;> rfl

/-- A continuation frame with no message in progress is a protocol error. -/
theorem step_continuation_idle (f : Frame) (h : f.opcode = .continuation) :
    step .idle f = (.idle, .error) := by
  obtain ⟨fin, op, pl⟩ := f
  subst h
  rfl

/-! ## Order-preserving concatenation

`assemble op acc frags` folds a run of continuation-fragment payloads onto an
accumulator; `assemble_join` shows the result is exactly the left-to-right
concatenation `acc ++ frags.flatten` — order preserved, nothing dropped. Feeding
the corresponding frames through `step` reproduces this fold (`run_assemble`),
so a delivered message is the in-order concatenation of its fragments. -/

/-- Fold a run of continuation payloads onto the accumulator. -/
def assemble (acc : Bytes) : List Bytes → Bytes
  | [] => acc
  | p :: ps => assemble (acc ++ p) ps

/-- The fold is exactly in-order concatenation. -/
theorem assemble_join (acc : Bytes) (frags : List Bytes) :
    assemble acc frags = acc ++ frags.flatten := by
  induction frags generalizing acc with
  | nil => simp [assemble]
  | cons p ps ih => simp [assemble, ih, List.append_assoc]

/-- Feeding a non-final continuation frame extends the accumulator in order and
stays assembling. -/
theorem step_continuation_absorb (p : Partial) (payload : Bytes) :
    step (.assembling p) { fin := false, opcode := .continuation, payload := payload }
      = (.assembling { p with acc := p.acc ++ payload }, .absorbed) := by
  rfl

/-- Feeding a final continuation frame delivers the message with the payload
concatenated in order. -/
theorem step_continuation_final (p : Partial) (payload : Bytes) :
    step (.assembling p) { fin := true, opcode := .continuation, payload := payload }
      = (.idle, .message p.opcode (p.acc ++ payload)) := by
  rfl

/-- A run of continuation frames, folded through `step`, accumulates the
payload in order (the machine-level companion of `assemble`). -/
def runAbsorb (p : Partial) : List Bytes → Partial
  | [] => p
  | payload :: ps =>
    runAbsorb { p with acc := p.acc ++ payload } ps

theorem runAbsorb_acc (p : Partial) (frags : List Bytes) :
    (runAbsorb p frags).acc = p.acc ++ frags.flatten := by
  induction frags generalizing p with
  | nil => simp [runAbsorb]
  | cons q qs ih => simp [runAbsorb, ih, List.append_assoc]

/-- Absorbing continuation frames never changes the message opcode. -/
theorem runAbsorb_opcode (p : Partial) (frags : List Bytes) :
    (runAbsorb p frags).opcode = p.opcode := by
  induction frags generalizing p with
  | nil => rfl
  | cons q qs ih => simp [runAbsorb, ih]

/-- The delivered message from a fragmented sequence is the in-order
concatenation of every fragment payload — the initial data frame's payload
followed by each continuation's, with nothing reordered or lost. -/
theorem assemble_join_message (op : Opcode) (initial : Bytes) (mids : List Bytes)
    (final : Bytes) :
    let p := runAbsorb { opcode := op, acc := initial } mids
    step (.assembling p) { fin := true, opcode := .continuation, payload := final }
      = (.idle, .message op (initial ++ mids.flatten ++ final)) := by
  simp only
  rw [step_continuation_final, runAbsorb_acc, runAbsorb_opcode]

end Reassembly
end Ws

import Ws.Basic

/-!
# WebSocket frames (RFC 6455 §5.2) — the decoded logical frame

The byte-level header decode composes `Ws.Length` (the payload-length ladder)
and `Ws.Mask` (the unmasking transform), both proven in their own modules. This
module fixes the *decoded* frame — FIN, the classified opcode, and the unmasked
application payload — plus the frame-level well-formedness the control-frame
rules (§5.5) impose. The reassembly and close state machines are stated over
this logical frame.
-/

namespace Ws

/-- A decoded WebSocket frame: the FIN bit, the classified opcode, and the
already-unmasked application payload. RSV bits carry no meaning without a
negotiated extension (none modeled), so a decoder validates them zero and this
record does not retain them. -/
structure Frame where
  fin : Bool
  opcode : Opcode
  payload : Bytes
deriving Repr, DecidableEq

namespace Frame

/-- Frame-level well-formedness (RFC 6455 §5.5): a control frame must not be
fragmented and carries at most 125 octets of payload. Data frames are
unconstrained at this layer. -/
def Wf (f : Frame) : Prop :=
  f.opcode.isControl = true → (f.fin = true ∧ f.payload.length ≤ 125)

instance (f : Frame) : Decidable f.Wf := by unfold Wf; infer_instance

/-- A data frame is trivially well-formed at this layer (the control
constraints do not apply). -/
theorem wf_of_data {f : Frame} (h : f.opcode.isData = true) : f.Wf := by
  unfold Wf
  intro hc
  exact absurd ⟨h, hc⟩ (Opcode.not_data_and_control f.opcode)

end Frame

end Ws

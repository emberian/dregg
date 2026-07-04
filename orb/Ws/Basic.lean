/-!
# WebSocket (RFC 6455) — shared vocabulary

Shared definitions for the `Ws` library: the byte-string type, the opcode
taxonomy (RFC 6455 §5.2), the control/data split, and the close codes the
handshake references (§7.4.1).

The library is layered:

* `Ws.Length` — the payload-length ladder (7-bit inline, 16-bit, 64-bit
  extended): shortest-encoding canonicity and encode/decode inversion.
* `Ws.Mask` — the rotating 4-byte XOR mask (§5.3): the unmask involution and
  the client-to-server masking well-formedness predicate.
* `Ws.Frame` — the frame header/decoder (§5.2): fin/rsv/opcode, the mask bit
  and key, control-frame constraints; totality and consumed-monotonicity.
* `Ws.Reassembly` — the fragmentation FSM (§5.4): a continuation-frame
  accumulator with control-frame interleaving.
* `Ws.Close` — the close handshake (§7): open / closing / closed with the
  status-code echo rule.

Byte strings are modeled as lists, matching the other libraries in this
package. Deliberately out of scope: negotiated extensions and
permessage-deflate (RFC 7692).
-/

namespace Ws

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- Every byte is below 256. -/
theorem u8_toNat_lt (x : UInt8) : x.toNat < 256 := x.toBitVec.isLt

/-! ## The opcode taxonomy (RFC 6455 §5.2) -/

/-- The RFC 6455 opcode taxonomy (the low nibble of byte 0). The six defined
opcodes plus a `reserved` catch-all that retains the raw nibble; classification
is total over all 16 values. -/
inductive Opcode where
  /-- `0x0` — a continuation of a fragmented message. -/
  | continuation
  /-- `0x1` — a text (UTF-8) data frame. -/
  | text
  /-- `0x2` — a binary data frame. -/
  | binary
  /-- `0x8` — a connection close control frame. -/
  | close
  /-- `0x9` — a ping control frame. -/
  | ping
  /-- `0xA` — a pong control frame. -/
  | pong
  /-- Reserved (`0x3`–`0x7` non-control, `0xB`–`0xF` control); retains the raw
  nibble. Reserved opcodes are a protocol error. -/
  | reserved (n : Nat)
deriving Repr, DecidableEq

/-- Total classification of an opcode nibble (RFC 6455 §5.2). Any value outside
the six defined opcodes maps to `reserved` — the taxonomy is total. -/
def Opcode.ofNat (n : Nat) : Opcode :=
  if n = 0x0 then .continuation
  else if n = 0x1 then .text
  else if n = 0x2 then .binary
  else if n = 0x8 then .close
  else if n = 0x9 then .ping
  else if n = 0xA then .pong
  else .reserved n

/-- The defined (non-reserved) opcode nibbles. -/
def isDefinedOpcode (n : Nat) : Bool :=
  n = 0x0 || n = 0x1 || n = 0x2 || n = 0x8 || n = 0x9 || n = 0xA

/-- **Taxonomy totality**: every nibble outside the defined set classifies as
`reserved` — `Opcode.ofNat` is total. -/
theorem Opcode.ofNat_reserved (n : Nat) (h : isDefinedOpcode n = false) :
    Opcode.ofNat n = .reserved n := by
  unfold isDefinedOpcode at h
  simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h
  obtain ⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h8⟩, h9⟩, ha⟩ := h
  unfold Opcode.ofNat
  simp [h0, h1, h2, h8, h9, ha]

/-- The control opcodes (RFC 6455 §5.5): close, ping, pong. Reserved control
opcodes (`0xB`–`0xF`) are not modeled as control here — they are rejected as
reserved before the control checks apply. -/
def Opcode.isControl : Opcode → Bool
  | .close | .ping | .pong => true
  | _ => false

/-- The data opcodes: continuation, text, binary. -/
def Opcode.isData : Opcode → Bool
  | .continuation | .text | .binary => true
  | _ => false

/-- No opcode is both data and control. -/
theorem Opcode.not_data_and_control (op : Opcode) :
    ¬ (op.isData = true ∧ op.isControl = true) := by
  cases op <;> simp [Opcode.isData, Opcode.isControl]

/-! ## Close codes (RFC 6455 §7.4.1) -/

/-- Normal closure. -/
def closeNormal : Nat := 1000
/-- No status code was present in the Close frame (reserved, never on wire). -/
def closeNoStatus : Nat := 1005
/-- Protocol error. -/
def closeProtocolError : Nat := 1002
/-- Message too big for the receiver. -/
def closeTooBig : Nat := 1009

def version : String := "0.1.0"

end Ws

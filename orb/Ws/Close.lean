import Ws.Frame

/-!
# WebSocket close handshake (RFC 6455 §7)

A three-state handshake: `open`, `closing` (a Close frame has crossed in one
direction), `closed` (both directions have sent Close). The endpoint that
receives a Close first echoes its status code (§7.1.2), and once an endpoint
has sent its Close it must not send further data frames (§7.1.1); `closed` is
absorbing.

Theorems:

* `closed_absorbing` — no event moves the machine out of `closed`.
* `no_data_after_close` — a data send is permitted only while `open`; once a
  Close has been sent (state `closing` or `closed`) it is a protocol error.
* `recv_close_echoes` — receiving a Close while `open` echoes the peer's status
  code.
-/

namespace Ws
namespace Close

/-- Close-handshake state. -/
inductive State where
  | opened
  | closing
  | closed
deriving Repr, DecidableEq

/-- Events driving the handshake. -/
inductive Event where
  | recvClose (code : Nat)
  | sendClose (code : Nat)
  | recvData
  | sendData
deriving Repr, DecidableEq

/-- Outputs. -/
inductive Output where
  | nothing
  | echoClose (code : Nat)
  | emitClose
  | deliver
  | emitData
  | error
deriving Repr, DecidableEq

/-- One handshake transition. -/
def step : State → Event → State × Output
  | .opened, .recvClose c => (.closing, .echoClose c)   -- peer initiates; echo its code
  | .opened, .sendClose _ => (.closing, .emitClose)     -- we initiate
  | .opened, .recvData    => (.opened, .deliver)
  | .opened, .sendData    => (.opened, .emitData)
  | .closing, .recvClose _ => (.closed, .nothing)     -- the reply completes the handshake
  | .closing, .sendClose _ => (.closed, .emitClose)   -- our reply completes it
  | .closing, .recvData    => (.closing, .deliver)    -- may still receive until closed
  | .closing, .sendData    => (.closing, .error)      -- no data after our Close (§7.1.1)
  | .closed, _ => (.closed, .error)                   -- absorbing

/-- `closed` is absorbing: no event leaves it. -/
theorem closed_absorbing (e : Event) : (step .closed e).1 = .closed := by
  cases e <;> rfl

/-- A data send is a protocol error unless the connection is still `open` — once
a Close frame has been sent (state `closing` or `closed`), no data frame may be
emitted. -/
theorem no_data_after_close (st : State) (h : st ≠ .opened) :
    (step st .sendData).2 = .error := by
  cases st with
  | opened => exact absurd rfl h
  | closing => rfl
  | closed => rfl

/-- Conversely, a data send while `open` emits the data frame. -/
theorem data_while_open : (step .opened .sendData).2 = .emitData := rfl

/-- Receiving a Close while `open` echoes the peer's status code and moves to
`closing`. -/
theorem recv_close_echoes (c : Nat) :
    step .opened (.recvClose c) = (.closing, .echoClose c) := rfl

end Close
end Ws

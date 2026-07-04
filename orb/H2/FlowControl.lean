import H2.Basic

/-!
# HTTP/2 flow control — window accounting (RFC 9113 §6.9 / RFC 7540 §6.9)

HTTP/2 carries a **credit-based** flow-control scheme on the send path. Two
signed windows govern DATA emission on a stream:

* a **connection-level** send window shared by every stream, and
* a **stream-level** send window, one per stream.

Both start at the peer's `SETTINGS_INITIAL_WINDOW_SIZE`, are **decremented** by
the payload length of every DATA frame sent, and are **incremented** by
`WINDOW_UPDATE` frames the peer sends. A DATA frame may be emitted only when its
payload fits under *both* windows; the sender emits `min(offered, credit)` where
`credit = max(0, min(conn, stream))`, and **parks** (buffers) the remainder to
retry when a later `WINDOW_UPDATE` restores credit.

This module models the send side as a transition system over signed windows
(`Int`, so "the window never goes negative" is a genuine proposition) and
proves the four flow-control accounting properties:

1. **Safety** (`sendData_emitted_le_conn` / `_stream`,
   `sendData_conn_window_nonneg` / `_stream`, and the trajectory form
   `Send.run_windows_nonneg`): a DATA frame is never emitted that would drive
   either window negative — the emitted payload is `≤` each current window, so
   the decrement leaves both `≥ 0`, under **any** interleaving of sends and
   `WINDOW_UPDATE`s from a well-formed start.
2. **Conservation** (`Window.consumed_eq`, `Send.run_stream_accounting`): total
   bytes sent on a window equals its initial size plus every `WINDOW_UPDATE`
   increment minus the current window — no bytes are conjured or lost. The
   ledger identity `window = initial + increments − consumed` is an invariant of
   every operation.
3. **Total `WINDOW_UPDATE` handling** (`windowUpdate_zero`,
   `windowUpdate_overflow`, `create_overflow`): a `WINDOW_UPDATE` of 0 is a
   PROTOCOL_ERROR, and an increment (or an initial-window setting) that would
   push a window past `2^31 − 1` is a FLOW_CONTROL_ERROR.
4. **Parked, not dropped** (`sendData_conserves_offered`, `sendData_blocked`):
   flow-blocked DATA is buffered, not discarded — `emitted + parked = offered`,
   and when there is no credit *all* offered bytes are parked and none emitted.

Windows are `Int`. `Nat` would make "never negative" vacuous; the whole point of
the safety property is that the signed decrement stays non-negative.
-/

namespace H2
namespace FlowControl

/-- The flow-control window cap (RFC 9113 §6.9.1): the available space in a
flow-control window MUST NOT exceed `2^31 − 1`. -/
def maxWindow : Int := 2 ^ 31 - 1

/-- Typed flow-control faults (RFC 9113 §6.9). -/
inductive Err where
  /-- A `WINDOW_UPDATE` with an increment of 0 (RFC 9113 §6.9). -/
  | protocolError
  /-- A window that would exceed `2^31 − 1` (RFC 9113 §6.9.1). -/
  | flowControlError
deriving Repr, DecidableEq

/-! ## A single flow-control window with its accounting ledger -/

/-- One send-side flow-control window. `window` is the stored available credit
(mirroring the endpoint's signed window field); `initial`, `increments`, and
`consumed` are the accounting ledger — the initial `SETTINGS_INITIAL_WINDOW_SIZE`,
the running sum of `WINDOW_UPDATE` increments, and the running sum of DATA
payload bytes charged against this window. -/
structure Window where
  /-- Current available send window (may be reduced to 0 but, once well-formed,
  never below 0). -/
  window : Int
  /-- `SETTINGS_INITIAL_WINDOW_SIZE` at window creation (ghost accounting). -/
  initial : Int
  /-- Running sum of `WINDOW_UPDATE` increments applied (ghost accounting). -/
  increments : Int
  /-- Running sum of DATA payload bytes charged against this window (ghost). -/
  consumed : Int
deriving Repr, DecidableEq

/-- **The conservation invariant**: the current window equals the initial size
plus every increment minus every byte consumed — no bytes conjured or lost. -/
def Window.Conserved (w : Window) : Prop :=
  w.window = w.initial + w.increments - w.consumed

/-- **Well-formedness**: conserved, non-negative, and within the `2^31 − 1` cap
(RFC 9113 §6.9.1). This is the transition-system invariant maintained by every
operation. -/
def Window.WF (w : Window) : Prop :=
  w.Conserved ∧ 0 ≤ w.window ∧ w.window ≤ maxWindow

/-! ## Operations on a window -/

/-- Create a window from `SETTINGS_INITIAL_WINDOW_SIZE` (RFC 9113 §6.5.2). A
setting outside `[0, 2^31 − 1]` is a FLOW_CONTROL_ERROR (RFC 9113 §6.9.1;
`initSize` is a 32-bit field, so only the upper bound can fire in practice). -/
def create (initSize : Int) : Except Err Window :=
  if initSize < 0 ∨ maxWindow < initSize then
    .error .flowControlError
  else
    .ok { window := initSize, initial := initSize, increments := 0, consumed := 0 }

/-- Apply a `WINDOW_UPDATE` of `inc` (RFC 9113 §6.9). An increment of 0 is a
PROTOCOL_ERROR; an increment that pushes the window past `2^31 − 1` is a
FLOW_CONTROL_ERROR; otherwise the window and the increment ledger both grow. -/
def windowUpdate (w : Window) (inc : Int) : Except Err Window :=
  if inc = 0 then
    .error .protocolError
  else if maxWindow < w.window + inc then
    .error .flowControlError
  else
    .ok { w with window := w.window + inc, increments := w.increments + inc }

/-- Charge `n` payload bytes against the window: decrement the available credit
and grow the consumed ledger. This is the effect of emitting `n` DATA bytes. -/
def Window.charge (w : Window) (n : Int) : Window :=
  { w with window := w.window - n, consumed := w.consumed + n }

/-! ## Window-level theorems -/

/-- **Conservation of the ledger identity across a DATA charge** (part of
property 2): charging bytes preserves `window = initial + increments −
consumed`. -/
theorem Window.charge_conserved {w : Window} (n : Int) (h : w.Conserved) :
    (w.charge n).Conserved := by
  unfold Window.Conserved at h ⊢
  show w.window - n = w.initial + w.increments - (w.consumed + n)
  omega

/-- **Conservation across a `WINDOW_UPDATE`** (part of property 2): a successful
increment preserves the ledger identity. -/
theorem windowUpdate_conserved {w w' : Window} {inc : Int}
    (h : w.Conserved) (hok : windowUpdate w inc = .ok w') : w'.Conserved := by
  unfold windowUpdate at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · rw [Except.ok.injEq] at hok
      subst hok
      unfold Window.Conserved at h ⊢
      show w.window + inc = w.initial + (w.increments + inc) - w.consumed
      omega

/-- **The conservation identity (property 2)**: whenever a window is conserved,
the total bytes consumed equal the initial window plus all increments minus the
current window. -/
theorem Window.consumed_eq {w : Window} (h : w.Conserved) :
    w.consumed = w.initial + w.increments - w.window := by
  unfold Window.Conserved at h
  omega

/-- **`WINDOW_UPDATE` of 0 is a PROTOCOL_ERROR** (property 3; RFC 9113 §6.9). -/
theorem windowUpdate_zero (w : Window) :
    windowUpdate w 0 = .error .protocolError := by
  unfold windowUpdate
  simp

/-- **An overflowing `WINDOW_UPDATE` is a FLOW_CONTROL_ERROR** (property 3;
RFC 9113 §6.9.1): a nonzero increment that pushes the window past `2^31 − 1` is
rejected. -/
theorem windowUpdate_overflow (w : Window) (inc : Int) (hne : inc ≠ 0)
    (hov : maxWindow < w.window + inc) :
    windowUpdate w inc = .error .flowControlError := by
  unfold windowUpdate
  rw [if_neg hne, if_pos hov]

/-- **An out-of-range initial window is a FLOW_CONTROL_ERROR** (property 3;
RFC 9113 §6.9.1): a `SETTINGS_INITIAL_WINDOW_SIZE` above `2^31 − 1` is
rejected. -/
theorem create_overflow (initSize : Int) (h : maxWindow < initSize) :
    create initSize = .error .flowControlError := by
  unfold create
  rw [if_pos (Or.inr h)]

/-- **`create` well-formedness**: a created window is well-formed (its ledger is
conserved and it sits in `[0, 2^31 − 1]`). -/
theorem create_WF {initSize : Int} {w : Window} (h : create initSize = .ok w) :
    w.WF := by
  unfold create at h
  split at h
  · exact absurd h (by simp)
  · rename_i hguard
    rw [Except.ok.injEq] at h
    subst h
    refine ⟨?_, ?_, ?_⟩
    · show initSize = initSize + 0 - 0
      omega
    · show (0 : Int) ≤ initSize
      omega
    · show initSize ≤ maxWindow
      omega

/-- **`WINDOW_UPDATE` preserves well-formedness**: a successful increment of a
well-formed window (with a non-negative increment) yields a well-formed window —
conserved, non-negative, and within the cap (the cap check is exactly what
guards the upper bound). -/
theorem windowUpdate_WF {w w' : Window} {inc : Int}
    (hinc : 0 ≤ inc) (hwf : w.WF) (hok : windowUpdate w inc = .ok w') : w'.WF := by
  unfold windowUpdate at hok
  split at hok
  · exact absurd hok (by simp)
  · split at hok
    · exact absurd hok (by simp)
    · rename_i _hne hle
      rw [Except.ok.injEq] at hok
      subst hok
      obtain ⟨hcons, hlo, hhi⟩ := hwf
      unfold Window.Conserved at hcons
      refine ⟨?_, ?_, ?_⟩
      · show w.window + inc = w.initial + (w.increments + inc) - w.consumed
        omega
      · show (0 : Int) ≤ w.window + inc
        omega
      · show w.window + inc ≤ maxWindow
        omega

/-- **`charge` preserves well-formedness** when the charged amount is
non-negative and within the current window: conserved, still non-negative (the
decrement never crosses 0), still within the cap. -/
theorem Window.charge_WF {w : Window} {n : Int}
    (hn : 0 ≤ n) (hle : n ≤ w.window) (hwf : w.WF) : (w.charge n).WF := by
  obtain ⟨hcons, hlo, hhi⟩ := hwf
  refine ⟨Window.charge_conserved n hcons, ?_, ?_⟩
  · show (0 : Int) ≤ w.window - n
    omega
  · show w.window - n ≤ maxWindow
    omega

/-! ## The two-window send state -/

/-- The send-side flow-control state for one focused stream: the shared
connection window and that stream's window (RFC 9113 §5.2). -/
structure Send where
  /-- Connection-level send window (shared across streams). -/
  conn : Window
  /-- Stream-level send window. -/
  stream : Window
deriving Repr, DecidableEq

/-- The **sendable credit**: the smaller of the two windows, floored at 0
(a negative window — reachable in general HTTP/2 via a `SETTINGS` reduction —
grants no credit). -/
def Send.credit (s : Send) : Int :=
  max 0 (min s.conn.window s.stream.window)

/-- Send-side well-formedness: both windows are well-formed. -/
def Send.WF (s : Send) : Prop :=
  s.conn.WF ∧ s.stream.WF

/-- The result of offering DATA to the send path: the bytes actually emitted,
the bytes parked (buffered for a later retry), and the successor state. -/
structure SendResult where
  /-- DATA payload bytes emitted now. -/
  emitted : Int
  /-- Payload bytes parked (flow-blocked), to retry after a `WINDOW_UPDATE`. -/
  parked : Int
  /-- Successor send state (both windows charged by `emitted`). -/
  next : Send
deriving Repr, DecidableEq

/-- Offer `offered` payload bytes of DATA on the focused stream. Emit
`min(offered, credit)` (never more than either window allows), park the
remainder, and charge both windows by the emitted amount. -/
def Send.sendData (s : Send) (offered : Int) : SendResult :=
  { emitted := min offered s.credit
    parked := offered - min offered s.credit
    next :=
      { conn := s.conn.charge (min offered s.credit)
        stream := s.stream.charge (min offered s.credit) } }

/-! ## Credit bounds -/

/-- The sendable credit is non-negative. -/
theorem Send.credit_nonneg (s : Send) : 0 ≤ s.credit := by
  unfold Send.credit
  omega

/-- The sendable credit never exceeds the connection window (when it is
non-negative). -/
theorem Send.credit_le_conn (s : Send) (h : 0 ≤ s.conn.window) :
    s.credit ≤ s.conn.window := by
  unfold Send.credit
  omega

/-- The sendable credit never exceeds the stream window (when it is
non-negative). -/
theorem Send.credit_le_stream (s : Send) (h : 0 ≤ s.stream.window) :
    s.credit ≤ s.stream.window := by
  unfold Send.credit
  omega

/-! ## Property 1 — flow-control safety (a DATA frame never drives a window
negative) -/

/-- **Safety, connection window**: the emitted DATA payload never exceeds the
current connection window. -/
theorem sendData_emitted_le_conn (s : Send) (offered : Int) (h : 0 ≤ s.conn.window) :
    (s.sendData offered).emitted ≤ s.conn.window := by
  have hcc := s.credit_le_conn h
  show min offered s.credit ≤ s.conn.window
  omega

/-- **Safety, stream window**: the emitted DATA payload never exceeds the
current stream window. -/
theorem sendData_emitted_le_stream (s : Send) (offered : Int) (h : 0 ≤ s.stream.window) :
    (s.sendData offered).emitted ≤ s.stream.window := by
  have hcs := s.credit_le_stream h
  show min offered s.credit ≤ s.stream.window
  omega

/-- **Safety, connection window (successor form)**: after the send, the
connection window is still non-negative. -/
theorem sendData_conn_window_nonneg (s : Send) (offered : Int) (h : 0 ≤ s.conn.window) :
    0 ≤ (s.sendData offered).next.conn.window := by
  have hcc := s.credit_le_conn h
  show (0 : Int) ≤ s.conn.window - min offered s.credit
  omega

/-- **Safety, stream window (successor form)**: after the send, the stream
window is still non-negative. -/
theorem sendData_stream_window_nonneg (s : Send) (offered : Int) (h : 0 ≤ s.stream.window) :
    0 ≤ (s.sendData offered).next.stream.window := by
  have hcs := s.credit_le_stream h
  show (0 : Int) ≤ s.stream.window - min offered s.credit
  omega

/-- **The send step preserves send-side well-formedness**: from a well-formed
state, offering non-negative DATA yields a well-formed successor — both windows
stay conserved, non-negative, and capped. -/
theorem sendData_WF {s : Send} {offered : Int} (hoff : 0 ≤ offered) (hwf : s.WF) :
    (s.sendData offered).next.WF := by
  obtain ⟨hc, hs⟩ := hwf
  have hcn := s.credit_nonneg
  have hcc := s.credit_le_conn hc.2.1
  have hcs := s.credit_le_stream hs.2.1
  have hn : 0 ≤ min offered s.credit := by omega
  have hlec : min offered s.credit ≤ s.conn.window := by omega
  have hles : min offered s.credit ≤ s.stream.window := by omega
  refine ⟨?_, ?_⟩
  · show (s.conn.charge (min offered s.credit)).WF
    exact Window.charge_WF hn hlec hc
  · show (s.stream.charge (min offered s.credit)).WF
    exact Window.charge_WF hn hles hs

/-! ## Property 4 — flow-blocked DATA is parked, not dropped -/

/-- **Offered bytes are conserved**: everything offered is either emitted or
parked — nothing is dropped. -/
theorem sendData_conserves_offered (s : Send) (offered : Int) :
    (s.sendData offered).emitted + (s.sendData offered).parked = offered := by
  show min offered s.credit + (offered - min offered s.credit) = offered
  omega

/-- Parked bytes are non-negative (the parked buffer is well-defined): the
emitted amount `min offered credit` never exceeds the offered amount. -/
theorem sendData_parked_nonneg (s : Send) (offered : Int) :
    0 ≤ (s.sendData offered).parked := by
  show (0 : Int) ≤ offered - min offered s.credit
  omega

/-- **Flow-blocked ⇒ all parked**: when there is no credit, no bytes are emitted
and every offered byte is parked (buffered), matching the endpoint that buffers
DATA it cannot yet send. -/
theorem sendData_blocked (s : Send) (offered : Int)
    (hblk : s.credit = 0) (h : 0 ≤ offered) :
    (s.sendData offered).emitted = 0 ∧ (s.sendData offered).parked = offered := by
  refine ⟨?_, ?_⟩
  · show min offered s.credit = 0
    rw [hblk]; omega
  · show offered - min offered s.credit = offered
    rw [hblk]; omega

/-! ## The transition system over operation sequences -/

/-- The send-path operation alphabet: offer DATA, or apply a `WINDOW_UPDATE` at
the connection or stream level. -/
inductive Op where
  /-- Offer `offered` payload bytes of DATA on the focused stream. -/
  | data (offered : Int)
  /-- A connection-level (stream 0) `WINDOW_UPDATE` of `inc`. -/
  | connUpdate (inc : Int)
  /-- A stream-level `WINDOW_UPDATE` of `inc`. -/
  | streamUpdate (inc : Int)
deriving Repr, DecidableEq

/-- Validity of an operation's payload: byte counts and increments are
non-negative (the wire increment is a 31-bit field, so `≥ 0`). -/
def Op.valid : Op → Prop
  | .data offered => 0 ≤ offered
  | .connUpdate inc => 0 ≤ inc
  | .streamUpdate inc => 0 ≤ inc

/-- One step of the send-path transition system. A DATA offer charges both
windows; a `WINDOW_UPDATE` that faults (increment 0 or overflow) is rejected —
the endpoint would tear the connection down, modeled here as leaving the state
unchanged (a faulting update never advances the accounting). -/
def Send.step (s : Send) : Op → Send
  | .data offered => (s.sendData offered).next
  | .connUpdate inc =>
      match windowUpdate s.conn inc with
      | .ok c' => { s with conn := c' }
      | .error _ => s
  | .streamUpdate inc =>
      match windowUpdate s.stream inc with
      | .ok st' => { s with stream := st' }
      | .error _ => s

/-- Run a sequence of operations through the send-path step. -/
def Send.run (s : Send) (ops : List Op) : Send :=
  ops.foldl Send.step s

/-- **The step preserves well-formedness**. -/
theorem Send.step_WF {s : Send} {o : Op} (hwf : s.WF) (hv : o.valid) :
    (s.step o).WF := by
  cases o with
  | data offered =>
      exact sendData_WF (s := s) (offered := offered) hv hwf
  | connUpdate inc =>
      simp only [Send.step]
      cases hupd : windowUpdate s.conn inc with
      | error e => exact hwf
      | ok c' => exact ⟨windowUpdate_WF hv hwf.1 hupd, hwf.2⟩
  | streamUpdate inc =>
      simp only [Send.step]
      cases hupd : windowUpdate s.stream inc with
      | error e => exact hwf
      | ok st' => exact ⟨hwf.1, windowUpdate_WF hv hwf.2 hupd⟩

/-- **The run preserves well-formedness**: from a well-formed start, under any
sequence of valid operations, the reached state is well-formed. -/
theorem Send.run_WF : ∀ (ops : List Op) (s : Send),
    s.WF → (∀ o ∈ ops, o.valid) → (s.run ops).WF
  | [], _, hwf, _ => hwf
  | o :: rest, s, hwf, hv => by
      have hstep : (s.step o).WF :=
        Send.step_WF hwf (hv o (List.mem_cons_self o rest))
      have hrest : ∀ o' ∈ rest, o'.valid :=
        fun o' ho' => hv o' (List.mem_cons_of_mem o ho')
      exact Send.run_WF rest (s.step o) hstep hrest

/-- **Property 1, trajectory form**: from a well-formed start, under **any**
interleaving of DATA sends and `WINDOW_UPDATE`s, both send windows remain
non-negative — no DATA frame ever drives either window negative. -/
theorem Send.run_windows_nonneg {s : Send} {ops : List Op}
    (hwf : s.WF) (hv : ∀ o ∈ ops, o.valid) :
    0 ≤ (s.run ops).conn.window ∧ 0 ≤ (s.run ops).stream.window := by
  obtain ⟨hc, hs⟩ := Send.run_WF ops s hwf hv
  exact ⟨hc.2.1, hs.2.1⟩

/-- **Property 2, trajectory form**: every reachable state is conserved. -/
theorem Send.run_conserved {s : Send} {ops : List Op}
    (hwf : s.WF) (hv : ∀ o ∈ ops, o.valid) :
    (s.run ops).conn.Conserved ∧ (s.run ops).stream.Conserved := by
  obtain ⟨hc, hs⟩ := Send.run_WF ops s hwf hv
  exact ⟨hc.1, hs.1⟩

/-- **Property 2, stream-accounting form**: at every reachable state, the total
DATA bytes consumed on the stream equal its initial window plus all
`WINDOW_UPDATE` increments minus the current window — no bytes conjured or
lost. -/
theorem Send.run_stream_accounting {s : Send} {ops : List Op}
    (hwf : s.WF) (hv : ∀ o ∈ ops, o.valid) :
    (s.run ops).stream.consumed =
      (s.run ops).stream.initial + (s.run ops).stream.increments
        - (s.run ops).stream.window :=
  Window.consumed_eq (Send.run_conserved hwf hv).2

/-- **Property 2, connection-accounting form**: the same conservation identity
holds for the shared connection window (its `consumed` aggregates every
stream's sends). -/
theorem Send.run_conn_accounting {s : Send} {ops : List Op}
    (hwf : s.WF) (hv : ∀ o ∈ ops, o.valid) :
    (s.run ops).conn.consumed =
      (s.run ops).conn.initial + (s.run ops).conn.increments
        - (s.run ops).conn.window :=
  Window.consumed_eq (Send.run_conserved hwf hv).1

/-! ## Wire vectors, checker-verified -/

/-- A default initial window (65535) creates cleanly. -/
example :
    create 65535
      = .ok { window := 65535, initial := 65535, increments := 0, consumed := 0 } := by rfl

/-- An initial window one past the cap (`2^31`) is a FLOW_CONTROL_ERROR. -/
example : create 2147483648 = .error .flowControlError := by rfl

/-- A `WINDOW_UPDATE` of 0 is a PROTOCOL_ERROR. -/
example (w : Window) : windowUpdate w 0 = .error .protocolError := windowUpdate_zero w

/-- A `WINDOW_UPDATE` that pushes a full window past `2^31 − 1` is a
FLOW_CONTROL_ERROR. -/
example :
    windowUpdate { window := 2147483647, initial := 2147483647, increments := 0, consumed := 0 } 1
      = .error .flowControlError := by rfl

/-- A valid `WINDOW_UPDATE` credits the window and grows the increment ledger. -/
example :
    windowUpdate { window := 100, initial := 100, increments := 0, consumed := 0 } 50
      = .ok { window := 150, initial := 100, increments := 50, consumed := 0 } := by rfl

/-- A send within credit emits everything and charges both windows. -/
example :
    Send.sendData
        { conn := { window := 100, initial := 100, increments := 0, consumed := 0 },
          stream := { window := 100, initial := 100, increments := 0, consumed := 0 } } 40
      = { emitted := 40, parked := 0,
          next :=
            { conn := { window := 60, initial := 100, increments := 0, consumed := 40 },
              stream := { window := 60, initial := 100, increments := 0, consumed := 40 } } } := by rfl

/-- A send limited by the smaller (connection) window emits `min` and parks the
rest; the stream window is charged by the same emitted amount. -/
example :
    Send.sendData
        { conn := { window := 30, initial := 100, increments := 0, consumed := 70 },
          stream := { window := 100, initial := 100, increments := 0, consumed := 0 } } 50
      = { emitted := 30, parked := 20,
          next :=
            { conn := { window := 0, initial := 100, increments := 0, consumed := 100 },
              stream := { window := 70, initial := 100, increments := 0, consumed := 30 } } } := by rfl

/-- A flow-blocked send (no credit) parks everything and emits nothing — the
DATA is buffered, not dropped. -/
example :
    Send.sendData
        { conn := { window := 0, initial := 100, increments := 0, consumed := 100 },
          stream := { window := 50, initial := 100, increments := 0, consumed := 50 } } 30
      = { emitted := 0, parked := 30,
          next :=
            { conn := { window := 0, initial := 100, increments := 0, consumed := 100 },
              stream := { window := 50, initial := 100, increments := 0, consumed := 50 } } } := by rfl

end FlowControl
end H2

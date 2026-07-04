import H2.FlowControl

/-!
# Correctness of HTTP/2 flow-control window arithmetic (RFC 9113 §5.2, §6.9)

`H2/FlowControl.lean` establishes *safety* facts about the send-side flow-control
machine — windows stay non-negative, the ledger is conserved, faults are typed,
flow-blocked DATA is parked. Those say the machine never misbehaves. They do not,
on their own, say the window *arithmetic* is the arithmetic the RFC mandates: that
a DATA frame of length `L` moves the window by exactly `L` (not `L−1`, not `2L`,
not `0`), that a `WINDOW_UPDATE` of `N` moves it by exactly `N`, and that the
sender is never permitted to transmit past the advertised window.

This file upgrades that to a *correctness* claim. It gives an **independent
specification** of the RFC-mandated window arithmetic, written *from the RFC*
over a plain signed integer window (`Int`) with no reference to the
implementation's `Window` structure, its ghost ledger, or its `Except` result
type. Then it proves the implementation **refines** that specification: the
observable window value the implementation computes equals the value the RFC
specification dictates, and the implementation's typed faults fire on exactly the
RFC's fault conditions.

## The RFC text specified here

* **RFC 9113 §5.2.1 (Flow-Control Principles):** "Flow control is directional …
  A receiver … sends a WINDOW_UPDATE frame … Flow control is based on
  WINDOW_UPDATE frames. Senders … send data up to the limit their receiver
  allows." — the sender MUST NOT exceed the window.
* **RFC 9113 §6.9 (WINDOW_UPDATE):** "The payload of a WINDOW_UPDATE frame is one
  reserved bit plus an unsigned 31-bit integer indicating the number of octets
  that the sender can transmit in addition to the existing flow-control window."
  — a `WINDOW_UPDATE` of `N` increases the window by exactly `N`. "A receiver
  MUST treat the receipt of a WINDOW_UPDATE frame with a flow-control window
  increment of 0 as a … PROTOCOL_ERROR."
* **RFC 9113 §6.9.1 (The Flow-Control Window):** "After sending a
  flow-controlled frame, the sender reduces the space available in both windows
  by the length of the transmitted frame." — a DATA frame of length `L` reduces
  the window by exactly `L`. "The sender MUST NOT send a flow-controlled frame
  with a length that exceeds the space available in either of the flow-control
  windows." "A sender MUST NOT allow a flow-control window to exceed 2^31−1
  octets. If a sender receives a WINDOW_UPDATE that causes a flow-control window
  to exceed this maximum, it MUST terminate … the connection … with an error
  code of FLOW_CONTROL_ERROR."

The specification below is these four sentences, written as integer arithmetic.
-/

namespace H2FlowSpec

/-! ## The independent specification (RFC 9113 §5.2, §6.9), over a plain `Int`
window — no reference to the implementation. -/

/-- RFC 9113 §6.9.1: a flow-control window MUST NOT exceed `2^31 − 1` octets. -/
def maxWindow : Int := 2 ^ 31 - 1

/-- **RFC 9113 §6.9.1 — the decrement law.** After sending a DATA frame of length
`L`, the available space in the flow-control window is reduced by exactly `L`. -/
def windowAfterData (window L : Int) : Int := window - L

/-- **RFC 9113 §6.9 — the increment law.** A `WINDOW_UPDATE` of `N` increases the
flow-control window by exactly `N`. -/
def windowAfterUpdate (window N : Int) : Int := window + N

/-- **RFC 9113 §5.2.1 / §6.9.1 — sendability.** A sender MUST NOT send a
flow-controlled frame whose length `L` exceeds the space available in the window;
equivalently, a length is transmittable now iff it does not exceed the window. -/
def sendable (window L : Int) : Prop := L ≤ window

/-- The RFC-mandated classification of a `WINDOW_UPDATE` of `N` against a window
(RFC 9113 §6.9 + §6.9.1), independent of the implementation's `Except`/`Err`
types: a `0` increment is a PROTOCOL_ERROR, an increment that would push the
window past `2^31 − 1` is a FLOW_CONTROL_ERROR, otherwise the window becomes
`window + N`. -/
inductive UpdateOutcome where
  /-- Increment of `0` (RFC 9113 §6.9): a PROTOCOL_ERROR. -/
  | protocolError
  /-- Increment overflows the `2^31 − 1` cap (RFC 9113 §6.9.1): a
  FLOW_CONTROL_ERROR. -/
  | flowControlError
  /-- Accepted: the new window value the RFC dictates. -/
  | accept (newWindow : Int)
deriving Repr, DecidableEq

/-- **RFC 9113 §6.9 / §6.9.1 — the `WINDOW_UPDATE` specification.** -/
def updateSpec (window N : Int) : UpdateOutcome :=
  if N = 0 then
    .protocolError
  else if maxWindow < windowAfterUpdate window N then
    .flowControlError
  else
    .accept (windowAfterUpdate window N)

/-- **RFC 9113 §5.2.1 / §6.9.1 — the maximal amount a conformant sender may emit
now.** Bounded above by the offered payload and by the space in each window; a
window driven negative by a `SETTINGS` reduction grants no credit (floored at 0),
so the sender defers rather than sends. This says nothing about the ledger — it
is the RFC's transmission budget as an integer. -/
def emittableSpec (offered conn stream : Int) : Int :=
  min offered (max 0 (min conn stream))

/-! ## Non-vacuity of the specification itself: the predicates reject wrong
behavior. A specification that accepted everything would be useless; these show
the RFC predicates genuinely discriminate. -/

/-- The decrement law is non-trivial: an implementation that IGNORED the frame
length (left the window unchanged) contradicts it for any positive `L`. -/
theorem ignoring_length_violates_decrement :
    ¬ ∀ (window L : Int), 0 < L → window = windowAfterData window L := by
  intro h
  have := h 10 1 (by decide)
  simp [windowAfterData] at this

/-- The increment law is non-trivial: an implementation that DOUBLED the
increment contradicts it whenever `N ≠ 0`. -/
theorem doubling_increment_violates_law :
    ¬ ∀ (window N : Int), windowAfterUpdate window N = window + 2 * N := by
  intro h
  have := h 0 1
  simp [windowAfterUpdate] at this

/-- Sendability is non-trivial: an implementation that OVER-SENT (transmitted a
frame longer than the window) contradicts it whenever the length exceeds the
window. -/
theorem oversend_violates_sendable : ¬ sendable 3 5 := by simp [sendable]

/-- The `WINDOW_UPDATE` classification is discriminating: a `0` increment is a
PROTOCOL_ERROR, a cap-overflowing increment is a FLOW_CONTROL_ERROR, and an
in-range increment yields exactly `window + N` — three distinct outcomes. -/
theorem updateSpec_discriminates :
    updateSpec 100 0 = .protocolError
      ∧ updateSpec maxWindow 1 = .flowControlError
      ∧ updateSpec 100 50 = .accept 150 := by
  refine ⟨rfl, ?_, rfl⟩
  decide

end H2FlowSpec

/-! ## The refinement: the implementation computes the RFC arithmetic.

Each theorem maps an observable of `H2.FlowControl` onto the independent
specification above. `H2.FlowControl.Window` carries a ghost ledger and returns
`Except Err Window`; the specification carries neither. The refinement projects
the implementation's *window value* (its only externally observable quantity) and
its *fault* and shows they agree with the RFC specification on **all** inputs. -/

namespace H2FlowCorrect

open H2FlowSpec
open H2.FlowControl

/-- The observable of a `windowUpdate` result: its fault, or the window value it
accepted. This is the refinement mapping from the implementation's rich
`Except Err Window` onto the specification's `UpdateOutcome` — it forgets the
ghost ledger. -/
def updateObs : Except Err Window → UpdateOutcome
  | .error .protocolError => .protocolError
  | .error .flowControlError => .flowControlError
  | .ok w => .accept w.window

/-- **Refinement A — `WINDOW_UPDATE` computes the RFC arithmetic (RFC 9113 §6.9,
§6.9.1).** For every window and every increment, the implementation's observable
outcome equals the specification's: it faults with PROTOCOL_ERROR exactly on a
`0` increment, faults with FLOW_CONTROL_ERROR exactly on a cap overflow, and
otherwise accepts exactly `window + N`. A mutant that incremented by anything but
`N`, or that failed to reject `0` / overflow, breaks this. -/
theorem windowUpdate_refines (w : Window) (inc : Int) :
    updateObs (windowUpdate w inc) = updateSpec w.window inc := by
  unfold windowUpdate updateSpec windowAfterUpdate
    H2FlowSpec.maxWindow H2.FlowControl.maxWindow
  by_cases h0 : inc = 0
  · simp [h0, updateObs]
  · rw [if_neg h0, if_neg h0]
    by_cases hov : (2 : Int) ^ 31 - 1 < w.window + inc
    · rw [if_pos hov, if_pos hov]; rfl
    · rw [if_neg hov, if_neg hov]; rfl

/-- **Refinement B — a DATA charge is the RFC decrement law (RFC 9113 §6.9.1).**
Charging a frame of length `L` moves the window to exactly `windowAfterData`, i.e.
`window − L`. A mutant `charge` that ignored `L` (or used `L−1`, `2L`, …) breaks
this. -/
theorem charge_refines (w : Window) (L : Int) :
    (w.charge L).window = windowAfterData w.window L := rfl

/-- **Refinement C — a DATA send decrements by exactly the emitted length
(RFC 9113 §6.9.1).** After offering DATA, the successor connection window is the
RFC decrement of the prior window by the number of bytes emitted; likewise for the
stream window. This ties the send path to the decrement law: the window moves by
exactly the transmitted length, no more, no less. -/
theorem sendData_conn_decrement (s : Send) (offered : Int) :
    (s.sendData offered).next.conn.window
      = windowAfterData s.conn.window (s.sendData offered).emitted := rfl

theorem sendData_stream_decrement (s : Send) (offered : Int) :
    (s.sendData offered).next.stream.window
      = windowAfterData s.stream.window (s.sendData offered).emitted := rfl

/-- **Refinement D — the sender never over-sends (RFC 9113 §5.2.1 / §6.9.1).** On
a non-negative window, the bytes the implementation emits are `sendable` on the
connection window — the transmitted length never exceeds the available space. A
mutant that emitted the full offered amount past the window breaks this. -/
theorem sendData_conn_sendable (s : Send) (offered : Int) (h : 0 ≤ s.conn.window) :
    sendable s.conn.window (s.sendData offered).emitted :=
  sendData_emitted_le_conn s offered h

theorem sendData_stream_sendable (s : Send) (offered : Int) (h : 0 ≤ s.stream.window) :
    sendable s.stream.window (s.sendData offered).emitted :=
  sendData_emitted_le_stream s offered h

/-- **Refinement E — the sender emits exactly the RFC transmission budget
(RFC 9113 §5.2.1 / §6.9.1).** The implementation emits precisely
`emittableSpec offered conn stream = min(offered, max(0, min conn stream))`: it
sends all it is offered up to the space in the binding window, and no more. This
pins emission from *both* sides — it forbids both over-sending (Refinement D) and
gratuitously withholding creditable bytes — so the emitted amount is uniquely
determined by the RFC budget, not merely bounded by it. -/
theorem sendData_emits_budget (s : Send) (offered : Int) :
    (s.sendData offered).emitted
      = emittableSpec offered s.conn.window s.stream.window := rfl

/-! ## Refinement on concrete vectors, and mutant rejection.

The equalities above are universally quantified; these ground them and exhibit
the discrimination: the correct implementation hits the RFC value, and named
wrong outputs miss it. -/

/-- A valid `WINDOW_UPDATE`: the implementation's observable equals the RFC value
`window + N = 150`. -/
example : updateObs (windowUpdate ⟨100, 100, 0, 0⟩ 50) = updateSpec 100 50 := rfl

/-- The RFC value here is `.accept 150`; a doubling mutant (`.accept 200`) is NOT
that value — Refinement A would reject it. -/
example : updateSpec 100 50 = .accept 150 ∧ updateSpec 100 50 ≠ .accept 200 := by
  decide

/-- A charge of length 40 decrements to exactly 60; an ignore-length mutant
(window unchanged at 100) is NOT the RFC value — Refinement B/C would reject it. -/
example :
    (Window.charge ⟨100, 100, 0, 0⟩ 40).window = windowAfterData 100 40
      ∧ windowAfterData 100 40 ≠ (100 : Int) := by
  refine ⟨rfl, ?_⟩
  decide

/-- A send offered 50 bytes against a connection window of 30 emits exactly 30
(the RFC budget) and decrements the window to 0; emitting the full 50 would
over-send (`¬ sendable 30 50`) — Refinement D/E would reject it. -/
example :
    (Send.sendData ⟨⟨30, 100, 0, 70⟩, ⟨100, 100, 0, 0⟩⟩ 50).emitted
        = emittableSpec 50 30 100
      ∧ emittableSpec 50 30 100 = 30
      ∧ ¬ sendable 30 50 := by
  refine ⟨rfl, ?_, ?_⟩
  · decide
  · simp [sendable]

end H2FlowCorrect

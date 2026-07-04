import H2.Basic

/-!
# The per-stream state machine (RFC 9113 §5.1 / RFC 7540 §5.1)

Each HTTP/2 stream progresses through a fixed set of states driven by the
frames sent and received on it. This models the state machine as a **total
deterministic step** `step : StreamState → Event → Outcome`, where `Outcome` is
either an accepted transition (`next`) or a typed rejection (`streamClosed` /
`protocolError`).

Headline properties:

* `step_total` / `step_deterministic` — the step is a total function
  (defined on every state/event) and deterministic (a function).
* `stepState_closed` — **closed is absorbing**: no event moves a closed stream
  to any other state.
* `recvData_halfClosedRemote` / `recvData_closed` and the invariant
  `recvData_accepted_legal` — **no DATA is delivered to a stream whose remote
  half is closed**: a `recvData` event is accepted only from `open` or
  `halfClosedLocal`, and is rejected (`streamClosed`) in `halfClosedRemote` and
  `closed` (RFC 9113 §5.1). The set `remoteClosed = {halfClosedRemote, closed}`
  is forward-closed under the step (`remoteClosed_step`, `remoteClosed_run`),
  so once the peer's sending half is closed, DATA is refused on the stream for
  the rest of the connection (`recvData_rejected_after_remoteClosed`) — a
  genuine trajectory invariant.
-/

namespace H2
namespace Stream

/-- The per-stream states (RFC 9113 §5.1). `reservedLocal`/`reservedRemote`
arise from PUSH_PROMISE (server push); the reference server does not push, so
those edges are transcribed from the RFC rather than an implementation. -/
inductive StreamState where
  | idle
  | reservedLocal
  | reservedRemote
  | open
  | halfClosedLocal
  | halfClosedRemote
  | closed
deriving Repr, DecidableEq

/-- Events that drive a stream. `recv*` are frames received from the peer;
`send*` are frames the endpoint sends. `endStream` is the `END_STREAM` flag. -/
inductive Event where
  | recvHeaders (endStream : Bool)
  | sendHeaders (endStream : Bool)
  | recvData (endStream : Bool)
  | sendData (endStream : Bool)
  | recvPushPromise
  | sendPushPromise
  | recvRstStream
  | sendRstStream
deriving Repr, DecidableEq

/-- The outcome of one step: an accepted transition to `next`, or a typed
rejection. `streamClosed` is RFC 9113's STREAM_CLOSED (a frame arriving on a
stream whose relevant half is closed); `protocolError` is a frame that is not
permitted in the current state at all. -/
inductive Outcome where
  | next (s : StreamState)
  | streamClosed
  | protocolError
deriving Repr, DecidableEq

/-- The total deterministic transition function (RFC 9113 §5.1). Every
state/event pair maps to exactly one outcome. -/
def step : StreamState → Event → Outcome
  -- idle
  | .idle, .recvHeaders es => .next (if es then .halfClosedRemote else .open)
  | .idle, .sendHeaders es => .next (if es then .halfClosedLocal else .open)
  | .idle, .recvPushPromise => .next .reservedRemote
  | .idle, .sendPushPromise => .next .reservedLocal
  | .idle, _ => .protocolError
  -- reserved (local): we sent PUSH_PROMISE; we may send response HEADERS
  | .reservedLocal, .sendHeaders _ => .next .halfClosedRemote
  | .reservedLocal, .recvRstStream => .next .closed
  | .reservedLocal, .sendRstStream => .next .closed
  | .reservedLocal, _ => .protocolError
  -- reserved (remote): the peer sent PUSH_PROMISE; we may receive HEADERS
  | .reservedRemote, .recvHeaders _ => .next .halfClosedLocal
  | .reservedRemote, .recvRstStream => .next .closed
  | .reservedRemote, .sendRstStream => .next .closed
  | .reservedRemote, _ => .protocolError
  -- open
  | .open, .recvData es => .next (if es then .halfClosedRemote else .open)
  | .open, .sendData es => .next (if es then .halfClosedLocal else .open)
  | .open, .recvHeaders es => .next (if es then .halfClosedRemote else .open)
  | .open, .sendHeaders es => .next (if es then .halfClosedLocal else .open)
  | .open, .recvRstStream => .next .closed
  | .open, .sendRstStream => .next .closed
  | .open, _ => .protocolError
  -- half-closed (local): we sent END_STREAM; we may still receive
  | .halfClosedLocal, .recvData es => .next (if es then .closed else .halfClosedLocal)
  | .halfClosedLocal, .recvHeaders es => .next (if es then .closed else .halfClosedLocal)
  | .halfClosedLocal, .recvRstStream => .next .closed
  | .halfClosedLocal, .sendRstStream => .next .closed
  | .halfClosedLocal, .sendData _ => .streamClosed
  | .halfClosedLocal, .sendHeaders _ => .streamClosed
  | .halfClosedLocal, _ => .protocolError
  -- half-closed (remote): the peer sent END_STREAM; we may still send
  | .halfClosedRemote, .sendData es => .next (if es then .closed else .halfClosedRemote)
  | .halfClosedRemote, .sendHeaders es => .next (if es then .closed else .halfClosedRemote)
  | .halfClosedRemote, .recvRstStream => .next .closed
  | .halfClosedRemote, .sendRstStream => .next .closed
  | .halfClosedRemote, .recvData _ => .streamClosed
  | .halfClosedRemote, .recvHeaders _ => .streamClosed
  | .halfClosedRemote, _ => .protocolError
  -- closed: absorbing; a reset is idempotent, everything else is STREAM_CLOSED
  | .closed, .recvRstStream => .next .closed
  | .closed, .sendRstStream => .next .closed
  | .closed, _ => .streamClosed

/-- The state-only view of the step: an accepted transition moves the state; a
rejection leaves it unchanged. -/
def stepState (s : StreamState) (e : Event) : StreamState :=
  match step s e with
  | .next s' => s'
  | _ => s

/-! ## Totality and determinism -/

/-- **Totality**: the step is defined on every state/event pair. -/
theorem step_total (s : StreamState) (e : Event) : ∃ o, step s e = o :=
  ⟨step s e, rfl⟩

/-- **Determinism**: the step is a function — equal inputs give equal
outcomes. -/
theorem step_deterministic (s : StreamState) (e : Event) (o₁ o₂ : Outcome)
    (h₁ : step s e = o₁) (h₂ : step s e = o₂) : o₁ = o₂ :=
  h₁.symm.trans h₂

/-! ## Closed is absorbing -/

/-- **Closed is absorbing**: no event moves a closed stream anywhere else. -/
theorem stepState_closed (e : Event) : stepState .closed e = .closed := by
  cases e <;> rfl

/-- Outcome-level form: whenever the step from `closed` accepts a transition,
the target is still `closed`. -/
theorem step_closed_no_reopen (e : Event) (s' : StreamState)
    (h : step .closed e = .next s') : s' = .closed := by
  cases e <;> simp_all [step]

/-! ## No DATA on a remote-closed stream -/

/-- Receiving DATA on a half-closed (remote) stream is rejected (RFC 9113
§5.1). -/
theorem recvData_halfClosedRemote (es : Bool) :
    step .halfClosedRemote (.recvData es) = .streamClosed := rfl

/-- Receiving DATA on a closed stream is rejected. -/
theorem recvData_closed (es : Bool) :
    step .closed (.recvData es) = .streamClosed := rfl

/-- **The per-stream well-formedness invariant**: a `recvData` event is
accepted only from a state whose remote half is still open — `open` or
`halfClosedLocal`. Equivalently, DATA is never delivered in `idle`,
`reserved*`, `halfClosedRemote`, or `closed`. -/
theorem recvData_accepted_legal (s s' : StreamState) (es : Bool)
    (h : step s (.recvData es) = .next s') :
    s = .open ∨ s = .halfClosedLocal := by
  cases s <;> simp_all [step]

/-- The predicate: the stream's remote (peer's sending) half is closed. -/
def remoteClosed : StreamState → Bool
  | .halfClosedRemote => true
  | .closed => true
  | _ => false

/-- **Forward-closure**: the remote-closed set is closed under the step — once
the peer's sending half is closed, no event reopens it. -/
theorem remoteClosed_step (s : StreamState) (e : Event) (h : remoteClosed s = true) :
    remoteClosed (stepState s e) = true := by
  cases s
  case halfClosedRemote => cases e <;> first | rfl | (rename_i b; cases b <;> rfl)
  case closed => cases e <;> first | rfl | (rename_i b; cases b <;> rfl)
  all_goals exact absurd h (by simp [remoteClosed])

/-- DATA is refused from any remote-closed state. -/
theorem recvData_remoteClosed (s : StreamState) (b : Bool) (h : remoteClosed s = true) :
    step s (.recvData b) = .streamClosed := by
  cases s <;> first | rfl | exact absurd h (by simp [remoteClosed])

/-! ## Multi-step trajectory invariants -/

/-- Run a list of events through `stepState`. -/
def run (s : StreamState) (es : List Event) : StreamState := es.foldl stepState s

/-- Closed is absorbing over whole runs. -/
theorem run_closed (es : List Event) : run .closed es = .closed := by
  induction es with
  | nil => rfl
  | cons e rest ih =>
    simp only [run, List.foldl_cons, stepState_closed]
    exact ih

/-- **The remote-closed trajectory invariant**: starting from a remote-closed
state, every reachable state is still remote-closed. -/
theorem remoteClosed_run (s : StreamState) (es : List Event) (h : remoteClosed s = true) :
    remoteClosed (run s es) = true := by
  induction es generalizing s with
  | nil => simpa [run] using h
  | cons e rest ih =>
    simp only [run, List.foldl_cons]
    exact ih (stepState s e) (remoteClosed_step s e h)

/-- **The safety consequence**: from a remote-closed state, DATA is refused for
the rest of the connection — under *any* interleaving of subsequent events, a
later `recvData` is always `streamClosed`. -/
theorem recvData_rejected_after_remoteClosed (s : StreamState) (es : List Event)
    (b : Bool) (h : remoteClosed s = true) :
    step (run s es) (.recvData b) = .streamClosed :=
  recvData_remoteClosed (run s es) b (remoteClosed_run s es h)

/-! ## Transition vectors, checker-verified -/

/-- idle + HEADERS (no END_STREAM) opens the stream. -/
example : step .idle (.recvHeaders false) = .next .open := rfl
/-- idle + HEADERS with END_STREAM half-closes the remote side. -/
example : step .idle (.recvHeaders true) = .next .halfClosedRemote := rfl
/-- open + peer END_STREAM (via DATA) half-closes the remote side. -/
example : step .open (.recvData true) = .next .halfClosedRemote := rfl
/-- Sending our END_STREAM from half-closed (remote) fully closes the stream. -/
example : step .halfClosedRemote (.sendData true) = .next .closed := rfl
/-- DATA into a half-closed (remote) stream is STREAM_CLOSED. -/
example : step .halfClosedRemote (.recvData false) = .streamClosed := rfl
/-- RST_STREAM closes an open stream. -/
example : step .open .recvRstStream = .next .closed := rfl
/-- A closed stream ignores further resets, staying closed. -/
example : stepState .closed .recvRstStream = .closed := rfl

end Stream
end H2

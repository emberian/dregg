/-
Send — per-socket send-path flow control and partial-write ordering.

The send path for one TCP socket, sans-IO. A producer hands the machine a
payload; the machine first attempts an *inline* non-blocking send (the kernel
accepts some prefix), and if any remainder is left it queues that remainder
as the single in-flight asynchronous send and marks the socket *blocked*.
While blocked, further payloads are refused outright (`SendResult.blocked`) —
the producer must wait for the write-ready notification. Completions advance
the in-flight remainder; a short completion re-queues the unsent tail (the
socket stays blocked); a full completion unblocks the socket.

The kernel's behavior is an explicit input: how many bytes each attempt
accepts arrives as event data (`accept` / `m`), never as an effect — the
theorems quantify over every kernel behavior.

The point of the machine is the **byte-stream ordering theorem**: at every
reachable state,

    wire ++ pendingBytes ++ killed = flatten accepted

— the bytes on the wire, followed by the queued remainder, followed by any
bytes explicitly abandoned at close, are *exactly* the concatenation of the
accepted payloads, in submission order. Nothing is reordered across a
partial write, nothing is duplicated, and nothing vanishes silently: every
accepted byte is on the wire, still queued, or in the explicit kill ledger.

Two structural decisions are deliberate and load-bearing:

  1. **Blocked-set refusal.** A machine without the blocked state cannot
     even state the no-overtake property — a payload accepted while a
     remainder is queued would interleave behind it. Here the refusal is
     `blocked_rejects`: a submit against a blocked socket is a no-op.
  2. **`full` implies no inline progress.** The transient
     resource-exhaustion result (`SendResult.full`, e.g. a full submission
     queue) is only issued *before* any bytes reach the wire, so the
     producer's retry of the same payload cannot duplicate a prefix. A
     design that attempts the inline send first and only then discovers the
     queue is full has already emitted the prefix and must not report
     plain `full`.
-/

namespace Flow

/-- Result code returned to the producer. -/
inductive SendResult where
  /-- Payload accepted: inline-sent in full, or partially sent with the
  remainder queued as the in-flight send. -/
  | submitted
  /-- Socket is blocked on an in-flight remainder; payload NOT accepted.
  The producer must stop until write-ready fires. -/
  | blocked
  /-- Transient resource exhaustion; payload NOT accepted, and no prefix
  of it reached the wire. Retry after flushing. -/
  | full
  /-- Socket already closed; payload NOT accepted. -/
  | closed
  /-- Acknowledgement for non-submit events. -/
  | ok
  deriving Repr, DecidableEq, Inhabited

/-- Per-socket send state, over an abstract byte type `α`.

`wire`, `pending`, `closed` are the operational state; `accepted` and
`killed` are ghost ledgers for the ordering theorem: `accepted` records
every payload the machine took responsibility for (result `submitted`), in
order; `killed` records bytes explicitly abandoned when the socket dies
with a remainder still queued. -/
structure SendConn (α : Type u) where
  /-- Bytes the kernel has accepted, in wire order. -/
  wire : List α
  /-- The single in-flight remainder, if the socket is blocked. -/
  pending : Option (List α)
  /-- The socket has been closed (error or explicit close). -/
  closed : Bool
  /-- Ghost: accepted payloads, in submission order. -/
  accepted : List (List α)
  /-- Ghost: bytes explicitly abandoned at close — the kill ledger. -/
  killed : List α

/-- The remainder as bytes (empty when not blocked). -/
def SendConn.pendingBytes (s : SendConn α) : List α := s.pending.getD []

/-- A fresh socket. -/
def SendConn.init : SendConn α := ⟨[], none, false, [], []⟩

/-- Events driving one socket's send path. Kernel behavior (how many bytes
each attempt accepts) is input data. -/
inductive SendEv (α : Type u) where
  /-- Producer submits `data`; the inline attempt accepts
  `min accept data.length` bytes. -/
  | submit (data : List α) (accept : Nat)
  /-- Producer submits, but the machine hits transient resource exhaustion
  before any byte reaches the wire. -/
  | submitFull (data : List α)
  /-- The in-flight send completes with `m` bytes written; a short
  completion re-queues the unsent tail. -/
  | complete (m : Nat)
  /-- The in-flight send fails: the remainder is explicitly killed and the
  socket closes. -/
  | completeErr
  /-- The socket is closed; any queued remainder is explicitly killed. -/
  | close

/-- One step of the send machine. -/
def SendConn.step (s : SendConn α) : SendEv α → SendConn α × SendResult
  | .submit data accept =>
    if s.closed then (s, .closed)
    else
      match s.pending with
      | some _ => (s, .blocked)
      | none =>
        let n := min accept data.length
        if n = data.length then
          ({ s with wire := s.wire ++ data,
                    accepted := s.accepted ++ [data] }, .submitted)
        else
          ({ s with wire := s.wire ++ data.take n,
                    pending := some (data.drop n),
                    accepted := s.accepted ++ [data] }, .submitted)
  | .submitFull _ =>
    if s.closed then (s, .closed)
    else
      match s.pending with
      | some _ => (s, .blocked)
      | none => (s, .full)
  | .complete m =>
    match s.pending with
    | none => (s, .ok)
    | some rem =>
      let k := min m rem.length
      if k = rem.length then
        ({ s with wire := s.wire ++ rem, pending := none }, .ok)
      else
        ({ s with wire := s.wire ++ rem.take k,
                  pending := some (rem.drop k) }, .ok)
  | .completeErr =>
    ({ s with pending := none, closed := true,
              killed := s.killed ++ s.pendingBytes }, .ok)
  | .close =>
    ({ s with pending := none, closed := true,
              killed := s.killed ++ s.pendingBytes }, .ok)

/-- Run a trace of events. -/
def SendConn.run (s : SendConn α) : List (SendEv α) → SendConn α
  | [] => s
  | e :: es => ((s.step e).1).run es

/-- The machine invariant.

1. The flow identity: wire, then queued remainder, then kill ledger, is
   exactly the accepted payloads concatenated in order.
2. The kill ledger only fills at close.
3. A closed socket holds no remainder. -/
def SendConn.Inv (s : SendConn α) : Prop :=
  s.wire ++ (s.pendingBytes ++ s.killed) = s.accepted.flatten ∧
  (s.closed = false → s.killed = []) ∧
  (s.closed = true → s.pending = none)

theorem SendConn.init_inv : (SendConn.init : SendConn α).Inv := by
  simp [Inv, init, pendingBytes]

/-- **Preservation**: every event preserves the flow identity. -/
theorem SendConn.step_inv (s : SendConn α) (e : SendEv α) (h : s.Inv) :
    (s.step e).1.Inv := by
  obtain ⟨hflow, hkill, hpend⟩ := h
  cases e with
  | submit data accept =>
    cases hc : s.closed with
    | true =>
      have hred : (s.step (.submit data accept)).1 = s := by simp [step, hc]
      rw [hred]; exact ⟨hflow, hkill, hpend⟩
    | false =>
      have hk : s.killed = [] := hkill hc
      cases hp : s.pending with
      | some rem =>
        have hred : (s.step (.submit data accept)).1 = s := by
          simp [step, hc, hp]
        rw [hred]; exact ⟨hflow, hkill, hpend⟩
      | none =>
        have hw : s.wire = s.accepted.flatten := by
          simpa [pendingBytes, hp, hk] using hflow
        by_cases hn : min accept data.length = data.length
        · simp [step, hc, hp, hn, Inv, pendingBytes, hk, hw]
        · simp [step, hc, hp, hn, Inv, pendingBytes, hk, hw,
            List.take_append_drop]
  | submitFull data =>
    cases hc : s.closed with
    | true =>
      have hred : (s.step (.submitFull data)).1 = s := by simp [step, hc]
      rw [hred]; exact ⟨hflow, hkill, hpend⟩
    | false =>
      have hred : (s.step (.submitFull data)).1 = s := by
        cases hp : s.pending <;> simp [step, hc, hp]
      rw [hred]; exact ⟨hflow, hkill, hpend⟩
  | complete m =>
    cases hp : s.pending with
    | none =>
      have hred : (s.step (.complete m)).1 = s := by simp [step, hp]
      rw [hred]; exact ⟨hflow, hkill, hpend⟩
    | some rem =>
      have hc : s.closed = false := by
        cases hcc : s.closed with
        | false => rfl
        | true => rw [hpend hcc] at hp; cases hp
      have hk : s.killed = [] := hkill hc
      have hw : s.wire ++ rem = s.accepted.flatten := by
        simpa [pendingBytes, hp, hk] using hflow
      by_cases hm : min m rem.length = rem.length
      · simp [step, hp, hm, Inv, pendingBytes, hk, hc, hw]
      · simp [step, hp, hm, Inv, pendingBytes, hk, hc,
          List.take_append_drop, hw]
  | completeErr =>
    refine ⟨?_, by simp [step], by simp [step]⟩
    cases hc : s.closed with
    | true =>
      have hp := hpend hc
      simpa [step, pendingBytes, hp] using hflow
    | false =>
      have hk := hkill hc
      simpa [step, pendingBytes, hk] using hflow
  | close =>
    refine ⟨?_, by simp [step], by simp [step]⟩
    cases hc : s.closed with
    | true =>
      have hp := hpend hc
      simpa [step, pendingBytes, hp] using hflow
    | false =>
      have hk := hkill hc
      simpa [step, pendingBytes, hk] using hflow

/-- The invariant holds along every trace from every invariant state. -/
theorem SendConn.run_inv (s : SendConn α) (es : List (SendEv α)) (h : s.Inv) :
    (s.run es).Inv := by
  induction es generalizing s with
  | nil => exact h
  | cons e es ih => exact ih _ (s.step_inv e h)

/-- The invariant holds along every trace from a fresh socket. -/
theorem SendConn.run_init_inv (es : List (SendEv α)) :
    ((SendConn.init : SendConn α).run es).Inv :=
  run_inv _ es init_inv

/-- **Order preservation.** The wire is always a prefix of the accepted
payloads' concatenation: no byte overtakes another across partial writes
and blocked/resume cycles. -/
theorem SendConn.wire_prefix (s : SendConn α) (h : s.Inv) :
    ∃ rest, s.wire ++ rest = s.accepted.flatten :=
  ⟨s.pendingBytes ++ s.killed, h.1⟩

/-- **Completeness on drain.** When the socket is open with no in-flight
remainder, the wire equals the accepted payloads' concatenation exactly. -/
theorem SendConn.drained (s : SendConn α) (h : s.Inv)
    (hp : s.pending = none) (hc : s.closed = false) :
    s.wire = s.accepted.flatten := by
  have := h.1
  simpa [pendingBytes, hp, h.2.1 hc] using this

/-- **No overtake.** A submit against a blocked socket is a strict no-op:
the payload cannot interleave behind the queued remainder. -/
theorem SendConn.blocked_rejects (s : SendConn α) (rem : List α)
    (hp : s.pending = some rem) (data : List α) (accept : Nat) :
    (s.step (.submit data accept)).1 = s := by
  cases hc : s.closed <;> simp [step, hc, hp]

/-- ... and the producer observes the refusal. -/
theorem SendConn.blocked_result (s : SendConn α) (rem : List α)
    (hp : s.pending = some rem) (hc : s.closed = false)
    (data : List α) (accept : Nat) :
    (s.step (.submit data accept)).2 = .blocked := by
  simp [step, hc, hp]

/-- **Wire monotonicity.** No step ever rewrites or removes bytes already
on the wire — the wire only grows by appending. -/
theorem SendConn.wire_monotone (s : SendConn α) (e : SendEv α) :
    ∃ t, (s.step e).1.wire = s.wire ++ t := by
  cases e with
  | submit data accept =>
    cases hc : s.closed
    · cases hp : s.pending
      · by_cases hn : min accept data.length = data.length
        · exact ⟨data, by simp [step, hc, hp, hn]⟩
        · exact ⟨data.take (min accept data.length), by simp [step, hc, hp, hn]⟩
      · exact ⟨[], by simp [step, hc, hp]⟩
    · exact ⟨[], by simp [step, hc]⟩
  | submitFull data =>
    cases hc : s.closed
    · cases hp : s.pending
      · exact ⟨[], by simp [step, hc, hp]⟩
      · exact ⟨[], by simp [step, hc, hp]⟩
    · exact ⟨[], by simp [step, hc]⟩
  | complete m =>
    cases hp : s.pending with
    | none => exact ⟨[], by simp [step, hp]⟩
    | some rem =>
      by_cases hm : min m rem.length = rem.length
      · exact ⟨rem, by simp [step, hp, hm]⟩
      · exact ⟨rem.take (min m rem.length), by simp [step, hp, hm]⟩
  | completeErr => exact ⟨[], by simp [step]⟩
  | close => exact ⟨[], by simp [step]⟩

/-- **Unblocking is exact.** A full completion of the remainder unblocks
the socket (the write-ready observable) and puts the entire remainder on
the wire. -/
theorem SendConn.complete_full_unblocks (s : SendConn α) (rem : List α)
    (hp : s.pending = some rem) (m : Nat) (hm : rem.length ≤ m) :
    (s.step (.complete m)).1.pending = none ∧
    (s.step (.complete m)).1.wire = s.wire ++ rem := by
  have : min m rem.length = rem.length := by omega
  simp [step, hp, this]

/-- **Short completions keep the socket blocked** with exactly the unsent
tail queued: the retry cannot lose or reorder the tail. -/
theorem SendConn.complete_short_requeues (s : SendConn α) (rem : List α)
    (hp : s.pending = some rem) (m : Nat) (hm : m < rem.length) :
    (s.step (.complete m)).1.pending = some (rem.drop m) ∧
    (s.step (.complete m)).1.wire = s.wire ++ rem.take m := by
  have h1 : min m rem.length = m := by omega
  have h2 : m ≠ rem.length := by omega
  simp [step, hp, h1, h2]

end Flow

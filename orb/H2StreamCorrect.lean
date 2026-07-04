import H2.Stream

/-!
# Correctness of the HTTP/2 stream state machine (RFC 9113 §5.1)

`H2/Stream.lean` establishes *safety* facts about the per-stream state machine —
the step is total and deterministic, `closed` is absorbing, DATA is refused once
the peer's sending half is closed. Those say the machine never misbehaves. They
do not, on their own, say the machine takes *exactly the edges RFC 9113 §5.1
draws*: that the only accepted transitions are the ones in the RFC's state
diagram, and that a frame arriving on a stream whose relevant half is closed is
answered with STREAM_CLOSED.

This file upgrades that to a *correctness* claim. It gives an **independent
specification** of the RFC-mandated transition relation, transcribed *from the
RFC §5.1 state diagram and its accompanying prose*, as an inductive relation
`Permitted s e s'` that mentions no part of the implementation — not `H2.Stream.step`,
not its `Outcome` type, not its `stepState`/`run` helpers. The permitted edges are
the diagram edges; nothing else is a member of the relation. A companion inductive
`MustStreamClosed s e` transcribes, again independently, the RFC's STREAM_CLOSED
obligation.

Then it proves the implementation **refines** that specification, in both
directions and non-vacuously:

* `refine_accept` — `step s e = next s'` **iff** `Permitted s e s'`. The
  implementation accepts a transition on exactly the state/event pairs the RFC
  diagram permits, and lands on exactly the RFC's target state. An implementation
  that took an edge the diagram omits (or landed on the wrong state) would make
  the forward direction FALSE.
* `refine_stream_closed` — `step s e = streamClosed` **iff** `MustStreamClosed s e`.
  The implementation raises STREAM_CLOSED on exactly the RFC's STREAM_CLOSED
  conditions.
* `closed_frame_is_stream_closed` — the headline consequence: any frame other
  than RST_STREAM arriving on a `closed` stream is a STREAM_CLOSED error.

Non-vacuity is witnessed concretely. `data_on_half_closed_remote_forbidden` shows
the RFC relation has **no** member for DATA received on `halfClosedRemote`, and
`bad_impl_refuted` exhibits a hypothetical implementation that takes that
forbidden edge and proves it *fails* the very refinement statement `refine_accept`
proves for the real implementation. The specification is therefore not the
implementation renamed: a wrong implementation is rejected by it.

## The RFC text specified here

* **RFC 9113 §5.1 (Stream States):** the state diagram over
  `idle`, `reserved (local)`, `reserved (remote)`, `open`,
  `half-closed (local)`, `half-closed (remote)`, and `closed`, with the labelled
  edges driven by HEADERS, PUSH_PROMISE, RST_STREAM, and the END_STREAM flag.
  "sending or receiving a HEADERS frame causes the stream to become 'open' … A
  stream … transitions … to 'half-closed (local)' [when the endpoint sends] …
  END_STREAM … 'half-closed (remote)' [when the endpoint receives] … END_STREAM …
  either endpoint can send a RST_STREAM frame … causing it to transition
  immediately to 'closed'."
* **RFC 9113 §5.1, "half-closed (remote)":** "If an endpoint receives additional
  frames, other than WINDOW_UPDATE, PRIORITY, or RST_STREAM, for a stream that is
  in this state, it MUST respond with a stream error … of type STREAM_CLOSED."
* **RFC 9113 §5.1, "half-closed (local)":** a stream in this state "cannot be used
  for sending frames other than WINDOW_UPDATE, PRIORITY, and RST_STREAM."
* **RFC 9113 §5.1, "closed":** "An endpoint that receives any frame other than
  PRIORITY after receiving a RST_STREAM MUST treat that as a stream error … of
  type STREAM_CLOSED. … An endpoint that receives any frame after receiving a
  frame with the END_STREAM flag set MUST treat that as a … STREAM_CLOSED …"

The frame set modelled is HEADERS / DATA / PUSH_PROMISE / RST_STREAM and the
END_STREAM flag — the frames that drive the §5.1 diagram. WINDOW_UPDATE and
PRIORITY do not change stream state and are outside this state machine.
-/

namespace H2
namespace StreamRfc

open H2.Stream (StreamState Event)

/-! ## The independent RFC §5.1 transition relation

`Permitted s e s'` holds exactly when RFC 9113 §5.1 draws an edge from state `s`,
labelled by event `e`, to state `s'`. Each constructor is one labelled edge of
the diagram (or its END_STREAM-flag refinement). This relation is defined without
reference to `H2.Stream.step`. -/

inductive Permitted : StreamState → Event → StreamState → Prop where
  -- idle: HEADERS opens the stream; END_STREAM immediately half-closes the
  -- sender's/receiver's own half; PUSH_PROMISE reserves.
  | idle_recvHeaders_open    : Permitted .idle (.recvHeaders false) .open
  | idle_recvHeaders_hcr     : Permitted .idle (.recvHeaders true)  .halfClosedRemote
  | idle_sendHeaders_open    : Permitted .idle (.sendHeaders false) .open
  | idle_sendHeaders_hcl     : Permitted .idle (.sendHeaders true)  .halfClosedLocal
  | idle_recvPushPromise     : Permitted .idle .recvPushPromise     .reservedRemote
  | idle_sendPushPromise     : Permitted .idle .sendPushPromise     .reservedLocal
  -- reserved (local): the endpoint may send response HEADERS (→ half-closed
  -- remote) or reset.
  | rl_sendHeaders (b : Bool) : Permitted .reservedLocal (.sendHeaders b) .halfClosedRemote
  | rl_recvRst               : Permitted .reservedLocal .recvRstStream .closed
  | rl_sendRst               : Permitted .reservedLocal .sendRstStream .closed
  -- reserved (remote): the endpoint may receive HEADERS (→ half-closed local)
  -- or reset.
  | rr_recvHeaders (b : Bool) : Permitted .reservedRemote (.recvHeaders b) .halfClosedLocal
  | rr_recvRst               : Permitted .reservedRemote .recvRstStream .closed
  | rr_sendRst               : Permitted .reservedRemote .sendRstStream .closed
  -- open: DATA/HEADERS in either direction; END_STREAM half-closes the acting
  -- side; RST_STREAM closes.
  | open_recvData_open       : Permitted .open (.recvData false) .open
  | open_recvData_hcr        : Permitted .open (.recvData true)  .halfClosedRemote
  | open_sendData_open       : Permitted .open (.sendData false) .open
  | open_sendData_hcl        : Permitted .open (.sendData true)  .halfClosedLocal
  | open_recvHeaders_open    : Permitted .open (.recvHeaders false) .open
  | open_recvHeaders_hcr     : Permitted .open (.recvHeaders true)  .halfClosedRemote
  | open_sendHeaders_open    : Permitted .open (.sendHeaders false) .open
  | open_sendHeaders_hcl     : Permitted .open (.sendHeaders true)  .halfClosedLocal
  | open_recvRst             : Permitted .open .recvRstStream .closed
  | open_sendRst             : Permitted .open .sendRstStream .closed
  -- half-closed (local): the endpoint sent END_STREAM; it may still RECEIVE.
  -- A received END_STREAM closes; a received RST_STREAM (either direction) closes.
  | hcl_recvData_stay        : Permitted .halfClosedLocal (.recvData false) .halfClosedLocal
  | hcl_recvData_close       : Permitted .halfClosedLocal (.recvData true)  .closed
  | hcl_recvHeaders_stay     : Permitted .halfClosedLocal (.recvHeaders false) .halfClosedLocal
  | hcl_recvHeaders_close    : Permitted .halfClosedLocal (.recvHeaders true)  .closed
  | hcl_recvRst              : Permitted .halfClosedLocal .recvRstStream .closed
  | hcl_sendRst              : Permitted .halfClosedLocal .sendRstStream .closed
  -- half-closed (remote): the peer sent END_STREAM; the endpoint may still SEND.
  | hcr_sendData_stay        : Permitted .halfClosedRemote (.sendData false) .halfClosedRemote
  | hcr_sendData_close       : Permitted .halfClosedRemote (.sendData true)  .closed
  | hcr_sendHeaders_stay     : Permitted .halfClosedRemote (.sendHeaders false) .halfClosedRemote
  | hcr_sendHeaders_close    : Permitted .halfClosedRemote (.sendHeaders true)  .closed
  | hcr_recvRst              : Permitted .halfClosedRemote .recvRstStream .closed
  | hcr_sendRst              : Permitted .halfClosedRemote .sendRstStream .closed
  -- closed: RST_STREAM is idempotent (the stream stays closed).
  | closed_recvRst           : Permitted .closed .recvRstStream .closed
  | closed_sendRst           : Permitted .closed .sendRstStream .closed

/-! ## The independent RFC §5.1 STREAM_CLOSED obligation

`MustStreamClosed s e` holds exactly when RFC 9113 §5.1 mandates a STREAM_CLOSED
stream error for event `e` in state `s`: a receive on a remotely-closed half, a
send on a locally-closed half, or any frame other than RST_STREAM on a `closed`
stream. Defined without reference to the implementation. -/

inductive MustStreamClosed : StreamState → Event → Prop where
  -- half-closed (local): the endpoint already sent END_STREAM; it must not SEND
  -- HEADERS or DATA.
  | hcl_sendData (b : Bool)    : MustStreamClosed .halfClosedLocal (.sendData b)
  | hcl_sendHeaders (b : Bool) : MustStreamClosed .halfClosedLocal (.sendHeaders b)
  -- half-closed (remote): the peer already sent END_STREAM; a received HEADERS or
  -- DATA is STREAM_CLOSED.
  | hcr_recvData (b : Bool)    : MustStreamClosed .halfClosedRemote (.recvData b)
  | hcr_recvHeaders (b : Bool) : MustStreamClosed .halfClosedRemote (.recvHeaders b)
  -- closed: any frame other than RST_STREAM is STREAM_CLOSED.
  | closed_recvData (b : Bool)  : MustStreamClosed .closed (.recvData b)
  | closed_sendData (b : Bool)  : MustStreamClosed .closed (.sendData b)
  | closed_recvHeaders (b : Bool) : MustStreamClosed .closed (.recvHeaders b)
  | closed_sendHeaders (b : Bool) : MustStreamClosed .closed (.sendHeaders b)
  | closed_recvPushPromise      : MustStreamClosed .closed .recvPushPromise
  | closed_sendPushPromise      : MustStreamClosed .closed .sendPushPromise

/-! ## Refinement: the implementation accepts exactly the RFC-permitted edges -/

/-- **Soundness of acceptance.** Every transition the implementation accepts is an
edge the RFC §5.1 diagram draws, landing on the RFC's target state. -/
theorem accept_permitted {s e s'} (h : H2.Stream.step s e = .next s') :
    Permitted s e s' := by
  cases s <;> cases e <;> (first | (rename_i b; cases b) | skip) <;>
    simp only [H2.Stream.step] at h <;>
    first
      | exact H2.Stream.Outcome.noConfusion h
      | (injection h with h'; subst h'; constructor)

/-- **Completeness of acceptance.** Every edge the RFC §5.1 diagram draws is a
transition the implementation accepts, to the RFC's target state. -/
theorem permitted_accept {s e s'} (h : Permitted s e s') :
    H2.Stream.step s e = .next s' := by
  cases h <;> rfl

/-- **The stream-transition refinement theorem.** The implementation accepts a
transition on exactly the state/event pairs RFC 9113 §5.1 permits, and lands on
exactly the RFC's target state:
`step s e = next s'  ↔  Permitted s e s'`. -/
theorem refine_accept (s : StreamState) (e : Event) (s' : StreamState) :
    H2.Stream.step s e = .next s' ↔ Permitted s e s' :=
  ⟨accept_permitted, permitted_accept⟩

/-! ## Refinement: STREAM_CLOSED fires on exactly the RFC's conditions -/

/-- Soundness: every STREAM_CLOSED the implementation raises is an RFC §5.1
STREAM_CLOSED condition. -/
theorem stream_closed_must {s e} (h : H2.Stream.step s e = .streamClosed) :
    MustStreamClosed s e := by
  cases s <;> cases e <;> (first | (rename_i b; cases b) | skip) <;>
    simp only [H2.Stream.step] at h <;>
    first
      | exact H2.Stream.Outcome.noConfusion h
      | constructor

/-- Completeness: every RFC §5.1 STREAM_CLOSED condition is answered with
STREAM_CLOSED by the implementation. -/
theorem must_stream_closed {s e} (h : MustStreamClosed s e) :
    H2.Stream.step s e = .streamClosed := by
  cases h <;> rfl

/-- **The STREAM_CLOSED refinement theorem.** The implementation raises
STREAM_CLOSED on exactly the RFC §5.1 STREAM_CLOSED conditions:
`step s e = streamClosed  ↔  MustStreamClosed s e`. -/
theorem refine_stream_closed (s : StreamState) (e : Event) :
    H2.Stream.step s e = .streamClosed ↔ MustStreamClosed s e :=
  ⟨stream_closed_must, must_stream_closed⟩

/-- **Headline consequence (RFC 9113 §5.1, "closed").** Any frame other than
RST_STREAM arriving on a `closed` stream is a STREAM_CLOSED error. -/
theorem closed_frame_is_stream_closed (e : Event)
    (hr : e ≠ .recvRstStream) (hs : e ≠ .sendRstStream) :
    H2.Stream.step .closed e = .streamClosed := by
  cases e <;> simp_all [H2.Stream.step]

/-! ## Non-vacuity: the specification rejects a wrong implementation

The refinement above is only meaningful if the RFC relation actually excludes the
edges the RFC forbids. It does: there is no member of `Permitted` for DATA
received on a `halfClosedRemote` stream, and a hypothetical implementation that
took that edge is refuted by the very statement `refine_accept` proves for the
real implementation. -/

/-- The RFC §5.1 diagram draws **no** edge for DATA received on a `halfClosedRemote`
stream: the relation has no such member. (RFC 9113 §5.1: such a frame is a
STREAM_CLOSED error, not a transition — see `MustStreamClosed.hcr_recvData`.) -/
theorem data_on_half_closed_remote_forbidden (b : Bool) (s' : StreamState) :
    ¬ Permitted .halfClosedRemote (.recvData b) s' := by
  intro h; cases h

/-- A hypothetical implementation identical to the real one except that it takes
the RFC-forbidden edge "DATA received on `halfClosedRemote` reopens the stream". -/
def badStep : StreamState → Event → H2.Stream.Outcome
  | .halfClosedRemote, .recvData _ => .next .open
  | s, e => H2.Stream.step s e

/-- **Non-vacuity witness.** The wrong implementation `badStep` FAILS the
acceptance-soundness statement that `accept_permitted` proves for the real `step`:
it accepts a transition (`badStep halfClosedRemote (recvData true) = next open`)
that the RFC relation does not permit. Hence the specification is not the
implementation renamed — a forbidden edge is genuinely rejected. -/
theorem bad_impl_refuted :
    ¬ (∀ s e s', badStep s e = .next s' → Permitted s e s') := by
  intro hbad
  exact data_on_half_closed_remote_forbidden true .open
    (hbad .halfClosedRemote (.recvData true) .open rfl)

/-! ## Named RFC edges, as corollaries of the refinement

These re-express individual §5.1 edges through the *independent* relation, so the
diagram can be read off the specification rather than the implementation. -/

/-- idle + HEADERS(END_STREAM) → half-closed (remote), via the RFC relation. -/
example : Permitted .idle (.recvHeaders true) .halfClosedRemote := .idle_recvHeaders_hcr
/-- open + peer END_STREAM (DATA) → half-closed (remote). -/
example : Permitted .open (.recvData true) .halfClosedRemote := .open_recvData_hcr
/-- half-closed (remote) + our END_STREAM (DATA) → closed. -/
example : Permitted .halfClosedRemote (.sendData true) .closed := .hcr_sendData_close
/-- RST_STREAM closes an open stream. -/
example : Permitted .open .recvRstStream .closed := .open_recvRst
/-- DATA on a half-closed (remote) stream is STREAM_CLOSED, not an edge. -/
example : MustStreamClosed .halfClosedRemote (.recvData false) := .hcr_recvData false

end StreamRfc
end H2

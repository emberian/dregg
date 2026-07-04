/-!
# QUIC connection state machine — core types (deterministic half)

A sans-IO model of the deterministic half of a QUIC connection state
machine (RFC 9000 / RFC 9001 vocabulary): the three packet-number spaces
with per-space send counters and largest-acked tracking (RFC 9000 §12.3,
RFC 9002 Appendix A), the connection lifecycle — idle, handshaking,
established, closing, draining (RFC 9000 §10) — and stream-count
bookkeeping against a static stream limit (RFC 9000 §4.6).

The machine is a total function

    step : Conn → Input → Conn × List Output

so totality and determinism hold by construction (stated as theorems for
the record in `Quic.Theorems`). Deliberately out of scope here:

* **Loss detection and congestion control** (RFC 9002) — the
  timing-dependent half; not representable faithfully without an explicit
  clock input, so it is not claimed by this model at all.
* **Wire parsing** — packets and frames enter pre-parsed; headers and
  payloads are abstract.
* **The 0-RTT early-data acceptance decision** — modeled separately, as a
  distributed anti-replay protocol across server shards (`Quic.Replay`),
  where the interesting property (global at-most-once acceptance) lives.
  This FSM consequently gates application-data *delivery* on the
  established phase; the early-data path bypassing that gate is exactly
  the `Quic.Replay` model's subject.
-/

namespace Quic

/-- The three QUIC packet-number spaces (RFC 9000 §12.3): packets in
different spaces are numbered independently and protected under
independent keys, so all packet-number bookkeeping is per-space. -/
inductive PnSpace where
  | initial
  | handshake
  | appData
deriving Repr, DecidableEq

/-- Per-space packet-number bookkeeping: the send-side counter (the number
of the *next* packet to be sent in this space — packet numbers are
consumed in order and never reused, RFC 9000 §12.3) and the largest packet
number the peer has acknowledged (ACK ranges are compressed to their
largest element; RFC 9000 §13.2). -/
structure SpaceSt where
  nextPn : Nat
  largestAcked : Option Nat
deriving Repr, DecidableEq

/-- Fresh space: nothing sent, nothing acknowledged. -/
def SpaceSt.zero : SpaceSt := { nextPn := 0, largestAcked := none }

/-- Well-formedness of a space: every acknowledged packet number was
actually sent. -/
def SpaceSt.Wf (s : SpaceSt) : Prop :=
  ∀ a, s.largestAcked = some a → a < s.nextPn

/-- Process an ACK frame reporting `l` as the largest acknowledged packet
number. An acknowledgment of a never-sent packet number is a peer protocol
violation; this model ignores it (the error path is a scope cut), which
keeps `Wf` invariant. -/
def SpaceSt.onAck (s : SpaceSt) (l : Nat) : SpaceSt :=
  if l < s.nextPn then
    match s.largestAcked with
    | none => { s with largestAcked := some l }
    | some a => { s with largestAcked := some (Nat.max a l) }
  else s

/-- Connection lifecycle phases (RFC 9000 §10): `closing` = this endpoint
sent CONNECTION_CLOSE and answers further packets only with
CONNECTION_CLOSE; `draining` = the peer sent CONNECTION_CLOSE and this
endpoint must send nothing at all (RFC 9000 §10.2.2). -/
inductive Phase where
  | idle
  | handshaking
  | established
  | closing
  | draining
deriving Repr, DecidableEq

/-- The connection state: lifecycle phase, the three packet-number spaces,
and stream-count bookkeeping (peer-opened streams against a static local
limit; the MAX_STREAMS-raising path is a scope cut). -/
structure Conn where
  phase : Phase
  spInitial : SpaceSt
  spHandshake : SpaceSt
  spApp : SpaceSt
  streamsOpened : Nat
  streamsClosed : Nat
  maxStreams : Nat
deriving Repr, DecidableEq

/-- Project the bookkeeping of one packet-number space. -/
def Conn.space (c : Conn) : PnSpace → SpaceSt
  | .initial => c.spInitial
  | .handshake => c.spHandshake
  | .appData => c.spApp

/-- Replace the bookkeeping of one packet-number space. -/
def Conn.setSpace (c : Conn) : PnSpace → SpaceSt → Conn
  | .initial, v => { c with spInitial := v }
  | .handshake, v => { c with spHandshake := v }
  | .appData, v => { c with spApp := v }

/-- Fresh connection with a static peer-stream limit. -/
def Conn.init (maxStreams : Nat) : Conn :=
  { phase := .idle, spInitial := .zero, spHandshake := .zero, spApp := .zero,
    streamsOpened := 0, streamsClosed := 0, maxStreams := maxStreams }

/-- Connection well-formedness: per-space `Wf` plus the stream-count
sandwich `closed ≤ opened ≤ limit`. -/
def Conn.Wf (c : Conn) : Prop :=
  (∀ sp, (c.space sp).Wf) ∧
    c.streamsClosed ≤ c.streamsOpened ∧ c.streamsOpened ≤ c.maxStreams

/-- Inputs: everything the environment (UDP datagram demux + TLS stack +
application) can tell the machine. Packets arrive pre-parsed and
pre-decrypted; a packet is its space and number. -/
inductive Input where
  /-- Begin the handshake (client: first flight sent; server: first
  Initial received). -/
  | start
  /-- A packet arrived (already decrypted and parsed) in space `sp` with
  packet number `pn`. -/
  | pktReceived (sp : PnSpace) (pn : Nat)
  /-- An ACK frame arrived in space `sp` reporting `largest` as the
  largest acknowledged packet number. -/
  | ackReceived (sp : PnSpace) (largest : Nat)
  /-- The environment asks the machine to emit one packet in space `sp`
  (datagram pacing lives outside; the machine allocates the number). -/
  | sendReady (sp : PnSpace)
  /-- The TLS stack reports the handshake complete (client: HANDSHAKE_DONE
  received; server: client Finished verified). -/
  | handshakeDone
  /-- The peer opened a stream. -/
  | streamOpened
  /-- A stream fully closed (both directions finished). -/
  | streamClosed
  /-- Local close request: emit CONNECTION_CLOSE, enter `closing`. -/
  | appClose
  /-- The peer's CONNECTION_CLOSE arrived: enter `draining`. -/
  | closeReceived
deriving Repr, DecidableEq

/-- Outputs: everything the machine can ask the environment to do. -/
inductive Output where
  /-- Emit one packet, numbered `pn`, in space `sp`. -/
  | emit (sp : PnSpace) (pn : Nat)
  /-- Emit a packet carrying CONNECTION_CLOSE, numbered `pn`, in `sp`. -/
  | emitClose (sp : PnSpace) (pn : Nat)
  /-- Hand the application-data payload of packet `pn` up the stack. -/
  | deliverApp (pn : Nat)
deriving Repr, DecidableEq

/-- The packet number an output spends in space `sp`, if any: both `emit`
and `emitClose` consume one number from the space's send counter. -/
def Output.pnOf (sp : PnSpace) : Output → Option Nat
  | .emit sp' pn => if sp' = sp then some pn else none
  | .emitClose sp' pn => if sp' = sp then some pn else none
  | .deliverApp _ => none

/-- The packet numbers a step's output list spends in space `sp`,
in emission order. -/
def emittedPns (sp : PnSpace) : List Output → List Nat
  | [] => []
  | o :: os =>
    match Output.pnOf sp o with
    | some pn => pn :: emittedPns sp os
    | none => emittedPns sp os

end Quic

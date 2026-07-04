import Quic.Basic

/-!
# QUIC connection state machine — the step function

`step : Conn → Input → Conn × List Output`, total and deterministic by
construction. The lifecycle skeleton follows RFC 9000 §10; per-space
packet numbering follows §12.3 (numbers spent in order, never reused);
stream accounting follows §4.6 (a peer stream beyond the advertised limit
is a STREAM_LIMIT_ERROR, answered by closing the connection).

Modeling choices visible here:

* `draining` is fully absorbing and silent — RFC 9000 §10.2.2's "MUST NOT
  send" rendered as: every input maps to `(c, [])`. The end-of-draining
  discard (3×PTO timer) is outside the model.
* `closing` answers any incoming packet with a CONNECTION_CLOSE in that
  packet's space (§10.2.1); the rate limiter the RFC asks for is a scope
  cut, so the model answers every packet.
* App-data *delivery* requires `established`. The 0-RTT early-data accept
  path that would relax this is deliberately not in this machine — it is
  the subject of the `Quic.Replay` model, which decides acceptance; a
  connection whose early data was accepted re-enters this FSM as ordinary
  delivery after `handshakeDone`. Sends in the app-data space during the
  handshake are allowed (client 0-RTT flights, server half-RTT data).
-/

namespace Quic

/-- Spend one packet number in space `sp`: bump the send counter. -/
def Conn.bump (c : Conn) (sp : PnSpace) : Conn :=
  c.setSpace sp { c.space sp with nextPn := (c.space sp).nextPn + 1 }

/-- Emit one ordinary packet in `sp` (number allocated from the space). -/
def Conn.sendPkt (c : Conn) (sp : PnSpace) : Conn × List Output :=
  (c.bump sp, [.emit sp (c.space sp).nextPn])

/-- Emit CONNECTION_CLOSE in `sp` and enter `closing`. -/
def Conn.closeIn (c : Conn) (sp : PnSpace) : Conn × List Output :=
  ({ c.bump sp with phase := .closing }, [.emitClose sp (c.space sp).nextPn])

/-- In `closing`, answer an incoming packet with CONNECTION_CLOSE in the
same space (phase already `closing`; stays). -/
def Conn.replyClose (c : Conn) (sp : PnSpace) : Conn × List Output :=
  (c.bump sp, [.emitClose sp (c.space sp).nextPn])

/-- Fold an ACK into the named space. -/
def Conn.onAck (c : Conn) (sp : PnSpace) (l : Nat) : Conn :=
  c.setSpace sp ((c.space sp).onAck l)

/-- The connection step function. Total and deterministic. -/
def step (c : Conn) (i : Input) : Conn × List Output :=
  match c.phase with
  | .draining => (c, [])
  | .idle =>
    match i with
    | .start => ({ c with phase := .handshaking }, [])
    | .closeReceived => ({ c with phase := .draining }, [])
    | _ => (c, [])
  | .handshaking =>
    match i with
    | .ackReceived sp l => (c.onAck sp l, [])
    | .sendReady sp => c.sendPkt sp
    | .handshakeDone => ({ c with phase := .established }, [])
    | .appClose => c.closeIn .handshake
    | .closeReceived => ({ c with phase := .draining }, [])
    | _ => (c, [])
  | .established =>
    match i with
    | .pktReceived sp pn =>
      match sp with
      | .appData => (c, [.deliverApp pn])
      | _ => (c, [])
    | .ackReceived sp l => (c.onAck sp l, [])
    | .sendReady sp => c.sendPkt sp
    | .streamOpened =>
      if c.streamsOpened < c.maxStreams then
        ({ c with streamsOpened := c.streamsOpened + 1 }, [])
      else
        -- STREAM_LIMIT_ERROR (RFC 9000 §4.6): close the connection.
        c.closeIn .appData
    | .streamClosed =>
      if c.streamsClosed < c.streamsOpened then
        ({ c with streamsClosed := c.streamsClosed + 1 }, [])
      else (c, [])
    | .appClose => c.closeIn .appData
    | .closeReceived => ({ c with phase := .draining }, [])
    | _ => (c, [])
  | .closing =>
    match i with
    | .pktReceived sp _ => c.replyClose sp
    | .closeReceived => ({ c with phase := .draining }, [])
    | _ => (c, [])

/-- Run the machine over an input list, concatenating outputs. -/
def run (c : Conn) : List Input → Conn × List Output
  | [] => (c, [])
  | i :: is =>
    let r₁ := step c i
    let r₂ := run r₁.1 is
    (r₂.1, r₁.2 ++ r₂.2)

end Quic

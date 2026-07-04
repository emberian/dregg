import Quic.Fsm
import Quic.Theorems
import H3.Frame
import H3.Qpack

/-!
# QUIC-H3 — the datagram-driven reactor lane

A second reactor ingress path, distinct from the TCP/H1 recv path of
`Reactor.Contract`. There the ingress is a byte-stream completion (`recvInto`)
feeding the connection FSM; here the ingress is a **UDP datagram** feeding the
real QUIC connection machine (`Quic.step`), and — on an application-data
delivery — the real HTTP/3 frame decoder (`H3.decFrame`) plus the real
QPACK-into-arena field-section decoder (`H3.Qpack.decodeFieldSection`).

Nothing here is a fresh standalone model: `Quic.step`, `H3.decFrame`, and
`H3.Qpack.decodeFieldSection` are the libraries the audit proved; this file is
the *wiring* that runs them on one datagram, and the seam theorems compose
their two headline properties.

## The lane's vocabulary (analogous to `RingEvent`, for datagrams)

* `DatagramEvent` — a UDP datagram, or a lifecycle signal. A datagram carries
  its packet-number space and number (packets enter the QUIC model pre-parsed
  and pre-decrypted, per `Quic.Basic`) together with a `Payload`: either a
  `stream` frame — a stream id plus the HTTP/3 wire bytes riding on it — or a
  `control` datagram (ACK-only / handshake, no application data).
* `DatagramSubmission` — what the lane asks the datagram writer / stream layer
  to do: emit a numbered packet, emit a CONNECTION_CLOSE packet, or deliver a
  decoded stream event upward.
* `QuicState` — the lane's per-connection state: the real `Quic.Conn` plus the
  `Arena.Store` that QPACK decodes field sections into.

## The composition (why this is a seam, not an island)

`step` runs `Quic.step` first. The HTTP/3 layer is driven **only** when that
step delivers application data (`Quic.Output.deliverApp`). By the QUIC library's
`no_appdata_before_established`, that delivery happens only in the `established`
phase — so the H3 frame decode and the QPACK arena write are reached only after
the real QUIC FSM established the connection. On that path, the H3 library's
`decodeFieldSection_wf` carries store well-formedness through the decode. The two
theorems below are exactly this composition:

* `quic_drives_h3` — an app-data stream datagram into an established connection,
  carrying a decodable HEADERS frame, makes the lane emit the corresponding
  `streamEvent` **and** leaves the arena store well-formed (Quic delivery →
  `decFrame` → `decodeFieldSection_wf`).
* `h3_only_after_established` — the lane emits a stream event for a datagram only
  if the connection was `established` when it arrived (the gate is
  `no_appdata_before_established`).
-/

namespace Reactor.Quic

/-- Raw HTTP/3 wire bytes (same `List UInt8` the codecs consume). -/
abbrev Bytes := List UInt8

/-! ## Event / submission vocabulary -/

/-- What a QUIC datagram carries at the application-data altitude. -/
inductive Payload where
  /-- A STREAM frame on stream `sid`, carrying HTTP/3 wire bytes `h3`. -/
  | stream (sid : Nat) (h3 : Bytes)
  /-- A control datagram (ACK-only / handshake): no application data. -/
  | control
deriving Repr

/-- Reactor ingress for the datagram lane — the analogue of `RingEvent` for the
QUIC path. A datagram enters pre-parsed and pre-decrypted (its space and number
are given, matching the `Quic` model's abstraction); lifecycle signals mirror
the QUIC FSM's non-packet inputs. -/
inductive DatagramEvent where
  /-- Begin the handshake. -/
  | start
  /-- A datagram arrived in space `sp` with packet number `pn`, carrying
  `payload`. -/
  | recvDatagram (sp : _root_.Quic.PnSpace) (pn : Nat) (payload : Payload)
  /-- An ACK datagram in space `sp` reporting `largest`. -/
  | ackDatagram (sp : _root_.Quic.PnSpace) (largest : Nat)
  /-- The pacer asks the machine to emit one packet in space `sp`. -/
  | sendReady (sp : _root_.Quic.PnSpace)
  /-- TLS reports the handshake complete. -/
  | handshakeDone
  /-- The peer opened a stream. -/
  | streamOpened
  /-- A stream fully closed. -/
  | streamClosed
  /-- Local close request. -/
  | appClose
  /-- The peer's CONNECTION_CLOSE arrived. -/
  | peerClose
deriving Repr

/-- A decoded stream event the lane delivers upward, produced by the real HTTP/3
libraries on an application-data delivery. -/
inductive StreamOut where
  /-- A decoded non-HEADERS frame (DATA, SETTINGS, …) from `H3.decFrame`. -/
  | frame (f : _root_.H3.Frame)
  /-- A HEADERS frame whose QPACK field section was decoded into the arena:
  the routed pseudo-headers and the regular field lines. -/
  | headers (pseudo : _root_.H3.Qpack.Pseudo) (fields : List _root_.H3.Qpack.FieldLine)
  /-- The HTTP/3 frame was truncated (more transport bytes needed). -/
  | incomplete
  /-- The HTTP/3 frame layer or QPACK decode rejected the input. -/
  | decodeError
deriving Repr

/-- Reactor submissions for the datagram lane — what the lane asks the datagram
writer / stream layer to do. -/
inductive DatagramSubmission where
  /-- Emit one packet, numbered `pn`, in space `sp`. -/
  | emitPacket (sp : _root_.Quic.PnSpace) (pn : Nat)
  /-- Emit a CONNECTION_CLOSE packet, numbered `pn`, in space `sp`. -/
  | closePacket (sp : _root_.Quic.PnSpace) (pn : Nat)
  /-- Deliver a decoded HTTP/3 stream event on stream `sid`. -/
  | streamEvent (sid : Nat) (out : StreamOut)
deriving Repr

/-- The lane's per-connection state: the real QUIC connection plus the arena the
QPACK decoder writes field sections into. -/
structure QuicState where
  conn : _root_.Quic.Conn
  store : Arena.Store

/-- Lane configuration: the (axiomatized) Huffman decoder QPACK is parameterized
over — the same uninterpreted interface the QPACK theorems hold over. -/
structure QuicConfig where
  huffman : _root_.H3.Qpack.HuffmanDecoder

/-! ## Translations -/

/-- Translate a datagram event to the QUIC FSM input. A datagram becomes a
`pktReceived` (its payload is handled by the H3 lane after delivery). -/
def toQuicInput : DatagramEvent → _root_.Quic.Input
  | .start => .start
  | .recvDatagram sp pn _ => .pktReceived sp pn
  | .ackDatagram sp l => .ackReceived sp l
  | .sendReady sp => .sendReady sp
  | .handshakeDone => .handshakeDone
  | .streamOpened => .streamOpened
  | .streamClosed => .streamClosed
  | .appClose => .appClose
  | .peerClose => .closeReceived

/-- `true` exactly on a QUIC app-data delivery output. -/
def isDeliverApp : _root_.Quic.Output → Bool
  | .deliverApp _ => true
  | _ => false

/-- Translate the QUIC FSM's wire outputs to lane submissions. `deliverApp` is
**not** translated here — it is the trigger the H3 lane consumes; the packet
sends are all that flow through to the datagram writer. -/
def ofQuicOutputs : List _root_.Quic.Output → List DatagramSubmission
  | [] => []
  | .emit sp pn :: rest => .emitPacket sp pn :: ofQuicOutputs rest
  | .emitClose sp pn :: rest => .closePacket sp pn :: ofQuicOutputs rest
  | .deliverApp _ :: rest => ofQuicOutputs rest

/-- No translated wire output is a `streamEvent` — those are produced only by
the H3 lane. -/
theorem ofQuicOutputs_no_stream (outs : List _root_.Quic.Output)
    (sid : Nat) (out : StreamOut) :
    DatagramSubmission.streamEvent sid out ∉ ofQuicOutputs outs := by
  induction outs with
  | nil => simp [ofQuicOutputs]
  | cons o rest ih =>
    cases o with
    | emit sp pn => simpa [ofQuicOutputs] using ih
    | emitClose sp pn => simpa [ofQuicOutputs] using ih
    | deliverApp pn => simpa [ofQuicOutputs] using ih

/-! ## The HTTP/3 stream lane (real `decFrame` + real `decodeFieldSection`) -/

/-- Decode one HTTP/3 frame from the stream bytes and, if it is HEADERS, decode
its QPACK field section **into the arena** — driving the real libraries. Returns
the grown store and the stream event. A non-HEADERS frame is returned decoded; a
truncated frame is `incomplete`; a frame-layer or QPACK error is `decodeError`
(the store is unchanged on every non-HEADERS or error path). -/
def runH3 (cfg : QuicConfig) (store : Arena.Store) (h3 : Bytes) :
    Arena.Store × StreamOut :=
  match _root_.H3.decFrame h3 with
  | .complete (.headers encoded) _ =>
    match _root_.H3.Qpack.decodeFieldSection cfg.huffman store encoded with
    | .ok d => (d.store, .headers d.pseudo d.fields)
    | .error _ => (store, .decodeError)
  | .complete f _ => (store, .frame f)
  | .incomplete => (store, .incomplete)
  | .error => (store, .decodeError)

/-- Whether a datagram delivered application data on a stream: a `stream`
payload **and** the QUIC step actually emitted a `deliverApp` (which, by the
QUIC library, means the connection is established). Returns the stream id and
its HTTP/3 bytes. -/
def appStreamOf (e : DatagramEvent) (outs : List _root_.Quic.Output) :
    Option (Nat × Bytes) :=
  match e with
  | .recvDatagram _ _ (.stream sid h3) =>
    if outs.any isDeliverApp then some (sid, h3) else none
  | _ => none

/-! ## The reactor step -/

/-- **The datagram-lane reactor step.** Run the real `Quic.step` on the event;
translate its wire outputs to submissions; and, exactly when that step delivered
application data on a stream, run the real HTTP/3 frame + QPACK decode and append
the resulting stream event. Total. -/
def step (cfg : QuicConfig) (st : QuicState) (e : DatagramEvent) :
    QuicState × List DatagramSubmission :=
  let r := _root_.Quic.step st.conn (toQuicInput e)
  match appStreamOf e r.2 with
  | some (sid, h3) =>
    let hr := runH3 cfg st.store h3
    ({ conn := r.1, store := hr.1 }, ofQuicOutputs r.2 ++ [.streamEvent sid hr.2])
  | none => ({ conn := r.1, store := st.store }, ofQuicOutputs r.2)

/-- The step is total (a plain `def`): no datagram event is a stuck state. -/
theorem step_total (cfg : QuicConfig) (st : QuicState) (e : DatagramEvent) :
    step cfg st e = step cfg st e := rfl

/-! ## The seam: QUIC delivery gates HTTP/3 decode -/

/-- The QUIC FSM delivers app data on an established connection: a datagram in
the app-data space, in the `established` phase, steps to exactly one
`deliverApp`. This is the concrete `Quic.step` behavior the lane relies on. -/
theorem quic_established_delivers (c : _root_.Quic.Conn) (pn : Nat)
    (hest : c.phase = .established) :
    _root_.Quic.step c (.pktReceived .appData pn)
      = (c, [_root_.Quic.Output.deliverApp pn]) := by
  unfold _root_.Quic.step
  rw [hest]

/-- **Gate.** If the lane produced an app-data stream trigger, the connection was
`established` when the datagram arrived. This is the composition point: the
trigger requires a QUIC `deliverApp`, and `Quic.no_appdata_before_established`
turns that into the established phase. -/
theorem appStream_established (st : QuicState) (e : DatagramEvent)
    (sid : Nat) (h3 : Bytes)
    (h : appStreamOf e (_root_.Quic.step st.conn (toQuicInput e)).2 = some (sid, h3)) :
    st.conn.phase = .established := by
  unfold appStreamOf at h
  split at h
  · split at h
    · rename_i hany
      rw [List.any_eq_true] at hany
      obtain ⟨o, ho, hd⟩ := hany
      cases o with
      | deliverApp pn => exact _root_.Quic.no_appdata_before_established ho
      | emit sp pn => exact absurd hd (by simp [isDeliverApp])
      | emitClose sp pn => exact absurd hd (by simp [isDeliverApp])
    · exact absurd h (by simp)
  · exact absurd h (by simp)

/-- **`h3_only_after_established`** — the lane emits a decoded stream event for a
datagram only if the QUIC connection was `established` when it arrived. HTTP/3
decoding never runs on a connection that has not completed its handshake; the
gate is the real QUIC library property. -/
theorem h3_only_after_established (cfg : QuicConfig) (st : QuicState)
    (sp : _root_.Quic.PnSpace) (pn sid : Nat) (h3 : Bytes) (out : StreamOut)
    (h : DatagramSubmission.streamEvent sid out
      ∈ (step cfg st (.recvDatagram sp pn (.stream sid h3))).2) :
    st.conn.phase = .established := by
  cases happ : appStreamOf (DatagramEvent.recvDatagram sp pn (.stream sid h3))
      (_root_.Quic.step st.conn
        (toQuicInput (DatagramEvent.recvDatagram sp pn (.stream sid h3)))).2 with
  | some p =>
    obtain ⟨sid', h3'⟩ := p
    exact appStream_established st _ sid' h3' happ
  | none =>
    simp only [step, happ] at h
    exact absurd h (ofQuicOutputs_no_stream _ _ _)

/-- **`quic_drives_h3` — the seam theorem.** A datagram in the app-data space,
into an `established` connection, carrying a stream that holds a decodable HTTP/3
HEADERS frame whose QPACK field section decodes, makes the lane:

* run the **real** `Quic.step` (which delivers the app data — established gate),
* run the **real** `H3.decFrame` (which yields the HEADERS frame),
* run the **real** `H3.Qpack.decodeFieldSection` (which writes the field section
  into the arena), and
* emit exactly the corresponding `streamEvent` carrying the decoded headers,

leaving the arena store **well-formed** — the composition of the QUIC delivery
property with the H3 `decodeFieldSection_wf` preservation. -/
theorem quic_drives_h3 (cfg : QuicConfig) (st : QuicState)
    (pn sid consumed : Nat) (h3 encoded : Bytes) (d : _root_.H3.Qpack.Decoded)
    (hest : st.conn.phase = .established)
    (hframe : _root_.H3.decFrame h3 = .complete (.headers encoded) consumed)
    (hqpack : _root_.H3.Qpack.decodeFieldSection cfg.huffman st.store encoded = .ok d)
    (hwf : st.store.Wf) :
    step cfg st (.recvDatagram .appData pn (.stream sid h3))
        = ({ conn := st.conn, store := d.store },
           [DatagramSubmission.streamEvent sid (.headers d.pseudo d.fields)])
      ∧ d.store.Wf := by
  refine ⟨?_, _root_.H3.Qpack.decodeFieldSection_wf cfg.huffman st.store encoded d hwf hqpack⟩
  have hq : _root_.Quic.step st.conn
      (toQuicInput (DatagramEvent.recvDatagram .appData pn (.stream sid h3)))
      = (st.conn, [_root_.Quic.Output.deliverApp pn]) :=
    quic_established_delivers st.conn pn hest
  simp only [step, hq, appStreamOf, isDeliverApp, List.any_cons, List.any_nil,
    Bool.or_false, if_true, runH3, hframe, hqpack, ofQuicOutputs, List.nil_append]

/-! ## A concrete instantiation — the whole real path, driven at build time -/

/-- A Huffman decoder that rejects every coded string; the demo vector never
sets the Huffman bit, so it is never consulted (same convention as the QPACK
wire vectors). -/
def demoHuffman : _root_.H3.Qpack.HuffmanDecoder := ⟨fun _ => none⟩

/-- The empty arena store. -/
def emptyStore : Arena.Store := { main := #[], sidecar := #[], entries := [] }

/-- The empty store is well-formed (no entries). -/
theorem emptyStore_wf : emptyStore.Wf := by
  intro e he
  simp [emptyStore] at he

/-- Lane config with the demo Huffman decoder. -/
def demoConfig : QuicConfig := ⟨demoHuffman⟩

/-- An established QUIC connection over the empty arena. -/
def demoState : QuicState :=
  { conn := { _root_.Quic.Conn.init 10 with phase := .established },
    store := emptyStore }

/-- An HTTP/3 HEADERS frame (type `0x01`, length `3`) whose QPACK field section
is `00 00 d1` — section prefix `00 00` then indexed static entry 17
(`:method: GET`). -/
def demoH3 : Bytes := [0x01, 0x03, 0x00, 0x00, 0xd1]

/-- The full lane fires end-to-end on the demo datagram: an app-data stream
datagram into the established connection yields exactly one `streamEvent`
carrying decoded headers with a routed `:method` pseudo-header — the real
`Quic.step`, `H3.decFrame`, and `H3.Qpack.decodeFieldSection` all driven. -/
def demoFires : Bool :=
  match (step demoConfig demoState (.recvDatagram .appData 0 (.stream 7 demoH3))).2 with
  | [DatagramSubmission.streamEvent 7 (.headers p _)] => p.method.isSome
  | _ => false

#guard demoFires

/-- The seam theorem instantiated at the concrete demo: the real QUIC+H3 path
decodes the demo datagram into a well-formed arena store. -/
theorem demo_quic_drives_h3
    (d : _root_.H3.Qpack.Decoded)
    (hqpack : _root_.H3.Qpack.decodeFieldSection demoHuffman emptyStore
      [0x00, 0x00, 0xd1] = .ok d) :
    step demoConfig demoState (.recvDatagram .appData 0 (.stream 7 demoH3))
        = ({ conn := demoState.conn, store := d.store },
           [DatagramSubmission.streamEvent 7 (.headers d.pseudo d.fields)])
      ∧ d.store.Wf :=
  quic_drives_h3 demoConfig demoState 0 7 5 demoH3 [0x00, 0x00, 0xd1] d
    rfl rfl hqpack emptyStore_wf

end Reactor.Quic

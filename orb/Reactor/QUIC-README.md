# Reactor.Quic — the QUIC/H3 datagram path

A second reactor ingress path, distinct from the TCP/H1 recv path in
`Reactor.Contract`. The ring path's ingress is a byte-stream completion
(`RingEvent.recvInto`) feeding the `Proto` connection FSM. The datagram ingress is
a **UDP datagram** feeding the real QUIC connection machine (`Quic.step`) and, on
an application-data delivery, the real HTTP/3 frame decoder (`H3.decFrame`) plus
the real QPACK-into-arena field-section decoder (`H3.Qpack.decodeFieldSection`).

Defined in `Reactor/Quic.lean`, wired into the `Reactor` lib via `Reactor.lean`.

## The datagram vocabulary (analogous to `RingEvent`, for datagrams)

- `Payload` — what a datagram carries at the app-data altitude: `stream sid h3`
  (a STREAM frame: stream id + HTTP/3 wire bytes) or `control` (ACK/handshake,
  no app data).
- `DatagramEvent` — the ingress: `recvDatagram sp pn payload` (a pre-parsed,
  pre-decrypted packet in space `sp`, number `pn`, per the `Quic` model's
  abstraction), plus the lifecycle signals mirroring the QUIC FSM's non-packet
  inputs (`start`, `ackDatagram`, `sendReady`, `handshakeDone`, `streamOpened`,
  `streamClosed`, `appClose`, `peerClose`).
- `DatagramSubmission` — the egress: `emitPacket sp pn`, `closePacket sp pn`
  (translated from `Quic.Output`), and `streamEvent sid out` (a decoded H3
  stream event).
- `StreamOut` — a decoded stream event: `frame f` (non-HEADERS), `headers pseudo
  fields` (a QPACK field section decoded into the arena), `incomplete`,
  `decodeError`.
- `QuicState` — `{ conn : Quic.Conn, store : Arena.Store }`: the real QUIC
  connection plus the arena QPACK writes field sections into.
- `QuicConfig` — carries the axiomatized `H3.Qpack.HuffmanDecoder` the QPACK
  theorems are uniform over.

## The step

`step cfg st e`:

1. runs the **real** `Quic.step st.conn (toQuicInput e)`;
2. translates its wire outputs with `ofQuicOutputs` (`emit`/`emitClose` →
   submissions; `deliverApp` is *not* translated — it is the H3 trigger);
3. **only when that step delivered app data on a stream** (`appStreamOf`: a
   `stream` payload and a `deliverApp` in the QUIC outputs) runs the H3 lane
   `runH3` — the real `H3.decFrame`, and for a HEADERS frame the real
   `H3.Qpack.decodeFieldSection` into `st.store` — and appends the resulting
   `streamEvent`.

`runH3` is where both real libraries are driven: `decFrame` classifies the frame
and, on HEADERS, `decodeFieldSection` appends the decoded name/value byte strings
into the sidecar arena and threads the grown store back into `QuicState`.

## The seam theorems (composition, not islands)

- **`quic_drives_h3`** — the headline seam. An app-data datagram
  (`recvDatagram .appData pn (.stream sid h3)`) into an `established` connection,
  carrying a decodable HEADERS frame whose QPACK field section decodes to `d`,
  makes `step` produce exactly
  `[streamEvent sid (.headers d.pseudo d.fields)]` **and** leaves the arena store
  `d.store.Wf`. This composes the QUIC delivery behavior
  (`quic_established_delivers`, the concrete established-phase `Quic.step`
  reduction) with the H3 library's `H3.Qpack.decodeFieldSection_wf` preservation.
  The running path uses the real libs: the theorem's conclusion is `step`'s
  output, and its store-Wf half *is* the QPACK library theorem applied to the
  lane's store.

- **`h3_only_after_established`** — the gate. `step` emits a `streamEvent` for a
  datagram only if the connection was `established` when it arrived. The proof
  runs through `appStream_established`, which extracts the `deliverApp` that the
  H3 trigger requires and feeds it to the QUIC library's
  `Quic.no_appdata_before_established`. So HTTP/3 decoding never runs on a
  connection that has not completed its handshake — the real QUIC FSM property is
  the gate on the real H3 decode.

- `quic_established_delivers`, `appStream_established`, `ofQuicOutputs_no_stream`,
  `step_total` — supporting lemmas.

## Driven at build time

`#guard demoFires` runs the whole real path at build time: an established QUIC
connection over an empty arena receives a datagram whose stream carries the H3
HEADERS frame `[0x01, 0x03, 0x00, 0x00, 0xd1]` (type `0x01`, length `3`, QPACK
payload = section prefix `00 00` then indexed static entry 17 → `:method: GET`).
`step` returns exactly one `streamEvent 7 (.headers p _)` with `p.method.isSome`.
`demo_quic_drives_h3` instantiates `quic_drives_h3` at that concrete datagram.

## Status

- `lake build Reactor` green (whole library, `Reactor.Quic` included).
- Zero `sorry`, zero `native_decide`.
- `#print axioms` of `quic_drives_h3`, `h3_only_after_established`,
  `appStream_established`, `demo_quic_drives_h3` ⊆ `{propext, Classical.choice,
  Quot.sound}`.

## Scope cuts

- Datagrams enter pre-parsed and pre-decrypted — the QUIC model's own boundary
  (`Quic.Basic`: wire parsing and record protection are abstract). This path
  wires the deterministic FSM half plus the H3 decode; it does not add a packet
  protector.
- One datagram carries at most one STREAM payload with one H3 frame; STREAM
  reassembly across datagrams and multi-frame coalescing within a datagram are
  not modeled here (the H3 frame *loop* `H3.decFrames` and its termination proof
  already exist in `H3.Frame` for the coalescing widening).
- The QPACK dynamic table stays the library's explicit out-of-scope stub;
  HEADERS with dynamic references decode to `StreamOut.decodeError` via the
  library's `Err.dynamicUnsupported`.

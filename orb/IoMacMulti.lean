/-
IoMacMulti — the proven reactor serving REAL traffic ACROSS PROTOCOLS on real
macOS sockets: HTTP/1.1 + h2c + WebSocket over one TCP listener, and QUIC/HTTP-3
over a real UDP socket — all driven by the *unchanged* proven core.

This is the multi-protocol sibling of `IoMac`. `IoMac` shipped a single blocking
TCP accept loop that served H1/h2c and closed after one response. Two proven
lanes existed in the kernel but were never wired to a socket:

  * the WebSocket lane (`Reactor.Ws.wsFeedFn` / `Reactor.WsDeploy`) — decoded and
    reassembled real masked frames, but no socket ever kept a connection open
    past the HTTP Upgrade to run one;
  * the QUIC/HTTP-3 datagram lane (`Reactor.QuicIngress.datagramServe`) — ran the
    real `Quic.step` + `H3.decFrame` + QPACK decode and DISPATCHED an H3 request,
    but nothing recv'd a UDP datagram to drive it.

This file hands three pure `ByteArray -> ByteArray` handlers to two untrusted C
shells (`ffi/mac_io.c`'s `orb_mac_serve_ws`, `ffi/mac_udp.c`'s `orb_mac_serve_udp`)
and runs both listeners at once. The proven core is untouched; only the shell's
IO scheduling is new.

Trust split (identical discipline to IoMac):
  * TRUSTED shell — `ffi/mac_io.c`, `ffi/mac_udp.c`: sockets, the accept/recv
    loops, the connection lifecycle, and the ONE handshake hash the RFC needs
    (`Sec-WebSocket-Accept` = base64(sha1(key ++ GUID)) — the proven core ships
    no SHA-1). It never touches the WebSocket data path or a datagram's content.
  * PROVEN, unchanged — the handlers below ARE the proven pipelines:
    `deployStepIngress` (HTTP), `wsFeedFn`/`wsEncodeFn` (WebSocket frames),
    `datagramServe` + `serveOverSubs` (QUIC/H3 dispatch → guarded serve).
-/
import Reactor.Ingress
import Reactor.Observe
import Reactor.Ws
import Reactor.Quic
import Reactor.QuicIngress

/-! ## (1) The HTTP handler — the same proven pipeline `orb-mac` serves.

One connection's request bytes in, the deployed guarded response bytes out
(`deployStepIngress` over a fresh `ObsState.init`), exactly as `IoMac.handleConn`
runs it. The WS shell calls this for any non-upgrade request. -/
@[export orb_mac_multi_http]
def multiHttpHandle (req : ByteArray) : ByteArray :=
  let (out, _obs) :=
    Reactor.Ingress.deployStepIngress Reactor.Observe.ObsState.init req.toList
  ByteArray.mk out.toArray

/-! ## (2) The WebSocket frame handler — the REAL frame engine, echoed.

The bytes of one inbound WS frame (client→server, masked) in; the proven
`Reactor.Ws.wsFeedFn` decodes them (real length ladder + real `applyMask` unmask
+ real `Ws.Reassembly` fold), delivering the logical frames; each delivered
frame is re-encoded to the wire by the proven `Reactor.Ws.wsEncodeFn` (server
frames unmasked) — a proven-path echo. The C shell writes these bytes straight
back over the open connection. Nothing here knows a socket exists. -/
@[export orb_mac_ws_handle]
def wsHandle (frame : ByteArray) : ByteArray :=
  let out := Reactor.Ws.wsFeedFn ({} : Proto.WsCodec) frame.toList
  let echoed := (out.frames.map Reactor.Ws.wsEncodeFn).flatten
  ByteArray.mk echoed.toArray

/-! ## (3) The QUIC/HTTP-3 datagram handler — the REAL H3 ingress, dispatched.

One UDP datagram's bytes in, treated as the application-data HTTP/3 stream bytes
delivered on an established QUIC connection (the proven datagram lane models a
datagram as arriving pre-parsed/pre-decrypted — `Reactor.Quic.DatagramEvent`).
The proven `Reactor.QuicIngress.datagramServe` runs the REAL `Quic.step` +
`H3.decFrame` + `H3.Qpack.decodeFieldSection` and emits the reactor
`RingSubmission`s — chiefly the `dispatch` of the H3-decoded request. Those
submissions feed the SAME proven guarded serve the TCP lanes run
(`Reactor.Ingress.serveOverSubs`), producing the response bytes the C shell
sends back as a datagram. A well-formed H3 HEADERS `GET /` datagram thus
dispatches through the real QUIC/H3 engines and is served by the real pipeline. -/
@[export orb_mac_udp_handle]
def udpHandle (datagram : ByteArray) : ByteArray :=
  let h3 := datagram.toList
  let ev := Reactor.Quic.DatagramEvent.recvDatagram .appData 0
              (Reactor.Quic.Payload.stream 7 h3)
  let subs := (Reactor.QuicIngress.datagramServe
    Reactor.QuicIngress.demoConfig Reactor.QuicIngress.demoState ev).2
  let resp := Reactor.Ingress.serveOverSubs subs h3
  ByteArray.mk resp.toArray

/-! ## (4) The two extern IO loops (in the untrusted C shells) -/

/-- The WebSocket+HTTP accept loop (`ffi/mac_io.c`). Binds `127.0.0.1:port`; on a
WebSocket Upgrade it completes the handshake, keeps the connection OPEN, and runs
every subsequent frame through `wsHandle`; otherwise it answers once with the
HTTP `handler`. Blocks forever. -/
@[extern "orb_mac_serve_ws"]
opaque serveWs (port : UInt16) (handler : ByteArray → ByteArray)
    (wsHandler : ByteArray → ByteArray) : IO Unit

/-- The QUIC/UDP datagram loop (`ffi/mac_udp.c`). Binds `127.0.0.1:port` as UDP;
for each datagram it applies `handler` (the proven H3 ingress) and sends the
response datagram back to the sender. Blocks forever. -/
@[extern "orb_mac_serve_udp"]
opaque serveUdp (port : UInt16) (handler : ByteArray → ByteArray) : IO Unit

/-! ## (5) main — run both listeners at once -/

/-- `orb-mac-multi [tcpPort] [udpPort]` (defaults 8080 / 8081): start the QUIC/UDP
datagram loop on a dedicated background thread, then run the WebSocket+HTTP accept
loop in the foreground. One process, the proven reactor serving across protocols
over real sockets. -/
def main (args : List String) : IO Unit := do
  let tcpPort : UInt16 := ((args[0]?).bind String.toNat?).map (·.toUInt16) |>.getD 8080
  let udpPort : UInt16 := ((args[1]?).bind String.toNat?).map (·.toUInt16) |>.getD 8081
  IO.eprintln s!"orb-mac-multi: proven reactor ACROSS PROTOCOLS — WS/HTTP on TCP {tcpPort}, QUIC/H3 on UDP {udpPort}"
  let _udp ← IO.asTask (serveUdp udpPort udpHandle) Task.Priority.dedicated
  serveWs tcpPort multiHttpHandle wsHandle

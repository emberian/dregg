import Tls.Basic
import Ws.Reassembly
import H2.Stream

/-!
# Connection state machine — core types

A sans-IO model of a per-connection protocol state machine for a
multi-protocol network server front end: HTTP/1.1 (keep-alive, pipelining),
TLS with ALPN and optional kernel record-layer offload, HTTP/2 multiplexing,
WebSocket, PROXY-protocol prefixes, SOCKS handshakes, CONNECT tunnels, and
byte-relay states.

The machine is a total, deterministic function

    step : Config → State → Input → State × List Output

All I/O is mediated by the `Input`/`Output` vocabulary. Embedded codecs
(TLS record layer, HTTP/2 framing, WebSocket framing, request parsing) enter
as abstract function-valued fields of `Config`: the state machine treats them
as uninterpreted total functions, so every theorem proved about `step` holds
uniformly for every codec behavior.
-/

namespace Proto

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- Live TLS engine state for a connection, carried as the real `Tls.St`
lifecycle record (handshake/record `Phase` plus the ghost consumed-set). The
FSM threads it opaquely; only the TLS-lane `Config` functions
(`hsFeed`/`tlsRecv`/`tlsSend`) inspect it. Was a `{id : Nat}` stub — a bare
handle carries no real handshake/record state, so no real TLS codec could be
wired without an external side table (the lossy trap). `Tls.St` derives `Repr`
but not `DecidableEq`, so `TlsConn` drops `DecidableEq` here (unused by the
FSM, `step`, and the theorems). -/
structure TlsConn where
  st : Tls.St
deriving Repr

/-- Live HTTP/2 framing-engine state for a connection: the undecoded
partial-frame byte buffer (`recvBuf`) that the framer accumulates across feeds,
plus the per-stream FSM table (`streams`) carrying each stream's
`H2.Stream.StreamState` (RFC 9113 §5.1). The FSM threads it opaquely; only the
H2-lane `Config` functions (`h2Feed`/`h2Send`) inspect it, driving the real H2
frame decoder + HPACK arena decode + per-stream state machine
(`Reactor.H2.h2FeedFn`). Was a `{id : Nat}` stub — a bare handle carries no
frame buffer or stream state, so no real H2 codec could be wired without an
external side table. Both fields carry `DecidableEq` (`Bytes` and
`H2.Stream.StreamState` do), so this keeps `Repr, DecidableEq`. -/
structure H2Conn where
  recvBuf : Bytes := []
  streams : List (Nat × H2.Stream.StreamState) := []
deriving Repr, DecidableEq

/-- Live WebSocket decoder state: the undecoded partial-frame byte buffer plus
the real `Ws.Reassembly.State` (idle, or assembling a fragmented message).
`wsFeed` advances both. Was a `{id : Nat}` stub. `Ws.Reassembly.State` derives
`DecidableEq`, so this keeps `Repr, DecidableEq`. -/
structure WsCodec where
  recvBuf : Bytes := []
  reasm : Ws.Reassembly.State := Ws.Reassembly.State.idle
deriving Repr, DecidableEq

/-- A decoded WebSocket frame, carried as the real `Ws.Frame`
(fin/opcode/payload). Was a `{id : Nat}` stub. `Ws.Frame` derives
`DecidableEq`, so `Output` (which carries a `WsFrame` in `deliverFrame`) keeps
its `DecidableEq`. -/
structure WsFrame where
  frame : Ws.Frame
deriving Repr, DecidableEq

/-- A parsed request, as handed to the application dispatch layer. Carries the
resolved request head — method, target, version, and header name/value pairs
(the FSM does not inspect these; they ride through `dispatch` to the handler).
A concrete `h1Parse` (e.g. the arena parser) fills these by resolving its parse;
`mk` is the placeholder for an empty request. -/
structure Request where
  method  : Bytes := []
  target  : Bytes := []
  version : Bytes := []
  headers : List (Bytes × Bytes) := []
deriving Repr, DecidableEq

/-- An opaque upstream address (host/port pair, already resolved or not —
the machine never inspects it). -/
structure Addr where
  id : Nat
deriving Repr, DecidableEq

/-- Application protocol negotiated by TLS ALPN. -/
inductive Alpn where
  | h1
  | h2
deriving Repr, DecidableEq

/-- Named per-phase deadline slots. A deadline is data in the connection
state; expiry arrives as an explicit `Input.timerFired`. The slots compress
the server's per-phase deadline taxonomy (header read, TLS handshake,
prefix read, body read, keep-alive idle, WebSocket drain) to five
representative phases. -/
inductive TimerSlot where
  | handshake   -- TLS (or intercepted-TLS) handshake completion deadline
  | header      -- request-header / protocol-prefix read deadline
  | body        -- request-body inactivity deadline
  | idle        -- keep-alive / tunnel idle deadline
  | wsClosing   -- WebSocket close-drain deadline
deriving Repr, DecidableEq, BEq

/-- Outcome of attempting to parse one request from the head of the receive
accumulation. The convention is tri-state (complete / incomplete / error),
with `complete` split into a dispatchable request and a validator-produced
canned rejection (oversized header field, overlong target, malformed
framing, ... — the rejection payload is the full canned response).

`consumed` is the number of bytes of the accumulation the parse consumed;
the machine drops exactly that prefix and keeps the rest (pipelining). -/
inductive ParseOutcome where
  | request (consumed : Nat) (req : Request) (keepAlive : Bool)
  | reject (consumed : Nat) (response : Bytes)
  | incomplete
  | error
deriving Repr, DecidableEq

/-- Outcome of feeding accumulated ciphertext to the TLS handshake engine. -/
inductive HsOut where
  /-- Handshake still in progress: new engine state, bytes consumed from the
  accumulation, and handshake bytes to send to the peer. -/
  | more (tc : TlsConn) (consumed : Nat) (toSend : Bytes)
  /-- Handshake complete: negotiated ALPN, whether the record layer was
  offloaded to the kernel, and any early plaintext drained during the
  handshake (0.5-RTT data). -/
  | done (tc : TlsConn) (consumed : Nat) (toSend : Bytes)
         (alpn : Alpn) (ktls : Bool) (earlyPlain : Bytes)
  /-- Handshake failure (alert, malformed record, policy refusal). -/
  | fail

/-- Events produced by the HTTP/2 framing engine for one plaintext feed.
The engine consumes all bytes given (it buffers partial frames itself). -/
inductive H2Event where
  | headers (sid : Nat) (req : Request) (endStream : Bool)
  | data (sid : Nat) (payload : Bytes) (endStream : Bool)
  | windowUpdate
  | goaway
  | protoError

/-- Result of feeding bytes to the WebSocket decoder. The decoder consumes
all bytes given (it buffers partial frames itself). -/
structure WsOut where
  codec : WsCodec
  frames : List WsFrame
  closeReceived : Bool

/-- Sub-phases of the server-side SOCKS handshake. -/
inductive SocksPhase where
  | versionDetect   -- awaiting first bytes to detect SOCKS version (4 vs 5)
  | s5AwaitAuth     -- SOCKS5: greeting parsed, awaiting auth sub-negotiation
  | s5AwaitRequest  -- SOCKS5: auth complete, awaiting CONNECT request
  | s4Parsing       -- SOCKS4/4a: parsing the combined greeting+request
deriving Repr, DecidableEq

/-- Outcome of feeding accumulated bytes to the SOCKS handshake parser. -/
inductive SocksOut where
  | progress (phase : SocksPhase) (consumed : Nat) (reply : Bytes)
  | connect (addr : Addr) (consumed : Nat)
  | fail

/-- Outcome of parsing a connection-prefix header (PROXY protocol). -/
inductive PrefixOut where
  | complete (consumed : Nat)
  | incomplete
  | error

/-- Per-stream state for an in-progress multiplexed (HTTP/2) request:
outbound data that could not be sent because the flow-control window was
exhausted, flushed when a window update arrives. -/
structure StreamSt where
  pendingSend : Option Bytes
deriving Repr, DecidableEq

/-- The multiplexed-stream table, keyed by stream id. -/
abbrev StreamTable := List (Nat × StreamSt)

/-- Per-connection protocol state. One variant per lifecycle stage; the
receive accumulations (`recvBuf` plaintext, `tlsBuf` ciphertext, prefix and
SOCKS handshake buffers) live inside the variant that owns them. -/
inductive ProtoState where
  /-- Awaiting a PROXY-protocol prefix before any TLS or HTTP processing.
  `tlsNext` carries the TLS engine to hand off to if the listener is
  TLS-enabled. -/
  | proxyHeaderAwait (buf : Bytes) (tlsNext : Option TlsConn)
  /-- Plain HTTP/1.1. `recvBuf` is the request accumulation; empty means
  keep-alive idle. -/
  | plainH1 (recvBuf : Bytes)
  /-- TLS handshake in progress — application protocol not yet determined. -/
  | tlsHandshake (tc : TlsConn) (tlsBuf : Bytes)
  /-- HTTP/1.1 over TLS. `tlsBuf` accumulates undecoded ciphertext;
  `recvBuf` accumulates decoded plaintext awaiting a complete request. -/
  | tlsH1 (tc : TlsConn) (tlsBuf : Bytes) (recvBuf : Bytes)
  /-- HTTP/2 over TLS, with the multiplexed stream table. -/
  | tlsH2 (tc : TlsConn) (tlsBuf : Bytes) (h2c : H2Conn) (streams : StreamTable)
  /-- HTTP/2 with the TLS record layer offloaded to the kernel: the machine
  reads and writes plaintext frames; TLS session identity lives outside. -/
  | plainH2 (h2c : H2Conn) (streams : StreamTable)
  /-- WebSocket (plain), server mode. -/
  | plainWs (codec : WsCodec)
  /-- WebSocket over TLS, server mode. -/
  | tlsWs (tc : TlsConn) (tlsBuf : Bytes) (codec : WsCodec)
  /-- WebSocket relay (plain): pure byte forwarding to a paired upstream. -/
  | plainWsRelay (upstream : Nat)
  /-- WebSocket relay over TLS: decrypt, forward plaintext to upstream. -/
  | tlsWsRelay (tc : TlsConn) (tlsBuf : Bytes) (upstream : Nat)
  /-- CONNECT blind tunnel (plain): bidirectional byte relay. -/
  | plainTunnel (upstream : Nat)
  /-- CONNECT blind tunnel, TLS on the client side: decrypt, relay. -/
  | tlsTunnel (tc : TlsConn) (tlsBuf : Bytes) (upstream : Nat)
  /-- WebSocket close frame sent; draining. Inbound data is discarded;
  send-drain or deadline expiry closes the socket. -/
  | wsClosing
  /-- Intercepting-proxy TLS handshake after a CONNECT was accepted for
  interception; on completion transitions to `tlsH1`/`tlsH2` with requests
  routed toward `target`. -/
  | mitmHandshake (tc : TlsConn) (tlsBuf : Bytes) (target : Addr)
  /-- SOCKS proxy handshake in progress; on CONNECT completion transitions
  to `plainTunnel`. -/
  | socksHandshake (buf : Bytes) (phase : SocksPhase)

/-- Events reported by the paired upstream connection or the application
layer (both live outside this machine and re-enter as inputs). -/
inductive UpEvent where
  /-- An outbound connect completed (SOCKS / tunnel setup). -/
  | connected (fd : Nat)
  /-- Bytes arrived from the paired upstream (relay / tunnel). -/
  | data (payload : Bytes)
  /-- The paired upstream closed. -/
  | closed
  /-- Application response bytes for the client (`sid` = 0 for HTTP/1.1). -/
  | response (sid : Nat) (payload : Bytes)
  /-- The application accepted a WebSocket upgrade on this connection. -/
  | wsUpgrade (codec : WsCodec)
  /-- The application established a CONNECT blind tunnel to upstream `fd`. -/
  | tunnel (fd : Nat)
  /-- The application chose to intercept a CONNECT: begin a server-side TLS
  handshake toward the client. -/
  | mitmStart (tc : TlsConn) (target : Addr)
  /-- The application sends an outbound WebSocket frame. -/
  | wsFrameOut (frame : WsFrame)

/-- Inputs to the sans-IO step: everything the environment can tell the
machine. -/
inductive Input where
  /-- Bytes received from the peer socket. -/
  | bytesReceived (data : Bytes)
  /-- A previously blocked send path drained; the socket is writable. -/
  | writeReady
  /-- The environment reports the send path blocked (partial write /
  would-block): stop producing sends until `writeReady`. -/
  | writeBlocked
  /-- A submitted send completed (drained to the kernel). -/
  | sendComplete
  /-- The deadline armed in `slot` fired. -/
  | timerFired (slot : TimerSlot)
  /-- An event from the paired upstream / application layer. -/
  | upstreamEvent (ev : UpEvent)
  /-- Local close requested (shutdown, admin). -/
  | closeRequested
  /-- The peer closed (EOF on receive). -/
  | peerClosed
deriving Inhabited

/-- Outputs of the sans-IO step: everything the machine can ask the
environment to do. -/
inductive Output where
  /-- Send bytes to the peer socket. -/
  | send (data : Bytes)
  /-- Forward bytes to the paired upstream socket. -/
  | sendUpstream (fd : Nat) (data : Bytes)
  /-- Open an outbound connection (SOCKS CONNECT). -/
  | connectUpstream (addr : Addr)
  /-- Install the negotiated record-layer keys in the kernel (TLS offload). -/
  | startTlsOffload
  /-- Arm the deadline in `slot`. -/
  | armTimer (slot : TimerSlot)
  /-- Cancel the deadline in `slot`. -/
  | cancelTimer (slot : TimerSlot)
  /-- Park the receive side (apply backpressure via the transport window). -/
  | cancelRecv
  /-- Re-arm the receive side after a `cancelRecv`. -/
  | resumeRecv
  /-- Close the peer socket. Terminal. -/
  | close
  /-- Hand a parsed request to the application dispatch layer. -/
  | dispatch (req : Request)
  /-- Deliver a request-body chunk for multiplexed stream `sid`. -/
  | deliverBody (sid : Nat) (data : Bytes)
  /-- Deliver an inbound WebSocket frame to the application. -/
  | deliverFrame (frame : WsFrame)
deriving Repr, DecidableEq

/-- `true` exactly on peer-socket `send` outputs (the send-block gate's
discriminator; upstream forwards target a different socket). -/
def Output.isSend : Output → Bool
  | .send _ => true
  | _ => false

/-- The payload of a peer-socket `send` output, if any. -/
def Output.sendPayload : Output → Option Bytes
  | .send b => some b
  | _ => none

/-- Static configuration and the abstract codec vocabulary. Every
function-valued field is an uninterpreted total function: theorems about
`step` hold for all of them. -/
structure Config where
  /-- Cap on the request-header accumulation; exceeding it produces
  `oversizeResponse` and a close. -/
  maxHeaderBytes : Nat
  /-- Cap on the connection-prefix accumulation. -/
  maxPrefixBytes : Nat
  /-- Canned malformed-request response (400-class). -/
  errorResponse : Bytes
  /-- Canned oversized-header response (431-class). -/
  oversizeResponse : Bytes
  /-- Encoded WebSocket close frame. -/
  wsCloseFrame : Bytes
  /-- Canned SOCKS connect-succeeded reply. -/
  socksConnectReply : Bytes
  /-- Parse one request from the head of a plaintext accumulation. -/
  h1Parse : Bytes → ParseOutcome
  /-- Parse a connection-prefix (PROXY protocol) header. -/
  prefixParse : Bytes → PrefixOut
  /-- Feed ciphertext to the TLS handshake engine. -/
  hsFeed : TlsConn → Bytes → HsOut
  /-- Decode established-session ciphertext: `(engine', consumed, plaintext)`,
  or `none` on a record-layer error. -/
  tlsRecv : TlsConn → Bytes → Option (TlsConn × Nat × Bytes)
  /-- Encrypt plaintext for sending on an established session. -/
  tlsSend : TlsConn → Bytes → TlsConn × Bytes
  /-- Fresh HTTP/2 engine for a newly negotiated connection. -/
  h2Init : H2Conn
  /-- Feed plaintext to the HTTP/2 framing engine (all-consuming). -/
  h2Feed : H2Conn → Bytes → H2Conn × List H2Event
  /-- Frame response bytes for stream `sid`: `(engine', wire, flowBlocked)` —
  `flowBlocked` is the remainder that exceeded the send window, parked on
  the stream until a window update. -/
  h2Send : H2Conn → Nat → Bytes → H2Conn × Bytes × Option Bytes
  /-- Feed bytes to the WebSocket decoder (all-consuming). -/
  wsFeed : WsCodec → Bytes → WsOut
  /-- Encode an outbound WebSocket frame. -/
  wsEncode : WsFrame → Bytes
  /-- Feed accumulated bytes to the SOCKS handshake parser. -/
  socksFeed : SocksPhase → Bytes → SocksOut

/-- The per-connection record: protocol state, send-block flag with the
queue of sends parked behind it, receive arming (backpressure), and the
armed deadline slots. -/
structure Conn where
  proto : ProtoState
  /-- Once the environment reports `writeBlocked`, no further peer-socket
  sends are emitted until `writeReady`; they queue in `pendingSend`. -/
  sendBlocked : Bool
  /-- Sends parked behind a blocked send path, in order. -/
  pendingSend : List Bytes
  /-- Whether the receive side is armed (`false` = parked for backpressure). -/
  recvArmed : Bool
  /-- Armed deadline slots. -/
  timers : List TimerSlot

/-- Top-level connection lifecycle: an active connection or closed. -/
inductive State where
  | active (c : Conn)
  | closed

/-- Fresh plain-listener connection (initial header deadline armed). -/
def Conn.mkPlain : Conn :=
  { proto := .plainH1 [], sendBlocked := false, pendingSend := [],
    recvArmed := true, timers := [.header] }

/-- Fresh TLS-listener connection. -/
def Conn.mkTls (tc : TlsConn) : Conn :=
  { proto := .tlsHandshake tc [], sendBlocked := false, pendingSend := [],
    recvArmed := true, timers := [.handshake] }

/-- Fresh connection awaiting a PROXY-protocol prefix. -/
def Conn.mkPrefixed (tlsNext : Option TlsConn) : Conn :=
  { proto := .proxyHeaderAwait [] tlsNext, sendBlocked := false,
    pendingSend := [], recvArmed := true, timers := [.header] }

/-- Fresh SOCKS-listener connection. -/
def Conn.mkSocks : Conn :=
  { proto := .socksHandshake [] .versionDetect, sendBlocked := false,
    pendingSend := [], recvArmed := true, timers := [.header] }

end Proto

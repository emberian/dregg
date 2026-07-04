import Proto.Basic

/-!
# Connection state machine — the sans-IO step

`step cfg s i` is total and pure. Protocol logic is written against the
abstract codec vocabulary in `Config`; the send-block gate (`gate`) and the
close plumbing live in `finish`, shared by every protocol branch.

Structure:

* `h1Loop` — the HTTP/1.1 keep-alive/pipelining loop: parse-dispatch-drop
  repeatedly from the head of the plaintext accumulation, fueled by the
  buffer length (a parse that consumes nothing terminates the loop with the
  accumulation intact, so fuel exhaustion can never drop bytes).
* `runH1` / `runH2` / `wsBytes` / `hsStep` — per-protocol byte handlers
  producing an `Eff` (successor protocol state, raw outputs, close intent).
* `finish` — applies the send-block gate to the raw outputs, queues parked
  sends, and realizes the close intent.
* `step` — the top-level total transition function.
-/

namespace Proto

/-- Emit a send only when there is something to send. -/
def sendIf (b : Bytes) : List Output :=
  if b.isEmpty then [] else [.send b]

/-- The effect of a protocol-level handler, before send-gating. -/
structure Eff where
  proto : ProtoState
  outs : List Output := []
  closeNow : Bool := false
  /-- Replacement deadline-slot set (`none` = unchanged). -/
  timers : Option (List TimerSlot) := none

/-- The send-block gate: when `blocked`, peer-socket sends are diverted to
the parked queue (in order) instead of being emitted; all other outputs pass
through. When not blocked, everything passes and nothing parks. -/
def gate (blocked : Bool) (outs : List Output) : List Output × List Bytes :=
  if blocked then
    (outs.filter (fun o => !o.isSend), outs.filterMap Output.sendPayload)
  else
    (outs, [])

/-- Result of the HTTP/1.1 request loop. `outs` never contains `close`;
close intent is the `closing` flag (realized by `finish`). -/
structure LoopOut where
  residual : Bytes
  outs : List Output := []
  closing : Bool := false

/-- The keep-alive/pipelining loop: repeatedly parse a request from the head
of the accumulation, emit its dispatch, and drop exactly the consumed
prefix. Stops on an incomplete parse (keeping the accumulation intact), a
close-carrying outcome (error / reject / non-keep-alive request), or fuel
exhaustion (also keeping the accumulation intact). -/
def h1Loop (cfg : Config) : Nat → Bytes → LoopOut
  | 0, buf => { residual := buf }
  | fuel + 1, buf =>
    if buf.isEmpty then { residual := buf }
    else
      match cfg.h1Parse buf with
      | .incomplete => { residual := buf }
      | .error =>
        { residual := buf, outs := [.send cfg.errorResponse], closing := true }
      | .reject n resp =>
        { residual := buf.drop n, outs := [.send resp], closing := true }
      | .request n req keepAlive =>
        if keepAlive then
          let r := h1Loop cfg fuel (buf.drop n)
          { residual := r.residual, outs := .dispatch req :: r.outs,
            closing := r.closing }
        else
          { residual := buf.drop n, outs := [.dispatch req], closing := true }

/-- Run the HTTP/1.1 path on a plaintext accumulation: oversize check, then
the pipelining loop. `frame` rebuilds the owning protocol state around the
residual accumulation. -/
def runH1 (cfg : Config) (frame : Bytes → ProtoState) (buf : Bytes)
    (pre : List Output) : Eff :=
  if buf.length > cfg.maxHeaderBytes then
    { proto := frame buf, outs := pre ++ [.send cfg.oversizeResponse],
      closeNow := true }
  else
    let r := h1Loop cfg (buf.length + 1) buf
    { proto := frame r.residual, outs := pre ++ r.outs, closeNow := r.closing }

/-- Park flow-blocked response bytes on stream `sid`. -/
def setPending (streams : StreamTable) (sid : Nat) (p : Option Bytes) :
    StreamTable :=
  streams.map (fun q => if q.1 = sid then (q.1, ⟨p⟩) else q)

/-- Interpret the HTTP/2 engine's events against the stream table:
`headers` registers the stream and dispatches; `data` delivers a body
chunk; `windowUpdate` flushes all flow-blocked sends; `goaway` and
`protoError` request close. -/
def h2Apply (streams : StreamTable) :
    List H2Event → StreamTable × List Output × Bool
  | [] => (streams, [], false)
  | .headers sid req _endStream :: rest =>
    let (s', outs, cl) := h2Apply ((sid, ⟨none⟩) :: streams) rest
    (s', .dispatch req :: outs, cl)
  | .data sid payload _endStream :: rest =>
    let (s', outs, cl) := h2Apply streams rest
    (s', .deliverBody sid payload :: outs, cl)
  | .windowUpdate :: rest =>
    let flushed := streams.filterMap (fun q => q.2.pendingSend)
    let cleared := streams.map (fun q => (q.1, StreamSt.mk none))
    let (s', outs, cl) := h2Apply cleared rest
    (s', flushed.map Output.send ++ outs, cl)
  | .goaway :: _ => (streams, [], true)
  | .protoError :: _ => (streams, [], true)

/-- Run the HTTP/2 path on decoded plaintext. -/
def runH2 (cfg : Config) (frame : H2Conn → StreamTable → ProtoState)
    (h2c : H2Conn) (streams : StreamTable) (plain : Bytes)
    (pre : List Output) : Eff :=
  let (h2c', events) := cfg.h2Feed h2c plain
  let (streams', outs, cl) := h2Apply streams events
  { proto := frame h2c' streams', outs := pre ++ outs, closeNow := cl }

/-- Run the WebSocket path on decoded plaintext: deliver inbound frames;
a close frame from the peer sends our close frame and enters the drain
state with its deadline armed. -/
def wsBytes (cfg : Config) (frame : WsCodec → ProtoState) (codec : WsCodec)
    (data : Bytes) : Eff :=
  let w := cfg.wsFeed codec data
  let deliver := w.frames.map Output.deliverFrame
  if w.closeReceived then
    { proto := .wsClosing,
      outs := deliver ++ [.send cfg.wsCloseFrame, .armTimer .wsClosing],
      timers := some [.wsClosing] }
  else
    { proto := frame w.codec, outs := deliver }

/-- Drive the TLS handshake engine on the ciphertext accumulation.
`stay` is the current protocol state (kept on failure so close-effects are
well-formed); `mitm` distinguishes the intercepting-proxy handshake (whose
successors route toward the recorded target and never use kernel offload).

On completion: cancel the handshake deadline, arm the header deadline, send
any final handshake bytes, and enter the negotiated protocol — feeding any
early plaintext (0.5-RTT) straight into it. Kernel offload with leftover
ciphertext in userspace is unrepresentable after key handoff, so that edge
closes defensively. -/
def hsStep (cfg : Config) (mitm : Option Addr) (stay : ProtoState)
    (tc : TlsConn) (buf : Bytes) : Eff :=
  match cfg.hsFeed tc buf with
  | .more tc' consumed toSend =>
    { proto := match mitm with
        | none => .tlsHandshake tc' (buf.drop consumed)
        | some t => .mitmHandshake tc' (buf.drop consumed) t,
      outs := sendIf toSend }
  | .fail => { proto := stay, closeNow := true }
  | .done tc' consumed toSend alpn ktls earlyPlain =>
    let residual := buf.drop consumed
    let pre := sendIf toSend ++ [.cancelTimer .handshake, .armTimer .header]
    let eff :=
      if ktls && mitm.isNone then
        if residual.isEmpty then
          let pre := pre ++ [.startTlsOffload]
          match alpn with
          | .h1 => runH1 cfg .plainH1 earlyPlain pre
          | .h2 => runH2 cfg .plainH2 cfg.h2Init [] earlyPlain pre
        else
          { proto := stay, closeNow := true }
      else
        match alpn with
        | .h1 => runH1 cfg (fun b => .tlsH1 tc' residual b) earlyPlain pre
        | .h2 =>
          runH2 cfg (fun h s => .tlsH2 tc' residual h s) cfg.h2Init []
            earlyPlain pre
    { eff with timers := some [.header] }

/-- Protocol-level handling of received bytes (ungated). -/
def onBytes (cfg : Config) (p : ProtoState) (data : Bytes) : Eff :=
  match p with
  | .proxyHeaderAwait buf tlsNext =>
    let buf' := buf ++ data
    if buf'.length > cfg.maxPrefixBytes then
      { proto := p, closeNow := true }
    else
      match cfg.prefixParse buf' with
      | .incomplete => { proto := .proxyHeaderAwait buf' tlsNext }
      | .error => { proto := p, closeNow := true }
      | .complete n =>
        let rest := buf'.drop n
        match tlsNext with
        | none => runH1 cfg .plainH1 rest []
        | some tc =>
          { hsStep cfg none (.tlsHandshake tc rest) tc rest with
              timers := some [.handshake] }
  | .plainH1 recvBuf => runH1 cfg .plainH1 (recvBuf ++ data) []
  | .tlsHandshake tc tlsBuf => hsStep cfg none p tc (tlsBuf ++ data)
  | .mitmHandshake tc tlsBuf target =>
    hsStep cfg (some target) p tc (tlsBuf ++ data)
  | .tlsH1 tc tlsBuf recvBuf =>
    let buf' := tlsBuf ++ data
    match cfg.tlsRecv tc buf' with
    | none => { proto := p, closeNow := true }
    | some (tc', consumed, plain) =>
      runH1 cfg (fun b => .tlsH1 tc' (buf'.drop consumed) b)
        (recvBuf ++ plain) []
  | .tlsH2 tc tlsBuf h2c streams =>
    let buf' := tlsBuf ++ data
    match cfg.tlsRecv tc buf' with
    | none => { proto := p, closeNow := true }
    | some (tc', consumed, plain) =>
      runH2 cfg (fun h s => .tlsH2 tc' (buf'.drop consumed) h s) h2c streams
        plain []
  | .plainH2 h2c streams => runH2 cfg .plainH2 h2c streams data []
  | .plainWs codec => wsBytes cfg .plainWs codec data
  | .tlsWs tc tlsBuf codec =>
    let buf' := tlsBuf ++ data
    match cfg.tlsRecv tc buf' with
    | none => { proto := p, closeNow := true }
    | some (tc', consumed, plain) =>
      wsBytes cfg (fun c => .tlsWs tc' (buf'.drop consumed) c) codec plain
  | .plainWsRelay fd => { proto := p, outs := [.sendUpstream fd data] }
  | .tlsWsRelay tc tlsBuf fd =>
    let buf' := tlsBuf ++ data
    match cfg.tlsRecv tc buf' with
    | none => { proto := p, closeNow := true }
    | some (tc', consumed, plain) =>
      { proto := .tlsWsRelay tc' (buf'.drop consumed) fd,
        outs := if plain.isEmpty then [] else [.sendUpstream fd plain] }
  | .plainTunnel fd => { proto := p, outs := [.sendUpstream fd data] }
  | .tlsTunnel tc tlsBuf fd =>
    let buf' := tlsBuf ++ data
    match cfg.tlsRecv tc buf' with
    | none => { proto := p, closeNow := true }
    | some (tc', consumed, plain) =>
      { proto := .tlsTunnel tc' (buf'.drop consumed) fd,
        outs := if plain.isEmpty then [] else [.sendUpstream fd plain] }
  | .wsClosing => { proto := p }   -- inbound data is silently discarded
  | .socksHandshake buf phase =>
    let buf' := buf ++ data
    match cfg.socksFeed phase buf' with
    | .progress phase' consumed reply =>
      { proto := .socksHandshake (buf'.drop consumed) phase',
        outs := sendIf reply }
    | .connect addr consumed =>
      { proto := .socksHandshake (buf'.drop consumed) phase,
        outs := [.connectUpstream addr] }
    | .fail => { proto := p, closeNow := true }

/-- Protocol-level handling of upstream/application events (ungated).
Unmatched (event, state) pairs are ignored: stale events from a previous
connection incarnation must not perturb the machine. -/
def onUp (cfg : Config) (p : ProtoState) (ev : UpEvent) : Eff :=
  match ev, p with
  -- SOCKS: outbound connect completed → success reply, enter the tunnel.
  | .connected fd, .socksHandshake _ _ =>
    { proto := .plainTunnel fd, outs := [.send cfg.socksConnectReply],
      timers := some [.idle] }
  -- Relay/tunnel: upstream bytes flow back to the client.
  | .data payload, .plainWsRelay _ => { proto := p, outs := [.send payload] }
  | .data payload, .plainTunnel _ => { proto := p, outs := [.send payload] }
  | .data payload, .tlsWsRelay tc tlsBuf fd =>
    let (tc', wire) := cfg.tlsSend tc payload
    { proto := .tlsWsRelay tc' tlsBuf fd, outs := [.send wire] }
  | .data payload, .tlsTunnel tc tlsBuf fd =>
    let (tc', wire) := cfg.tlsSend tc payload
    { proto := .tlsTunnel tc' tlsBuf fd, outs := [.send wire] }
  -- Relay/tunnel: upstream closed → close the client side.
  | .closed, .plainWsRelay _ => { proto := p, closeNow := true }
  | .closed, .tlsWsRelay _ _ _ => { proto := p, closeNow := true }
  | .closed, .plainTunnel _ => { proto := p, closeNow := true }
  | .closed, .tlsTunnel _ _ _ => { proto := p, closeNow := true }
  -- Application response bytes.
  | .response _ payload, .plainH1 b =>
    { proto := .plainH1 b, outs := [.send payload] }
  | .response _ payload, .tlsH1 tc tlsBuf recvBuf =>
    let (tc', wire) := cfg.tlsSend tc payload
    { proto := .tlsH1 tc' tlsBuf recvBuf, outs := [.send wire] }
  | .response sid payload, .plainH2 h2c streams =>
    let (h2c', wire, pend) := cfg.h2Send h2c sid payload
    { proto := .plainH2 h2c' (setPending streams sid pend),
      outs := sendIf wire }
  | .response sid payload, .tlsH2 tc tlsBuf h2c streams =>
    let (h2c', wire, pend) := cfg.h2Send h2c sid payload
    let (tc', cipher) := cfg.tlsSend tc wire
    { proto := .tlsH2 tc' tlsBuf h2c' (setPending streams sid pend),
      outs := sendIf cipher }
  -- Upgrades out of HTTP/1.1: residual pipelined bytes are carried into
  -- the successor protocol, never dropped.
  | .wsUpgrade codec, .plainH1 recvBuf =>
    wsBytes cfg .plainWs codec recvBuf
  | .wsUpgrade codec, .tlsH1 tc tlsBuf recvBuf =>
    wsBytes cfg (fun c => .tlsWs tc tlsBuf c) codec recvBuf
  | .tunnel fd, .plainH1 recvBuf =>
    { proto := .plainTunnel fd,
      outs := if recvBuf.isEmpty then [] else [.sendUpstream fd recvBuf],
      timers := some [.idle] }
  | .tunnel fd, .tlsH1 tc tlsBuf recvBuf =>
    { proto := .tlsTunnel tc tlsBuf fd,
      outs := if recvBuf.isEmpty then [] else [.sendUpstream fd recvBuf],
      timers := some [.idle] }
  | .mitmStart tc target, .plainH1 _ =>
    { proto := .mitmHandshake tc [] target,
      outs := [.armTimer .handshake], timers := some [.handshake] }
  -- Outbound WebSocket frames from the application.
  | .wsFrameOut f, .plainWs codec =>
    { proto := .plainWs codec, outs := [.send (cfg.wsEncode f)] }
  | .wsFrameOut f, .tlsWs tc tlsBuf codec =>
    let (tc', wire) := cfg.tlsSend tc (cfg.wsEncode f)
    { proto := .tlsWs tc' tlsBuf codec, outs := [.send wire] }
  | _, _ => { proto := p }

/-- Apply the send-block gate to an effect and realize its close intent.
While blocked, peer-socket sends park in order on `pendingSend`; every
other output passes through. A closing effect yields the terminal state
with an explicit `close` output (parked sends are discarded — the socket
is going away). -/
def finish (c : Conn) (e : Eff) : State × List Output :=
  let (passed, parked) := gate c.sendBlocked e.outs
  if e.closeNow then
    (.closed, passed ++ [.close])
  else
    (.active { c with
        proto := e.proto,
        pendingSend := c.pendingSend ++ parked,
        timers := e.timers.getD c.timers },
     passed)

/-- The sans-IO step: total and deterministic by construction.

* `closed` is absorbing and silent.
* `writeReady` / `writeBlocked` are handled uniformly across all protocol
  states: blocking parks the receive side (backpressure) and future sends;
  readiness flushes the parked sends in order and re-arms receive.
* `sendComplete` matters only to the WebSocket drain state.
* `timerFired` on an armed slot closes the connection (per-phase deadline);
  a stale timer is ignored.
* Received bytes and upstream events go to the protocol handlers, through
  the send-block gate. -/
def step (cfg : Config) (s : State) (i : Input) : State × List Output :=
  match s with
  | .closed => (.closed, [])
  | .active c =>
    match i with
    | .bytesReceived data => finish c (onBytes cfg c.proto data)
    | .upstreamEvent ev => finish c (onUp cfg c.proto ev)
    | .writeReady =>
      (.active { c with sendBlocked := false, pendingSend := [],
                        recvArmed := true },
       c.pendingSend.map Output.send
         ++ (if c.recvArmed then [] else [.resumeRecv]))
    | .writeBlocked =>
      (.active { c with sendBlocked := true, recvArmed := false },
       if c.recvArmed then [.cancelRecv] else [])
    | .sendComplete =>
      match c.proto with
      | .wsClosing => (.closed, [.close])
      | _ => (.active c, [])
    | .timerFired slot =>
      if c.timers.contains slot then (.closed, [.close]) else (.active c, [])
    | .closeRequested => (.closed, [.close])
    | .peerClosed => (.closed, [.close])

/-- The step relation (the graph of `step`), for stating determinism. -/
def Steps (cfg : Config) (s : State) (i : Input)
    (s' : State) (outs : List Output) : Prop :=
  step cfg s i = (s', outs)

end Proto

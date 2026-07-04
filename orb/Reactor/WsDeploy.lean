import Reactor.Deploy

/-!
# Reactor.WsDeploy — making the WebSocket lane RUNTIME-REACHABLE

The starting point: the real WebSocket engine (`Reactor.Ws.wsFeedFn` — byte-level
frame decode + unmask + the real `Ws.Reassembly` fold) is *installed* in the
deployed config (`deployConfig.wsFeed = Ws.wsFeedFn`, `Deploy.deploy_uses_real_ws`),
and `Reactor.Ws` proves the reassembly seam (`ws_reassembly_seam` / `wsBytes_seam`)
for the field. But the deployed FSM only ever *entered* the HTTP/1.1 and (via
`Ingress`) h2c paths — nothing drove a connection **into** `.plainWs` and then ran
a real frame through `wsFeedFn`. "Installed in the config" is not "executed on the
path": the WebSocket engine was runtime-dead.

This file closes that gap. It wires the RFC 6455 upgrade + framing onto a runnable
`Proto.step` path:

1. an HTTP/1.1 `Upgrade: websocket` request is received on a plain-listener
   connection (`Conn.mkPlain`, parked in `.plainH1`); the REAL arena parser
   (`h1ParseFn`) parses it and the FSM dispatches it — the connection stays in
   `.plainH1`, keep-alive (`Connection: Upgrade`, not `close`);
2. the application accepts the upgrade and re-enters the machine as
   `UpEvent.wsUpgrade codec` — the **FSM upgrade transition** (`onUp`'s
   `.wsUpgrade, .plainH1` arm) drives the connection into `.plainWs codec`;
3. a subsequent inbound **masked WS text frame** is received in `.plainWs` and
   runs through the REAL `wsFeedFn` (decode → unmask → `Ws.Reassembly`), emitting
   `Output.deliverFrame` with the decoded payload.

## The runtime execution proof (`#guard`, kernel-evaluated)

`ws_upgrade_guard` drives `Proto.step` over `deployConfig` three times — real
Upgrade request, `wsUpgrade` accept, masked text frame — and checks the third
step's outputs carry a `deliverFrame` of the decoded payload `"HI"` (`[0x48,0x49]`).
The `#guard` forces evaluation of `Proto.step → onBytes(.plainH1) → runH1 →
h1ParseFn` (real arena parse), then `onUp(.wsUpgrade,.plainH1) → wsBytes`, then
`onBytes(.plainWs) → wsBytes → wsFeedFn → decodeFrame(applyMask) → Reassembly.step`
— the real engines run on real bytes, not a correspondence beside the pipeline.

## The theorem

`ws_upgrade_runtime` is the composition the goal names: the FSM upgrade transition
composed with the reassembly seam. For any config whose `wsFeed` is the real
engine (`deployConfig` by `deploy_uses_real_ws`), from a `.plainH1` connection:
(1) the `wsUpgrade` event drives the FSM into `.plainWs` on the supplied codec, and
(2) the very next `bytesReceived`, if its bytes decode to a fragmented WebSocket
message, is reassembled by the real `Ws.Reassembly` engine (via
`Reactor.Ws.feedFrames_fragmented`) and delivered as a single `deliverFrame` whose
payload is the in-order concatenation of every fragment. Conjunct (2) feeds the
literal output state of conjunct (1) — the two `Proto.step`s are chained, so this
is the genuine runtime successor, not a re-derivation.
-/

namespace Reactor
namespace WsDeploy

open Proto (Bytes State Input Output Conn WsCodec WsFrame Config UpEvent ProtoState)

/-! ## (1) A real HTTP/1.1 WebSocket upgrade request -/

/-- A concrete RFC 6455 §4.1 client handshake: `GET /chat HTTP/1.1` with the
`Upgrade: websocket` / `Connection: Upgrade` header pair and the
`Sec-WebSocket-Key` / `Sec-WebSocket-Version` fields. The REAL arena parser
(`Reactor.Config.h1ParseFn`) parses it to a keep-alive `request` (the
`Connection` value is `Upgrade`, not `close`), consuming all 144 octets — so the
FSM dispatches it and holds the connection open in `.plainH1` for the application
to accept the upgrade. -/
def upgradeReq : Bytes :=
  (String.toUTF8
    "GET /chat HTTP/1.1\r\nHost: x\r\nUpgrade: websocket\r\nConnection: Upgrade\r\nSec-WebSocket-Key: dGhlIHNhbXBsZSBub25jZQ==\r\nSec-WebSocket-Version: 13\r\n\r\n").toList

/-- The fresh WebSocket codec the application hands the FSM on accepting the
upgrade: an empty partial-frame buffer and an `idle` reassembly state. -/
def wsFreshCodec : WsCodec := {}

theorem wsFreshCodec_recvBuf : wsFreshCodec.recvBuf = [] := rfl
theorem wsFreshCodec_reasm : wsFreshCodec.reasm = Ws.Reassembly.State.idle := rfl

/-! ## (2) A concrete masked WebSocket text frame -/

/-- A client→server single WebSocket **text** frame, masked (RFC 6455 §5.2/§5.3):
`0x81` (`fin=1`, opcode `text`), `0x82` (mask bit set, 7-bit length `2`), masking
key `[0x01,0x02,0x03,0x04]`, masked payload `[0x49,0x4B]`. The real `Ws.applyMask`
recovers `[0x48,0x49]` — `"HI"`. -/
def maskedTextFrame : Bytes := [0x81, 0x82, 0x01, 0x02, 0x03, 0x04, 0x49, 0x4B]

/-! ## (3) The runtime driver — three `Proto.step`s over the deployed config -/

/-- The full runtime sequence over the DEPLOYED config (`deployConfig`, whose
`wsFeed` IS `Ws.wsFeedFn` by `Deploy.deploy_uses_real_ws`):

* receive the HTTP/1.1 Upgrade request (real arena parse + dispatch, stays
  `.plainH1`);
* the application accepts — `wsUpgrade` drives the FSM into `.plainWs`;
* receive the WS frame — the real `wsFeedFn` decodes it.

Returns the third step's outputs: the delivered frames. -/
def runUpgrade (req frame : Bytes) : List Output :=
  let s0 := Proto.step Reactor.Deploy.deployConfig
              (.active Conn.mkPlain) (.bytesReceived req)
  let s1 := Proto.step Reactor.Deploy.deployConfig
              s0.1 (.upstreamEvent (.wsUpgrade wsFreshCodec))
  (Proto.step Reactor.Deploy.deployConfig s1.1 (.bytesReceived frame)).2

/-! **RUNTIME EXECUTION PROOF (`#guard`, kernel-evaluated).** A real HTTP/1.1
`Upgrade: websocket` request, then the `wsUpgrade` accept, then a masked WS text
frame — driven through `Proto.step` over `deployConfig` — deliver the decoded
payload `"HI"` (`[0x48, 0x49]`). This forces the kernel to run the real arena
parser, the FSM upgrade transition, and the real `wsFeedFn` (decode + `applyMask`
+ `Ws.Reassembly`) on real bytes. -/
#guard
  runUpgrade upgradeReq maskedTextFrame
    = [Proto.Output.deliverFrame ⟨{ fin := true, opcode := .text, payload := [0x48, 0x49] }⟩]

/-! ## (4) The theorem — the FSM upgrade transition composed with reassembly -/

/-- **`ws_upgrade_runtime`.** For any config whose WebSocket lane is the real
engine (`hwsFeed : cfg.wsFeed = Ws.wsFeedFn` — `deployConfig` by
`Deploy.deploy_uses_real_ws`), driven from a plain HTTP/1.1 connection `c`
(`c.proto = .plainH1 []`, send path unblocked):

* **(1) the upgrade transition reaches `.plainWs`.** The application's
  `UpEvent.wsUpgrade wsFreshCodec` drives `Proto.step` to the successor state
  `.active { c with proto := .plainWs wsFreshCodec }` — the FSM has entered the
  WebSocket path on the supplied codec.

* **(2) the next frame is decoded by the REAL `wsFeedFn`.** Feeding the *literal
  successor state of (1)* a `bytesReceived frame` whose bytes decode to a
  fragmented WebSocket message (an initial data frame `fin=false`, a run of
  continuation fragments, a final `fin` continuation) emits exactly one output —
  a `deliverFrame` whose payload is the in-order concatenation
  `initial ++ mids.flatten ++ final`. The reassembly is performed by the real
  `Ws.Reassembly` engine (`Reactor.Ws.feedFrames_fragmented`), reached through
  `cfg.wsFeed = wsFeedFn`.

The two `Proto.step`s are chained (conjunct 2's inner state is `(step … wsUpgrade).1`),
so this is the connection's genuine runtime evolution: upgrade, then a real frame
decoded on the `.plainWs` successor. -/
theorem ws_upgrade_runtime
    (cfg : Config) (c : Conn)
    (hproto : c.proto = .plainH1 [])
    (hunblocked : c.sendBlocked = false)
    (hwsFeed : cfg.wsFeed = Reactor.Ws.wsFeedFn)
    (frame : Bytes)
    (op : Ws.Opcode) (hop : op = .text ∨ op = .binary)
    (initial : Bytes) (mids : List Bytes) (final : Bytes)
    (hdec : (Reactor.Ws.decodeAll frame).1
        = ({ fin := false, opcode := op, payload := initial } : Ws.Frame)
            :: mids.map (fun m => ({ fin := false, opcode := .continuation, payload := m } : Ws.Frame))
            ++ [{ fin := true, opcode := .continuation, payload := final }]) :
    (Proto.step cfg (.active c) (.upstreamEvent (.wsUpgrade wsFreshCodec))).1
        = .active { c with proto := .plainWs wsFreshCodec }
    ∧ (Proto.step cfg
        (Proto.step cfg (.active c) (.upstreamEvent (.wsUpgrade wsFreshCodec))).1
        (.bytesReceived frame)).2
      = [Proto.Output.deliverFrame ⟨{ fin := true, opcode := op, payload := initial ++ mids.flatten ++ final }⟩] := by
  -- (1) the upgrade transition: wsUpgrade on .plainH1 [] enters .plainWs.
  have hempty : cfg.wsFeed wsFreshCodec [] = { codec := wsFreshCodec, frames := [], closeReceived := false } := by
    rw [hwsFeed]; rfl
  have step1 : Proto.step cfg (.active c) (.upstreamEvent (.wsUpgrade wsFreshCodec))
      = (.active { c with proto := .plainWs wsFreshCodec }, []) := by
    show Proto.finish c (Proto.onUp cfg c.proto (.wsUpgrade wsFreshCodec)) = _
    rw [hproto]
    show Proto.finish c (Proto.wsBytes cfg ProtoState.plainWs wsFreshCodec []) = _
    simp only [Proto.wsBytes, hempty, List.map_nil, if_neg (by decide : ¬ (false = true)),
      Proto.finish, Proto.gate, hunblocked, List.append_nil, Option.getD]
  have c1 : (Proto.step cfg (.active c) (.upstreamEvent (.wsUpgrade wsFreshCodec))).1
      = .active { c with proto := .plainWs wsFreshCodec } := by rw [step1]
  refine ⟨c1, ?_⟩
  -- (2) the real wsFeedFn decodes the fragmented frame on the .plainWs successor.
  rw [step1]
  -- wsFeedFn on the fresh idle codec: decode → reassemble the fragmented message.
  have hfeed : cfg.wsFeed wsFreshCodec frame
      = { codec := { recvBuf := (Reactor.Ws.decodeAll frame).2, reasm := Ws.Reassembly.State.idle }, frames := [⟨{ fin := true, opcode := op, payload := initial ++ mids.flatten ++ final }⟩], closeReceived := false } := by
    rw [hwsFeed]
    show Reactor.Ws.wsFeedFn wsFreshCodec frame = _
    simp only [Reactor.Ws.wsFeedFn, wsFreshCodec_recvBuf, wsFreshCodec_reasm, List.nil_append]
    rw [hdec, Reactor.Ws.feedFrames_fragmented op hop initial mids final,
        Reactor.Ws.fragmented_no_close op hop initial mids final]
  show (Proto.finish { c with proto := .plainWs wsFreshCodec }
          (Proto.onBytes cfg (ProtoState.plainWs wsFreshCodec) frame)).2 = _
  simp only [Proto.onBytes, Proto.wsBytes, hfeed, List.map_cons, List.map_nil,
    if_neg (by decide : ¬ (false = true)), Proto.finish, Proto.gate, hunblocked]

end WsDeploy
end Reactor

# WebSocket — now runtime-reachable

`Reactor/WsDeploy.lean` wires the WebSocket **upgrade + framing** onto a runnable
`Proto.step` path and proves it, so the real WebSocket engine is no longer merely
*installed* in the deployed config — it **executes** on a connection driven from a
real HTTP/1.1 `Upgrade` request.

## The gap this closes

The real WebSocket engine already existed and was proven:

- `Reactor/Ws.lean` — `wsFeedFn`: byte-level RFC 6455 §5.2 frame decode
  (`decodeFrame`), unmask via the real `Ws.applyMask`, and the real
  `Ws.Reassembly` fragmentation fold (`feedFrames`); plus the reassembly seam
  theorems (`ws_reassembly_seam`, `wsBytes_seam`, `feedFrames_fragmented`).
- `Reactor/Deploy.lean` — `deployConfig.wsFeed = Ws.wsFeedFn`
  (`deploy_uses_real_ws`): the deployed config's WebSocket lane *is* that engine.

But nothing drove a connection **into** `.plainWs` and then ran a real frame
through `wsFeedFn`. Installed-in-the-config is not executed-on-the-path: the
WebSocket lane was runtime-dead, the same shape the h2c ingress
(`Reactor/H2Ingress.lean`) fixed for HTTP/2.

## The runnable path (RFC 6455 §4 handshake → §5 framing)

Three `Proto.step`s over `deployConfig`:

1. **Upgrade request received.** A concrete client handshake — `GET /chat
   HTTP/1.1` with `Upgrade: websocket` / `Connection: Upgrade` and the
   `Sec-WebSocket-Key` / `Sec-WebSocket-Version` fields (`upgradeReq`) — is fed to
   a plain-listener connection (`Conn.mkPlain`, parked in `.plainH1`). The REAL
   arena parser (`Reactor.Config.h1ParseFn`) parses it to a keep-alive request
   (its `Connection` value is `Upgrade`, not `close`), consuming all 144 octets,
   and the FSM dispatches it — the connection stays open in `.plainH1`.
2. **Upgrade accepted.** The application re-enters the machine as
   `UpEvent.wsUpgrade codec`. This is the **FSM upgrade transition** (`onUp`'s
   `.wsUpgrade, .plainH1` arm), which drives the connection into `.plainWs codec`.
3. **Masked frame decoded.** A masked client→server text frame
   (`maskedTextFrame = [0x81, 0x82, 0x01,0x02,0x03,0x04, 0x49,0x4B]`) received in
   `.plainWs` runs through the REAL `wsFeedFn`: `decodeFrame` reads the header,
   `applyMask` unmasks with key `[0x01,0x02,0x03,0x04]`, and `Ws.Reassembly`
   delivers the payload `[0x48, 0x49]` (`"HI"`) as `Output.deliverFrame`.

## The runtime execution proof — `#guard` (kernel-evaluated)

```
#guard
  runUpgrade upgradeReq maskedTextFrame
    = [Proto.Output.deliverFrame ⟨{ fin := true, opcode := .text, payload := [0x48, 0x49] }⟩]
```

`runUpgrade` is the three-step driver above over `deployConfig`. The `#guard`
forces the kernel to evaluate the whole path — real arena parse
(`h1ParseFn → Arena.Parse.parse`), the FSM upgrade transition, and the real
`wsFeedFn` (`decodeFrame → applyMask → Reassembly.step`) — on real bytes. Green
at compile time; not a correspondence beside the pipeline, an execution of it.

## The theorem — `ws_upgrade_runtime`

The composition the goal names: the **FSM upgrade transition** composed with the
**reassembly seam**. For any config whose WebSocket lane is the real engine
(`cfg.wsFeed = Ws.wsFeedFn` — `deployConfig` by `deploy_uses_real_ws`), from a
`.plainH1` connection with an unblocked send path:

1. `Proto.step … (UpEvent.wsUpgrade wsFreshCodec)` steps to
   `.active { c with proto := .plainWs wsFreshCodec }` — the FSM has entered the
   WebSocket path on the supplied codec.
2. Feeding **the literal successor state of (1)** a `bytesReceived frame` whose
   bytes decode to a fragmented WebSocket message (initial data frame `fin=false`,
   a run of continuation fragments, a final `fin` continuation) emits exactly one
   output: a `deliverFrame` whose payload is the in-order concatenation
   `initial ++ mids.flatten ++ final`. The reassembly is the real `Ws.Reassembly`
   engine, via `Reactor.Ws.feedFrames_fragmented`, reached through
   `cfg.wsFeed = wsFeedFn`.

The two `Proto.step`s are **chained** (conjunct 2's inner state is
`(step … wsUpgrade).1`), so the statement is the connection's genuine runtime
evolution: upgrade, then a real frame decoded on the `.plainWs` successor — not a
re-derivation of an isolated lemma.

## Verification

```
lake build WsDeployLane          # builds Reactor.WsDeploy; the #guard evaluates green
#print axioms …ws_upgrade_runtime # ⇒ [propext]
```

Zero `sorry`, zero `native_decide`; the sole axiom is `propext` (within
`{propext, Quot.sound, Classical.choice}`). Registered as the single-root lib
`WsDeployLane` in `lakefile.toml`.

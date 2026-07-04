# WS-CODEC — the real `Ws` library wired into the FSM WebSocket path

`Reactor/Ws.lean` closes the WebSocket codec gap: `Proto.Config`
carries `wsFeed : WsCodec → Bytes → WsOut` and `wsEncode : WsFrame → Bytes` as
abstract fields, and `Reactor.Config.demoConfig` stubs both to inert totals
(empty decode, empty encode). Every FSM theorem held "for all codecs," but no
*real* WebSocket decoder — unmask + fragmentation reassembly — was ever plugged
in, so nothing proved that a fragmented message reaches the `deliverFrame`
outputs the machine emits. This file wires the real `Ws` library in and proves
the seam, **without touching `Reactor/Config.lean`**: a config transformer
`wireWs` overrides exactly the two WebSocket fields.

## Codec-state types

The codec-state types carry real library state, not a `{ id : Nat }` stub:

- `Proto.WsCodec = { recvBuf : Bytes, reasm : Ws.Reassembly.State }` — the
  undecoded partial-frame buffer plus the real reassembly state.
- `Proto.WsFrame = { frame : Ws.Frame }` — the real decoded frame.

So real library state rides through the fields.

## What the real `Ws` library supplies vs. what the adapter builds

The library proves the *pieces* but ships no byte-level frame cutter, so the
adapter builds that cutter and drives it straight into the proven pieces:

| concern | real `Ws` component used |
|---|---|
| payload length ladder (7-bit / 16-bit / 64-bit) | `Ws.decodeLenField`, `Ws.encodeLenField` (canonical, decode-inverts-encode) |
| unmasking (§5.3 rotating XOR) | `Ws.applyMask` (involution proven) |
| opcode classification (§5.2) | `Ws.Opcode.ofNat` (total) |
| fragmentation FSM (§5.4) | `Ws.Reassembly.step` + `runAbsorb` + `step_continuation_final` |

Adapter surface (all in `Reactor/Ws.lean`):

- `decodeFrame : Bytes → Option (Ws.Frame × Bytes)` — one RFC 6455 §5.2 frame off
  the head: FIN/opcode from byte 0, mask bit + length from byte 1, extended
  length via `decodeLenField`, payload unmasked via `applyMask`. `none` on a
  partial header or short payload (buffered for the next feed).
- `decodeAll : Bytes → List Ws.Frame × Bytes` — cut every complete frame; second
  component is the partial-frame leftover.
- `feedFrames : State → List Frame → State × List WsFrame` — fold
  `Ws.Reassembly.step`, threading the state that lives in `WsCodec.reasm`,
  collecting delivered frames (`message`/`control`; `absorbed`/`error` deliver
  nothing).
- `wsFeedFn` / `wsEncodeFn` — the installed fields. `wsFeedFn` is *defined* as
  `decodeAll` then `feedFrames`, so the FSM's reassembly is literally the real
  library's `step`.
- `wireWs (cfg) := { cfg with wsFeed := wsFeedFn, wsEncode := wsEncodeFn }`.

## The seam

`ws_reassembly_seam` — the headline. For any base `cfg`, with `cfg' := wireWs
cfg`: feed a byte stream into `cfg'.wsFeed` on an **idle** codec whose decode is
a fragmented message (an initial `text`/`binary` frame with `fin = false`, a run
of continuation frames, and a final `fin` continuation). Then `cfg'.wsFeed`
delivers **exactly one** frame — the reassembled message, whose payload is the
in-order concatenation `initial ++ mids.flatten ++ final` — and carries the
reassembly state back to `idle`. The reassembly is the real
`Ws.Reassembly` engine: `wsFeedFn_frames` / `wsFeedFn_reasm` (both `rfl`) tie the
wired field to `feedFrames`, and `feedFrames_fragmented` is built on the
library's own `runAbsorb` / `step_continuation_final`.

Supporting the composition:

- `feedFrames_append` — feeding two batches (two `wsFeed` calls, state persisted
  in `WsCodec.reasm` between them) equals feeding their concatenation: the
  engine is state-threaded, not reset per feed. This is the **across-feeds**
  guarantee — a fragment left mid-assembly on one `bytesReceived` completes on
  the next.
- `feedFrames_control_transparent` — a control frame interleaved between
  fragments leaves the reassembly-in-progress state exactly where the run left
  it and is delivered as-is (control frames interleave transparently, §5.4/§5.5;
  rests on `Ws.Reassembly.step_control_state` / `step_control_output`).
- `feedFrames_fragmented` — the pure fragment-concat property at the frame level.

`wsBytes_seam` — one layer up, the anti-island crown: the real FSM helper
`Proto.wsBytes`, driven by the `wireWs`-wired config over the same fragmented
byte feed, emits exactly one output — `Proto.Output.deliverFrame` carrying the
reassembled payload — and lands on the `plainWs` successor. Real config field →
real FSM helper → the payload the machine delivers. (`fragmented_no_close`
discharges `closeReceived = false`, keeping the FSM on the WebSocket path rather
than draining.)

## Concrete byte grounding

Two `example`s check the byte path in the kernel (`rfl`), not just the
frame-level algebra:

- A two-frame fragmented text message `"Hi"` — `[0x01,0x01,0x48]` then
  `[0x80,0x01,0x69]` — fed to `wsFeedFn` on a fresh codec reduces to the
  delivered message `"Hi"`, codec back to idle, no leftover.
- A masked client→server frame `[0x81,0x82,0x01,0x02,0x03,0x04,0x49,0x4B]`
  decodes through `Ws.applyMask` to the unmasked payload `[0x48,0x49]` (`"HI"`).

## Build / axioms

`lake build Reactor` green (aggregate lib, `Reactor.Ws` included). Zero
`sorry`. Every seam theorem's `#print axioms` is `[propext]` — inside the
allowed `{propext, Quot.sound, Classical.choice}` subset.

## Notes

- The implementation lives in `Reactor/Ws.lean`, imported by the `Reactor.lean`
  aggregate. `Reactor/Config.lean` and `Proto/*` are unchanged — `wireWs`
  overrides only the two WebSocket fields.
- `wireWs` is a transformer, not a new config: a caller writes `wireWs
  demoConfig` to obtain a config whose WebSocket path is the real engine while
  every other protocol (HTTP/1, TLS, HTTP/2, SOCKS) is inherited unchanged.
- Out of scope (matching the `Ws` library): negotiated extensions and
  permessage-deflate (RFC 7692); the RSV bits are validated-zero at decode by
  the library's `Frame` model, not retained.

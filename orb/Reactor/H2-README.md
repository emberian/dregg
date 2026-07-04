# H2 codec — the connection-engine state requirement

Wiring the real H2 engine (framing + HPACK + per-stream FSM + Mux) into the FSM
codec fields `Config.h2Feed` / `Config.h2Send`, with a seam theorem
`h2_frame_seam` composing the real H2 HEADERS decode with FSM stream handling,
requires `Proto.H2Conn` to carry a real H2 engine-state record — exactly as
`TlsConn` carries `Tls.St` and `WsCodec` carries `Ws.Reassembly.State`. A
bare-handle `H2Conn = { id : Nat }` is not enough. `Reactor/H2-FIX-README.md`
documents the reshape that satisfies this and the engine wired against it.

## Why a bare handle is insufficient

The H2 library exposes the pieces — `H2.Frame` / `H2.FrameHeader` framing,
`H2.Hpack.*` (incl. `Decoded` / `FieldLine` / dynamic table),
`H2.Stream.StreamState` / `H2.Stream.Event`, `H2.FlowControl.Window`. The real
H2 decode is **stateful across feeds**: the framer buffers **partial frames**
between feeds and the per-stream FSM advances across frames (and an HPACK
**dynamic table** would mutate per HEADERS block). With `H2Conn = { id : Nat }`
there is nowhere to persist any of this between feeds, so an adapter would be
forced stateless — dropping every partial frame and the per-stream state.

The seam theorem's core claim — the `Request` carries the HPACK-decoded head,
Wf-preserved via H2/Arena, composing real decode with FSM stream handling —
cannot be stated over such a stateless adapter without misrepresenting the
threaded state. It would describe a degenerate island rather than the real
engine.

## The reshape

`Proto.H2Conn` carries a real H2 connection-engine state (the partial-frame
receive buffer and the per-stream `H2.Stream.StreamState` table), replacing the
bare `{ id : Nat }` handle whose anonymous constructor `⟨0⟩` pinned the arity to
exactly one `Nat` field. `Reactor.Config.demoConfig` builds it via `h2Init`.

`Reactor/H2.lean` provides the real-frame-decode → HPACK-into-Arena →
stream-event adapter for `h2Feed`, a framer adapter for `h2Send`, and the
`h2_frame_seam` theorem composing the real H2 HEADERS decode with FSM stream
handling. `Reactor.lean` imports `Reactor.H2`. See `Reactor/H2-FIX-README.md`
for the full structure, seam theorems, and evidence.

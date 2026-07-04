# H2 — the real H2 engine, wired into the running reactor

The real H2 engine (framing + HPACK + per-stream FSM) drives the FSM codec
fields `Config.h2Feed` / `Config.h2Send`. Carrying real engine state requires
`Proto.H2Conn` to hold more than a bare `{ id : Nat }` handle: the anonymous
constructor `h2Init := ⟨0⟩` would force exactly one `Nat` field, so `H2Conn`
carries the framing state described below. (See `Reactor/H2-README.md` for the
design requirement this satisfies.)

## Structure

### `Proto/Basic.lean` — `H2Conn` reshaped (opaque thread, like `TlsConn`)

```lean
structure H2Conn where
  recvBuf : Bytes := []                              -- undecoded partial frame
  streams : List (Nat × H2.Stream.StreamState) := [] -- per-stream FSM table
deriving Repr, DecidableEq
```

`H2Conn` carries the real framing-engine state: the partial-frame byte buffer
the framer accumulates across feeds, plus the per-stream `H2.Stream.StreamState`
table (RFC 9113 §5.1). Both components carry `DecidableEq` (`Bytes` and
`StreamState` do), so `H2Conn` keeps `Repr, DecidableEq` — nothing downstream
loses an instance. The FSM threads it opaquely: only the H2-lane `Config`
functions inspect it. `Proto/Basic.lean` imports `H2.Stream` for it. `H2Conn`
appears only in `ProtoState.plainH2/tlsH2` and the three `Config` fields, all
opaque, so `Proto.Step` and `Proto.Theorems` are unaffected.

### `Reactor/H2.lean` (new) — the real engine + the seam

The concrete `Config` realizations that drive the reshaped state:

- `framePump` — decodes as many whole frames as the buffer holds with the **real
  frame decoder** `H2.decode` (from `H2/Frame.lean`), advances the per-stream
  FSM via `H2.Stream.stepState`, and emits `Proto.H2Event`s in wire order. Fuel
  is `buf.length + 1` (each completed frame consumes ≥ 9 octets, so it always
  drains).
- `h2FeedFn : H2Conn → Bytes → H2Conn × List H2Event` (`Config.h2Feed`): appends
  plaintext to `recvBuf`, pumps frames. On a HEADERS frame it runs the **real
  HPACK decode into a fresh arena** (`H2.Hpack.decodeHeaderBlock`) and resolves
  the decoded head — the `:method`/`:path` pseudo-headers and the regular fields
  — back to bytes (`Store.resolve`) into a `Proto.Request` via `requestOfDecoded`.
- `h2SendFn : … ` (`Config.h2Send`): frames response bytes as a real DATA frame
  (`encodeDataFrame`) and advances the stream FSM by `sendData`.
- `h2InitVal : H2Conn := {}` (`Config.h2Init`).

### `Reactor/Config.lean` — the three fields, pointed at the real engine

```lean
h2Init := Reactor.H2.h2InitVal
h2Feed := Reactor.H2.h2FeedFn
h2Send := Reactor.H2.h2SendFn
```

`Reactor/Config.lean` imports `Reactor.H2` for these. `demoConfig` is the config
the running reactor uses (`Reactor.Serve`, `Reactor.Contract`), so the real
engine is on the reactor path — **not an island**. `Reactor.lean` imports
`Reactor.H2`.

## The seam theorem — `h2_frame_seam` (and `h2_seam_reactor`)

Composes the real H2 decode with the FSM's `plainH2`/`tlsH2` handling. Given a
config whose `h2Feed` is `h2FeedFn` (`demoConfig` qualifies, by `rfl`), a
well-formed HEADERS frame that fills `bs` whose HPACK payload decodes to `d`:

```lean
theorem h2_frame_seam (hcfg : cfg.h2Feed = h2FeedFn) … :
    (Proto.onBytes cfg (.plainH2 h2InitVal []) bs).outs
        = [Output.dispatch (requestOfDecoded d)]
      ∧ (Proto.onBytes cfg (.plainH2 h2InitVal []) bs).closeNow = false
      ∧ d.store.Wf
```

The `Request` carries the HPACK-decoded head (`requestOfDecoded d`, the single
resolution point) and the HPACK store is well-formed (`d.store.Wf`, discharged
by `H2.Hpack.decodeHeaderBlock_wf` from the empty store's `Wf`) — Wf-preserved.

`h2_seam_reactor` carries this all the way through the **actual transition
function**: from a connection parked in `plainH2` with the fresh engine and an
unblocked send path,

```lean
    (Proto.step cfg (.active c) (.bytesReceived bs)).2
      = [Output.dispatch (requestOfDecoded d)]
```

i.e. `Proto.step demoConfig` on a `bytesReceived` input emits exactly the
dispatch of the HPACK-decoded request.

## Evidence

- `lake build Reactor.H2`, `Reactor.Config`, `Reactor.Serve`, `Reactor.App`,
  `Proto.Theorems`: green. Zero `sorry`.
- `#print axioms h2_frame_seam` / `h2_seam_reactor` / `h2FeedFn_singleHeaders` /
  `Reactor.Config.demoConfig` ⊆ `{propext, Classical.choice, Quot.sound}`.
- Runtime, on the real wire vector
  `00 00 02 | 01 | 05 | 00 00 00 01 | 82 84` (HEADERS, stream 1,
  END_STREAM+END_HEADERS, HPACK `:method GET`/`:path /`):
  - `H2.decode … = .complete (.headers 1 true true [130,132]) 11`.
  - `(Proto.step demoConfig (.active ⟨plainH2 h2InitVal [], …⟩) (.bytesReceived …)).2`
    `= [Output.dispatch { method := "GET", target := "/", version := "HTTP/2",
    headers := [] }]` — the real decode → HPACK → resolve → dispatch flows
    through the running `step`.

## Limitations

- HPACK dynamic table (the H2 lib's explicit stub); each header block decodes
  into a fresh arena — no cross-block table state.
- Flow control on the send path (`h2SendFn` assumes an open window; the model is
  in `H2/FlowControl.lean`, not yet threaded).
- `Config.h2Send`'s DATA encoder is unproven-round-trip (encode only); the seam
  is the receive path (frame decode → HPACK → dispatch).

# PROTO-CODEC — the codec-state interface

The FSM codec-state types in `Proto/Basic.lean` carry real library state. A bare
`{id : Nat}` handle carries no real handshake / framing / reassembly state, so a
codec function wired into `Proto.Config` (`hsFeed`, `tlsRecv`, `tlsSend`,
`h2Feed`, `h2Send`, `wsFeed`, `wsEncode`) could not recover its state from such a
handle — the same lossy trap `Proto.Request` avoids by carrying real head bytes.
The types are shaped so real library state rides through.

The FSM and its theorems thread these types **opaquely** (no field access, no
fresh construction inside `Proto/Step.lean` or `Proto/Theorems.lean`; the only
inspecting functions are the abstract `Config` fields). So carrying real state
is invisible to every `step` theorem — they still hold for all codec behaviors.

## What each codec-state type now carries

| type | carries | representation |
|------|---------|----------------|
| `Proto.TlsConn` | `st : Tls.St` — the real TLS lifecycle record (`Phase` = handshake/record state, incl. the `HsConn`/`RecConn` and their ciphertext buffers, plus the ghost consumed-set). | type-carrying |
| `Proto.WsCodec` | `recvBuf : Bytes` (undecoded partial-frame bytes) + `reasm : Ws.Reassembly.State` (idle / assembling a fragmented message). | type-carrying |
| `Proto.WsFrame` | `frame : Ws.Frame` — the real decoded frame (fin / opcode / payload). | type-carrying |
| `Proto.H2Conn` | `{ id : Nat }` — stub. | stub (see below) |

`Proto/Basic.lean` now `import`s `Tls.Basic` and `Ws.Reassembly` (which pulls in
`Ws.Frame`, `Ws.Basic`). Verified no import cycle: `Tls/*`, `Ws/*`, `H2/*` do
not import `Proto`.

### Deriving impact
- `TlsConn` **drops `DecidableEq`** (kept `Repr`): `Tls.St` derives `Repr` only.
  Nothing in the FSM, `step`, the theorems, or `Reactor/*` needs `DecidableEq`
  on `TlsConn` (swept — no equality/`BEq`/`decide` on a codec-state value).
- `WsCodec` keeps `Repr, DecidableEq` (`Ws.Reassembly.State` derives both).
- `WsFrame` keeps `Repr, DecidableEq` (`Ws.Frame` derives both) — this is what
  keeps `Proto.Output` (which carries a `WsFrame` in `deliverFrame`) deriving
  `DecidableEq`.

## Instantiating the real libraries in a concrete `Proto.Config`

When wiring the real libraries into a concrete `Proto.Config` (the future
sibling of `Reactor.Config.demoConfig`, which today stubs these fields to
inert/refusing totals):

- **TLS.** `hsFeed tc bytes` → run `Tls` on `tc.st`, adapt the `Tls`
  handshake outcome into `Proto.HsOut`, wrapping the advanced `Tls.St` back as
  `⟨st'⟩ : TlsConn`. Likewise `tlsRecv`/`tlsSend` drive the record layer on
  `tc.st`. Fresh handshake connection = `⟨Tls.init cfgTls⟩`.
- **WebSocket.** `wsFeed codec bytes` → append to `codec.recvBuf`, cut
  complete frames (`Ws.Length`/`Ws.Frame`), feed each through
  `Ws.Reassembly.step` starting from `codec.reasm`, and return
  `{ codec := ⟨leftover, reasm'⟩, frames := decoded.map (⟨·⟩), closeReceived }`.
  `wsEncode ⟨f⟩` → `Ws` frame encoder on `f`. Fresh codec = `⟨[], .idle⟩` (the
  field defaults, so `({} : WsCodec)` works too).

## H2 — the remaining stub

`H2Conn` remains the `{ id : Nat }` stub for two independent reasons:

1. **No H2 engine-state type to carry.** The `H2` library exposes framing,
   HPACK, and per-stream pieces (`H2.Stream.StreamState`, `H2.Hpack.*`) but no
   single connection-engine record analogous to `Tls.St` /
   `Ws.Reassembly.State`. There is nothing to point the field at.

2. **`h2Init := ⟨0⟩` pins the arity.** `Reactor/Config.lean:114` constructs the
   engine via the anonymous constructor `⟨0⟩`. The anonymous constructor
   requires exactly the number of *explicit* fields, and a defaulted extra field
   still counts as explicit — so **any** added field (even `id : Nat := 0; st …`)
   makes `⟨0⟩` ill-typed. Widening the type requires changing `Reactor/Config.lean`
   in lockstep.

**To carry real H2 state:** add an H2 connection-engine state type to the
`H2` library (dynamic HPACK table + partial-frame `recvBuf` + per-stream table),
then in `Reactor/Config.lean` change `h2Init := ⟨0⟩` to construct that engine
(e.g. `h2Init := H2.Conn.init` or `⟨…⟩` with the real fields). Once that one
line is free, reshape `H2Conn` to `{ st : H2.Conn }` exactly as `TlsConn` is
shaped. Until then `H2Conn` stays a stub and the framing/window/HPACK state
threads through inertly.

## Build status

`lake build Proto` green; whole-tree `lake build` green (only `unusedVariables`
linter warnings in `Dns/`, `Ct/`). `#print axioms Proto.mkTls_wf` → depends on no
axioms.

# Reactor.Tls — wiring the real TLS engine into the connection FSM

## What was an island

The connection FSM (`Proto`) takes its TLS record/handshake behaviour as three
abstract `Config` fields:

- `hsFeed  : TlsConn → Bytes → HsOut` — drive the handshake
- `tlsRecv : TlsConn → Bytes → Option (TlsConn × Nat × Bytes)` — AEAD-open (decrypt)
- `tlsSend : TlsConn → Bytes → TlsConn × Bytes` — AEAD-seal (encrypt)

`Reactor.Config.demoConfig` stubbed all three to inert/refusing totals
(`hsFeed := fun _ _ => .fail`, `tlsRecv := fun _ _ => none`,
`tlsSend := fun tc _ => (tc, [])`). Every FSM theorem held "for all TLS codecs,"
but no *real* record layer was ever plugged in — the same island the arena
parser (`Reactor.Config`) and body reader (`Reactor.Body`) were pulled off of.

The proto-codec seed (`PROTO-CODEC-SEED-README.md`) reshaped `Proto.TlsConn`
from a `{id : Nat}` stub into a record carrying the real lifecycle value
`st : Tls.St`, so the live TLS state now rides through the FSM's opaque handle.
This file (`Reactor/Tls.lean`, namespace `Reactor.TlsWire`) drives the *real*
`Tls` state machine through that handle.

## The wiring

Three adapters drive `Tls.step` and translate between the FSM's vocabulary and
the TLS machine's `Tls.Output`s:

- `hsFeedReal tcfg tc buf` — runs `Tls.step tcfg tc.st (.bytesReceived buf)` and
  reads the successor `Tls.Phase` back into `Proto.HsOut`: `accum`/`handshaking`
  → `.more` (with the flight to send); `estabUser` → `.done` (`ktls := false`);
  `offloadAttach` → `.done` (`ktls := true`); `closed` → `.fail`. Handshake
  flights go out via `sendBytes`, drained 0.5-RTT plaintext via `earlyBytes`.
- `tlsRecvReal tcfg tc buf` — runs the same step; a transition into the terminal
  `closed` phase (record-layer failure: bad MAC / malformed record) becomes the
  FSM's `none` (which closes the connection). Otherwise returns the successor
  connection and the decrypted plaintext (`plainBytes` of the step's outputs).
- `tlsSendReal tcfg tc plain` — runs `Tls.step tcfg tc.st (.appData plain)`; the
  sealed record surfaces as a `.send` output, collected into the FSM's wire
  bytes via `sendBytes`.

Every adapter reports `consumed := buf.length`. The `Tls` machine owns
partial-record buffering internally (inside its `Phase`), so the FSM's external
ciphertext accumulation (`tlsBuf`) stays empty — no double buffering.

`wireTls : Tls.Config → Proto.Config → Proto.Config` installs the three adapters
into a base config, leaving every other field untouched. `demoConfig` is **not**
edited (task constraint). `wiredDemoConfig := wireTls demoTlsCfg demoConfig` is
the concrete reactor config with the real TLS engine plugged over the
arena-backed HTTP/1.1 lane; `demoTlsCfg` is an inert-but-total crypto boundary
(the seam quantifies over *all* `Tls.Config`, so the crypto behaviour behind
these fields is irrelevant to the lifecycle property).

No-drift field identities (`rfl`): `wireTls_hsFeed`, `wireTls_tlsRecv`,
`wireTls_tlsSend`, `wiredDemoConfig_tlsSend`.

## The seam theorem

**`tls_no_plaintext_seam`** ties `Tls.no_plain_after_close` to the FSM wiring:

```
theorem tls_no_plaintext_seam (tcfg : Tls.Config) (tc : TlsConn)
    (h : tc.st.phase.closingOrClosed = true) (is : List Tls.Input) :
    ∀ e ∈ (Tls.run tcfg tc.st is).2, plainBytes e.out = []
```

Once the TLS record layer underlying a `TlsConn` is torn down (its `Tls.Phase`
is `closing` or `closed`), **no** input sequence the FSM can drive through the
adapters ever surfaces application plaintext — the plaintext content
(`plainBytes`) of every step's output along the run is `[]`. The adapters all
drive `Tls.step tcfg tc.st ·`, so a run of FSM receives is a `Tls.run`, and the
trace-form security theorem of the TLS machine
(`Tls.no_plain_after_close` — the consume-and-vanish / no-plaintext-after-close
discipline) transfers verbatim.

### Supporting / composed lemmas

- `step_plainBytes_nil_after_close` — the core: after teardown, `plainBytes` of
  any single `Tls.step` output is `[]` (directly from
  `Tls.no_plain_in_close_step`, via `plainOf_none_of_no_plain` +
  `filterMap_plainOf_nil`).
- `tlsRecv_plain_nil_after_close` — the plaintext the record codec hands *back
  into the FSM* on a receive is `[]` once torn down, so an FSM
  `runH1`/`wsBytes`/relay-forward sees no new application plaintext.
- `tlsTunnel_no_forward_after_close` — composed at the FSM `onBytes`: a
  received-bytes step on a TLS CONNECT tunnel (`.tlsTunnel`) whose record layer
  is gone either closes the connection (`closeNow = true`) or forwards
  **nothing** upstream (`outs = []`). This is the wiring composed with
  `tlsRecv_plain_nil_after_close` at the running FSM level.
- `tlsSend_absorbing` / `tlsRecv_absorbing` — the adapters preserve teardown
  (via `Tls.close_absorbing`): once the record layer is torn down the FSM can
  never revive it.

## Build / axioms

- `lake build Reactor.Tls` — green, zero `sorry`.
- `#print axioms` on the seam theorems: `{propext, Quot.sound}` (a subset of the
  permitted `{propext, Quot.sound, Classical.choice}`); `tlsSend_absorbing`
  depends only on `propext`.
- The full `Reactor` target currently fails only on sibling in-progress files
  (`Reactor.Socks`, `Reactor.Ws`) owned by other agents; `Reactor.Tls` and its
  dependencies are green. `Reactor.lean` imports `Reactor.Tls`.

# H2C-REACHABLE — the real HTTP/2 engine now EXECUTES at runtime

**File:** `Reactor/H2Ingress.lean` · **Status:** `lake build Reactor` green, zero
sorries, axioms `{propext, Classical.choice, Quot.sound}`.

## Prior state

Before this file, the H2 engine was in a half-state: *installed but runtime-dead*:

- `deployConfig.h2Feed` **is** the real engine — `Reactor.H2.h2FeedFn`: real frame
  decode (`H2.decode`), real HPACK-into-arena decode (`decodeHeaderBlock`), the
  per-stream FSM. Proven by `Reactor.Deploy.deploy_h2_real`.
- `Reactor.H2.h2_seam_reactor` proves that engine, from a `.plainH2` connection,
  dispatches the HPACK-decoded request.
- **But** the deployed orb's `main` only ever drives a **plainH1** connection
  (`Proto.Conn.mkPlain`). The `.plainH2` state was never entered on the running
  binary, so the H2 engine never executed. "Installed in the config" is not
  "executed on an input."

## What this file adds

An **h2c prior-knowledge** ingress (RFC 9113 §3.3) — no TLS, no crypto. A
connection that *starts* parked in `.plainH2`, so a real HTTP/2 client preface +
HEADERS frame runs straight through the real `h2FeedFn`.

- **`mkH2c : Proto.Conn`** — a fresh h2c connection: `proto := .plainH2 h2InitVal []`
  (fresh real engine: empty frame buffer, empty stream table), unblocked, receive
  armed, header deadline armed. The `.plainH2` sibling of `Conn.mkPlain`. The
  An `h2` listener exe can bind to this initial connection.

- **`h2cHeadersFrame : Bytes`** — a concrete on-wire h2c HEADERS frame:
  `00 00 02 | 01 | 05 | 00 00 00 01 | 82 84` — stream 1,
  `END_STREAM|END_HEADERS`, HPACK payload `[0x82, 0x84]` = indexed static 2
  (`:method: GET`) + indexed static 4 (`:path: /`).

- **The `#guard` (runtime execution proof, kernel-evaluated).** It drives
  `Reactor.step deployConfig` from `mkH2c` on `h2cHeadersFrame` and checks the
  dispatched request is `GET` / `/`. This forces evaluation of the whole real
  path:

  ```
  Reactor.step → Proto.step → onBytes(.plainH2) → runH2 → h2FeedFn
    → framePump → H2.decode → decodeHeaderBlock → Store.resolve
  ```

  The real functions run on a real input. (`#eval` on the same expression prints
  `("GET", "/", "HTTP/2")`; a deliberately-wrong `#guard` with `POST` fails —
  the `#guard` genuinely evaluates, it is not a no-op.)

- **`h2c_runtime_dispatch`** — the theorem. From `mkH2c`, over `deployConfig`, on
  any well-formed HEADERS frame `bs` that fills the framer buffer (`n = bs.length`)
  and whose HPACK payload decodes to `d`:

  ```
  (Reactor.step deployConfig (.active mkH2c) (.recvInto bid bs)).2
    = [ RingSubmission.dispatch (H2.requestOfDecoded d),
        RingSubmission.recycleBuffer bid ]
  ```

  The dispatch of the HPACK-decoded request (the real `h2FeedFn` executed, via
  `h2_seam_reactor` over `deployConfig`) followed by the reactor's copy-once
  buffer recycle. The equality is of `Reactor.step deployConfig`'s **own** output
  — the deployed path being driven, not a correspondence stated beside it.

## Honest scope

The **shipped orb exe still defaults to H1**: `Arena.Orb.main` runs a plainH1
connection. This file does *not* flip that default. What it establishes is that
the H2 path is now **runtime-reachable and kernel-executed** — the real engine
provably runs, on a real frame, over the deployed config — and it hands the
`mkH2c` so an `h2` listener exe can later select the `.plainH2`
initial connection. The mechanism is real and executes today; wiring an h2 exe
onto it is a separate, later step, not a re-verification of the engine.

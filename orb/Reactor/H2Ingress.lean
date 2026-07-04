import Reactor.Contract
import Reactor.H2
import Reactor.Deploy

/-!
# Reactor.H2Ingress — making the real HTTP/2 engine EXECUTE at runtime (h2c)

The H2 engine can be installed in the config yet never entered at runtime.
`deployConfig.h2Feed` IS the real engine (`Reactor.H2.h2FeedFn` — real frame
decode + HPACK arena decode + per-stream FSM, `deploy_h2_real`), and the
composition seam `h2_seam_reactor` proves it dispatches. The deployed orb `main`
drives a **plainH1** connection (`Proto.Conn.mkPlain`), so on that binary the H2
engine is *installed but never entered* — runtime-dead. "Installed in the config"
is not "executed on an input."

This file provides the **h2c prior-knowledge** ingress (RFC 9113 §3.3,
"HTTP/2 with prior knowledge"): a connection that STARTS parked in `.plainH2`,
needing no TLS and no crypto. Feeding it a real HTTP/2 HEADERS frame drives the
bytes straight through the REAL `h2FeedFn` at runtime.

* `mkH2c` — a fresh h2c `Proto.Conn`: `proto := .plainH2 h2InitVal []`, unblocked,
  header deadline armed. The `.plainH2` sibling of `Conn.mkPlain`, the initial
  connection an `h2` server exe hangs off.

* `h2cHeadersFrame` — a concrete, on-wire h2c HEADERS frame: stream 1,
  `END_STREAM|END_HEADERS`, HPACK payload `[0x82, 0x84]` (indexed static 2 =
  `:method: GET`, indexed static 4 = `:path: /`).

* The `#guard` below is the **runtime execution proof**: it drives `Reactor.step`
  over `deployConfig` on that frame, from `mkH2c`, and checks the submissions
  carry a `dispatch` of the request the real HPACK decoder produced
  (`GET` / `/`). The `#guard` forces evaluation of `Reactor.step → Proto.step →
  onBytes(.plainH2) → runH2 → h2FeedFn → framePump → H2.decode → decodeHeaderBlock
  → Store.resolve` — the real engine, run on a real input. (Same evaluation
  mechanism the `H2.Hpack` wire vectors use.)

* `h2c_runtime_dispatch` — the theorem form: from `mkH2c`, on any well-formed
  HEADERS frame that fills the buffer and whose HPACK payload decodes to `d`, the
  deployed reactor emits exactly `[dispatch (requestOfDecoded d), recycleBuffer bid]`
  — the real `h2FeedFn` executed (via `h2_seam_reactor` over `deployConfig`), then
  the reactor's copy-once buffer recycle. Not a correspondence beside the pipeline:
  the equality is of `Reactor.step deployConfig`'s own output.

The shipped orb exe still DEFAULTS to H1 (`Arena.Orb.main` runs a plainH1
connection); this file makes the H2 path **runtime-reachable and kernel-executed**,
and exposes `mkH2c` so an h2 listener exe can later select it.
-/

namespace Reactor
namespace H2Ingress

open Proto (Bytes)

/-! ## The h2c initial connection -/

/-- **`mkH2c` — a fresh h2c (prior-knowledge) connection.** Parked directly in
`.plainH2` with the fresh real H2 engine (`h2InitVal`: empty frame buffer, empty
stream table), send path unblocked, receive armed, the header-read deadline
armed. This is the `.plainH2` sibling of `Proto.Conn.mkPlain` — an `h2` listener
exe binds to it so the deployed reactor enters the real H2 engine on the very
first recv. -/
def mkH2c : Proto.Conn :=
  { proto := .plainH2 Reactor.H2.h2InitVal []
    sendBlocked := false
    pendingSend := []
    recvArmed := true
    timers := [.header] }

/-- `mkH2c` is parked in `.plainH2` with the fresh engine (the entry precondition
of `h2_seam_reactor`). -/
theorem mkH2c_proto : mkH2c.proto = .plainH2 Reactor.H2.h2InitVal [] := rfl

/-- `mkH2c`'s send path is unblocked (so the dispatch is not diverted to the park
queue by the send-block gate). -/
theorem mkH2c_unblocked : mkH2c.sendBlocked = false := rfl

/-! ## A concrete on-wire h2c HEADERS frame -/

/-- A concrete HTTP/2 HEADERS frame, h2c prior-knowledge:

```text
00 00 02   length = 2
01         type   = 0x1 (HEADERS)
05         flags  = END_STREAM(0x1) | END_HEADERS(0x4)
00 00 00 01  stream id = 1
82 84      HPACK: indexed static 2 (:method: GET), indexed static 4 (:path: /)
```

11 octets total; `H2.decode` completes consuming all 11 (`n = bs.length`), and the
2-octet HPACK payload decodes to `:method: GET`, `:path: /`. -/
def h2cHeadersFrame : Proto.Bytes :=
  [0x00, 0x00, 0x02, 0x01, 0x05, 0x00, 0x00, 0x00, 0x01, 0x82, 0x84]

/-! ## The runtime execution proof -/

/-- Extract the first `dispatch`ed request from a submission list (the reactor's
copy-once recycle rides after it). Lets the `#guard` compare the decoded request
without needing `DecidableEq` on the whole `RingSubmission` list. -/
def dispatchedReq : List RingSubmission → Option Proto.Request
  | RingSubmission.dispatch req :: _ => some req
  | _ :: rest => dispatchedReq rest
  | [] => none

/-- The request the real HPACK decoder produces from `h2cHeadersFrame`: method
`GET`, target `/`, version `HTTP/2`, no regular headers. -/
def expectedH2cReq : Proto.Request :=
  { method  := (String.toUTF8 "GET").toList
    target  := (String.toUTF8 "/").toList
    version := (String.toUTF8 "HTTP/2").toList
    headers := [] }

/-! **RUNTIME EXECUTION PROOF (`#guard`, kernel-evaluated).** Driving the DEPLOYED
reactor (`Reactor.step deployConfig`) from the h2c connection `mkH2c` on the real
HEADERS frame runs the bytes through the REAL H2 engine (`h2FeedFn` → `H2.decode`
→ `decodeHeaderBlock` → `Store.resolve`) and dispatches the HPACK-decoded request.
This evaluates the real functions on a real input — not a correspondence theorem,
an execution. -/
#guard
  dispatchedReq
      (Reactor.step Reactor.Deploy.deployConfig
        (Proto.State.active mkH2c)
        (RingEvent.recvInto 0 h2cHeadersFrame)).2
    = some expectedH2cReq

/-! ## The theorem -/

/-- **`h2c_runtime_dispatch` — the deployed H2 engine executes and dispatches.**
From the h2c connection `mkH2c` (parked in `.plainH2` with the fresh real engine),
the DEPLOYED reactor over `deployConfig`, on a well-formed HEADERS frame `bs` that
fills the framer buffer (`n = bs.length`) and whose HPACK payload decodes to `d`,
emits exactly

```text
[ dispatch (requestOfDecoded d), recycleBuffer bid ]
```

— the dispatch of the HPACK-decoded request (the REAL `h2FeedFn` executed, via
`h2_seam_reactor` over `deployConfig`, whose `h2Feed` IS `h2FeedFn` by
`deploy_h2_real`), followed by the reactor's copy-once buffer recycle. The
equality is of `Reactor.step deployConfig`'s own output, so this is the deployed
path being driven, not an island beside it. -/
theorem h2c_runtime_dispatch (bid : Nat) (bs payload : Bytes) (sid n : Nat)
    (es eh : Bool) (d : H2.Hpack.Decoded)
    (hframe : H2.decode bs Reactor.H2.h2MaxFrameSize
      = .complete (.headers sid es eh payload) n)
    (hfill : n = bs.length)
    (hhpack : H2.Hpack.decodeHeaderBlock Reactor.H2.h2Huffman Reactor.H2.h2EmptyStore payload
      = .ok d) :
    (Reactor.step Reactor.Deploy.deployConfig (Proto.State.active mkH2c)
        (RingEvent.recvInto bid bs)).2
      = [ RingSubmission.dispatch (Reactor.H2.requestOfDecoded d)
        , RingSubmission.recycleBuffer bid ] := by
  have hseam := Reactor.H2.h2_seam_reactor (cfg := Reactor.Deploy.deployConfig)
    Reactor.Deploy.deploy_h2_real.1 bs payload sid n es eh d mkH2c
    hframe hfill hhpack mkH2c_proto mkH2c_unblocked
  show ((Proto.step Reactor.Deploy.deployConfig (Proto.State.active mkH2c)
        (Proto.Input.bytesReceived bs)).2.map ofOutput
      ++ [RingSubmission.recycleBuffer bid])
    = [ RingSubmission.dispatch (Reactor.H2.requestOfDecoded d)
      , RingSubmission.recycleBuffer bid ]
  rw [hseam]
  rfl

end H2Ingress
end Reactor

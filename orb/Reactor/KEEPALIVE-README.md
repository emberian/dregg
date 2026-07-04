# Reactor.KeepAlive — pipelining / keep-alive driver + seam

## The audit finding this fixes

`serve` answered only the **first** request on a connection. The culprit was
`Reactor/Serve.lean`'s `demoResp`: it walks the submission list but returns a
single `Response` for the first `dispatch` it meets, silently dropping every
subsequent pipelined request.

The FSM was never the problem. `Proto.h1Loop` (`Proto/Step.lean`) parses requests
from the head of the receive accumulation **repeatedly**, emitting one
`Output.dispatch req` per request in order, and the reactor translates each one
faithfully (`ofOutput (.dispatch req) = .dispatch req`). The gap was purely the
reactor's response half.

## What this file adds

A reactor-level driver over the submission list:

- `respondEach : List RingSubmission → List Bytes` — walks the whole list and
  emits **one response per `dispatch`, in order** (contrast: the old first-only
  responder).
- `driveKeepAlive : List RingSubmission → Bytes` — concatenates them onto the
  wire.
- `appResponse req := serialize (ok200 (okBody req))` — reuses the proven
  serializer and `Serve.okBody`, so every response byte carries
  `serialize_framing`.

Order-preserving extractors `dispatchOuts` (over FSM `Output`) and `dispatchSubs`
(over `RingSubmission`) name the dispatched-request sequence on each side of the
translation.

## The seam theorem

`keepalive_all_dispatched`:

```
respondEach (Reactor.step cfg s (.recvInto bid data)).2
  = (dispatchOuts (Proto.step cfg s (.bytesReceived data)).2).map appResponse
```

The driver's response list is **exactly** the FSM's dispatched requests mapped to
responses, in the same order. A pipelined pair (two `Output.dispatch` in the FSM
output) yields two responses, not one. Proved by composing:

- `reactor_carries_dispatches` — the reactor step carries every FSM
  `Output.dispatch` through to a `RingSubmission.dispatch`, in order; the extra
  copy-once `recycleBuffer` submission is not a dispatch and drops out. This is
  the FSM→reactor fidelity half.
- `respondEach_eq_map` — the driver emits one response per dispatch submission.

Supporting facts:

- `keepalive_response_count` — response count equals dispatch count (nothing
  dropped, nothing answered twice).
- `respondEach_pipelined_pair` — concrete witness: `[dispatch r₁, dispatch r₂,
  recycleBuffer]` ↦ `[appResponse r₁, appResponse r₂]` by `rfl`.

## Composition with the FSM residual invariant

`keepalive_discipline` wires the driver to `Proto.residual_suffix_plainH1`. On a
plaintext HTTP/1.1 connection a recv event both:

- **(a)** answers every dispatched request in order (`keepalive_all_dispatched`),
  and
- **(b)** leaves the successor either `closed` or holding a **suffix**
  `(buf ++ data).drop k` of the whole accumulation — no unconsumed byte dropped —
  so the next recv resumes the pipeline exactly where this one stopped.

Part (b) is the FSM's residual-preservation theorem lifted through the reactor
(`Reactor.step` returns the FSM successor state unchanged). Together (a)+(b) are
the keep-alive discipline: all pipelined requests handled now, the residual
carried for the requests still arriving.

## Build / verification

- `lake build Reactor.KeepAlive` — green.
- Zero `sorry`.
- `#print axioms` for every theorem: `{propext, Quot.sound}` — a subset of the
  allowed `{propext, Quot.sound, Classical.choice}`.

Note: `lake build Reactor` (the root) currently fails inside the sibling file
`Reactor/Body.lean`, which is unrelated to this module — `Reactor.KeepAlive` does
not depend on it.

## Follow-ups

- Fold `driveKeepAlive` into `Serve.serve` so the running per-request view emits
  all pipelined responses (interleaving forwarded FSM sends with app responses in
  submission order), replacing the first-only `demoResp`. Kept separate here to
  land the seam without racing the concurrent `Serve`/`Body` edits.

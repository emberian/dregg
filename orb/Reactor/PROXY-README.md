# Reactor.Proxy — reverse-proxy handler wired onto the real LB

`Reactor/Proxy.lean` instantiates the **real** `Proxy` load-balancer into the reactor's
submission vocabulary as a reverse-proxy handler that sits *above* dispatch. It is a
wiring plus a seam theorem, not a fresh model: every selection decision is delegated to
the proven `Proxy.selectChain` algebra; the reactor only translates that verdict into
its own `RingSubmission`s.

## Where it sits

```
reactor step ──emits──▶ RingSubmission.dispatch req        (Reactor.Contract)
                              │
                    onDispatch │  (the hand-off seam)
                              ▼
              proxyHandle pool ctx req
                              │
             chooseUpstream = Proxy.selectChain            (the REAL LB)
                              │  best-tier eligible (healthy ∧ active) pool
              ┌───────────────┴───────────────┐
        some b │                               │ none
              ▼                               ▼
  [connectUpstream ⟨b.id⟩]                    []   (no upstream traffic)
              │
   (tunnel established, fd known)
              ▼
   proxyRelay fd data = [submitSendUpstream fd data]
```

`onDispatch` matches the reactor's own `RingSubmission.dispatch` and runs the handler
on the request payload, so the proxy is genuinely driven by the reactor's dispatch
hand-off (`onDispatch_runs_handler`), not standing on its own.

## The library that is driven

- `Proxy.selectChain` (`Proxy/Balance.lean`) — first-match fallback across a policy
  chain; each `Proxy.select` runs its policy (`Proxy.Wrr`, least-connections,
  `Proxy.Rendezvous`) on `tierPool`: the best (lowest-numbered) nonempty tier of the
  **eligible** (`healthy ∧ active`) subset.
- `Proxy.Backend.healthy` is the verdict snapshotted from the `Proxy.Health` hysteresis
  machine; `status` is the admin drain/down state. Both feed `Backend.eligible`, which
  `select` filters on before any policy runs.
- `chooseUpstream pool ctx := Proxy.selectChain pool.policies ctx pool.backends` — the
  reactor delegates; it does not re-implement selection.

The upstream address the reactor dials is `addrOf b = ⟨b.id⟩ : Proto.Addr`, carried by
`RingSubmission.connectUpstream` from `Reactor.Contract`.

## Seam theorem

`proxy_selects_healthy` — for any pool/ctx/request, if the real LB picks `b`
(`chooseUpstream pool ctx = some b`) then:

1. `targetedUpstream (proxyHandle pool ctx req) = some (addrOf b)` — the upstream the
   reactor targets (recovered from the emitted submissions) is exactly the selector's
   choice, forwarded unchanged;
2. `b ∈ pool.backends ∧ b.eligible = true ∧ Proxy.bestTier pool.backends = some b.tier`
   — that backend is a healthy, active pool member in the best nonempty tier. This is
   `Proxy.selectChain_eligible` transported through the reactor's submission list.

A stubbed selector fails this: conjunct 1 fails if the handler ignores the selector;
conjunct 2 fails if the selector returns an unhealthy or non-pool backend. The `demo_*`
theorems exhibit a concrete three-backend pool where backend 0 is unhealthy — the naive
"first backend" stub targets id 0 (`demoB0.eligible = false`), while the real
least-connections LB targets the healthy least-loaded id 2 (`demo_chooses_b2`).

Supporting theorems:

- `proxy_target_in_healthy_set` — the target lies in `Proxy.eligibleOf pool.backends`
  (the current healthy set); the reactor never dials a down backend.
- `proxy_no_upstream_without_choice` — **no upstream traffic before a backend is
  chosen**: with no eligible backend, `proxyHandle` emits `[]` (no connect, no send).
- `proxyHandle_no_relay` — `proxyHandle` never emits `submitSendUpstream`; relaying is a
  strictly later phase gated behind a connect-produced `fd` (`proxyRelay`), so no
  upstream *send* can precede a connect.
- `proxy_total_when_eligible` — liveness companion: a least-connections link plus any
  eligible pool backend guarantees the LB (and the handler) chooses an upstream, so a
  proxied request is never stuck when the pool has capacity.

## Status

- `lake build Reactor.Proxy` — green.
- Zero `sorry`. Axiom footprint of every theorem ⊆ `{propext, Quot.sound}` (the two
  compute-only demo lemmas depend on none).

## Integration note

This module touches **only** `Reactor/Proxy.lean`. To fold the
module into the `Reactor` library root, add one line to `Reactor.lean`:

```
import Reactor.Proxy
```

The module already builds standalone (`lake build Reactor.Proxy`); this import only
makes `lake build Reactor` compile it as part of the library glob.

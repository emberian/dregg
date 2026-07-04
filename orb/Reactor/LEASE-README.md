# A-compose: the reactor recycle against the ring LTS

`Reactor/Lease.lean` composes the copy-once reactor step (`Reactor.step`) with
the submission/completion ring's transition system (`Uring.Step`), closing the
gap left open by `Reactor.Contract`: that a recycled buffer id is one the ring
actually lent the client.

## The coupling

`Reactor.Contract.recv_recycles_exactly_once` shows a `recvInto bid` event
produces exactly one `recycleBuffer bid` submission — but that is a statement
about the reactor's output list alone. It says nothing about whether `bid` is a
buffer the ring leased.

The coupling names the missing invariant:

```
def Leased (bid : Uring.Bid) (s : Uring.St) : Prop := bid ∈ s.held
```

A `recvInto bid` event is not spontaneous: the reactor only observes a recv
completion because the client reaped a buffer-select completion carrying `bid`,
and `Uring.dispatch` on a `.buf bid` payload puts `bid` into `held`. That is the
coupling constructor, `reap_establishes_lease` / `step_reap_establishes_lease`.

## What composed (proven, zero sorries)

All theorems are `lake`-accepted; axiom footprints are a subset of
`{propext, Quot.sound, Classical.choice}` (verified via `#print axioms`).

- `reap_establishes_lease` — reaping a `.buf bid` completion establishes
  `Leased bid` on the resulting ring state. (`propext`)
- `step_reap_establishes_lease` — same, stated against a `Uring.Step.reap`
  transition. (`propext`)
- `recv_emits_recycle` — the reactor's recv step contains `recycleBuffer bid` in
  its submissions. (`propext, Quot.sound`)
- **`reactor_recycle_is_held`** — the A-compose single step: when the reactor
  emits `recycleBuffer bid` for `recvInto bid` and the coupling holds
  (`bid ∈ held`), the ring's `Uring.Step.recycle bid` move is enabled. The
  reactor only ever asks to recycle a buffer the ring lent it. (`propext,
  Quot.sound`)
- `recycleLabels` / `recv_recycle_labels` — reading the reactor's recv-step
  submissions as ring labels yields exactly `[Uring.Lbl.recycle bid]`: the
  translated FSM outputs contribute no recycle label (via
  `map_ofOutput_no_recycle`), the copy-once obligation contributes one.
  (`propext, Classical.choice, Quot.sound`)
- `reactor_recycle_trace` — that single recycle label is a one-step `Uring.Trace`
  from the leased state (the emitted request extends any ring trace by a valid
  `recycle` move). (no axioms)
- `reactor_recycle_at_most_once` — `Uring.recycle_at_most_once` transported to
  reactor-emitted recycle labels: across any ring trace from `init`, two recycles
  of the same `bid` are separated by a fresh delivery of `bid`. (`propext,
  Classical.choice, Quot.sound`)

Composed end-to-end reading: each `recvInto bid` yields exactly one recycle
request (Contract), that request is enabled against the ring precisely when
`bid` was leased (`reactor_recycle_is_held`), the request is a valid one-step
ring trace (`reactor_recycle_trace`), and the ring forbids any second recycle of
the same lease without a fresh delivery (`reactor_recycle_at_most_once`). Per
lease, the reactor's recycle happens exactly once and only against a held buffer.

## What is UNCLOSED (honest)

The **full reactor+LTS product trace induction** is not built. Specifically: that
an arbitrary stream of reactor events, interleaved with the demonic environment's
reaps / deliveries / exhaustion / overflow, assembles into a *single* valid
`Uring.Trace` from `init` whose recycle labels are exactly the reactor's emitted
ones.

What is present are the two ends of that bridge:
- the single-step embedding (`reactor_recycle_trace`: a reactor recycle request
  is a valid one-step ring trace from the leased state), and
- the trace-level guarantee (`reactor_recycle_at_most_once`: the ring admits no
  double recycle).

What is missing is the interleaving *driver* — an induction threading reactor
steps and environment steps into one product trace and showing the reactor's
`recycleBuffer` outputs land as the trace's `recycle` labels with the coupling
(`Leased`) maintained as an invariant across every step. That is the one
remaining piece for a fully trace-level product statement; it is deferred, not
claimed.

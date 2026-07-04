# OBSERVE-WIRE — Metrics, Trace and Tap on the running reactor path

`Reactor/Observe.lean` wires three observability libraries — proven in
isolation and, on their own, consulted by nothing that serves — `Metrics`,
`Trace.Correlation`, and `Tap` — onto the **running** per-request reactor path.

## The wiring

`observe` wraps the proven reactor view `Reactor.serve` — the same per-request
view the Rate, App, and Body wirings use. In one step it:

1. serves the request through `Reactor.serve` (the proven parse → FSM → reactor →
   serializer path), returning the response bytes **unchanged**;
2. bumps the **real** `Metrics` request counter by exactly one
   (`Metrics.Registry.inc reqCounter 1`);
3. offers the request bytes to the **real** `Tap.step` gate — the only path a
   request can take to the diagnostic sink;
4. records the correlation id the **real** `Trace.process` assigned.

`obsRun` threads the observation state (`ObsState` = the three real library
states bundled) over a window of requests; `respWindow` collects the served
responses.

The libraries are used as-is, by name, on the path — not re-modelled:
`Metrics.Registry.inc` / `Metrics.inc_exact`, `Trace.process` / `Trace.inject` /
`Trace.upstreamCorr`, `Tap.step` / `Tap.run` / `Tap.no_copy_when_disabled` /
`Tap.enabled_faithful`.

## Seam theorems

- **`metrics_counts_requests`** — from a cold start, the reactor's served-request
  counter after a window of `N` requests equals the **real** `Metrics` counter
  incremented `N` times (`metricsAfter inputs.length`). Composition:
  `metricsAfter_counter` accumulates `Metrics.inc_exact` to show the
  `N`-times-incremented counter reads `N`; `obsRun_metrics_counter` shows the
  reactor fold adds exactly one per served request via the same `inc_exact`. A
  wrapper that dropped or double-counted a served request would break the
  per-step exact delta and fail the equality.

- **`tap_gated_in_reactor`** (PF-6, the info-leak boundary, on the running path) —
  from a cold start (tap gate DISABLED, the default), over any window of served
  requests the diagnostic sink stays EMPTY. Because traffic never carries a
  control edge (`pktTrace_no_enable`: a request-only trace has no `.enable`), this
  is the real `Tap.no_copy_when_disabled` composed with the reactor path
  (`obsRun_tap`, which proves the reactor's tap state is exactly `Tap.run` over the
  denoted packet trace). The reactor copies a request to the sink **only** when
  the gate has been explicitly enabled.

- **`tap_enabled_copies`** (the other direction) — from a gate-enabled start, the
  sink is EXACTLY the served requests, in arrival order (no drop, no injection, no
  reorder), composing the real `Tap.enabled_faithful`. Together with
  `tap_gated_in_reactor` this pins the copy to the gate: sink non-empty ⟺ gate
  enabled.

- **`reactor_corr_propagates`** / **`observe_records_corr`** — the correlation id
  `observe` records on the running path (`corrOf`) is exactly the id the upstream
  request built by the real `Trace.inject` exposes when read back with
  `Trace.upstreamCorr`. Composes `Trace.upstream_sees_request_corr`: the upstream
  actually *sees* the id, not merely a copied projection.

## Transparency (non-interference)

`observe_transparent` and `respWindow_eq_map_serve` prove the served bytes are
exactly `Reactor.serve`'s — the observation layer is a pure side-channel that
never rewrites the response. This is the observability analogue of the tap's own
`forward_packet_id`: the observation cannot perturb the traffic it observes.

## Status

- `lake build Reactor` — green (full library).
- Zero `sorry` / `admit` / UNCLOSED in `Reactor/Observe.lean`.
- `#print axioms` for every seam theorem ⊆ `{propext, Classical.choice,
  Quot.sound}` (`reactor_corr_propagates` uses only `propext`).

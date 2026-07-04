# RATE-WIRE — the real token bucket in front of the real reactor

`Reactor/Rate.lean` (namespace `Reactor.RateGate`) wires the **real** `Rate`
token-bucket limiter into the reactor admission path, and proves the rate bound
holds over the reactor — not over a fresh standalone model.

## What was stranded

- `Rate/Bucket.lean` + `Rate/Trace.lean` prove `Rate.rate_bound_cap`: over any
  window of duration `D`, the bucket admits at most `cap + rate * D` requests.
  Proven in isolation — nothing that *serves* ever consulted the bucket.
- `Reactor/Serve.lean` proves `serve : Bytes → Bytes` drives the proven reactor
  end to end — but admits every request; no limiter.

## The wiring (anti-island)

An `Arrival` carries the client's request bytes **and** the clock reading that is
its time input (time-as-input, exactly as `Rate` requires — no ambient clock).

`admit (b : Rate.Bucket) (a : Arrival) : Rate.Bucket × Bytes` does one thing:

1. refill the **real** `Rate.refill` to `a.now`;
2. consult the **real** `Rate.tryAdmit`;
3. on admit → serve through the **proven** reactor, `Reactor.serve a.input`;
   on reject → answer with a `429` built by the **proven** serializer
   (`serialize (error4xx 429 …)`), so its framing is a theorem, not `s!`-glue.

`serveWindow` runs a whole window and returns the per-arrival response bytes in
order; `servedCount` counts the arrivals the reactor **admitted** (served, not
429'd).

## The seam

Two definitional equalities pin the gate to the real bucket:

- `admit_bucket : (admit b a).1 = Rate.stepB b (eventOf a)` — the gate does not
  fork bucket state; the next bucket is exactly the bucket's own next state.
- `served_admits : (if served b a then 1 else 0) = Rate.admits b (eventOf a)` —
  the served/rejected decision is exactly the bucket's own admit indicator.

These lift to the **count seam**:

- `servedCount_eq_countAdmits : servedCount b arrivals = Rate.countAdmits b (eventsOf arrivals)`

so the reactor's admit-count *is* the bucket's admit-count. A stubbed limiter
(one that served without consulting the bucket) would break `served_admits` and
so fail this equality — the seam is load-bearing.

## Seam theorem

```
reactor_rate_bound (b) (arrivals) (h : b.tokens ≤ b.cap) :
    servedCount b arrivals ≤ b.cap + b.rate * Rate.duration b (eventsOf arrivals)
```

`Rate.rate_bound_cap` transported through the admission wrapper by rewriting with
the count seam: **the reactor cannot serve more requests than the real token
bucket allows.**

Restatements:

- `reactor_rate_bound_init` — cold-start full bucket: `≤ cap + rate * D`.
- `run_last_le` — over arrivals whose clocks never exceed `W`, the recorded clock
  never exceeds `W`.
- `reactor_rate_bound_window` — with an explicit window ceiling `W`:
  `servedCount ≤ cap + rate * (W - last)`.
- `reactor_rate_bound_window_init` — **the headline**: from a cold start, over a
  window ending by clock `W`, the reactor serves at most `cap + rate * W`
  requests.
- `resp429_framing` — the 429 rejection is a well-formed HTTP response
  (`serialize_framing`), no hand-interpolation on the rejection path.

## Verification

- `lake build Reactor` — green (31/31).
- Zero `sorry`.
- `#print axioms` for every headline theorem: subset of `{propext, Quot.sound}`
  (not even `Classical.choice`), within the allowed set.

## Files

- `Reactor/Rate.lean` — the wiring + seam (new; imported from `Reactor.lean`).
- Reads: `Rate/Bucket.lean`, `Rate/Trace.lean`, `Reactor/Serve.lean`,
  `Reactor/Serialize.lean`, `Proto/Basic.lean`.

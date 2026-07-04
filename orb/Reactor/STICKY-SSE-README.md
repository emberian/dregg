# STICKY-SSE — session affinity and event-stream fan-out on the reactor path

Two wirings, both sitting on the reactor's `dispatch` seam — the same seam the
deployed `serve` (`Arena.Orb.main` → `Reactor.serve`) answers with a Response
and `Reactor.ProxyServe` answers with load-balancer submissions. Both are
driven by `ProxyServe.reactorSubs` (one recv completion through the proven
`Reactor.step`), with `reactorSubs_demoConfig : ProxyServe.reactorSubs
Config.demoConfig = Reactor.reactorSubs` (`rfl`) pinning the demo corollaries
to the exact submission producer behind the deployed binary's `serve`.

Both files: zero sorries; axioms ⊆ {propext, Quot.sound, Classical.choice}
(checked with `#print axioms` on every seam theorem); `lake build Reactor`
green.

## Reactor/Sticky.lean — session affinity over the proxy path

The real `Sticky` library supplies the stickiness table (`Sticky.Table`), the
routing step (`Sticky.route` — honour a live pin, re-pin a dead one from the
rendezvous winner), and the proofs (`sticky_stability`, `failover_repin`,
`sticky_minimal_disruption`). The wiring composes it with the reactor's
upstream choice:

- `upstreams pool` — the eligible list `Sticky.route` selects over is the real
  `Proxy.eligibleOf` (healthy ∧ active) subset of the `ProxyServe` pool,
  snapshotted exactly as `Sticky.Basic` specifies.
- `stickyChoose` = literally `Sticky.route` over that list. `stickyHandle`
  emits the reactor's own `connectUpstream (addrOf b)` and threads the updated
  table out. `serveStickyOn` pins the handler onto the reactor's `dispatch`
  (session key extracted by a caller-supplied `keyOf` adapter); `serveSticky`
  runs it on `ProxyServe.reactorSubs cfg input`.

**Seam: `sticky_affinity_seam`.** Two inputs the proven reactor dispatches with
the same session key target the same backend `b` that the real `Sticky.route`
chose:

1. first serve = `(t', [connectUpstream (addrOf b)])` — the table `t'` is the
   library's, not a side-channel;
2. `t' k = some b.id` (`route_pin` — what a successful route pins is the served
   backend's id, both in the live-pin and fresh-pin branches);
3. second serve with the threaded `t'` = the identical submission with the
   table untouched (`route_repeat` = `Sticky.sticky_stability` packaged for the
   composition);
4. `b` is a healthy, active member of the pool (`Sticky.chosen_mem` +
   `Proxy.mem_eligibleOf`).

**Failover: `sticky_failover_seam`.** `removePoolBackend d pool` applies the
real `Sticky.removeBackend` membership transition to the pool. Any dispatched
request whose observed assignment (`Sticky.chosen`) was `b ≠ d` (by id) still
dials exactly `b` over the shrunken pool — `Sticky.sticky_minimal_disruption`
composed through the reactor: only the departed backend's sessions can move.

**Demo (deployed config).** `Config.demoConfig` + the real
`Reactor.Proxy.demoPool`: eligible list `[demoB1, demoB2]` (backend 0 is
unhealthy — `demo_upstreams`, by the real filter). Fresh session key 7
rendezvous-pins to backend 2 (`demo_route_snd`, `demo_route_pin`, checked by
`decide`); `demo_sticky_affinity` shows both serves dial backend 2 with the pin
recorded and the table stable; `demo_failover_isolation` removes the unrelated
backend 1 and the pinned session is undisturbed.

Falsifiability: a handler that re-selected per request (ignoring the table)
breaks conjunct 3 whenever the stateless winner differs; one that pinned
anything but the routed backend breaks conjunct 2; a selector off the eligible
list breaks conjunct 4.

## Reactor/Sse.lean — event-stream fan-out

The real `Sse` library owns the broadcaster: `Sse.published` (the monotone
sequence-tagged stream) and `Sse.delivered` (per-subscriber log) over a trace
of `subscribe`/`unsubscribe`/`publish` ops, with the fan-out accounting proven
in `Sse.Broadcast`. The wiring:

- `subscribeOnDispatch` — a connection subscribes through the reactor's own
  `dispatch`: the request that flowed through the proven `Reactor.step` opens
  the subscription; no dispatch ⇒ no subscription.
- `sseSession` — the broadcaster trace of one reactor-driven session:
  reactor-produced subscribe, then the broadcast ops.
- `fanOut`/`sseServe` — one `submitSend (eventBytes e)` per entry of the real
  `Sse.delivered` log, in log order. `eventBytes` is the real
  `Sse.encodeFrame` (whose parse round-trip is `Sse.parseFrame_encodeFrame`),
  lines closed with `LF`.

**Seam: `sse_fanout_seam`.** The reactor's deliveries to a subscriber are
exactly the image of the real broadcaster's log, and that log is an
order-preserving subsequence of the published stream with strictly increasing
sequence tags (`delivered_sublist_published`, `delivered_pairwise`): only real
events, in publish order, never duplicated. The last conjunct reads the bytes
back out with the deployed path's own `Reactor.sendsOf`.

**Completeness: `sse_no_gap` / `sse_no_gap_bytes`.** Once the reactor's
dispatch opens the subscription and the client is never unsubscribed, the
delivery IS the published stream — every event, in order, tags `0, 1, …`
intact (`Sse.delivered_split` composed through the reactor).

**Silence: `sse_no_dispatch_silent`.** No dispatch and no re-subscribe ⇒ the
reactor sends nothing (`Sse.deliveredAux_silent`) — no invented deliveries.

**Demo (deployed config).** `demo_sse_fanout`: at `Config.demoConfig`, a
reactor-dispatched subscribe followed by `publish (data: "1")`, `publish
(data: "2")` delivers exactly the two encoded frames, in order.

Falsifiability: dropping, reordering, or duplicating an event breaks
`sse_no_gap`/the sublist conjunct; delivering to a never-subscribed connection
breaks silence.

## Files

- `Reactor/Sticky.lean` (new, owned) — affinity wiring + seams + demos.
- `Reactor/Sse.lean` (new, owned) — fan-out wiring + seams + demos.
- `Reactor.lean` — two imports appended.

## Honest scope

- The session-key adapter (`keyOf : Request → Nat`) is a parameter (cookie /
  header extraction is a parsing concern of a later slice); the demo fixes one
  session. The general theorems quantify over every adapter.
- `serveSticky` is per-request with the table threaded by the caller, matching
  the reactor's one-completion step granularity; a multi-request driver loop is
  the same fold the KeepAlive lane owns.
- The Sse broadcaster trace (`ops`) is the model of the publish side; the
  subscribe side is reactor-driven. Wiring publishes to a second connection's
  `dispatch` (a POST-to-publish route) is a natural successor slice.
- `Last-Event-ID` resumption (`Sse.Resume`) is not wired here.

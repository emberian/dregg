# UDP-FALLBACK — wiring report

Two lanes, both `lake build Reactor` green, zero sorries, axioms within
`{propext, Quot.sound, Classical.choice}` on every seam theorem.

## Lane 1: Reactor/Udp.lean — the real `Udp` session relay

**What was stranded.** `Udp/` proves a full L4 datagram relay — key-unique,
binding-injective, allocator-dominated session table (`Relay.Inv`), session
affinity (`binding_stable_onClient`, `affinity_run`), payload integrity,
reply correlation (`reply_routes_to_owner`), deadline-honored eviction — but
none of its `Udp.Out` decisions ever became a reactor submission.

**The wiring.**

- `payloadOf` — wire bytes viewed as the relay's opaque payload.
- `subOfOut` — the faithful translation into `Reactor.RingSubmission` (the
  same stream `Reactor.step` emits into): `forward _ u _` →
  `submitSendUpstream u data` (out on the per-session upstream binding the
  REAL relay chose), `deliver _ _` → `submitSend data` (addressee named by
  the library's `Out.deliver`, `onReply_names_owner`), `drop` → nothing. The
  submission carries the original wire bytes verbatim; the routing decision
  is read from the library's output, never re-made.
- `onDatagram` / `onReply` — one step of the REAL `Udp.onClient` /
  `Udp.onUpstream`, translated. The next relay state is the library's own.
- `OrbState` / `orbStep` / `orbRun` — the composition with the reactor: the
  connection FSM and the relay side by side; a ring event runs the REAL
  `Reactor.step` (at `Reactor.Config.demoConfig`, exactly the step the
  deployed `serve`/`main` runs — `orb_ring_is_reactor` is `rfl`), a
  datagram/reply/sweep event runs the real relay; both lanes emit into the
  one shared submission stream.

**Seam: `udp_session_affinity_seam`** (over `orbStep` at the deployed
`demoConfig`). If the real session table holds binding `u` for client `a`
(`Udp.bindingOf … = some u`):

1. a datagram from `a` is submitted as exactly
   `[submitSendUpstream u data]` — the very binding the real table holds,
   bytes verbatim; and
2. after ANY eviction-free schedule of composed events (datagrams from any
   client, upstream replies, ring events through the deployed reactor step),
   a datagram from `a` still routes to that same `u`
   (`orb_affinity_run`, lifting `binding_stable_onClient/_onUpstream`; the
   invariant is threaded by `orbStep_relay_inv`/`orbRun_relay_inv`).

A wiring that re-chose upstreams per datagram fails (2); one that ignored the
table fails (1) — the emitted `u` is *defined* to be what `Udp.onClient` read
from its table.

**Composition hygiene.** `orb_recv_recycles_exactly_once` — the copy-once
recycle accounting of `Reactor.Contract` survives the composition verbatim;
`orb_datagram_no_recycle` / `subOfOut_no_recycle` — the UDP lane never forges
a buffer recycle; `orb_lanes_independent` — ring events don't touch the
relay, datagrams don't touch the FSM.

**Concrete data.** `demoRelay` is reached by the REAL `Udp.run` (clients 1, 2
at t=0), its invariant by the library's `run_init_inv`; `demo_datagram_routes`
(client 1 → binding 0 through the composed step at `demoConfig`, any payload,
any time), `demo_reply_routes` + `demo_reply_owner` (a reply on binding 0 is
submitted back and the library names client 1 as the unique owner).

**Honest scope.** The deployed `main` is a single-request HTTP view over
`serve`; it has no datagram ingress. The UDP lane is wired into the reactor's
own submission language and composed with the deployed reactor step
(`Reactor.step` at `demoConfig`) in `orbStep`; the IO shell that feeds
datagram completions alongside recv completions is environment, per the
assurance boundary.

## Lane 2: Reactor/Fallback.lean — the real `Fallback` chain on the serve dispatch

**What was stranded.** `Fallback/` proves the chain evaluator `runChain`
(served-exactly-once accounting `Served.served_once`, first-success stop,
non-retryable immediate termination, exhaustion, trace-prefix, totality) but
nothing connected it to the reactor's dispatch.

**The wiring.**

- `terminalPage` — the terminal error page per `Fallback.ErrClass`, built as
  a serializer `Response` (bytes carry `serialize_framing` by construction);
  taxonomy statuses: `badGateway/connectFailed/upstream5xx` → 502,
  `timeout/gatewayTimeout` → 504, `notFound` → 404, `forbidden` → 403.
- `fallbackHandle` — the REAL `Fallback.Chain.runChain`, outcome rendered by
  `responseOfServed` (winner's response, or the terminal page).
- `serveFallback` — `serve`'s exact shape: the DEPLOYED reactor
  (`reactorSubs` = `Reactor.step Config.demoConfig`) produces the
  submissions, FSM sends are forwarded faithfully and byte-identically to
  `serve` (`serveFallback_faithful_eq_serve`), and only a bare
  `dispatch req` is answered by the chain (`serveFallback_dispatch`).
- `appAttempt` — the chain head that IS the deployed application:
  definitionally `App.handle demoAppConfig req` (the same `demoAppConfig`
  that `serve` routes with — `appAttempt_is_deployed_app` is `rfl`), its 502
  proxy placeholder classified as retryable `badGateway`, everything else a
  success (`outcomeOfResponse`).

**Seam: `fallback_serves_once_seam`.** For any input the deployed reactor
answers with a bare `dispatch req`:

1. the served bytes are `serialize (responseOfServed (runChain …).2)` — the
   outcome is DECIDED by the real evaluator;
2. `servedResponses + servedTerminal = 1` (the library's `served_once` —
   never zero, never two); and
3. concretely the bytes are EITHER some handler's response OR the terminal
   page for the class that stopped the chain — the only two constructors,
   disjoint by (2).

**Chain behavior on the composed path.** `fallback_first_success_serves`
(winner's response served; trace = handlers up to and including the winner —
nothing after it ran), `fallback_terminal_serves_page` (non-retryable class →
that terminal page, later handlers untried), `fallback_exhaust_serves_page`
(all fall through → terminal page, full trace).

**Conservative over the deployed path.**
`fallback_app_head_serves_deployed`: with `appAttempt` at the chain head and
a non-502 app response, `serveFallback` is byte-identical to the deployed
`serve input` (via `serve_routes`) — the fallback layer changes nothing until
the deployed dispatch actually fails. `fallback_app_head_bestMatch` lifts
`app_routes_total`: the response is still the route the REAL
`Route.Match.bestMatch` chose — the chain does not bypass the router.

**Concrete data.** Three computed (`rfl`) chain runs: exhaustion renders the
last class seen with a full trace; a terminal `forbidden` stops before the
backup; a retryable `timeout` falls through to the backup, which serves —
exactly once.

## Status

- `lake build Reactor` — completed successfully (whole spine, including the
  other lanes' modules).
- `#print axioms` on all seam theorems: subset of
  `{propext, Quot.sound, Classical.choice}`.
- Files touched: `Reactor/Udp.lean` (new), `Reactor/Fallback.lean` (new),
  `Reactor.lean` (two `import` lines), this README.
- No sorries, no `native_decide`, no config fields touched — both lanes are
  transformers/compositions beside the deployed `demoConfig`/`serve`, in the
  same style as the Dns/Socks lanes.

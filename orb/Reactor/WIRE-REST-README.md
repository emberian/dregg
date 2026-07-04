# WireRest — eight more islands attached to the deployed serve path

`Reactor/WireRest.lean` moves eight library "islands" from proven-in-isolation to
attached-to-the-deployed-path, each via a corollary of the library's own core
theorem stated over the values the deployed binary actually produces
(`Arena.Orb.main` → `Reactor.Deploy.deployStep(Guarded)` → `serveFull`/`serveGuarded`).
The anchor is `Reactor.Bridge` (`deploySubs_eq_reactorSubs`), the same lift
`Reactor.WireMore` and `Reactor.CacheDeploy` use.

Verify: `lake build WireRest` (and `lake build Reactor`). Both build clean; zero
sorries; every theorem `#print axioms`-clean within `{propext, Quot.sound,
Classical.choice}` (several depend on none at all).

## Libraries now deployed-attached (8)

| Library | Deployed corollary | Transports (library core theorem) | Deployed value keyed on |
|---|---|---|---|
| **Fallback** | `fallback_serves_once_deployed`, `fallback_deployed_wins` | `runChain_served_once`, `runChain_stops_at_first_success` | `deployResp input` as the last-resort backend response |
| **Cgi** | `cgi_env_total_deployed` (+ `deployCgi_requestMethod`/`_scriptName`) | `cgi_env_total`, `envList_length` | the dispatched request's method/target → CGI env |
| **Redirect** | `redirect_3xx_deployed`, `redirect_method_deployed` | `redirect_location_wellformed`, `method_preserved`/`method_safe_downgrade` | the dispatched request's target as the `{path}` |
| **ForwardProxy** | `forwardproxy_no_relay_deployed`, `forwardproxy_relay_once_connected`, `forwardproxy_needs_upstreamOk_deployed` | `connect_no_relay_before_connected`, `connect_relay_transparent`, `run_connected_needs_upstreamOk` | `(deployResp input).body` as the tunnel relay payload |
| **Udp** | `udp_integrity_deployed`, `udp_affinity_deployed` | `onClient_forward_payload`, `affinity_two_datagrams` | `(deployResp input).body` as the datagram payload |
| **Mtls** | `mtls_no_bypass_deployed`, `mtls_unverified_no_identity_deployed` | `verify_empty`/`authenticate_empty`, `authenticate_unverified` | the plaintext deployed surface (empty / unverified client chain) |
| **Drain** | `drain_no_accept_deployed`, `drain_accounted_deployed`, `drain_completes_reaches_drained_deployed` (+ `deployDraining_mode`) | `acceptReq_refused_of_not_running`, `step_accounted`, `complete_reaches_drained` | a concrete deployed SIGTERM scenario over `Drain.step` |
| **Resume** | `resume_window_deployed`, `resume_expired_deployed`, `resume_rotation_invalidates_deployed` | `accept_in_window`, `expired_refused`, `rotate_invalidates` | a deployed session ticket under the deployed key generation |

What each corollary establishes, in plain terms:

- **Fallback** — every deployed fallback run serves exactly one thing (never zero,
  never two); when every prior backend fails retryably, the served result is
  *exactly* the deployed response.
- **Cgi** — the CGI/1.1 meta-variable environment built from the deployed request
  is total (all 17 variables mapped), with `REQUEST_METHOD`/`SCRIPT_NAME`
  definitionally the deployed request head.
- **Redirect** — a redirect built for the deployed target has a faithful
  in-order-substituted `Location` and a genuine RFC 9110 §15.4 3xx status; the
  followed method is preserved (307/308) or safely downgraded (301/302).
- **ForwardProxy** — the deployed served body relayed through a CONNECT tunnel
  escapes *nothing* before the tunnel is established (either direction), is blindly
  forwarded verbatim once `connected`, and `connected` is reachable only after the
  upstream connect succeeds.
- **Udp** — relaying the deployed served body as a UDP datagram preserves it
  byte-for-byte, and two datagrams from one client pin one upstream (no mid-session
  split).
- **Mtls** — the deployed (plaintext) surface authenticates no one without a
  verified chain: an empty/unverified client chain yields *no* identity. No-bypass.
- **Drain** — after SIGTERM the deployed listener refuses new connections while
  letting the in-flight connection complete, with the accounting identity intact
  (no connection silently lost); completing the last one reaches `drained`.
- **Resume** — a deployed session ticket is accepted only inside its validity
  window, refused once expired, and invalidated wholesale by a key rotation
  (SIGHUP) — the single-owner handover.

## Honest note (same posture as WireMore / Deploy CW5–CW6)

These are **proof-attachment seams**, not runtime byte-drivers. Each states the
library's real, meaning-constraining theorem *about the actual deployed served
bytes or dispatched request*, discharged by the library's own proof — it does not
yet run a CONNECT tunnel, drain connections on a live SIGTERM, or relay UDP inside
the event loop. What is closed is the island: the library's guarantee provably
holds of the data the deployed path carries, rather than of a bespoke side model.

Two of the eight (Drain, Resume) are lifecycle machines with no serve-path bytes
to key on; their seams are concrete deployed *scenarios* over the deployed
listener id / key generation — the same modeled-state posture
`Reactor.Deploy.deploySystem` (Isolation) and `deployRunning` (Policy) already use,
static not runtime-byte-driven.

## Registration

`lakefile.toml` gains one appended target:

```toml
[[lean_lib]]
name = "WireRest"
srcDir = "."
roots = ["Reactor.WireRest"]
```

## Progress toward the goal clause

Combined with the previously attached path — Deploy's proxy/DNS/header/trace,
Policy, Safety, EarlyHints, HtmlRewrite; CacheDeploy's Cache; WireMore's Har,
StickTable, DownloadMgr, Sse, Isolation, Metrics; the codec lanes (Tls, Ws, Socks)
and the parser/H2 engines — these eight (Fallback, Cgi, Redirect, ForwardProxy,
Udp, Mtls, Drain, Resume) push the count of deployed-path-attached libraries
toward ~25 of the ~31 islands. The remaining unattached ones (e.g. Mux, Acme, Ct,
and the subsystem-standalone capture-wave libs Stun/Ice/Dcep/Wireguard/Derp/Disco)
are out of scope for the reactor HTTP path.

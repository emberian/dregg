# WireMore — six more islands attached to the deployed serve path

`Reactor/WireMore.lean` advances the goal clause *"the ~31 islands are connected,
not proven-in-isolation."* Six libraries that had proved a strong core theorem but
were never referenced by the config or the response the deployed binary runs are
now attached: each library's core theorem is restated over the values the deployed
path actually produces and discharged by the library's own proof.

The deployed path is `Arena.Orb.main` → `Reactor.Deploy.deployStep(Guarded)` →
`serveFull` / `serveGuarded`. The values these seams range over are
`Reactor.Deploy.deploySubs input` (the submissions the deployed reactor emits),
`Reactor.Deploy.deployResp input` (the response `serveFull` serializes), and the
request the deployed reactor dispatched.

## The anchor

`deployed_dispatch_agrees` — the request the DEPLOYED reactor extracts
(`dispatchReqOf (deploySubs input)`) is *exactly* the one the test reactor extracts
(`dispatchReqOf (reactorSubs input)`), transported along
`Bridge.deploySubs_eq_reactorSubs`. So every seam keyed on the deployed dispatch is
anchored to the one shared reactor the island lanes were proven over, not a fresh
side model.

## Libraries moved from island → connected

| Library | Deployed seam | Core theorem transported | Meaning constrained |
|---|---|---|---|
| **Har** | `har_records_deployed`, `har_evicts_oldest_deployed` | `record_length_le_cap`, `record_suffix`, `record_full_evicts` | the served request/response is recorded within the ring's capacity, newest retained as an order-preserving suffix, oldest FIFO-evicted when full |
| **StickTable** | `sticktable_deployed` | `bump_getCount_self`, `bump_getCount_other`, `bump_getLastSeen_mono` | tracking the served request raises *exactly* its key's counter by one, frames every other key, never moves last-seen backward |
| **DownloadMgr** | `downloadmgr_deployed` | `activate_reqFrom_queued`, `step_recv_mono`, `resume_reassembles` | a resumable download of the served body issues a full GET (`reqFrom 0`), the cursor never regresses, and the body reassembles with no gap/overlap at any resume cursor |
| **Sse** | `sse_deployed` | `stepField` (SSE §9.2.6 dispatch) | the deployed SSE frame's `data` payload is exactly the served body, in order, default `message` type |
| **Isolation** | `isolation_deployed`, `isolation_no_cross_tenant_deployed` | `touched_in_scope`, `no_cross_tenant` | every resource the served exposure touches is in the owning tenant's scope; a request on the deployed exposure never reaches a different tenant's resource |
| **Metrics** | `metrics_counts_deployed`, `metrics_histogram_deployed` | `inc_exact`, `inc_others`, `observe_total`, `observe_sum` | the served response bumps its per-status counter by exactly one with no side effect; observing the served body length keeps the histogram's total and bucket-sum accounting exact |

(`EarlyHints` / `HtmlRewrite` were already folded onto this path by
`Reactor.Deploy.deploy_transforms_applied`; `Trace` by `deploy_emits_corr`. This
file adds the six above.)

## Honest scope

These are **proof-attachment seams**, the same posture as CW5/CW6 in
`Reactor.Deploy`. They state each library's real, meaning-constraining theorem about
the actual deployed served bytes / dispatch and discharge it with the library's own
proof — closing the island. They are **not** (yet) runtime byte-drivers: nothing
here streams SSE frames onto the socket, persists HAR to disk, or runs the download
manager inside the event loop. What is established is that the library's guarantee
*holds of the data the deployed path carries*.

One `whnf` note carried over from `Reactor.Deploy`: projecting `.status` / `.body`
off `deployResp input` and reducing it forces the whole reactor computation (a
heartbeat blow-up). The seams therefore reference those projections only as opaque
subterms passed into the libraries' generic lemmas; the status/body ties are
definitional in the `deployHarEntry` / `deploySseEvent` / `deployObserveVal`
constructors rather than restated as `rfl` lemmas.

## Verification

- Registered as its own `lean_lib WireMore` (root `Reactor.WireMore`) appended to
  `lakefile.toml`; building it forces the whole `Reactor` tree it depends on.
- `lake build WireMore` — completes successfully, zero sorries, zero unclosed goals.
- `#print axioms` on all ten theorems: each depends only on a subset of
  `{propext, Classical.choice, Quot.sound}` (`sticktable_deployed` and both
  `isolation_*` seams need only `propext`).

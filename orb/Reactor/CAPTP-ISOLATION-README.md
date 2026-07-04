# CAPTP-ISOLATION — the real Captp and Isolation libraries on the deployed path

Two libraries are wired into the reactor the deployed orb runs, rather than
standing as islands: `Captp` (the netlayer capability seam: import/export
tables, epoch guard, promise one-shot) and `Isolation` (the per-tenant
capability partition). Both wirings sit on the path `Arena.Orb.main`
executes — `Reactor.serve` over `demoConfig` / `demoAppConfig` — not on a
bespoke side config.

Files: `Reactor/Captp.lean` (namespace `Reactor.Netlayer`),
`Reactor/Isolation.lean` (namespace `Reactor.Tenant`), both imported by the
`Reactor.lean` root. `lake build Reactor` green; zero sorries; every named
theorem's axioms ⊆ {propext, Quot.sound, Classical.choice}.

## Captp — `Reactor/Captp.lean`

The wiring threads the REAL `Captp.Session` down the deployed request path:

- `grantStep st input` serves `input` through the deployed `Reactor.serve` and,
  in the same step, exports the request's object identity into the real
  session export table (`Captp.Session.exportObject`). What crosses the
  netlayer seam is a `Grant`: the wire descriptor (`Descriptor.Export pos`)
  plus the **epoch stamp** captured at grant time.
- `acceptPeer` is the inbound half (real `importObject`); `pipeline`/`settle`
  are promise pipelining over the real `allocateAnswer`/`tryResolve`.
- Transparency: `grantStep_transparent`, `respWindow_eq_map_serve`, and
  `pipeline_transparent` prove the wiring never touches a served byte;
  `grant_serves_routed` re-exposes the deployed routing fact (`serve_routes`)
  through the captp step.
- Well-formedness is **discharged, not assumed**: `init_wf` (cold start),
  `exportObject_wf` / `importObject_wf` (new preservation lemmas),
  `grantStep_wf`, `grantRun_wf` (any window of served requests).

### Seam: `captp_epoch_seam`

A descriptor the reactor resolves is valid **only within its epoch**: any
stamped reference that resolves in the reactor's post-grant session is
*rejected* (`resolveStamped = none`) after any future run of session operations
that bumped the epoch and rebound the descriptor's position at the new epoch.
This is the real `Captp.Session.bump_invalidates` composed with the reactor's
session state, with its `WF` precondition supplied by the reactor's own
preservation chain.

- `captp_epoch_seam_grant` — instantiated at the reactor's own grant (which
  provably resolved at grant time, `grant_resolves`): the reference `grantStep`
  handed across the seam dies with its epoch.
- `reset_rebind_rejects_stale` — the concrete ABA replay on the accept path:
  session reset (`bumpEpoch`) + peer rebinds the same import position ⇒ the
  pre-reset stamp no longer resolves (real `bump_then_reimport_invalidates`).
- `pipeline_one_shot` / `settle_once` — a promise pipelined for a served
  request settles exactly once: first delivery succeeds (real
  `tryResolve_success`), second is refused (real `tryResolve_once`).

## Isolation — `Reactor/Isolation.lean`

The real `Isolation.System` is built **over the deployed route table**:
exposure `e` is index `e` of `demoAppConfig.table` — the exact table
`Reactor.serve` routes against via `App.handle`. A `Binding` is the operator's
declaration (exposure → owning tenant, exposure → touched resources);
`scopeOf` *generates* tenant scopes from it, so the `System.wf`
router-respects-the-partition obligation holds by construction
(`touched_scoped`) and `systemOf ac b` is a total, well-formed instance of the
actual `Isolation` model for any binding. `scopeOf_disjoint` turns disjoint
per-tenant resource declarations into the disjoint-scopes hypothesis
`Isolation.no_cross_tenant` needs. The deployed instantiation is `demoSystem`
(= `systemOf demoAppConfig demoBinding`), with `demoBinding_disjoint` proven.

### Seam: `tenant_isolation_seam`

On the deployed path: when the reactor dispatches `req` and `serve` answers
with the route the real `Route.Match.bestMatch` chose
(`serve_routes_bestMatch`), that chosen route **is** an exposure `e` of
`demoSystem` (`demoAppConfig.table[e]? = some r`, via `bestMatch_mem`), and

1. **served within scope** — every resource the request touches lies in the
   owning tenant's scope (real `Isolation.touched_in_scope`);
2. **no cross-tenant reach** — for every other tenant `t`, none of the touched
   resources is in `t`'s scope (real `Isolation.no_cross_tenant` +
   `demoBinding_disjoint`).

So a request served under tenant A only touches resources in the scope of
tenant A, composed with the App/serve dispatch. `tenant_isolation_seam_binding`
is the same positive half for an arbitrary operator binding. The attenuation
layer is driven too: `request_cap_attenuates` (the capability a request
exercises is an `Isolation.Sub` of the owning tenant's held capability) and
`exercised_within_held` (real `Isolation.grant_subset_held` on the serving
path).

## Scope notes

- The Captp **frame decoder** (`Captp.Frame.decodeFrame`) is not yet driven by
  the reactor's byte path; the session/table layer is what is wired here.
  Driving `decodeStream` off `RingEvent.recvInto` payloads is a named successor.
- `objOf` (request bytes → `Captp.Obj`) and the demo `Binding` (identity
  tenants, one resource per exposure) are the adapter constants of this wiring;
  the seam theorems are stated over any state/binding, so richer adapters
  inherit them unchanged.
- Epoch bumps are modeled as session operations (`Session.Op.bumpEpoch` inside
  a run), matching the Captp model; the reactor does not yet emit a bump on a
  transport-level reconnect event — that hook lands with the netlayer transport
  wiring.

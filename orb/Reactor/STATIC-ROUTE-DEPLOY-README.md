# STATIC-ROUTE-DEPLOY — the real static-file handler and the vhost router on the deployed dispatch

`Reactor/StaticRouteDeploy.lean` wires two real single-file libraries —
`StaticFile` and `RouteAdvanced` — onto the request the DEPLOYED reactor actually
dispatches. The anchor is `Reactor.Deploy.deploySubs input` together with
`Reactor.Deploy.dispatchReqOf`: that is exactly the pair `Reactor.Deploy.serveGuarded`
reads and branches on (`serveGuarded input` → `dispatchReqOf (deploySubs input)` →
`guardOne`), and `serveGuarded` is the response function `Arena.Orb.main` runs via
`deployStepGuarded`. So every theorem here ranges over the submissions the deployed
orb produces, not a side model.

## (1) The deployed static-file route

- `deployStaticCfg : StaticFile.Config` has `docRoot = Reactor.Deploy.deployDocRoot`
  (`/srv/www`) and a modeled filesystem: one regular file at
  `/srv/www/static/app.js` (`assetBytes = "hi"`), nothing else, no directories.
  The filesystem fields are the library's documented boundary; the traversal seam
  depends only on `resolvePath`, which is independent of their contents.
- `staticReqOf req` turns the dispatched request's raw target segments
  (`Reactor.Deploy.rawSegsOf req` — the same pre-normalize slash-split the deployed
  serve derives) into a `StaticFile.Req`.
- `deployStaticResolved input` / `deployStaticServe input` run the REAL
  `StaticFile.resolvePath` / `StaticFile.serve` over the request the deployed
  reactor dispatched.

Key definitional bridge — `deployStatic_resolvePath` (by `rfl`):

```
StaticFile.resolvePath deployStaticCfg (staticReqOf req)
  = Safety.Traversal.serveStatic Reactor.Deploy.deployDocRoot (Reactor.Deploy.rawSegsOf req)
```

That right-hand side is the exact expression `Reactor.Deploy.deploy_no_path_escape`
already certifies within-root (and equal to `deployDocRoot ++ App.targetSegments`).
So the real handler's resolution *is* the deployed serve's resolution.

### Seam theorem — `deployed_static_no_escape`

```
theorem deployed_static_no_escape (input : Bytes) (p : List String)
    (hp : deployStaticResolved input = some p) :
    Reactor.Deploy.deployDocRoot <+: Route.Path.descend [] p
```

For whatever request the deployed reactor dispatched, walking the served static
path with the `..`-popping filesystem interpreter (`Route.Path.descend`) keeps
`/srv/www` as a prefix — no target, however many encoded or literal `..` it
carries, escapes the document root. This is the REAL `StaticFile.static_no_escape`
transported onto the deployed dispatch (its cleanliness side condition
`deployDocRoot_clean` is discharged: `/srv/www` carries no dot-segments).

`deployStaticResolved_on_dispatch` ties the resolved path back to the deployed
serve's own within-root expression; `deployStaticRouted_no_escape` re-lands the
same guarantee under the router-then-handler composition (part 3).

## (2) The vhost router upgrade

The flat deployed decision (`Reactor.Deploy.routeKeyOfSegs`, a `"health"/"static"`
match) has no host dimension. `deployRouter : List (RouteAdvanced.ServerBlock DeployH)`
upgrades it to a real two-level `RouteAdvanced` table:

- `blockA` — bound to the **exact** host A (`a.example.com`), carrying a
  `/static/**` route to the static handler and a `404` catch-all;
- `blockB` — bound to the **exact** host B (`b.example.com`), a distinct virtual
  host answering a fixed `200`.

`advReqOf host req` lifts the dispatched request into a `RouteAdvanced.Req` (the
authoritative host arrives pre-split — the RFC 9110 §7.2 / RFC 6066 §3 SNI/Host
boundary the library documents; method and path come from the dispatched request,
`App.targetSegments` being the same traversal-safe normalization the router
matches on). `deployBlockSelected` / `deployRouteOf` run the REAL
`RouteAdvanced.selectBlock` / `dispatch` over the deployed dispatch.

### Seam theorem — `deployed_host_routing`

```
theorem deployed_host_routing (input : Bytes) :
    deployBlockSelected input hostA ≠ some blockB
```

A request for host A on the deployed path is routed by the real
`RouteAdvanced.selectBlock` and never selects the host-B-only block: `blockB` is
bound to the exact host B, host A is not host B, so the REAL selection cannot
return it. This is the RFC 9110 §7.4 no-misdirection property
(`RouteAdvanced.route_host_isolation`) transported onto the deployed dispatch.
`deployed_selects_hostA` is the positive companion: host A selects `blockA`.

## (3) The two wirings compose

`deployStaticRouted input host` is the composition: over the deployed dispatch,
run the REAL `RouteAdvanced` router; when it picks the `/static` route
(`serveStatic`), serve the REAL `StaticFile.serve` over the modeled filesystem.
`deployStaticRouted_no_escape` shows the router's decision cannot conjure a path
outside the root — the served path is the same resolution the no-escape seam
covers.

## Non-vacuity — the real handler and router execute (kernel `decide` / `#guard`)

- `deployStatic_serves_asset` — `/static/app.js` → `200` with exactly `assetBytes`.
- `deployStatic_missing_404` — a missing file → `404`.
- `deployStatic_confines_dotdot` / `deployStatic_confines_encoded` —
  `../../etc/passwd` and `%2e%2e/%2e%2e/etc/passwd` both resolve to
  `/srv/www/etc/passwd`, confined under the root.
- `router_hostA_static` → `serveStatic`; `router_hostA_other` → `fixed 404`;
  `router_hostB` → `fixed 200` — the same router sends host A and host B to
  disjoint blocks.

Matching `#guard` lines execute these on concrete inputs at elaboration.

## Verification

- `lake build Reactor.StaticRouteDeploy` — green. Spine (`Reactor.Deploy`,
  `Reactor.Bridge`, `Reactor.Serve`, `Reactor.Config`, `Proto.Basic`,
  `Arena.Orb`) — green.
- Zero `sorry`, zero `admit`, no `UNCLOSED`.
- `#print axioms` on every seam theorem ⊆ `{propext, Classical.choice, Quot.sound}`
  (`deployStatic_serves_asset` uses only `propext`).

## Ownership / boundaries

- Owned files: `Reactor/StaticRouteDeploy.lean` (new), this README, and the single
  `import Reactor.StaticRouteDeploy` line added to `Reactor.lean`.
- Filesystem contents (`fs`/`isDir`/`readDir`/`etag`) and host extraction are the
  libraries' named boundaries, not re-derived here.
- The sibling `Reactor.MiddlewareDeploy` / `Reactor.AuthDeploy` modules (other
  lanes) were red at build time; they are not in this
  module's scope and not on the deployed spine.

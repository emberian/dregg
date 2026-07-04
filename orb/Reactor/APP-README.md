# Reactor.App — the application layer (APP-SEED)

`Reactor/App.lean` turns a dispatched request into a response by driving the
**real** `Route.Match` library. It is the interface seed the other lanes build
against, and it is wired to the reactor's response path, not a standalone model.

## Where it sits in the spine

```
Proto.Output.dispatch (req : Proto.Request)      -- the reactor hand-off
        │  req : {method, target, version, headers}
        ▼
Reactor.App.handle : AppConfig → Proto.Request → Reactor.Response
        │  drives Route.Match.bestMatch over the effective table
        ▼
Reactor.Response      -- the value Reactor.serialize renders on the wire
```

`Reactor.Response` is exactly the serializer's input type (`Reactor/Serialize.lean`),
and `Proto.Request` is exactly the `dispatch` payload (`Proto/Basic.lean`). So
`handle` is a genuine adapter between the two proven ends — the routing decision
now sits where `Reactor/Serve.lean`'s `demoResp` currently synthesizes a demo 200.

## What is wired

- **`Handler := { status : Nat, body : Bytes }`** — the per-route payload for this
  slice (a static response). This is what instantiates `Route.Match.Route Handler`,
  letting a route table carry application handlers. A request-dependent handler is
  a later widening that keeps this as its constant case.

- **`AppConfig`** — `routes : List (Route.Match.Route Handler)`, a `defaultHandler`,
  and the Policy admission fields (`lid`, `policy : Policy.Running`, `routeKeyOf`).
  `AppConfig.table` folds the default handler in as an explicit `Pat.default`
  route, so the effective table **always** contains a default by construction
  (`table_has_default`) — `handle` is total with no side condition.

- **`targetSegments : Proto.Bytes → List String`** — drop the query (`?…`),
  slash-split, drop empty segments, then `Route.Path.normalize`. Normalization is
  where percent-decoding happens (once) and where the RFC 3986 dot-segment walk
  runs — the traversal-safe boundary. The result is exactly what `bestMatch`
  matches against.

- **`handle`** — normalize the target, `Route.Match.bestMatch` over `ac.table`,
  build the response from the chosen handler (`responseOfHandler`). The `none`
  arm is unreachable (default always present) but spelled with the default
  handler so `handle` is a plain total `def`.

## The seam theorem (anti-island)

**`app_routes_total`** — for **any** `AppConfig` and request:

```
∃ r, Route.Match.bestMatch ac.table (targetSegments req.target) = some r
   ∧ handle ac req = responseOfHandler r.handler
```

Two facts in one: `handle` never gets stuck (there is always such an `r`;
totality rides on `Route.Match.bestMatch_total` + `table_has_default`), and the
response is **exactly** `responseOfHandler` of the route the *real*
`Route.Match.bestMatch` selected. A `handle` that ignored `bestMatch` (a stubbed
router returning a fixed response) would fail the second conjunct.

**`app_chosen_route_matches`** strengthens it via `Route.Match.bestMatch_sound`:
the route whose handler produced the response actually matches the request target
(`matchesAny … r = true`) — the response is decided by a route that really
matches, not a fallback slipped in behind `bestMatch`.

`demoApp_routes_total` instantiates the seam at the concrete `demoApp` (exact
`/health`, prefix `/static`, 404 default).

## The Policy admission seam (real, driven — completion left to the policy lane)

The shapes do not line up on their own: `bestMatch` yields a `Route Handler`,
while `Policy.serveDecision` keys on the opaque `Policy.RouteKey`. So the wiring
is provided but not yet gated into `handle`:

- **`admitDecision ac r plaintext`** is the genuine composition onto the real
  `Policy.serveDecision` (`admitDecision_is_serveDecision` is `rfl`), through the
  `routeKeyOf` adapter field.
- **`admit_refuses_undeclared`** drives that real admission logic (an undeclared
  listener admits nothing), so `Policy` is exercised here, not islanded.

**For the policy lane to complete:** supply `routeKeyOf` (route → `RouteKey`
identity), then gate `handle`:

```
def handleGated (ac) (req) (plaintext) : Response :=
  match Route.Match.bestMatch ac.table (targetSegments req.target) with
  | some r =>
      match admitDecision ac r plaintext with
      | some _ => responseOfHandler r.handler          -- admitted
      | none   => responseOfHandler ac.forbiddenHandler -- 403 (add the field)
  | none => responseOfHandler ac.defaultHandler
```

with a theorem `admitDecision … = some _ → handleGated … = handle …` (routing
decides once admission passes), reusing `app_routes_total` for the admitted case.

## Build / audit status

- `lake build Reactor` — green (`Reactor/App.lean` compiles; import added to
  `Reactor.lean`).
- Zero `sorry`.
- `#print axioms` for every theorem here: subset of `{propext, Quot.sound}`
  (within the allowed `{propext, Quot.sound, Classical.choice}`).

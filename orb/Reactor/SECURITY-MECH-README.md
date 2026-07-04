# SECURITY-MECH — Policy and Safety as real byte mechanisms

`Reactor.Deploy` proves **mechanism, not just correspondence**. Sections (3a)/(3b)
prove that the bytes `serveFull` emits correspond to a Policy-admitted, within-root
request — but on their own those are only correspondence: a `serveFull` that
serialized `deployResp` no matter what Policy or Safety decided would satisfy them
while never *branching*. Without the gate below,

```
GET /nope           -> 404 Not Found  "not found"     (default route)
GET /../etc/passwd  -> 404 Not Found  "not found"     (default route, incidental)
```

both fall out as the *same* default-route 404, with neither the admission gate nor
the traversal check touching the emitted bytes.

The gate installs the branch. The deployed response **gates**: the REAL
`Policy.serveDecision` and the REAL `Safety`/`Route.Path` decode are consulted on
the dispatched request, and the bytes `main` writes differ per outcome.

## The gate (`Reactor/Deploy.lean`, section 4)

`serveFull` is byte-for-byte unchanged — `Reactor.RespTransform` rfl-locks
its shape (`serveFull_dispatch`, `htmlrewrite_deployed`, …). The gate is
`serveGuarded`, and `main` runs it via `deployStepGuarded`.

The decision logic is factored to the **segment level** so it is kernel-decidable
(the byte→segment step uses `String.splitOn`, which only reduces in the compiled
binary):

- `routeKeyOfSegs : List String → Policy.RouteKey` — the adapter `App.routeKeyOf`
  left as a hole. `/health` and `/static` map to the declared key
  `deployRouteKey = ⟨0,0⟩`; everything else maps to `⟨0,1⟩`, which
  `deployPolicyConfig` does **not** declare.
- `decisionOfSegs` — the REAL `Policy.serveDecision deployLid (routeKeyOfSegs …)
  false deployRunning`. Declared → `some`; undeclared → `none`.
- `escapesSegs : List String → Bool` — the REAL `Route.Path.decodeSegs` (the
  single percent-decode boundary), `true` iff a decoded `..` is present.

The request-level wrappers `routeKeyOfReq` / `deployDecisionOf` / `targetEscapes`
prepend `App.targetSegments` / `rawSegsOf`; `deployDecisionOf_eq_segs` and
`targetEscapes_eq_segs` bridge the two (definitional).

`guardOne` is the branch, on one dispatched request:

```
guardOne input req :=
  if the target escapes (escapesSegs)      -> serialize traversalBlocked404   -- 404
  else if serveDecision refuses            -> serialize forbidden403          -- 403
  else                                     -> serialize (deployResp input)    -- the 200 path
```

Both `forbidden403` and `traversalBlocked404` are `error4xx`-built (serializer
responses), with target-independent bodies — no application handler body and no
resolved file bytes can flow on those arms.

`serveGuarded` mirrors `serveFull` exactly on the FSM-send path (faithful in-order
forwarding); on a bare dispatch it runs `guardOne`.

## Seam theorems — over the bytes `main` writes

- `deploy_refuses_undeclared_bytes` — a dispatched request the REAL
  `serveDecision` refuses (non-escaping) makes `serveGuarded input` **equal** the
  serializer-built 403. Byte-level, not correspondence.
- `deploy_traversal_blocked_bytes` — a dispatched request whose decoded target
  carries an escaping `..` makes `serveGuarded input` **equal** the serializer-built
  404 ("traversal blocked"), status `404`. The escaped resource is never
  serialized.
- `serveGuarded_dispatch` — reduces `serveGuarded` to `guardOne` on the dispatch
  path (kept off the deployed-config `whnf` blow-up, the same discipline as
  `serveFull_serializes_dispatch`).
- `guardOne_refuses` / `guardOne_blocks` / `guardOne_admits` — the three arms as
  pure facts about `guardOne` (no reactor hypothesis).

## The branch is real — kernel-checked (`decide` / `#guard`)

Real executions of the REAL gate functions on the concrete segment lists a parsed
target produces:

- `decision_admits_health : decisionOfSegs ["health"] = some ⟨…⟩`
- `decision_admits_static : decisionOfSegs ["static","app.js"] = some ⟨…⟩`
- `decision_refuses_nope  : decisionOfSegs ["nope"] = none`
- `escape_fires_dotdot    : escapesSegs ["..","etc","passwd"] = true`
- `escape_fires_encoded   : escapesSegs ["%2e%2e","etc","passwd"] = true`  (decoded once)
- `escape_quiet_health    : escapesSegs ["health"] = false`
- `escape_quiet_double_encoded : escapesSegs ["%252e%252e","etc"] = false` (decodes to `%2e%2e`, not `..`)
- `gate_statuses_distinct : 403 ≠ 404` — the arms emit different responses.

Plus the matching `#guard` lines that force the same evaluations at elaboration.

## Runtime evidence (the deployed binary)

`Arena.Orb.main` runs `deployStepGuarded`. The sans-IO core, one request in,
one response out:

```
$ printf 'GET /health HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 200 OK
Server: drorb
x-upstream: 1572395042
x-corr: 71.69.84.32.47.104.101.97.108.116.104.…
Content-Length: 2

ok

$ printf 'GET /nope HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 403 Forbidden
Content-Length: 27

policy: undeclared surface

$ printf 'GET /../etc/passwd HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 404 Not Found
Content-Length: 18

traversal blocked

$ printf 'GET /static/app.js HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 200 OK
Server: drorb
x-upstream: 1572395042
…
asset
```

`/nope` is a Policy **403**; `/../etc/passwd` is an explicit traversal
**404 "traversal blocked"**; `/health` and `/static` serve **200** with
`x-upstream`/`x-corr`. The gate outcome selects the bytes.

## Assurance

- `lake build Reactor` and `lake build orb` are green; full `lake build` green.
- Zero `sorry` / `admit`.
- `#print axioms serveGuarded`, `deployStepGuarded`, the seam theorems, and `main`
  are all within `{propext, Quot.sound, Classical.choice}`; the pure gate facts
  (`escape_fires_dotdot`, …) use even fewer, and `escape_fires_dotdot` depends on
  no axioms at all.

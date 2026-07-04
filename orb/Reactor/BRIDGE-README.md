# Reactor.Bridge — lifting the test-reactor seams onto the deployed path

## The two reactors

Two functions run the *same* proven reactor (`Reactor.step`) from a fresh plain
connection on a single `recvInto` completion, differing only in the `Config`:

| function | file | config |
|---|---|---|
| `Reactor.reactorSubs` | `Reactor/Serve.lean` | `Reactor.Config.demoConfig` |
| `Reactor.Deploy.deploySubs` | `Reactor/Deploy.lean` | `Reactor.Deploy.deployConfig` |

`deployConfig` is `demoConfig` with the three codec lanes replaced by their real
engines through the lanes' own structure-update transformers:

```
deployConfig = wireSocks ⟨0⟩ false (Ws.wireWs (TlsWire.wireTls demoTlsCfg demoConfig))
```

`Arena.Orb.main` runs `Deploy.deployStep → serveFull → Reactor.step deployConfig`
over `deploySubs`. So every seam the island lanes proved about `reactorSubs` /
`serve` (App routing, keep-alive, rate, SSE, faithful forwarding, …) is stated
over the config the deployed binary does **not** run. This file closes that gap
for the HTTP/1.1 plaintext path.

## The theorem

`deploySubs_eq_reactorSubs (input) : deploySubs input = reactorSubs input`

Exact equality, for every input. The proof is a congruence chain, not a black-box
`rfl` (a full `rfl` fails — see below):

1. The initial state is `Conn.mkPlain`, whose protocol state is `.plainH1 []`.
2. On a `recvInto` completion the reactor runs `onBytes cfg (.plainH1 …) data`,
   which is `runH1 cfg .plainH1 …`. `runH1`/`h1Loop` read **exactly four**
   `Config` fields: `maxHeaderBytes`, `h1Parse`, `oversizeResponse`,
   `errorResponse`. None is a codec field.
3. The three wire transformers are `{ cfg with <codec fields> }` structure
   updates, so each of those four fields is **definitionally equal** between
   `deployConfig` and `demoConfig` — recorded field-by-field as
   `deployConfig_h1Parse`, `deployConfig_maxHeaderBytes`,
   `deployConfig_oversizeResponse`, `deployConfig_errorResponse` (all `rfl`).
4. `h1Loop_eq` (induction on fuel) → `runH1_eq` → `onBytes_plainH1_eq` →
   `protoStep_eq` lift that field-wise agreement up to `Proto.step`;
   `deploySubs_eq_reactorSubs` lifts it through the `Reactor.step` wrapper
   (translate outputs, append the buffer recycle — a pure function of the inner
   `Proto.step` result).

### Why not a one-line `rfl`

`h1Loop` recurses on `buf.length + 1`; for a symbolic `input` that fuel is stuck,
so the recursion carries the **whole** config value, and `deployConfig` and
`demoConfig` are not defeq as whole structures (their codec fields genuinely
differ). The congruence chain contracts the config to just the four fields the
path reads, on which the configs *are* defeq.

## What lifts, and how

`lift {P} (input) (h : P (reactorSubs input)) : P (deploySubs input)`

For **any** predicate `P` on submission lists: a fact proven once about the test
reactor's submissions transports verbatim onto the deployed reactor's
submissions. `lift_symm` goes the other way.

Because `deploySubs input = reactorSubs input` is a plain equality, *any* island
seam phrased over `reactorSubs input` (or, since `serve`/`serveFull` are the same
`sendsOf`/`demoResp` pipeline over these subs, over the served bytes on the
no-FSM-send dispatch path) rewrites onto the deployed path. Two worked transports
are included as evidence the lift is real, each proved *only* by rewriting along
the equality:

- `deployed_routes` — the `serve_routes` seam (dispatched request → real
  `App.handle` over the demo route table) landed via `deploySubs`' hypotheses.
- `deployed_routes_bestMatch` — the `serve_routes_bestMatch` seam (the served
  route is the one `Route.Match.bestMatch` actually selected).

## Scope — what this does *not* claim

- **HTTP/1.1 plaintext path only.** The equality holds for the `.plainH1` recv
  arm from `mkPlain`. The codec lanes (`tlsRecv`/`hsFeed`/`wsFeed`/`socksFeed`)
  are exactly where the two configs differ; on those states the reactors diverge
  by construction, and the deployed lanes have their own seams in
  `Reactor/Deploy.lean` (`deploy_uses_real_tls`, `deploy_uses_real_ws`,
  `deploy_uses_real_socks`).
- The deployed *serving* pipeline (`serveFull`) additionally runs the header
  rewrite / proxy / DNS / trace stamps on top of these submissions; those are
  proven separately in `Reactor/Deploy.lean`. This bridge is about the
  **submissions** (`deploySubs = reactorSubs`), which is the shared root both
  pipelines start from.

## Verification

- `lake build Reactor.Bridge` (and `lake build Reactor`) — green.
- Zero `sorry`.
- `#print axioms deploySubs_eq_reactorSubs` (and `lift`, `deployed_routes`,
  `deployed_routes_bestMatch`) ⊆ `{propext, Classical.choice, Quot.sound}`.

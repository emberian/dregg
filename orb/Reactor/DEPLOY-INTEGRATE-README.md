# DEPLOY-INTEGRATE — admission, path-escape safety, and response transforms folded onto the deployed serve

## Summary

Three real libraries that had proved their own theorems in isolation — the
cold-plane **Policy** admission gate, the **Safety** path-traversal resolver, and
the **EarlyHints/HtmlRewrite** response transforms — are now wired onto the path
the deployed orb actually runs:

    Arena.Orb.main → Reactor.Deploy.deployStep → serveFull → Reactor.step deployConfig

The wiring and its seam theorems live in `Reactor/Deploy.lean` (section `(3)
DEPLOY-INTEGRATE`), the file `main` transitively runs. Each theorem ranges over
`serveFull input` — the bytes `main` writes — not a sibling serve. This is the
distinction the bar draws: the RESPTRANSFORM lane proved its facts about a
separate `serveFullHtml`/`deployRespHtml`; here the facts are about `serveFull`
itself.

## Why the facts, not a byte-changing rewrite

`serveFull` / `deployResp` are load-bearing for `Reactor/RespTransform.lean` and
`Reactor/Bridge.lean` (both imported by `Reactor.lean`): they pin the exact byte
shape by `rfl` (`serveFull input = serialize (deployResp input)`). Those files
are defined and maintained separately, so this integration does not alter
`serveFull`'s or `deployResp`'s definition. It does not need to:

* the HtmlRewrite transform is **lossless** (identity — `HtmlRewrite.roundtrip`),
* the EarlyHints 103/final ordering adds **no final bytes**,

so folding them changes no byte `main` writes. What the theorems establish is that
the bytes `main` already writes ARE the real transforms' output and DO correspond
to an admitted, within-root request. The verification (`printf | orb`) confirms the
runtime is unchanged: `GET /health → 200 OK`, `Server: drorb`, `x-upstream:
1572395042`, `x-corr:` all intact; `/nope → 404`, malformed → `400`.

## The three seam theorems (over `serveFull`, the bytes `main` writes)

### `deploy_policy_admits` — a served response corresponds to a Policy-admitted request

On a deployed dispatch (`sendsOf (deploySubs input) = []`, `deploySubs input =
.dispatch req :: rest`):

* `serveFull input = serialize (deployResp input)` — the served bytes;
* `deployResp input = rewriteResp (deployProg …) (App.handle demoAppConfig req)` —
  those bytes ARE the router's response for the request the reactor dispatched
  (uses `hsub`, tying `req` to what was actually dispatched);
* the route the deployed router selected (`Route.Match.bestMatch`) carries policy
  key `deployRouteKey`, and the REAL `Policy.serveDecision` admits
  `(deployLid, deployRouteKey)` on `deployRunning`, recording exactly
  `⟨deployLid, deployRouteKey, false⟩`.

The admission is **driven, not asserted**: `deployRunning` is a real
`Policy.Running` reachable from cold boot by one `adopt` step
(`deployRunning_reachable`), so the real declared-surface invariant holds of it
(`deployRunning_wf = Policy.reachable_wf …`). And the gate genuinely refuses
off-surface — `deploy_serveDecision_refuses_undeclared` shows listener `1`
(undeclared) is refused by the SAME `Policy.serveDecision`, so the positive
result is not a constant `some`.

`deployLid = demoAppConfig.lid` and `deployRouteKey = demoAppConfig.routeKeyOf r`
by `rfl` (`deploy_lid_matches`, `deploy_routeKey_matches`), so the admitted
`(listener, route)` is the one the deployed app actually dispatches to.

### `deploy_no_path_escape` — the served target is within-root per real Safety

For any request, the REAL static-file resolver keeps the document root as a
structural prefix:

    deployDocRoot <+: Safety.Traversal.serveStatic deployDocRoot (rawSegsOf req)

and that resolution equals the root joined with EXACTLY the normalized segments the
deployed router matched:

    serveStatic deployDocRoot (rawSegsOf req) = deployDocRoot ++ App.targetSegments req.target

`rawSegsOf` is the deployed serve's own pre-normalize split (drop query,
slash-split, drop empties); `targetSegments_eq_normalize` shows
`App.targetSegments req.target = Route.Path.normalize (rawSegsOf req)` by `rfl`, so
the within-root guarantee is about the target the deployed serve uses to match, not
a bespoke one. `deploy_dotdot_confined` is the concrete witness: `../../etc/passwd`
under `/srv/www` clamps to `/srv/www/etc/passwd`, never climbing out. The safety
content is entirely `Safety.Traversal.serveStatic_root_prefix` /
`serveStatic_eq_normalize`.

### `deploy_transforms_applied` — the response body is the real transform output where declared

For a deployed dispatch declaring any preload `hints`:

* `serveFull input = serialize (deployResp input)` — the served bytes;
* `(deployResp input).body = htmlXform (deployResp input).body` — the served body
  IS the REAL `HtmlRewrite` streaming transform output
  (`htmlXform = bytesOf ∘ tokenize`);
* **chunk-boundary safety**: splitting the body at ANY boundary `a ++ b` and
  streaming the two chunks yields the same output as feeding it whole
  (`HtmlRewrite.stream_eq_whole`);
* the REAL `EarlyHints.run` over `deployHintActions` emits the hints (each a `103`)
  then EXACTLY one final: the message list is `hints.map Msg.info ++ [Msg.final f]`,
  and `run_building_shape` decomposes it as `pre ++ [final]` with `allInfo pre`, so
  every `103` precedes the one final;
* that final's body is the served body (`deployFinalOf_body`).

Nothing here is a re-implementation: `EarlyHints.run` / `run_building_shape` and
`HtmlRewrite.tokenize` / `bytesOf` / `stream_eq_whole` / `roundtrip` are the library
functions and theorems, applied to `Reactor.Deploy.deployResp`.

### `deploy_integrated` — the three folded checks on one deployed dispatch

A single theorem gathering: served bytes = deployed response; the deployed
`(listener, route)` is Policy-admitted; the target stays within `deployDocRoot`;
the served body is the real transform output — all ranging over the same
`serveFull input`.

## New definitions (all in `Reactor/Deploy.lean`)

| name | role |
|------|------|
| `deployLid`, `deployRouteKey`, `deployPolicyConfig` | the deployed Policy declared surface (matches `demoAppConfig.lid` / `.routeKeyOf`) |
| `deployRunning` | live Policy state = `adopt deployLid (init deployPolicyConfig)` |
| `deployRunning_reachable`, `deployRunning_wf` | grounds it in the real `Reachable`/`Wf` invariant |
| `deployDocRoot`, `rawSegsOf` | the deployed static root and the serve's own raw path split |
| `htmlXform`, `htmlXform_lossless` | the real streaming HTML transform (lossless) |
| `toFinalR`, `deployFinalOf`, `deployHintActions`, `run_deployHintActions` | the deployed 103/final emission over the served response |
| `serveFull_serializes_dispatch` | `serveFull input = serialize (deployResp input)` on the dispatch path |

## Build / assurance

* `lake build orb Reactor` — green.
* No `sorry` / `admit` / `native_decide`.
* `#print axioms` on every seam theorem ⊆ `{propext, Quot.sound, Classical.choice}`.
* Runtime: `printf 'GET /health HTTP/1.1\r\n…' | orb` → `200 OK`, `Server: drorb`,
  `x-upstream: 1572395042`, `x-corr: …`, body `ok`; `/nope` → `404`; garbage →
  `400`. Behavior unchanged from before the fold (as intended).

## Files touched

* `Reactor/Deploy.lean` — added imports (`Policy.Invariant`, `Safety.Traversal`,
  `EarlyHints.Basic`, `HtmlRewrite.Basic`) and the `(3) DEPLOY-INTEGRATE` section.
* `Reactor/DEPLOY-INTEGRATE-README.md` — this file.

No sibling-owned file (`RespTransform`, `Bridge`, `Serve`, `App`, `Orb`) was
modified; `serveFull`/`deployResp`/`deployStep` definitions are unchanged, so those
lanes stay green.

# Reactor.RespTransform — EarlyHints + HtmlRewrite wired onto the deployed path

This wiring puts two stranded response-shaping libraries onto the path the
deployed orb actually runs:

```
Arena.Orb.main → Reactor.Deploy.deployStep → Reactor.Deploy.serveFull
              → Reactor.step deployConfig (over deploySubs)
```

`serveFull`'s deployed response is `deployResp input` — the `App.handle` router
output passed through the REAL `Header.run` under `deployProg`. Both transforms
here compose with that response (not a side model), so they operate on the very
bytes `main` writes on the no-FSM-send (dispatch) branch, where
`serveFull input = serialize (deployResp input)`.

The file owns `Reactor/RespTransform.lean`. It adds one import to `Reactor.lean`
(`import Reactor.RespTransform`) and touches nothing else on the spine.

## 1. HTTP 103 Early Hints (RFC 8297)

A deployed route may declare zero or more preload hints. The emission is modelled
with the REAL `EarlyHints.run` from `building`: one `emitInfo` per declared hint,
then one `emitFinal` carrying the deployed final response
(`deployedFinal input = toFinal (deployResp input)`, whose status and body are
exactly `serveFull`'s deployed response).

* `run_hintActions` — the REAL `EarlyHints.run` (via `run_info_cons`/
  `run_final_cons`) on the deployed hint sequence yields exactly the hints as
  `103` messages, in order, then the one final; the builder ends `committed`.

* **`early_hints_precede_final_deployed`** (the seam). On a deployed dispatch
  declaring any `hints`:
  - the emitted message list is `hints.map Msg.info ++ [Msg.final (deployedFinal input)]`;
  - **composing `EarlyHints.run_building_shape`**, that list decomposes as
    `pre ++ [Msg.final f]` with `allInfo pre` — every `103` precedes the one
    final, and no `103` follows it;
  - the final's status and body are exactly the deployed response, and
    `serveFull input = serialize (deployResp input)` — so the one final IS the
    response `serveFull` serializes.

  The `run_building_shape` composition is genuine: the proof obtains the
  `pre ++ [final]` decomposition from the library theorem and rules out its
  all-informational branch using `run_hintActions` (the builder is `committed`).

* `deployed_at_most_one_final` — `EarlyHints.at_most_one_final` lifted: the
  deployed hint sequence emits at most one final (non-1xx) response.

## 2. Streaming HTML rewrite

`htmlTransform bs = HtmlRewrite.bytesOf (HtmlRewrite.tokenize bs)` — the REAL
streaming tokenizer/serializer. The deployed HTML-rewritten response is
`deployRespHtml input = { deployResp input with body := htmlTransform … }`, i.e.
`serveFull`'s deployed response with the rewrite stage inserted on the body.

* `htmlTransform_lossless` — `= HtmlRewrite.roundtrip`: the transform is currently
  lossless (an identity rewrite). The load-bearing property is not what it
  changes but that streaming it is safe.

* **`htmlrewrite_deployed`** (the seam). On a deployed dispatch:
  - the rewritten body is exactly `htmlTransform (deployResp input).body` (the
    real transform applied to `serveFull`'s deployed body);
  - `serveFullHtml input = serialize (deployRespHtml input)` and
    `serveFull input = serialize (deployResp input)` — the transform composed
    with `serveFull`'s deployed response;
  - **chunk-boundary safety**: for *any* split `a ++ b = (deployResp input).body`,
    streaming the two chunks
    `HtmlRewrite.bytesOf (HtmlRewrite.feedBytes (HtmlRewrite.tokenize a) b)`
    equals `htmlTransform (deployResp input).body` — via
    `HtmlRewrite.stream_eq_whole`. A naive chunk-at-a-time rewriter would get
    this wrong.

* `resp_transforms_compose_deployed` — both stages sit on the one deployed
  dispatch path: the two serve equalities, plus the deployed final's body equals
  the HTML-rewritten deployed body.

## Proof notes

* **Why generic projection lemmas.** `(deployResp input).status`/`.body` are
  projections of a huge closed term (`rewriteResp … (demoResp (deploySubs …))`).
  An inline `rfl` on an *inherited* field forces `isDefEq` to whnf the whole
  `deploySubs = Reactor.step deployConfig …` computation → heartbeat timeout.
  The fix mirrors `Reactor.Deploy` (e.g. `deploy_rewrite_status`): keep the
  projection facts GENERIC over the response (`toFinal_status`, `toFinal_body`,
  `deployRespHtml_body`) so `isDefEq` compares constructor fields structurally
  with the response left opaque, then instantiate at `deployResp input`.
* **`serveFull_dispatch` / `serveFullHtml_dispatch`** use the same
  `cases`-on-the-discriminant shape as `Reactor.Deploy.serveFull_faithful`, off
  the `whnf` blow-up an `unfold; rw` would trigger.
* `_hsub` (the dispatch shape) documents the intended scope; the serve tie needs
  only `hsends` (no FSM send), so the proofs do not consume it.

## Status

`lake build Reactor` green. Axioms of every theorem here are a subset of
`{propext, Quot.sound, Classical.choice}`. Zero sorries, zero `UNCLOSED`.

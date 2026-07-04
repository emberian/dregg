/-
Arena.Orb — the deployed orb: a runnable HTTP/1.1 server core over the *proven*
reactor, running the DEPLOYED multi-protocol configuration.

This is the sans-IO core: raw request bytes on stdin → an HTTP/1.1 response on
stdout. `main` runs `Reactor.Deploy.deployStepFull` — whose response component is
definitionally `Reactor.Deploy.servePipelineFull` (`deployStepFull_serves`), the
extensible stage fold over `deployStagesFull` (the gated `deployStages` plus the
two safe pure response-additions: `securityheadersStage` — the real RFC 6797 HSTS
set — and `headerStage`). So the path this binary executes is:

  * `Reactor.step` over `Reactor.Deploy.deployConfig` — the config whose every
    codec lane is the REAL engine: arena HTTP/1.1 parser, H2 engine, TLS
    (`Tls.step` via `TlsWire.wireTls`), WebSocket (frame decode + reassembly via
    `Ws.wireWs`), SOCKS (`Socks.hstep` via `wireSocks`);
  * FSM sends forwarded faithfully; a dispatch runs the stage fold — the REAL
    security gates (INNERMOST-safe order, so a gate short-circuits before the pure
    additions): a route the REAL `Policy.serveDecision` refuses (undeclared surface)
    is answered with a serializer-built 403; a target whose decoded `..` escapes the
    document root (REAL `Route.Path.decodeSegs`) is answered with a serializer-built
    404; every admitted, within-root dispatch is answered by the real application
    router (`App.handle` / `Route.Match.bestMatch`);
  * on the admitted arm the response is enriched by the two byte-driving stages
    (the REAL `SecurityHeaders.render` — HSTS + X-Frame-Options / X-Content-Type-
    Options / Referrer-Policy — and the `Header.run` `Server`/hop-strip stage), then
    the deploy header rewrite runs the REAL `Header.run` (`Lifecycle.stdRewrite` +
    the deploy stamps): `Server: drorb`, `x-upstream:` the backend the REAL proxy LB
    (`Proxy.selectChain`) chose and the REAL DNS parser (`DnsWire.resolve`) resolved,
    `x-corr:` the id the REAL `Trace.process` assigned; the security headers, being
    non-hop and non-`Server`, survive that rewrite (`deployProg_preserves_field`);
  * the observation state advanced by the REAL `Metrics.inc` / `Tap.step`.

Note: repointing `main` from `deployStepIngress` to `deployStepFull` serves the
HTTP/1.1 path through the full stage fold; folding the h2c-preface fork over
`servePipelineFull` (as `deployStepIngress` did over `serveGuarded`) is the noted
follow-on.

The socket, accept loop, and connection lifecycle live in a separate IO shell
(the untrusted environment, validated by testing per the assurance boundary);
this binary is the proven core it drives, one request in, one response out.
-/
import Reactor.Deploy
import Reactor.Ingress

/-- The IO shell for one request: drain stdin, run the deployed pipeline, emit
the response bytes verbatim on stdout; one observability line (the REAL Metrics
counter after this request) goes to stderr, never the response stream.

The pipeline is `Reactor.Deploy.deployStepFull`: the guarded, gated deployed serve
re-expressed as the extensible stage fold (`servePipelineFull` over
`deployStagesFull`), with the two verified pure response-additions folded in.
`servePipeline_agrees` keeps the gated fold byte-equal to the original
`serveGuarded` on every arm; the two additions only enrich the admitted 200. -/
def main : IO Unit := do
  let stdin ← IO.getStdin
  let bytes ← stdin.read 65536
  -- Fork on the HTTP/2 connection preface (h2c prior knowledge) exactly as the
  -- ingress did, so repointing to the full stage fold does not regress h2c: an
  -- h2c-preface input runs the real H2 engine (`serveIngress`), everything else
  -- runs the HTTP/1.1 path through the full ten-stage fold (`deployStepFull2`,
  -- which carries ALL ten byte-drivers: the five gates jwt/ipfilter/rate/cache/
  -- redirect, the traversal/policy gates, and the cors/gzip/htmlrewrite/security/
  -- header transforms).
  let (out, obs) :=
    if Reactor.Ingress.hasH2Preface bytes.toList then
      (Reactor.Ingress.serveIngress bytes.toList, Reactor.Observe.ObsState.init)
    else
      Reactor.Deploy.deployStepFull2 Reactor.Observe.ObsState.init bytes.toList
  let stdout ← IO.getStdout
  stdout.write (ByteArray.mk out.toArray)
  let stderr ← IO.getStderr
  stderr.putStrLn
    s!"orb: {Reactor.Observe.reqCounter}={obs.metrics.counters Reactor.Observe.reqCounter} corrs={obs.corrs.length}"

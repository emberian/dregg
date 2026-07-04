/-
Dataplane — the proven serve exposed with a C ABI for a native host to drive.

`Arena.Orb.main` runs the deployed serve as a one-shot stdin→stdout filter, and
`IoMac` drives that same proven core from a C accept loop with Lean as the
CALLEE of `@[extern]`. This module inverts the direction: it hands the proven
pipeline OUT across the C ABI as an `@[export]` symbol (`drorb_serve`), so a
native host (the Rust dataplane) is the CALLER — it owns the socket and the
accept loop and calls into the proven core for every request.

The handler is byte-identical to the one the shipped binaries run: request bytes
in, the deployed guarded response bytes out, `deployStepIngress` over a fresh
`ObsState.init`. Nothing here knows a socket exists; the host moves the bytes.
-/
import Reactor.Deploy
import Reactor.Ingress
import Reactor.Observe

/-- The proven pipeline as a pure byte function, exported under the C symbol
`drorb_serve`. One request's bytes in, the deployed response bytes out — the
exact serve `Arena.Orb.main` runs: fork on the HTTP/2 connection preface (h2c
prior knowledge) to the real H2 engine (`serveIngress`); everything else runs
the HTTP/1.1 path through the full ten-stage fold (`deployStepFull2`), which
carries all ten byte-drivers — the five gates (jwt/ipfilter/rate/cache/redirect),
the traversal/policy gates, and the cors/gzip/htmlrewrite/security/header
transforms. The observation state is a fresh `ObsState.init` per call. The native
host calls this once per accepted connection; nothing here knows a socket exists. -/
@[export drorb_serve]
def drorbServe (input : ByteArray) : ByteArray :=
  let bytes := input.toList
  let (out, _obs) :=
    if Reactor.Ingress.hasH2Preface bytes then
      (Reactor.Ingress.serveIngress bytes, Reactor.Observe.ObsState.init)
    else
      Reactor.Deploy.deployStepFull2 Reactor.Observe.ObsState.init bytes
  ByteArray.mk out.toArray

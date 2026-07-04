/-
IoMac — a real macOS TCP server that drives the *proven* reactor.

This is the native IO driver: it replaces the one-shot stdin filter of
`Arena.Orb` with a live socket accept loop, but the request-handling core is
*identical and unchanged*. Every connection is answered by exactly the same
proven function the shipped `orb` binary runs — `Reactor.Ingress.deployStepIngress`
— over a freshly-`init`ed observation state. The socket, the accept loop, and
the connection lifecycle live entirely in the untrusted C shell (`ffi/mac_io.c`);
Lean here does two things: declare the `@[extern]` seam, and provide the pure
`ByteArray -> ByteArray` handler that IS the proven pipeline.

The trust boundary is explicit:

  * TRUSTED (untested-but-tested environment): `ffi/mac_io.c` — bind/accept/recv/
    send/close. It never parses or rewrites HTTP; it only moves bytes across the
    seam.
  * PROVEN (sacred, unchanged): `handleConn` calls `deployStepIngress`, whose
    response is `serveIngress` (`deployStepIngress_serves`), which on the HTTP/1.1
    branch is byte-for-byte `Reactor.Deploy.serveGuarded` (`ingress_serves_h1`):
    the REAL Policy 403, the REAL traversal 404, the REAL 200 with
    `x-upstream`/`x-corr`. The socket driver drives it; it does not touch it.
-/
import Reactor.Ingress
import Reactor.Observe

/-- The proven pipeline as a pure byte function. One connection's request bytes
in, the deployed guarded response bytes out — `deployStepIngress` over a fresh
`ObsState.init`, exactly as `Arena.Orb.main` runs it per invocation. The C shell
calls this once per accepted connection; nothing here knows a socket exists. -/
@[export orb_mac_handle]
def handleConn (req : ByteArray) : ByteArray :=
  let (out, _obs) :=
    Reactor.Ingress.deployStepIngress Reactor.Observe.ObsState.init req.toList
  ByteArray.mk out.toArray

/-- The accept loop, in C. Binds `127.0.0.1:port`, and for every connection
applies `handleConn` to the request bytes and writes the result back. Blocks
forever (a server). The whole IO surface of this program is this one extern. -/
@[extern "orb_mac_serve"]
opaque serveLoop (port : UInt16) (handler : ByteArray → ByteArray) : IO Unit

/-- Port from argv[1] (default 8080), then hand control to the C accept loop
with the proven handler. -/
def main (args : List String) : IO Unit := do
  let port : UInt16 :=
    match args.head?.bind String.toNat? with
    | some n => n.toUInt16
    | none   => 8080
  IO.eprintln s!"orb-mac: starting proven-reactor HTTP server on 127.0.0.1:{port}"
  serveLoop port handleConn

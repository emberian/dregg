/-
IoWin — a real Windows TCP server that drives the *proven* reactor.

This is the native IO driver for Windows. It replaces the one-shot stdin filter
of `Arena.Orb` with a live socket accept loop built on Windows I/O Completion
Ports (IOCP) — the native Windows proactor, the counterpart to io_uring on Linux
and kqueue on macOS/BSD. The request-handling core is *identical and unchanged*:
every connection is answered by exactly the same proven function the shipped
`orb` binary runs — `Reactor.Ingress.deployStepIngress` — over a freshly-`init`ed
observation state.

The trust boundary is explicit and small:

  * TRUSTED (the untrusted-but-tested environment): `ffi/win_io.c` — WSAStartup,
    bind, AcceptEx, WSARecv, WSASend, closesocket, driven by an IOCP completion
    loop. It never parses or rewrites HTTP; it only moves bytes across the seam.
    Its only knowledge of a "request" is: read until CRLFCRLF, hand the bytes to
    Lean, write back what Lean returns. Every crossing is documented in that file.
  * PROVEN (sacred, unchanged): `handleConn` calls `deployStepIngress`, whose
    response is `serveIngress` (`deployStepIngress_serves`), which on the HTTP/1.1
    branch is byte-for-byte `Reactor.Deploy.serveGuarded` (`ingress_serves_h1`) —
    the REAL Policy 403, the REAL traversal 404, the REAL 200 with
    `x-upstream`/`x-corr` — and on an h2c preface enters the REAL h2 engine
    (`ingress_h2_dispatch`). The socket driver drives it; it does not touch it.

SCOPE: this driver cannot run in the environment it was authored in (macOS). The
IOCP path in `ffi/win_io.c` is guarded by `#ifdef _WIN32` and compiles only under
a Windows toolchain; on any other host the C symbol is a stub that fails with an
IO error, so this module still typechecks and the `orb-win` exe still *links*
everywhere (verified on macOS). See WINDOWS-IO-README.md.

The single IO effect of this whole program is `serveLoop`, the one `@[extern]`
seam. Nothing in `handleConn` knows a socket exists.
-/
import Reactor.Ingress
import Reactor.Observe

/-- The proven pipeline as a pure byte function. One connection's request bytes
in, the deployed guarded response bytes out — `deployStepIngress` over a fresh
`ObsState.init`, exactly as `Arena.Orb.main` runs it per invocation. The C shell
calls this once per accepted connection; nothing here knows a socket exists.

Also `@[export]`ed under a stable C name so the shell may call it by symbol as
well as through the closure the seam passes it. -/
@[export orb_win_handle]
def handleConn (req : ByteArray) : ByteArray :=
  let (out, _obs) :=
    Reactor.Ingress.deployStepIngress Reactor.Observe.ObsState.init req.toList
  ByteArray.mk out.toArray

/-- The accept loop, in C (`ffi/win_io.c`). Binds `0.0.0.0:port`, brings up an
IOCP, and for every connection applies `handler` to the request bytes and writes
the result back. Blocks forever (it is a server). The whole IO surface of this
program is this one extern. The C side runs an AcceptEx/WSARecv/WSASend IOCP loop
on Windows; on a non-Windows host the symbol is a stub that fails with an IO
error, so this module still builds. -/
@[extern "orb_win_serve"]
opaque serveLoop (port : UInt16) (handler : ByteArray → ByteArray) : IO Unit

/-- Port from argv[1] (default 8080), then hand control to the C accept loop with
the proven handler. -/
def main (args : List String) : IO Unit := do
  let port : UInt16 :=
    match args.head?.bind String.toNat? with
    | some n => n.toUInt16
    | none   => 8080
  IO.eprintln s!"orb-win: starting proven-reactor HTTP server on 0.0.0.0:{port}"
  serveLoop port handleConn

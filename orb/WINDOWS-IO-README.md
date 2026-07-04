# orb-win — the proven reactor as a Windows IOCP TCP server (scaffold)

`orb-win` is the native **Windows** IO driver for the proven HTTP reactor core: a
live TCP accept loop built on **I/O Completion Ports (IOCP)** — the native
Windows proactor — that answers each connection by running the *same* proven
pipeline the shipped `orb` binary runs, `Reactor.Ingress.deployStepIngress`, over
a real socket instead of a one-shot stdin filter. It is the Windows counterpart
to `orb-linux` (io_uring/epoll) and `orb-mac` (BSD sockets).

## Honest scope: what runs vs. what is scaffolded

This driver was authored on **macOS and cannot run here.** Be precise about the
state:

| piece | status in this environment (macOS) |
|---|---|
| `IoWin.lean` (the seam + handler) | **typechecks and compiles** — verified. |
| `orb-win` executable | **builds and links** — verified (links the non-Windows stub). |
| the `@[extern]` wiring | **exercised** — running `orb-win` calls through the seam into `orb_win_serve`; the stub returns its honest IO error, proving the symbol resolves and the closure crosses the boundary. |
| the **IOCP accept loop** (`#ifdef _WIN32` in `ffi/win_io.c`) | **scaffold only** — not compiled and not run here. It compiles under a Windows toolchain; see the BUILD note below. |

So: the Lean side is real and verified on this mac; the C IOCP server body is a
written-but-unbuilt scaffold that needs a Windows box. Nothing about the *proven
core* is scaffolded — `handleConn` is exactly `deployStepIngress ObsState.init`,
identical to what `orb`, `orb-mac`, and `orb-linux` all run.

## The trust boundary

Same split as every other IO driver in this package — the whole point:

| | file | status |
|---|---|---|
| **The untrusted IO shell** | `ffi/win_io.c` | Winsock2 + IOCP: `WSAStartup`/`bind`/`AcceptEx`/`WSARecv`/`WSASend`/`closesocket`, driven by one `GetQueuedCompletionStatus` loop. **Not verified.** It never parses or rewrites HTTP — it only moves bytes across the C↔Lean seam. |
| **The `@[extern]` seam + handler** | `IoWin.lean` | declares `serveLoop` (the extern `orb_win_serve`) and `handleConn : ByteArray → ByteArray`, the pure function that IS the proven pipeline. |
| **The proven core** | `Reactor/Ingress.lean` etc. | **unchanged.** `handleConn` calls `deployStepIngress`; nothing in the core knows a socket exists. |

The seam is one line of coupling: for each completed request the C shell does a
single `lean_apply_1(handler, request_bytes)` (in `orb_run_core`) and writes the
returned bytes back. Every crossing is that one call. The C shell is the
"untrusted-but-tested environment"; the Lean handler is the sacred core it drives.

Because `handleConn` is exactly `deployStepIngress ObsState.init` (the same call
`Arena.Orb.main` makes per invocation), the HTTP/1.1 branch is byte-for-byte
`Reactor.Deploy.serveGuarded` (`ingress_serves_h1`): the REAL Policy-403, the REAL
traversal-404, the REAL 200 with `x-upstream`/`x-corr`; the h2c preface enters the
REAL h2 engine (`ingress_h2_dispatch`). The socket driver drives the proof; it
does not touch it.

## The IOCP design (`ffi/win_io.c`, `#ifdef _WIN32`)

A single-threaded IOCP proactor, structurally the same shape as the io_uring
backend in `linux_io.c`:

- **Bring-up:** `WSAStartup(2.2)` → overlapped listen socket → bind `0.0.0.0:port`
  → `CreateIoCompletionPort` → associate the listener → resolve `AcceptEx` at
  runtime via `WSAIoctl(SIO_GET_EXTENSION_FUNCTION_POINTER)`.
- **Per-op context:** an `orb_ctx` whose first field is the `OVERLAPPED`, so a
  completed `LPOVERLAPPED` casts straight back to the context. `kind` (ACCEPT /
  RECV / SEND) tells the completion loop what a dequeued packet means.
- **Accept:** a small pool of outstanding `AcceptEx` calls (`dwReceiveDataLength=0`
  so a silent client cannot pin an accept). On completion: `SO_UPDATE_ACCEPT_CONTEXT`,
  associate the new socket with the IOCP, re-prime an accept, post the first `WSARecv`.
- **Recv:** accumulate into a growable buffer; when `CRLFCRLF` is seen (or EOF, or
  the 1 MiB `ORB_MAX_REQ` cap), call `orb_run_core` — the one seam crossing — then
  post `WSASend` of the response; otherwise post another `WSARecv` into the tail.
- **Send:** drain the response with repeated `WSASend`, then `closesocket`.
  v1 is one response per connection (no keep-alive).

Refcounting matches the other shells: `handler` is borrowed, `lean_inc` before
`lean_apply_1` (which consumes the closure), `lean_dec(resp)` after; `handler` is
`lean_dec`'d on the loop's exit/error paths.

## Build

### Build-check here (macOS): links the stub, verifies the Lean side

```sh
# 1. compile the shell to an object (compiles to the non-Windows stub on macOS):
./ffi/build-win-io.sh          # produces ffi/win_io.o

# 2. build the exe (links the stub; verifies IoWin.lean typechecks + links):
lake build orb-win
```

The `orb-win` stanza in `lakefile.toml`:

```toml
[[lean_exe]]
name = "orb-win"
root = "IoWin"
moreLinkArgs = ["-Wl,-no_data_const", "ffi/win_io.o"]
```

Running the resulting binary here exercises the seam and hits the honest stub:

```
$ ./.lake/build/bin/orb-win 8080
orb-win: starting proven-reactor HTTP server on 0.0.0.0:8080
uncaught exception: orb_win_serve: this driver is Windows-only (IOCP); build and run it on Windows with MSVC + ws2_32
```

### BUILD note — what a real Windows build needs

The IOCP path only compiles and runs under a Windows toolchain. To produce a
running server:

1. **Toolchain:** MSVC (`cl`) or clang-cl, i.e. a Windows target with the Windows
   SDK headers (`winsock2.h`, `ws2tcpip.h`, `mswsock.h`).
2. **Lean toolchain for Windows:** the same `leanprover/lean4:v4.17.0` installed
   on the Windows host (elan supports Windows), providing `<lean/lean.h>` and the
   runtime import library. Lake will drive the whole build on that host.
3. **Compile the shell** with `_WIN32` naturally defined by the Windows compiler:
   ```
   cl /c /O2 /I "%LEAN_PREFIX%\include" ffi\win_io.c /Fo:ffi\win_io.obj
   ```
   (or the clang-cl equivalent). This activates the `#ifdef _WIN32` IOCP body.
4. **Link libraries:** `ws2_32.lib` (Winsock) and `mswsock.lib` (AcceptEx /
   GetAcceptExSockaddrs). Point the exe's `moreLinkArgs` at the object and libs,
   and **drop** `-Wl,-no_data_const` — that flag is the macOS ld64 `__DATA_CONST`
   workaround and is meaningless to the MSVC linker:
   ```toml
   moreLinkArgs = ["ffi/win_io.obj", "ws2_32.lib", "mswsock.lib"]
   ```
5. **Run:** `orb-win.exe 8080`, then drive it with `curl` over real TCP. Expected
   responses are byte-identical to `orb`/`orb-mac`/`orb-linux` for the same
   requests (same `deployStepIngress`):
   - `/health` → `200 OK`, `Server: drorb`, `x-upstream`, `x-corr`
   - `/nope` → `403 Forbidden` (real `Policy.serveDecision`: undeclared surface)
   - `/../etc/passwd` (curl `--path-as-is`) → `404 Not Found` (real traversal guard)

None of that touches the proven core. It changes only the environment the proof
runs in, which is exactly where untrusted, test-validated code belongs.

## v1 scope and higher-throughput paths

v1 is a **single-threaded IOCP loop**: one completion thread, one response per
connection, then close. What a higher-throughput target needs (all IO-shell
changes; the core stays untouched):

- **Multiple completion threads.** IOCP is built for it: spawn N worker threads
  all blocked on `GetQueuedCompletionStatus` for the same port. `handleConn` is
  pure and re-entrant, so this is a shell-side scaling change only. (`ObsState` is
  per-request `init` here, so there is no shared reactor state to guard; a shared
  observation state would be a separate design decision on the Lean side.)
- **Keep-alive / pipelining.** v1 closes after one response; connection reuse is a
  shell-side loop back to `orb_post_recv` over the same per-request `handleConn`.
- **Body-aware reads.** v1 reads the request *head* (CRLFCRLF); a
  `Content-Length`/chunked-aware read is a shell concern layered on the same seam.
- **RIO (Registered I/O).** For very high connection counts, Winsock RIO reduces
  per-op overhead vs. AcceptEx/WSARecv; again a shell swap, identical bytes to the
  core.

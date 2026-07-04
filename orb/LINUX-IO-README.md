# orb-linux — a native Linux TCP server driving the proven reactor

`orb-linux` makes the formally-verified reactor core *runnable on real Linux
hardware*. It swaps the one-shot stdin filter of `Arena.Orb` for a live socket
accept loop, but the request-handling core is **identical and unchanged**: every
connection is answered by exactly the same proven function the shipped `orb`
binary runs — `Reactor.Ingress.deployStepIngress` — over a freshly-`init`ed
observation state.

## The trust boundary

There are two pieces, and the line between them is the whole point.

| piece | file | status |
|-------|------|--------|
| the IO shell | `ffi/linux_io.c` | **TRUSTED** — untrusted-but-tested C. Every crossing documented. |
| the seam | `IoLinux.lean` | the `@[extern]` declaration + the pure handler |
| the proven core | `Reactor.Ingress.deployStepIngress` | **SACRED** — unchanged, called not modified |

**The IO shell (`ffi/linux_io.c`) knows nothing about HTTP.** It binds, accepts,
reads bytes until CRLFCRLF (or EOF/cap), hands the raw buffer to Lean, and writes
back whatever bytes Lean returns. It never parses a request line, never builds a
response, never rewrites a header. Its entire notion of a "request" is a byte
buffer. That is deliberate: the shell is the tested environment; the semantics
live in the proven core.

**The proven core is reached through one pure function** (`IoLinux.handleConn :
ByteArray → ByteArray`), which is `deployStepIngress` over `ObsState.init`. By the
core's own theorems:

- `deployStepIngress_serves` — what is written is `serveIngress`;
- `ingress_serves_h1` — on a non-preface (HTTP/1.1) input, `serveIngress` is
  **byte-for-byte** `Reactor.Deploy.serveGuarded`: the REAL Policy `403`, the REAL
  traversal `404`, the REAL `200` with `x-upstream` / `x-corr`;
- `ingress_h2_dispatch` — on an `h2c` preface it enters the REAL h2 engine.

The socket driver *drives* the core; it does not *touch* it. The core is compiled
from the same `.lean` sources whether it runs behind stdin (`orb`), a macOS socket
(`orb-mac`), or a Linux socket (`orb-linux`).

## What the C shell does, crossing by crossing

Every FFI crossing in `ffi/linux_io.c` is one of:

1. **into Lean** (`orb_process`): build a `ByteArray` from `(buf, len)` with
   `lean_alloc_sarray(1, len, len)` + `memcpy`; `lean_inc(handler)` (apply
   consumes its function argument); `lean_apply_1(handler, req)` → response
   `ByteArray`; read its bytes with `lean_sarray_cptr` / `lean_sarray_size`;
   `write(2)` them; `lean_dec(resp)`.
2. **out of Lean** (`orb_linux_serve`): entered from `IoLinux.main` with the
   port (unboxed `uint16_t`) and the handler closure; returns
   `lean_io_result_mk_ok(lean_box(0))` on shutdown, or
   `lean_io_result_mk_error(…)` if `bind`/`listen`/backend-init fails.

`handler` is borrowed across the whole loop; each connection `lean_inc`s before
applying so the closure survives. The response object is decref'd after its bytes
are written.

## Backends: io_uring preferred, epoll fallback

Two Linux backends, selected at compile time in `ffi/build-linux-io.sh`:

- **epoll (default).** A level-triggered `epoll(7)` readiness loop, no external
  dependency. Accepts on a non-blocking listener, accumulates each connection's
  request into a per-fd buffer until CRLFCRLF, then runs the proven core and
  writes the response. This is what builds and runs out of the box.
- **io_uring (`ORB_IO_URING=1`).** A `liburing`-based proactor: `prep_accept` /
  `prep_recv` submitted to the ring, completions drive the same `orb_process`.
  Requires `liburing-dev` and `-luring` at link time (add it to the exe's
  `moreLinkArgs`). Not built by default because `liburing` is not installed on
  every host.

The request-completion signal is CRLFCRLF: the proven H1/h2c core is a
head-driven server (GET/HEAD carry no body), fed the head verbatim exactly as
`Arena.Orb` feeds a single 64 KiB stdin chunk. Request bodies are out of scope
for this shell.

On a **non-Linux host** the whole backend is `#ifdef`-guarded out and
`orb_linux_serve` compiles to a stub that returns an IO error — so `IoLinux.lean`
still typechecks, and `orb-linux` still *links* on macOS for a build-check (it
just refuses to serve at runtime).

## Build & run

### On Linux (the real target)

```sh
# 1. build the epoll object (or ORB_IO_URING=1 for io_uring + -luring)
./ffi/build-linux-io.sh

# 2. the orb-linux stanza in lakefile.toml ships with the macOS -no_data_const
#    link flag; lld-ELF rejects that Mach-O-only flag, so drop it on Linux:
sed -i 's#\["-Wl,-no_data_const", "ffi/linux_io.o"\]#["ffi/linux_io.o"]#' lakefile.toml

# 3. build and run
lake build orb-linux
./.lake/build/bin/orb-linux 8080
```

Then, from another shell:

```sh
curl -sv http://127.0.0.1:8080/
```

### On macOS (build-check only)

```sh
./ffi/build-linux-io.sh          # compiles the Linux-only stub object
lake build orb-linux             # links (stub); the exe runs but refuses:
./.lake/build/bin/orb-linux 8080 # => "orb_linux_serve: this driver is Linux-only"
```

`IoLinux.lean` typechecks and `orb-linux` links on macOS; only the *serve*
refuses, because the socket backend is Linux-only.

## Why the object is precompiled

TOML lakefiles cannot compile a C source directly (Lake's TOML schema exposes no
custom C target). So `ffi/build-linux-io.sh` precompiles `ffi/linux_io.c` to
`ffi/linux_io.o` with the system `cc` plus the Lean toolchain's include path (so
`<lean/lean.h>` and the runtime ABI match), and the `orb-linux` stanza links that
object via `moreLinkArgs`. Same pattern as `orb-mac` / `crypto-selftest`.

## Status

- macOS: `IoLinux.lean` typechecks; `ffi/linux_io.c` compiles (stub path);
  `orb-linux` links; the binary runs and honestly refuses (Linux-only).
- Linux (Ubuntu 24, x86_64): built with the epoll backend and served real
  `curl` traffic through the proven core.

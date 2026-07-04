# orb-mac — the proven reactor as a real macOS TCP server

`orb-mac` is the proven HTTP reactor core made **runnable on real hardware**: a
live TCP accept loop on `127.0.0.1` that answers each connection by running the
*same* proven pipeline the shipped `orb` binary runs — `Reactor.Ingress.deployStepIngress`
— over a real socket instead of a one-shot stdin filter.

## What actually runs vs. what is the shell

There are two pieces, and the split is the whole point:

| | file | status |
|---|---|---|
| **The untrusted IO shell** | `ffi/mac_io.c` | plain BSD sockets: `socket`/`bind`/`listen`/`accept`/`recv`/`send`/`close`. Not verified. It never parses or rewrites HTTP — it only moves bytes across the C↔Lean seam. |
| **The `@[extern]` seam + handler** | `IoMac.lean` | declares `serveLoop` (the extern) and `handleConn : ByteArray → ByteArray`, the pure function that IS the proven pipeline. |
| **The proven core** | `Reactor/Ingress.lean` etc. | **unchanged.** `handleConn` calls `deployStepIngress`; nothing in the core knows a socket exists. |

The seam is one line of coupling: for each accepted connection the C shell does a
single `lean_apply_1(handler, request_bytes)` and writes the returned bytes back.
Every crossing is that one call. The C shell is the "untrusted-but-tested
environment"; the Lean handler is the sacred core it drives.

Because `handleConn` is exactly `deployStepIngress ObsState.init` (the same call
`Arena.Orb.main` makes per invocation), the HTTP/1.1 branch is byte-for-byte
`Reactor.Deploy.serveGuarded` (`ingress_serves_h1`): the REAL Policy-403, the
REAL traversal-404, the REAL 200 with `x-upstream`/`x-corr`. The socket driver
drives the proof; it does not touch it.

## Build

```sh
# 1. compile the untrusted C shell to an object (TOML lakefiles can't compile a
#    C source directly, so we precompile and link it via moreLinkArgs):
./ffi/build-mac-io.sh          # produces ffi/mac_io.o

# 2. build the exe:
lake build orb-mac
```

The `orb-mac` stanza in `lakefile.toml`:

```toml
[[lean_exe]]
name = "orb-mac"
root = "IoMac"
moreLinkArgs = ["-Wl,-no_data_const", "ffi/mac_io.o"]
```

(`-Wl,-no_data_const` is the same ld64/`__DATA_CONST` workaround the other exes
in this package use on current macOS.)

## Run

```sh
./.lake/build/bin/orb-mac 8080     # port from argv[1], default 8080
```

On startup it prints to **stderr** (never the response stream):

```
orb-mac: starting proven-reactor HTTP server on 127.0.0.1:8080
orb-mac: listening on 127.0.0.1:8080 (proven reactor over real TCP)
```

## Live curl transcript

Captured on darwin (macOS), `orb-mac 8080` running, driven by real `curl` over a
real TCP socket:

```
$ curl -s -i http://127.0.0.1:8080/health
HTTP/1.1 200 OK
Server: drorb
x-upstream: 1572395042
x-corr: 71.69.84.32.47.104.101.97.108.116.104.32.72.84.84.80.47.49.46.49.13.10...
Content-Length: 2

ok

$ curl -s -i http://127.0.0.1:8080/nope
HTTP/1.1 403 Forbidden
Content-Length: 27

policy: undeclared surface

$ curl -s -i --path-as-is http://127.0.0.1:8080/../etc/passwd
HTTP/1.1 404 Not Found
Content-Length: 18

traversal blocked
```

Status-code summary (`curl -o /dev/null -w '%{http_code}'`):

```
/health        -> 200      (admitted route: real App.handle)
/nope          -> 403      (real Policy.serveDecision: undeclared surface)
/../etc/passwd -> 404      (real Route.Path.decodeSegs: traversal blocked)
```

> `--path-as-is` is required for the traversal case because `curl` otherwise
> collapses `..` client-side; we want the raw `/../etc/passwd` target to reach
> the reactor so the REAL traversal guard is the thing that answers it.

These are the deployed guarded pipeline's responses, byte-identical to what the
stdin-driven `orb` binary produces for the same requests — now delivered over a
kernel TCP socket to an unmodified `curl`.

## v1 scope and the kqueue path

v1 is a **blocking accept loop** (`ffi/mac_io.c`): accept one connection, read
the request head (until `CRLFCRLF`, EOF, or a 1 MiB cap), apply the handler,
write the response, close, repeat. Correctness over throughput — one connection
served at a time, deterministically.

What a higher-throughput target needs (all IO-shell changes; the core stays
untouched):

- **kqueue readiness loop.** Register the listen fd and each accepted fd with
  `kqueue`/`kevent` (`EVFILT_READ`), drive recv/accept off readiness, keep many
  live fds. This changes only *how the shell schedules* recv/accept — the bytes
  handed to `deployStepIngress` are identical.
- **Body-aware reads.** v1 reads the request *head*; the curl GETs carry no body,
  so `CRLFCRLF` is a complete request. A `Content-Length`/chunked-aware read is a
  shell concern layered on the same seam.
- **Keep-alive / pipelining.** v1 closes after one response. Connection reuse is
  a shell-side loop over the same per-request `handleConn` call.

None of these touch the proven core. They change the environment the proof runs
in, which is exactly where untrusted, test-validated code belongs.
```

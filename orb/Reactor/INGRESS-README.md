# Reactor.Ingress — one listener, both protocols (HTTP/1.1 + h2c prior-knowledge)

## What changed

The shipped orb `main` used to drive a single `plainH1` connection: it served
HTTP/1.1 and nothing else. The HTTP/2 engine was installed in `deployConfig`
(`deploy_h2_real`) and even proven runtime-reachable in isolation
(`Reactor.H2Ingress.h2c_runtime_dispatch`), but `main` never *entered* it — the
running binary spoke one protocol.

`Reactor.Ingress` is the front door that speaks both. It inspects the first bytes
of a connection and picks the initial `Proto.Conn` before a single frame is
parsed, then runs the SAME proven reactor over the SAME `deployConfig` from that
connection. `Arena.Orb.main` now runs `Reactor.Ingress.deployStepIngress`.

## The fork (RFC 9113 §3.4, HTTP/2 with prior knowledge)

* `h2Preface` — the 24-octet connection preface
  `PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n`. No HTTP/1.1 request line can begin with it.
* `hasH2Preface input` — exact-prefix test on the first octets.
* `ingressConn input` — `cond (hasH2Preface input) H2Ingress.mkH2c Conn.mkPlain`:
  preface ⇒ the real h2c engine parked in `.plainH2`; otherwise the plain HTTP/1.1
  listener connection `.plainH1`.
* `ingressFeed input` — for h2c the preface is consumed by the discriminator and
  the post-preface bytes (first real frame onward) are fed to the H2 engine; for
  HTTP/1.1 the whole input is the request.
* `ingressSubs input` — `Reactor.step deployConfig` from the *selected* connection.
  Identical to `Deploy.deploySubs` except the initial `Proto.Conn` and fed bytes
  are chosen rather than hardwired to `mkPlain`.
* `serveIngress` / `deployStepIngress` — the guarded serve and observed step over
  the selected reactor run; the function `main` runs.

## Seam theorem — `ingress_selects_protocol`

Stated over the bytes `main` reads:

* **H1 branch** (`ingress_serves_h1`): a non-preface input runs the reactor from
  `Proto.Conn.mkPlain`, and `serveIngress input = Deploy.serveGuarded input`
  *definitionally* — every guarded seam (Policy 403, traversal 404, the 200 with
  `x-upstream`/`x-corr`) carries over byte-for-byte, no regression.
* **H2 branch** (`ingress_h2_dispatch`): a preface-led input whose post-preface
  bytes are a well-formed HEADERS frame runs the reactor from `H2Ingress.mkH2c`
  (the real `h2Feed` engine) and emits exactly
  `[dispatch (requestOfDecoded d), recycleBuffer 0]` — the REAL `h2FeedFn`
  (frame decode → HPACK arena decode → per-stream FSM) executed, via
  `H2Ingress.h2c_runtime_dispatch`. `ingress_h2_serves` carries that dispatch on
  into the guarded serve.

`#print axioms ingress_selects_protocol` = `{propext, Classical.choice,
Quot.sound}`. Zero sorries. `lake build orb` green.

## Runtime verification (the shipped `.lake/build/bin/orb`)

HTTP/1.1 — the request line is parsed by the arena parser:

```
$ printf 'GET /health HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 200 OK
Server: drorb
x-upstream: 1572395042
x-corr: 71.69.84.32.47.104.101.97.108.116.104.…
Content-Length: 2

ok

$ printf 'GET /static/app.js HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 200 OK …                       # declared surface admitted

$ printf 'GET / HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 403 Forbidden … policy: undeclared surface

$ printf 'GET /../etc/passwd HTTP/1.1\r\nHost: x\r\n\r\n' | orb
HTTP/1.1 404 Not Found … traversal blocked
```

HTTP/2 (h2c prior-knowledge) — the request is decoded by the real HPACK/frame
engine. Preface + one HEADERS frame (stream 1, `END_STREAM|END_HEADERS`, HPACK
`82 84` = indexed static `:method: GET`, `:path: /`):

```
$ printf 'PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n\x00\x00\x02\x01\x05\x00\x00\x00\x01\x82\x84' | orb
HTTP/1.1 403 Forbidden
Content-Length: 27

policy: undeclared surface
```

The 403 is the **dispatch signal**: the H2 engine decoded `GET /`, dispatched it,
and the guarded pipeline ran the REAL Policy gate (target `/` is an undeclared
surface). Compare the preface-only control (no frame ⇒ no dispatch):

```
$ printf 'PRI * HTTP/2.0\r\n\r\nSM\r\n\r\n' | orb
HTTP/1.1 400 Bad Request … malformed request head
```

**Cross-protocol parity.** The exact same request `GET /`, decoded by two entirely
different codecs — the HTTP/1.1 arena parser and the HTTP/2 HPACK/frame decoder —
lands on the same guarded gate and produces byte-identical `403 policy: undeclared
surface` responses. One binary, two protocols, one serving pipeline.

## Files

* `Reactor/Ingress.lean` — the dispatcher, serve, step, and seam theorems (new).
* `Arena/Orb.lean` — `main` repointed to `Reactor.Ingress.deployStepIngress`.
* `Reactor.lean` — imports `Reactor.Ingress`.

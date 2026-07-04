# BODY-WIRE — the real Body reader wired into the recv boundary

## The request-smuggling hazard

`Proto.Step.h1Loop` (in `Proto/Step.lean`) is the HTTP/1.1 keep-alive /
pipelining loop. On a parsed head it does:

```
| .request n req keepAlive =>
  if keepAlive then
    let r := h1Loop cfg fuel (buf.drop n)      -- n = HEAD length only
    { residual := r.residual, outs := .dispatch req :: r.outs, ... }
```

`n` is the number of octets the **head** parse consumed. It does **not** include
the message body. So for a `POST` with a `Content-Length` (or
`Transfer-Encoding: chunked`) body, `buf.drop n` still begins with the body
octets, and the next loop turn re-parses **the body as a fresh pipelined
request** — a request-smuggling hole.

## Wiring the real Body reader at the boundary

New file `Reactor/Body.lean` (imported from `Reactor.lean`). It reads the body
framing off the parsed `Proto.Request` head and drives the **real** `Body`
library readers over the residual bytes to consume exactly the body, then reports
where the next request must begin — which is past the body.

It is a wiring into the running reactor, not a standalone model:

- `framingOf : Proto.Request → Framing` reads `Content-Length` / `Transfer-Encoding:
  chunked` off the head the FSM actually parsed (RFC 7230: chunked wins over
  content-length).
- `advance : Proto.Request → Bytes → Advance` drives the real readers:
  - content-length `n`: `Body.ContentLength.Reader.init n |>.feed residual`, then
    reads `.complete` / `.delivered`;
  - chunked: `Body.Chunked.decodeStream residual`.
- `recvNextStart : Bytes → Option Bytes` parses the head with the arena-backed
  `Reactor.Config.demoConfig.h1Parse` (the *same* concrete parser the connection
  FSM runs, proven in `Reactor.Config`), then `advance`s past the body. The
  result is the byte offset where the next request's head parse must begin.

## Seam theorems (all `lake`-accepted, zero sorries)

Axioms: each depends only on `{propext, Quot.sound}` — a strict subset of the
allowed `{propext, Quot.sound, Classical.choice}` (no choice used).

- **`body_bytes_conserved`** (content-length). If `framingOf req = .length n` and
  `n ≤ residual.length`, then
  `advance req residual = .body (residual.take n) n (residual.drop n)` and
  `residual.take n ++ residual.drop n = residual`. The body is exactly the
  length-`n` prefix, the next message is exactly the remainder, nothing leaks
  either way. Composes `Body.ContentLength.complete_delivers_prefix`.

- **`body_bytes_conserved_chunked`** (chunked). If `framingOf req = .chunked` and
  the residual is a well-formed `encodeStream chunks` (non-empty chunks within
  `maxChunkSize`), then
  `advance req (encodeStream chunks) = .body chunks.flatten (encodeStream chunks).length []`.
  The decoded body is exactly the in-order chunk-data concatenation, the consumed
  octets are exactly the whole encoded stream, and the next message begins right
  after the terminal chunk — no framing octet (size digits, CRLFs, terminal)
  leaks into the body. Composes `Body.Chunked.decodeStream_encodeStream`.

- **`body_not_reparsed`** (the anti-smuggling wiring). If the real
  `demoConfig.h1Parse input = .request consumed req _`, `framingOf req = .length n`,
  and the body is present, then
  `recvNextStart input = some (input.drop (consumed + n))`. The next request's
  head parse starts at `consumed + n` — **past** the body. The buggy loop starts
  at `consumed` (i.e. at the first body byte). This composes `Reactor.Config`
  (the concrete parser) with `Body.ContentLength` (the reader) via
  `body_bytes_conserved`.

## Scope / integration note

`Reactor/Body.lean` supplies the verified boundary component and the
`body_not_reparsed` theorem the pipelining loop must satisfy: the drop applied
between pipelined requests must be `consumed + bodyLen` (via `recvNextStart` /
`advance`), not `consumed`. Threading `advance` into `h1Loop`'s recursion — so the
FSM's own residual advances past the body — is the integration edit in
`Proto/Step.lean`; the seam it must uphold is proven here.

The chunked seam matches the `Body.Chunked` library's scope: chunk extensions and
trailers are excluded, and the chunked conservation theorem is stated for a
residual that is exactly a well-formed `encodeStream` (a pipelined tail after the
chunked terminal is a straightforward tail-generalisation of
`decodeStream_encodeStream`).

## Build

```
lake build Reactor        # green (27/28 built; Reactor.Body among them)
```

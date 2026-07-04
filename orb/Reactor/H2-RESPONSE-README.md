# H2-RESPONSE — the full-duplex HTTP/2 path

`Reactor/H2Response.lean`. Builds clean (`lake build ReactorH2Response`), zero
sorries, axioms `{propext, Quot.sound}` (a strict subset of the permitted set —
no `Classical.choice`, no `sorryAx`, no `ofReduceBool`).

## Why an H2 response path

The request side speaks real HTTP/2: an h2c HEADERS frame is decoded by the real
H2 engine — real frame decode (`H2.decode`), real HPACK arena decode
(`H2.Hpack.decodeHeaderBlock`), per-stream FSM — and dispatched
(`Reactor.H2Ingress.h2c_runtime_dispatch`). The H1 serializer
(`Reactor.Serialize.serialize`) renders `HTTP/1.1 <status> <reason> CRLF …`; on
its own it would hand a client that spoke HTTP/2 on the way in HTTP/1.1 bytes on
the way out.

This file provides the real H2 response path: a `Reactor.Response` (the value the
app layer produces — `Reactor.App.handle` → `responseOfHandler`) is encoded as
**real HTTP/2 frames** — a HEADERS frame carrying an HPACK-encoded `:status` (+
headers) followed by a DATA frame carrying the body — through the same H2
machinery the decoder round-trips against.

## What is built

* `encodeStatusField` / `encodeHeaderBlock` — the HPACK encoder (RFC 7541), the
  inverse of `H2.Hpack.decodeOneField`. A `:status` for a static-table code
  (200, 204, 206, 304, 400, 404, 500) is a single **indexed** octet
  (`0x80 ||| index`); other codes and all regular headers are literal fields
  (§6.2.2).
* `encodeHeadersFrame` — a real HTTP/2 HEADERS frame (RFC 9113 §6.2): the 9-octet
  frame header (`u24 length | 0x01 type | flags | u31 stream-id`, the real
  `Reactor.H2.u24`/`u31`) then the HPACK block. `END_HEADERS` set; `END_STREAM`
  clear when a DATA frame follows.
* `encodeResponse` — HEADERS (END_STREAM clear) ++ DATA (END_STREAM set, the real
  `Reactor.H2.encodeDataFrame`): a complete HTTP/2 response for one request.
* `decodeResponseFrames` / `decodeResponse` — the inverses over the **real**
  decoders (`H2.decode`, `H2.Hpack.decodeHeaderBlock`, arena `Store.resolve`).

## The theorem — `h2_response_roundtrip`

```
decodeResponseFrames (encodeResponse sid resp)
  = some (encodeHeaderBlock resp.status resp.headers, resp.body)
```

for every response whose HPACK block and body fit the advertised max frame size,
and every stream id `< 2^31`. The real H2 frame decoder, applied to the encoded
response, recovers **byte-for-byte** the HPACK header block that encodes the
status + headers, and **byte-for-byte** the body. This constrains meaning, not
bounds or totality: the encoded H2 response decodes back to exactly what it
encoded.

It rests on the genuine frame-layer content, all proven and general:

* `parseHeader_encoded` — `u24`/`u31` are inverse to the real `H2.parseHeader`:
  an encoded 9-octet header parses back to the exact 24-bit length, type/flags,
  and 31-bit stream id (reserved bit clear).
* `decode_headersFrame` / `decode_dataFrame` — an encoded HEADERS/DATA frame
  decodes, through the real `H2.decode`, back to exactly its frame
  (`.headers sid false true block` / `.data sid true body`), consuming exactly
  `9 + length` octets — general over the payload, stream id, and length.

The `:status` encode side is pinned to the RFC static table by
`encodeStatusField_200` / `encodeStatusField_404`: the emitted indexed octet is
exactly HPACK static index 8 / 13, whose entry is `:status: 200` / `:status: 404`.

## The execution round-trips — `#guard`

The `:status` **decode** re-derivation runs through `H2.Hpack.decodeHeaderBlock`
and `Store.resolve`, which involve `String.toUTF8`. `toUTF8` does not
kernel-reduce (and Lean core ships no `toUTF8` injectivity/round-trip lemma), so
the HPACK-decode semantic recovery is demonstrated by **execution** — the same
standard the `H2Ingress` request path uses (its `#guard` drives
`decodeHeaderBlock`; its theorem `h2c_runtime_dispatch` takes the HPACK decode as
a hypothesis). Three kernel-evaluated `#guard`s force the whole engine on real
values:

1. `decodeResponse (encodeResponse 1 demoResp) = some (natToDec 200, demoBody)`
   — a real app-layer `Response` (static 200), encoded and decoded back through
   the real `H2.decode` + `decodeHeaderBlock` + `Store.resolve`, recovers status
   and body exactly.
2. status `418` (the **literal** `:status` encoder path, not a static entry) +
   body, round-tripped through the real engine.
3. **The full duplex loop**: `GET /health` routed by the real application router
   (`Reactor.App.handle` over `Reactor.App.demoApp`) → the `200 / "ok"` response
   → encoded as real H2 frames → decoded back through the real engine to exactly
   `200 / "ok"`.

Request in over HTTP/2 (`H2Ingress`), response out over HTTP/2 (this file): the
H2 path serves real traffic in both directions.

## Verify

```
lake build ReactorH2Response      # builds Reactor.H2Response; the #guards run at elaboration
lake env lean Reactor/H2Response.lean
```

Registered as its own `lean_lib ReactorH2Response` in `lakefile.toml` (appended).

# Reactor.Serialize — a proven HTTP/1.1 response serializer

`Reactor/Serialize.lean` renders a response head and body onto the wire as

```
HTTP/1.1 SP status SP reason CRLF (name ": " value CRLF)* CRLF body
```

Bytes are `List UInt8`; `CRLF = [13, 10]`.

## Model

- `Response` — the public model: `status : Nat`, `reason : Bytes`,
  `headers : List (Bytes × Bytes)`, `body : Bytes`. It has **no**
  `Content-Length` field: length framing is not a caller input.
- `Wire` — the internal record the serializer builds. Its `contentLength : Nat`
  field is fixed to `body.length` by `build`, and the emitted `Content-Length`
  header value is `natToDec contentLength`. So the framing length is correct by
  construction, not by a caller's promise.
- `serialize : Response → Bytes = serializeWire ∘ build`.

Helper constructors for other lanes:
- `ok200 (body) : Response` — `200 OK`, no caller headers.
- `error4xx (code) (reason) (body) : Response` — explicit status/reason/body.

Named components used by the theorems:
- `statusLineOf resp = HTTP/1.1 SP status SP reason` (no trailing CRLF).
- `headerBlockOf resp` = header lines `name ": " value` joined by CRLF, **no**
  trailing CRLF, with the derived `Content-Length` line appended last.

## Theorems (all `lake`-accepted, zero `sorry`)

1. `serialize_content_length (resp) : (build resp).contentLength = resp.body.length`
   — the builder pins the content length to the body length. Companion
   `content_length_header_present` shows `(clName, natToDec body.length)` is in
   the wire header list.
2. `serialize_framing (resp) : serialize resp = statusLineOf resp ++ CRLF ++ headerBlockOf resp ++ CRLF ++ CRLF ++ resp.body`
   — append-structure theorem: the body occurs once, at the very end, after the
   blank-line separator (`CRLF ++ CRLF`).
3. `serialize_body_suffix (resp) : resp.body <:+ serialize resp`
   — the body is a suffix; nothing is emitted after it.
4. `serialize_total (resp)` — `serialize` is a plain (total) `def`; no response
   is a stuck state.

## Axiom footprint

`#print axioms`: `serialize_content_length` depends on no axioms; the others
depend only on `[propext, Quot.sound]`. All within the permitted subset
`{propext, Quot.sound, Classical.choice}`; no `Classical.choice`, no `sorry`.

## Wiring

`Reactor/Serialize.lean` imports only `Proto.Basic`; its import is appended to
`Reactor.lean`. `lake build Reactor` is green.

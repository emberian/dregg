# Reactor.Serve — the proven response path

`serve : Bytes → Bytes` is a single-request **test view** over the proven
reactor. It exists to close the audit finding that the demo's *response half* was
unproven `s!`-interpolation glue: the request was parsed by model code whose
properties are theorems, but the response bytes were hand-built strings.

## What it does

```
serve input
  = serialize (respOf (Reactor.step demoConfig (active mkPlain) (recvInto 0 input)).2)
```

1. **Wrap** the input bytes as one completion event `RingEvent.recvInto 0 input`
   — a recv completion whose buffer contents are already materialized (the
   copy-once altitude of `Reactor.Contract`).
2. **Step** the proven reactor: `Reactor.step demoConfig (active mkPlain) event`.
   Inside, `Proto.step` parses with `demoConfig.h1Parse`, which is the
   arena-backed parser (`Reactor.Config.h1ParseFn`) proven to carry the resolved
   request head byte-for-byte (`Reactor.Config.h1Parse_complete_content`). The FSM
   emits `Output`s; the reactor translates them to `RingSubmission`s.
3. **Fold** the submissions into one `Response` value (`respOf`) and hand it to
   the proven serializer `Reactor.serialize`.

The response bytes are therefore produced by the **proven serializer** from the
**proven parse** via the **proven reactor step**. No `s!`-interpolation appears on
the response path.

## Submission → response mapping (`respOf`)

Priority mirrors the reactor's own output order:

| first relevant submission | response |
| --- | --- |
| `dispatch req` (good path) | `ok200` whose body reflects the resolved `req.method` / `req.target` |
| `closeSock` (error / non-keep-alive close) | serializer-built `4xx` |
| `submitSend _` (a canned reject/oversize/error the reactor emitted) | serializer-built `4xx` |
| no output | serializer-built `4xx` |

Note the error path **rebuilds** the `4xx` through the proven serializer rather
than forwarding the reactor's canned bytes — so *every* response byte is
`serialize resp` for a `Response` value, keeping the whole response path inside
proven-serializer territory. (This is a deliberate strengthening over a literal
"forward the canned send" mapping, which would reintroduce non-serializer bytes on
the response path and break the framing theorem below.)

## Theorems (all `lake`-accepted, axioms ⊆ {propext, Quot.sound})

- **`serve_wf`** — end-to-end well-formedness. For *any* input, `serve input`
  decomposes as `statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body`, with
  the body once at the end. This is the serializer's `serialize_framing` lifted
  through the reactor: the response half is now a theorem.
- **`serve_is_serialize`** — `serve input = serialize (respFor input)`; the
  response is produced no other way.
- **`serve_content_length`** — the emitted `Content-Length` is `natToDec` of the
  actual body length, correct by construction (not a caller promise).
- **`serve_total`** — `serve` is a plain total `def`; no input is a stuck state.

## Runnable check (`orb` exe)

`Arena.Orb` is the IO shell: it drains stdin, runs `Reactor.serve`, and writes the
response bytes verbatim to stdout. Build with `lake build orb`.

```
$ printf 'GET /orb/status HTTP/1.1\r\nHost: dragons.example\r\n\r\n' | orb
HTTP/1.1 200 OK
Content-Length: 31

you asked for: GET /orb/status

$ printf 'NOT-A-REQUEST-LINE\r\n\r\n' | orb
HTTP/1.1 400 Bad Request
Content-Length: 23

malformed request head
```

The `200` body reflects the parsed method (`GET`) and target (`/orb/status`); a
malformed request head yields a `400`. Both responses are `serialize resp` values,
so both satisfy `serve_wf`.

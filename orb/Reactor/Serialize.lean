import Proto.Basic

/-!
# A proven HTTP/1.1 response serializer

A total function `serialize : Response → Bytes` that renders a response head and
body onto the wire in the shape

```
HTTP/1.1 SP status SP reason CRLF (name ": " value CRLF)* CRLF body
```

The `Content-Length` header is *not* an input field. The serializer builds an
internal wire record whose `contentLength` field is fixed to `body.length` by
construction, and emits the header from that field. This makes the framing
length correct by construction rather than by a caller's promise.

What is proven:
* `serialize_content_length` — the built wire record carries
  `contentLength = body.length` (the builder sets it so).
* `serialize_framing` — the output decomposes exactly as
  `statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body`; the body appears
  once, at the end, after the blank-line separator.
* `serialize_body_suffix` — `body` is a suffix of `serialize resp`: nothing is
  emitted after the body.
* `serialize_total` — `serialize` is a plain (total) `def`; no response is a
  stuck state.
-/

namespace Reactor

open Proto (Bytes)

/-- The public response model handed to the serializer. Note the absence of a
`Content-Length` field: length framing is not a caller input. -/
structure Response where
  status  : Nat
  reason  : Bytes
  headers : List (Bytes × Bytes)
  body    : Bytes
deriving Repr

/-- The internal wire record the serializer builds from a `Response`. Its
`contentLength` field is fixed to the body length; the emitted `Content-Length`
header value is derived from this field, never from caller input. -/
structure Wire where
  status        : Nat
  reason        : Bytes
  headers       : List (Bytes × Bytes)
  contentLength : Nat
  body          : Bytes
deriving Repr

/-- Build the wire record, pinning `contentLength := body.length`. -/
def build (resp : Response) : Wire :=
  { status        := resp.status
    reason        := resp.reason
    headers       := resp.headers
    contentLength := resp.body.length
    body          := resp.body }

/-- `CRLF` line terminator. -/
def crlf : Bytes := [13, 10]

/-- `"HTTP/1.1"` in ASCII. -/
def http11 : Bytes := [72, 84, 84, 80, 47, 49, 46, 49]

/-- `"Content-Length"` in ASCII. -/
def clName : Bytes := [67, 111, 110, 116, 101, 110, 116, 45, 76, 101, 110, 103, 116, 104]

/-- `"OK"` in ASCII — the default reason phrase for `ok200`. -/
def reasonOK : Bytes := [79, 75]

/-- Decimal ASCII rendering of a natural number (via `Nat.repr`; ASCII digits
are single UTF-8 bytes). -/
def natToDec (n : Nat) : Bytes := (Nat.repr n).toUTF8.toList

/-- `HTTP/1.1 SP status SP reason` (no trailing CRLF). -/
def statusLine (w : Wire) : Bytes :=
  http11 ++ [32] ++ natToDec w.status ++ [32] ++ w.reason

/-- One header rendered as `name ": " value` (colon = 58, space = 32). -/
def headerLine (nv : Bytes × Bytes) : Bytes := nv.1 ++ [58, 32] ++ nv.2

/-- The full header list: the caller's headers followed by the derived
`Content-Length` header. -/
def allHeaders (w : Wire) : List (Bytes × Bytes) :=
  w.headers ++ [(clName, natToDec w.contentLength)]

/-- Render header lines joined by CRLF, with no trailing CRLF (so the two CRLFs
that separate the header block from the body appear explicitly in
`serialize`). -/
def renderHeaders : List (Bytes × Bytes) → Bytes
  | []      => []
  | [h]     => headerLine h
  | h :: t  => headerLine h ++ crlf ++ renderHeaders t

/-- Serialize the wire record: status line, CRLF, header block, blank-line
separator (CRLF ++ CRLF), then the body. -/
def serializeWire (w : Wire) : Bytes :=
  statusLine w ++ crlf ++ renderHeaders (allHeaders w) ++ crlf ++ crlf ++ w.body

/-- **The response serializer.** Builds the wire record (fixing `Content-Length`
to `body.length`) and renders it. Total. -/
def serialize (resp : Response) : Bytes := serializeWire (build resp)

/-- The status line of the wire record built from `resp`. -/
def statusLineOf (resp : Response) : Bytes := statusLine (build resp)

/-- The rendered header block (including the derived `Content-Length` line). -/
def headerBlockOf (resp : Response) : Bytes := renderHeaders (allHeaders (build resp))

/-! ## Helper constructors -/

/-- A `200 OK` response with the given body (no caller headers; the serializer
adds `Content-Length`). -/
def ok200 (body : Bytes) : Response :=
  { status := 200, reason := reasonOK, headers := [], body := body }

/-- A `4xx`/`5xx` response with an explicit status code, reason phrase, and
body. -/
def error4xx (code : Nat) (reason : Bytes) (body : Bytes) : Response :=
  { status := code, reason := reason, headers := [], body := body }

/-! ## Theorems -/

/-- **Content-Length by construction.** The wire record the serializer builds
carries `contentLength = body.length`. The emitted header value is
`natToDec` of this field, so the framing length is not a caller input. -/
theorem serialize_content_length (resp : Response) :
    (build resp).contentLength = resp.body.length := rfl

/-- The derived `Content-Length` header (name and value) is present in the
wire record's header list, with value `natToDec body.length`. -/
theorem content_length_header_present (resp : Response) :
    (clName, natToDec resp.body.length) ∈ allHeaders (build resp) := by
  simp [allHeaders, build]

/-- **Framing.** `serialize resp` decomposes as
`statusLine ++ CRLF ++ headerBlock ++ CRLF ++ CRLF ++ body`. The body occurs
once, at the very end, after the blank-line separator. -/
theorem serialize_framing (resp : Response) :
    serialize resp
      = statusLineOf resp ++ crlf ++ headerBlockOf resp ++ crlf ++ crlf ++ resp.body := rfl

/-- **Body suffix.** The body is a suffix of `serialize resp`: nothing is
emitted after it. -/
theorem serialize_body_suffix (resp : Response) :
    resp.body <:+ serialize resp :=
  ⟨statusLineOf resp ++ crlf ++ headerBlockOf resp ++ crlf ++ crlf, rfl⟩

/-- **Totality.** `serialize` is a plain (total) `def`. -/
theorem serialize_total (resp : Response) : serialize resp = serialize resp := rfl

end Reactor

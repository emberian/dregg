import Proto.Basic
import Proto.Step
import Arena.Parse
import Reactor.Serialize
import Reactor.H2

/-!
# Reactor.Config — wiring the real arena parser into the connection FSM

On its own, `Proto.Config.h1Parse` is a bare abstract field: every FSM
theorem holds "for all codecs," but without a *concrete* parser plugged in,
nothing proves the real parsed bytes reach the dispatch layer. This file closes
that gap. It instantiates `h1Parse` with the proven-total arena parser
(`Arena.Parse.parse`) through an adapter that resolves the arena's view entries
back to their bytes via the proven-total `Store.resolve` — the method, target,
version, and header name/value pairs of a `complete` parse flow through to
`Proto.Request`, byte-for-byte, not discarded.

The load-bearing obligation is `h1Parse_complete_content`: on a `complete` arena
parse the adapter yields `ParseOutcome.request` whose `Request` fields are
*exactly* the resolved arena entries. A degenerate adapter that returned an empty
`Request` (a "bare id") would fail this theorem.
-/

namespace Reactor
namespace Config

open Proto (Bytes Request ParseOutcome Config TlsConn H2Conn WsCodec WsFrame
  HsOut PrefixOut SocksOut WsOut H2Event SocksPhase)

/-- Bytes of an ASCII/UTF-8 string literal (for canned responses and header
comparisons). Computable; used only for fixed literals. -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## The adapter: arena parse → FSM parse outcome -/

/-- Resolve one arena view entry to its bytes through the proven-total
`Store.resolve`. On a `complete` parse every stored entry is in-bounds
(`parse_wf` + `resolve_total`), so the `none` arm is dead for the entries a
`complete` outcome carries; `resolve` is total-as-`Option`, so the match is
still spelled. Bytes, not a `String` — this stays off the UTF-8 `Option`. -/
def resolveBytes (s : Arena.Store) (e : Arena.Entry) : Bytes :=
  match s.resolve e with
  | some b => b.toList
  | none => []

/-- The `Proto.Request` a `complete` arena parse denotes: each head field is the
byte range the arena entry addresses, read back through `resolveBytes`. This is
the single point that fills `Request.{method,target,version,headers}` — the
theorem and the adapter both reference it, so they cannot drift. -/
def protoReqOf (req : Arena.Parse.Request) : Request :=
  { method  := resolveBytes req.store req.method
    target  := resolveBytes req.store req.target
    version := resolveBytes req.store req.version
    headers := req.headers.map fun h =>
      (resolveBytes req.store h.name, resolveBytes req.store h.value) }

/-- Keep-alive derivation from the resolved headers. Header names are canonical
(lowercase) out of the arena, so we compare against the lowercase literal.
Default `true` (HTTP/1.1 persistent connections); an explicit
`Connection: close` turns it off. -/
def deriveKeepAlive (headers : List (Bytes × Bytes)) : Bool :=
  match headers.find? (fun h => h.1 == strBytes "connection") with
  | some (_, v) => v != strBytes "close"
  | none => true

/-- The adapter. A `complete` arena parse becomes a dispatchable
`ParseOutcome.request` carrying the resolved head and the arena's `consumed`
count; `incomplete` maps through; a typed arena error becomes `ParseOutcome.error`
(the FSM answers it from `Config.errorResponse`, the canned 400 below, and
closes). -/
def arenaToProto : Arena.Parse.Outcome → ParseOutcome
  | .complete req =>
    let r := protoReqOf req
    .request req.consumed r (deriveKeepAlive r.headers)
  | .incomplete => .incomplete
  | .error _ _ => .error

/-- `h1Parse` proper: parse with the arena parser (default header cap), then
adapt. (`Arena.Parse.Bytes` and `Proto.Bytes` are both `List UInt8`.) -/
def h1ParseFn (buf : Bytes) : ParseOutcome :=
  arenaToProto (Arena.Parse.parse buf)

/-! ## The concrete config -/

/-- Canned 400-class response for a malformed request head — built by the proven
serializer, so its bytes carry `serialize_framing` (they are `serialize` of a
known `Response`, not an opaque literal). When the FSM emits this, `serve`
forwards it faithfully and its framing is a theorem. -/
def badRequest400 : Bytes :=
  serialize (error4xx 400 (strBytes "Bad Request") [])

/-- Canned 431-class response for an oversized request head — serializer-built,
same discipline as `badRequest400`. -/
def oversize431 : Bytes :=
  serialize (error4xx 431 (strBytes "Request Header Fields Too Large") [])

/-- A concrete `Proto.Config` wiring the real arena parser as `h1Parse`, with
reasonable caps and canned responses. The remaining codec fields (TLS, HTTP/2,
WebSocket, SOCKS, PROXY-prefix) are placeholder totals — this config is the
HTTP/1.1 plaintext lane the arena parser drives; the other lanes are stubbed to
inert/refusing behavior and are outside this config's scope. -/
def demoConfig : Config where
  maxHeaderBytes := 65536
  maxPrefixBytes := 4096
  errorResponse := badRequest400
  oversizeResponse := oversize431
  wsCloseFrame := [0x88, 0x00]
  socksConnectReply := [0x05, 0x00, 0x00, 0x01, 0, 0, 0, 0, 0, 0]
  h1Parse := h1ParseFn
  prefixParse := fun _ => .error
  hsFeed := fun _ _ => .fail
  tlsRecv := fun _ _ => none
  tlsSend := fun tc _ => (tc, [])
  h2Init := Reactor.H2.h2InitVal
  h2Feed := Reactor.H2.h2FeedFn
  h2Send := Reactor.H2.h2SendFn
  wsFeed := fun codec _ => { codec := codec, frames := [], closeReceived := false }
  wsEncode := fun _ => []
  socksFeed := fun _ _ => .fail

/-- `demoConfig`'s `h1Parse` is exactly the arena-backed parser. -/
theorem demoConfig_h1Parse : demoConfig.h1Parse = h1ParseFn := rfl

/-! ## The parsed-content theorem -/

/-- **The real parsed bytes flow through.** When the arena parser reports
`complete req`, `h1ParseFn` returns `ParseOutcome.request` whose `Request` head
fields are *exactly* the arena entries resolved through the proven-total
`Store.resolve` — nothing discarded, nothing invented. A bare-id adapter (empty
`Request`) would fail the `method`/`target`/`version` equalities. -/
theorem h1Parse_complete_content (buf : Bytes) (req : Arena.Parse.Request)
    (h : Arena.Parse.parse buf = .complete req) :
    h1ParseFn buf = .request req.consumed (protoReqOf req)
        (deriveKeepAlive (protoReqOf req).headers)
      ∧ (protoReqOf req).method  = resolveBytes req.store req.method
      ∧ (protoReqOf req).target  = resolveBytes req.store req.target
      ∧ (protoReqOf req).version = resolveBytes req.store req.version := by
  refine ⟨?_, rfl, rfl, rfl⟩
  show arenaToProto (Arena.Parse.parse buf) = _
  rw [h]
  rfl

/-- The same content, stated against `demoConfig.h1Parse` directly (the field
the FSM actually calls). -/
theorem demoConfig_complete_content (buf : Bytes) (req : Arena.Parse.Request)
    (h : Arena.Parse.parse buf = .complete req) :
    demoConfig.h1Parse buf = .request req.consumed (protoReqOf req)
      (deriveKeepAlive (protoReqOf req).headers) :=
  (h1Parse_complete_content buf req h).1

end Config
end Reactor

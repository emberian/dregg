import Body.ContentLength
import Body.Chunked
import Reactor.Config
import Reactor.Bridge

/-!
# Reactor.Body — wiring the real Body reader into the HTTP/1.1 recv boundary

The keep-alive/pipelining loop (`Proto.Step.h1Loop`) has a request-smuggling
hazard: after the head parse reports `.request n req keepAlive`, the loop
recurses on `buf.drop n`, where `n` is *only the head length*. A `POST`
carrying a `Content-Length` (or `Transfer-Encoding: chunked`) body leaves those
body octets sitting right after the head, so the next loop turn re-parses the
**body as a fresh request** — a smuggled request.

The fix is to consume the framed body before deciding where the next request
begins. This file wires the *real* `Body` readers (`Body.ContentLength`,
`Body.Chunked`) into the reactor: it reads the framing off the parsed
`Proto.Request` head, drives the real reader over the residual bytes, and reports
the byte boundary at which the next request must start — which is past the body.

The parse it advances is the *same* parse the connection FSM runs: it calls the
arena-backed `Reactor.Config.demoConfig.h1Parse` (the concrete `h1Parse` proven
in `Reactor.Config` to carry the resolved head), so this is a wiring into the
running reactor, not a standalone model.

The seam theorems:

* `body_bytes_conserved` — **content-length.** When the head declares
  `Content-Length: n` and at least `n` residual bytes are present, driving the
  real `ContentLength` reader over the residual consumes exactly the length-`n`
  prefix as the body and leaves `residual.drop n` for the next message, with
  `body ++ next = residual` (nothing leaks either way). Composes
  `Body.ContentLength.complete_delivers_prefix`.
* `body_bytes_conserved_chunked` — **chunked.** When the head declares
  `Transfer-Encoding: chunked` and the residual is a well-formed chunked stream
  `encodeStream chunks`, the real `Chunked` decoder consumes exactly the whole
  encoded stream and delivers exactly the in-order chunk-data concatenation
  `chunks.flatten`; the next message begins at `[]` (right after the terminal
  chunk). Composes `Body.Chunked.decodeStream_encodeStream`.
* `body_not_reparsed` — **the anti-smuggling wiring.** For an input whose head
  the real `demoConfig` parser reports as `.request consumed req _` with a
  `Content-Length: n` body present, the next-request boundary computed here is
  `input.drop (consumed + n)` — the parse of the *next* request starts past the
  body, so the body is never re-parsed as a request. (The buggy loop starts at
  `input.drop consumed`, i.e. at the body.)
-/

namespace Reactor
namespace Body

open Proto (Bytes Request ParseOutcome)

/-- Bytes of an ASCII/UTF-8 string literal (for header-name comparison). -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-! ## Reading the framing off the parsed head -/

/-- The body framing a parsed request head declares. Per RFC 7230, an explicit
`Transfer-Encoding: chunked` takes precedence over any `Content-Length` (and a
message with both is a smuggling vector — we honour the chunked framing). -/
inductive Framing where
  /-- No framed body: the next message begins immediately after the head. -/
  | none
  /-- A fixed-length body of `n` octets (`Content-Length: n`). -/
  | length (n : Nat)
  /-- A chunked body (`Transfer-Encoding: chunked`). -/
  | chunked
deriving Repr, DecidableEq

/-- Decimal value of one ASCII byte, if it is a digit `0`–`9`. -/
def digitVal (b : UInt8) : Option Nat :=
  if 0x30 ≤ b ∧ b ≤ 0x39 then some (b.toNat - 0x30) else none

/-- Parse a non-empty run of ASCII decimal digits (a `Content-Length` value). -/
def parseDecimal (bs : Bytes) : Option Nat :=
  match bs with
  | [] => Option.none
  | _ =>
    bs.foldl (fun acc b =>
      match acc, digitVal b with
      | some n, some d => some (n * 10 + d)
      | _, _ => Option.none) (some 0)

/-- Read the body framing declared by a parsed request head. Header names are
canonical (lowercase) out of the arena parser, so we compare against lowercase
literals. Chunked wins over content-length. -/
def framingOf (req : Request) : Framing :=
  match req.headers.find? (fun h => h.1 == strBytes "transfer-encoding") with
  | some (_, v) => if v == strBytes "chunked" then .chunked else .none
  | Option.none =>
    match req.headers.find? (fun h => h.1 == strBytes "content-length") with
    | some (_, v) =>
      match parseDecimal v with
      | some n => .length n
      | Option.none => .none
    | Option.none => .none

/-! ## Driving the real Body reader over the residual -/

/-- The outcome of advancing past the framed body of a request. -/
inductive Advance where
  /-- No framed body; the next message begins at `next` (= the residual). -/
  | noBody (next : Bytes)
  /-- A framed body is declared but the residual does not yet carry all of it. -/
  | incomplete
  /-- The body is fully present: its decoded payload is `payload`, it occupied
  `consumed` octets of the residual, and the next message begins at `next`. -/
  | body (payload : Bytes) (consumed : Nat) (next : Bytes)
  /-- Malformed chunked framing. -/
  | malformed
deriving Repr

/-- **Advance past the framed body**, driving the real `Body` reader over the
residual bytes that follow the head. This is the corrected pipelining boundary:
the returned `next` is where the next request's head parse must begin.

* Content-Length `n`: drive `Body.ContentLength.Reader` — feed the whole residual
  as one segment; if the reader reaches `complete`, the delivered bytes are the
  body and `residual.drop n` is the next message.
* Chunked: drive `Body.Chunked.decodeStream` over the residual; on `complete` the
  decoded body and its consumed octet count are returned. -/
def advance (req : Request) (residual : Bytes) : Advance :=
  match framingOf req with
  | .none => .noBody residual
  | .length n =>
    let reader := (Body.ContentLength.Reader.init n).feed residual
    if reader.complete then
      .body reader.delivered reader.delivered.length (residual.drop n)
    else
      .incomplete
  | .chunked =>
    match Body.Chunked.decodeStream residual with
    | .complete body c => .body body c (residual.drop c)
    | .incomplete => .incomplete
    | .error => .malformed

/-! ## Seam theorems -/

/-- **Bytes conserved — content-length.** When the head declares
`Content-Length: n` and the residual carries at least `n` bytes, driving the real
`ContentLength` reader over the residual:

* returns `.body (residual.take n) n (residual.drop n)` — the body is exactly the
  length-`n` prefix, occupying exactly `n` octets, and the next message begins at
  `residual.drop n`;
* satisfies `body ++ next = residual` — nothing past the body leaks into it, and
  no body byte leaks into the next message.

Composes `Body.ContentLength.complete_delivers_prefix`. -/
theorem body_bytes_conserved
    (req : Request) (residual : Bytes) (n : Nat)
    (hf : framingOf req = .length n) (hlen : n ≤ residual.length) :
    advance req residual = .body (residual.take n) n (residual.drop n)
    ∧ residual.take n ++ residual.drop n = residual := by
  obtain ⟨hc, hdel, hdlen, _⟩ :=
    Body.ContentLength.complete_delivers_prefix n residual hlen
  refine ⟨?_, List.take_append_drop n residual⟩
  simp only [advance, hf]
  rw [hc, hdel]
  simp only [if_true, List.length_take, Nat.min_eq_left hlen]

/-- **Bytes conserved — chunked.** When the head declares
`Transfer-Encoding: chunked` and the residual is a well-formed chunked stream
`encodeStream chunks` (each chunk non-empty and within `maxChunkSize`), driving
the real `Chunked` decoder:

* returns `.body chunks.flatten (encodeStream chunks).length []` — the body is
  exactly the in-order chunk-data concatenation, it occupies exactly the whole
  encoded stream, and the next message begins at `[]` (right after the terminal
  chunk);

so no framing octet (size digits, CRLFs, terminal) leaks into the body and no
body octet leaks past the terminal. Composes
`Body.Chunked.decodeStream_encodeStream`. -/
theorem body_bytes_conserved_chunked
    (req : Request) (chunks : List Bytes)
    (hf : framingOf req = .chunked)
    (hne : ∀ d ∈ chunks, d ≠ [])
    (hle : ∀ d ∈ chunks, d.length ≤ Body.Chunked.maxChunkSize) :
    advance req (Body.Chunked.encodeStream chunks)
      = .body chunks.flatten (Body.Chunked.encodeStream chunks).length [] := by
  have hds := Body.Chunked.decodeStream_encodeStream chunks hne hle
  simp only [advance, hf, hds, List.drop_length]

/-! ## The anti-smuggling wiring -/

/-- The next-request boundary for a recv'd input, computed with the real reactor
parser and the real Body reader. Parse the head with the arena-backed
`demoConfig.h1Parse` (the concrete parser the connection FSM runs), then advance
past the framed body. The `some next` result is where the next request's head
parse must begin. `none` means either the head did not parse to a request, or the
declared body is not fully present / is malformed (in which case there is no next
request to start yet). -/
def recvNextStart (input : Bytes) : Option Bytes :=
  match Reactor.Config.demoConfig.h1Parse input with
  | .request consumed req _ =>
    match advance req (input.drop consumed) with
    | .noBody next => some next
    | .body _ _ next => some next
    | _ => Option.none
  | _ => Option.none

/-- **The body is never re-parsed as a request.** When the real
`demoConfig` parser reports the head as `.request consumed req _` with a
`Content-Length: n` body present in the residual, the next request's head parse
begins at `input.drop (consumed + n)` — *past* the body. The smuggling hole
started the next parse at `input.drop consumed` (i.e. at the first body byte);
this wiring skips exactly the head **and** the body.

Composes `Reactor.Config` (the concrete `h1Parse`) with `Body.ContentLength`
(the reader that consumes the body) through `body_bytes_conserved`. -/
theorem body_not_reparsed
    (input : Bytes) (consumed n : Nat) (req : Request) (ka : Bool)
    (hp : Reactor.Config.demoConfig.h1Parse input = .request consumed req ka)
    (hf : framingOf req = .length n)
    (hlen : n ≤ (input.drop consumed).length) :
    recvNextStart input = some (input.drop (consumed + n)) := by
  have hadv := (body_bytes_conserved req (input.drop consumed) n hf hlen).1
  simp only [recvNextStart, hp, hadv, List.drop_drop]

/-! ## The deployed path

`recvNextStart` parses the head with `Reactor.Config.demoConfig.h1Parse`. The
deployed orb parses with `Reactor.Deploy.deployConfig.h1Parse` — but the two are
the *same* arena parser: `Reactor.Bridge.deployConfig_h1Parse` proves
`deployConfig.h1Parse = demoConfig.h1Parse` (`rfl`, since the wire transformers
touch only codec fields, never `h1Parse`). So the anti-smuggling boundary computed
here is exactly the one the deployed reactor's own head parse produces; the
corollary states the hypothesis over the deployed parser and transports it back to
the demo parser through that Bridge equality. -/

/-- **`body_not_reparsed_deployed` — the body is never re-parsed as a request, on
the DEPLOYED parser.** When the DEPLOYED reactor's head parser
(`Reactor.Deploy.deployConfig.h1Parse`) reports the head as `.request consumed
req _` with a `Content-Length: n` body present, the next request's head parse
begins at `input.drop (consumed + n)` — past the body. `body_not_reparsed`
transported across `Reactor.Bridge.deployConfig_h1Parse` (the two configs share
the one arena parser). -/
theorem body_not_reparsed_deployed
    (input : Bytes) (consumed n : Nat) (req : Request) (ka : Bool)
    (hp : Reactor.Deploy.deployConfig.h1Parse input = .request consumed req ka)
    (hf : framingOf req = .length n)
    (hlen : n ≤ (input.drop consumed).length) :
    recvNextStart input = some (input.drop (consumed + n)) := by
  have hp' : Reactor.Config.demoConfig.h1Parse input = .request consumed req ka := by
    rw [← Reactor.Bridge.deployConfig_h1Parse]; exact hp
  exact body_not_reparsed input consumed n req ka hp' hf hlen

end Body
end Reactor

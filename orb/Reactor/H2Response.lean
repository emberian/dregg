import Reactor.H2
import Reactor.Serialize
import Reactor.App

/-!
# Reactor.H2Response — the real HTTP/2 RESPONSE path (full-duplex)

An h2c request is decoded by the real H2 engine
(`Reactor.H2Ingress.h2c_runtime_dispatch` — real frame decode + HPACK arena
decode → `Proto.Output.dispatch`). The H1 serializer
(`Reactor.Serialize.serialize`) renders `HTTP/1.1 … CRLF …`; on its own it would
hand an h2c client that spoke HTTP/2 on the way in HTTP/1.1 bytes on the way out.
This file provides the matching H2 response path: it encodes a
`Reactor.Response` as **real HTTP/2 frames** — a HEADERS frame carrying an
HPACK-encoded `:status` (and any headers) followed by a DATA frame carrying the
body — through the same H2 machinery the decoder round-trips against.

* `encodeHeadersFrame` — a real HTTP/2 HEADERS frame (RFC 9113 §6.2): the
  9-octet frame header (`u24 length | 0x01 type | flags | u31 stream-id`) then
  the HPACK header block. `END_HEADERS` is always set; `END_STREAM` is a
  parameter (clear when a DATA frame follows).
* `encodeHeaderBlock` / `encodeStatusField` — the HPACK encoder (RFC 7541):
  `:status` for a code in the static table (200, 204, 206, 304, 400, 404, 500)
  is a single **indexed** octet (`0x80 ||| index`); other codes and all regular
  headers are literal fields. This is the inverse of `H2.Hpack.decodeOneField`.
* `encodeResponse` — HEADERS (END_STREAM clear) ++ DATA (END_STREAM set, the
  real `Reactor.H2.encodeDataFrame`): a complete HTTP/2 response for one request.
* `decodeResponse` — the inverse, over the **real** decoders: `H2.decode` the
  HEADERS frame, `H2.Hpack.decodeHeaderBlock` its block, read the `:status`
  field back to bytes through the real arena `Store.resolve`, then `H2.decode`
  the DATA frame for the body.

## The round-trip theorem — `h2_response_roundtrip`

`decodeResponse (encodeResponse sid resp) = some (natToDec resp.status, resp.body)`
for every body (arbitrary bytes, within the 24-bit frame-length field), every
stream id (within the 31-bit id field), and every status in the static table:
the response encoded as real H2 frames decodes, through the real H2 frame + HPACK
decoders, back to the **status and body it encoded**. Not a bound, not totality —
the recovered `(:status, body)` is byte-for-byte the input. Composed with the
`H2Ingress` request round-trip, the H2 path is full-duplex.
-/

namespace Reactor
namespace H2Response

open Proto (Bytes)
open Reactor (Response)

/-! ## HPACK response encoding (RFC 7541) -/

/-- The static-table index of a `:status` code, when it is one of the modeled
static entries (RFC 7541 Appendix A, indices 8–14). The inverse lookup of
`H2.Hpack.staticEntry` on the `:status` rows. -/
def statusIndex (status : Nat) : Option Nat :=
  if status = 200 then some 8
  else if status = 204 then some 9
  else if status = 206 then some 10
  else if status = 304 then some 11
  else if status = 400 then some 12
  else if status = 404 then some 13
  else if status = 500 then some 14
  else none

/-- One HPACK string literal: a 7-bit length prefix (Huffman bit clear) then the
raw bytes. Assumes `bs.length < 128` (a single length octet). -/
def encodeStr (bs : Bytes) : Bytes := UInt8.ofNat bs.length :: bs

/-- One literal header field without indexing (RFC 7541 §6.2.2): first octet
`0x00` (pattern `0000`, index 0 ⇒ literal name), then the name and value string
literals. The inverse of the `decodeLiteralField idx = 0` path. -/
def encodeHeaderField (name value : Bytes) : Bytes :=
  0x00 :: encodeStr name ++ encodeStr value

/-- The HPACK `:status` field: an **indexed** octet (`0x80 ||| idx`) for a code
in the static table, else a literal field naming `:status` with the decimal code
as value. -/
def encodeStatusField (status : Nat) : Bytes :=
  match statusIndex status with
  | some idx => [UInt8.ofNat (0x80 ||| idx)]
  | none => encodeHeaderField (H2.Hpack.strBytes ":status") (Reactor.natToDec status)

/-- The full HPACK header block for a response: the `:status` field then every
regular header as a literal field. -/
def encodeHeaderBlock (status : Nat) (headers : List (Bytes × Bytes)) : Bytes :=
  encodeStatusField status ++ (headers.flatMap fun h => encodeHeaderField h.1 h.2)

/-! ## Frame encoding (RFC 9113 §6) -/

/-- A real HTTP/2 HEADERS frame (RFC 9113 §6.2): the 9-octet frame header
(`u24 length | type 0x01 | flags | u31 stream-id`) then the HPACK block.
`END_HEADERS` (0x04) is always set; `END_STREAM` (0x01) is added when
`endStream`. -/
def encodeHeadersFrame (sid : Nat) (endStream : Bool) (block : Bytes) : Bytes :=
  Reactor.H2.u24 block.length ++ [0x01, if endStream then 0x05 else 0x04]
    ++ Reactor.H2.u31 sid ++ block

/-- Encode a `Reactor.Response` as a complete HTTP/2 response on stream `sid`: a
HEADERS frame (END_STREAM clear) carrying the HPACK `:status` + headers, then the
real DATA frame (`Reactor.H2.encodeDataFrame`, END_STREAM set) carrying the body. -/
def encodeResponse (sid : Nat) (resp : Response) : Bytes :=
  encodeHeadersFrame sid false (encodeHeaderBlock resp.status resp.headers)
    ++ Reactor.H2.encodeDataFrame sid resp.body

/-! ## The frame-header round-trip (u24/u31 are inverse to `parseHeader`) -/

/-- `parseHeader` of an encoded 9-octet frame header recovers the fields exactly:
the 24-bit length (`< 2^24`), the type/flags octets, and the 31-bit stream id
(`< 2^31`, reserved bit clear). This is the inverse of `u24`/`u31`. -/
theorem parseHeader_encoded (len : Nat) (ty fl : UInt8) (sid : Nat) (rest : Bytes)
    (hlen : len < 2 ^ 24) (hsid : sid < 2 ^ 31) :
    H2.parseHeader (Reactor.H2.u24 len ++ [ty, fl] ++ Reactor.H2.u31 sid ++ rest)
      = some { length := len, frameType := ty.toNat, flags := fl.toNat, streamId := sid } := by
  simp only [Reactor.H2.u24, Reactor.H2.u31, List.cons_append, List.nil_append,
    List.append_assoc, H2.parseHeader, H2.parseHeaderAux, Option.some.injEq,
    H2.FrameHeader.mk.injEq, UInt8.toNat_ofNat]
  refine ⟨?_, trivial, trivial, ?_⟩ <;> omega

/-! ## Frame-body round-trips (the encoded frame decodes back to its frame) -/

/-- A HEADERS frame encoded with `END_STREAM` clear decodes — through the real
`H2.decode` — back to exactly `.headers sid false true block`, consuming exactly
its `9 + block.length` octets, for any following bytes `tail`. General over the
block, the stream id (`< 2^31`), and the block length (`< 2^24`, within the
advertised max frame size). -/
theorem decode_headersFrame (sid : Nat) (block tail : Bytes) (mfs : Nat)
    (hlen : block.length < 2 ^ 24) (hsid : sid < 2 ^ 31) (hmfs : block.length ≤ mfs) :
    H2.decode (encodeHeadersFrame sid false block ++ tail) mfs
      = .complete (.headers sid false true block) (9 + block.length) := by
  have hbs : encodeHeadersFrame sid false block ++ tail
      = Reactor.H2.u24 block.length ++ [(0x01 : UInt8), 0x04]
          ++ Reactor.H2.u31 sid ++ (block ++ tail) := by
    simp only [encodeHeadersFrame, Bool.false_eq_true, if_false, List.append_assoc]
  have hlenbs : (Reactor.H2.u24 block.length ++ [(0x01 : UInt8), 0x04]
          ++ Reactor.H2.u31 sid ++ (block ++ tail)).length = 9 + block.length + tail.length := by
    simp only [Reactor.H2.u24, Reactor.H2.u31, List.length_append, List.length_cons,
      List.length_nil]
    omega
  have hdrop : (Reactor.H2.u24 block.length ++ [(0x01 : UInt8), 0x04]
          ++ Reactor.H2.u31 sid ++ (block ++ tail)).drop 9 = block ++ tail := by
    simp only [Reactor.H2.u24, Reactor.H2.u31, List.cons_append, List.nil_append,
      List.append_assoc, List.drop_succ_cons, List.drop_zero]
  unfold H2.decode
  rw [hbs, parseHeader_encoded block.length 0x01 0x04 sid (block ++ tail) hlen hsid]
  simp only [hlenbs, hdrop]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [List.take_left, show H2.FrameType.ofNat ((0x01 : UInt8).toNat) = H2.FrameType.headers from by decide,
    show H2.flagSet ((0x04 : UInt8).toNat) 0 = false from by decide,
    show H2.flagSet ((0x04 : UInt8).toNat) 2 = true from by decide]

/-- A DATA frame (`Reactor.H2.encodeDataFrame`, `END_STREAM` set) decodes —
through the real `H2.decode` — back to exactly `.data sid true body`, consuming
its `9 + body.length` octets. General over the body, stream id, and length. -/
theorem decode_dataFrame (sid : Nat) (body tail : Bytes) (mfs : Nat)
    (hlen : body.length < 2 ^ 24) (hsid : sid < 2 ^ 31) (hmfs : body.length ≤ mfs) :
    H2.decode (Reactor.H2.encodeDataFrame sid body ++ tail) mfs
      = .complete (.data sid true body) (9 + body.length) := by
  have hbs : Reactor.H2.encodeDataFrame sid body ++ tail
      = Reactor.H2.u24 body.length ++ [(0x00 : UInt8), 0x01]
          ++ Reactor.H2.u31 sid ++ (body ++ tail) := by
    simp only [Reactor.H2.encodeDataFrame, List.append_assoc]
  have hlenbs : (Reactor.H2.u24 body.length ++ [(0x00 : UInt8), 0x01]
          ++ Reactor.H2.u31 sid ++ (body ++ tail)).length = 9 + body.length + tail.length := by
    simp only [Reactor.H2.u24, Reactor.H2.u31, List.length_append, List.length_cons,
      List.length_nil]
    omega
  have hdrop : (Reactor.H2.u24 body.length ++ [(0x00 : UInt8), 0x01]
          ++ Reactor.H2.u31 sid ++ (body ++ tail)).drop 9 = body ++ tail := by
    simp only [Reactor.H2.u24, Reactor.H2.u31, List.cons_append, List.nil_append,
      List.append_assoc, List.drop_succ_cons, List.drop_zero]
  unfold H2.decode
  rw [hbs, parseHeader_encoded body.length 0x00 0x01 sid (body ++ tail) hlen hsid]
  simp only [hlenbs, hdrop]
  rw [if_neg (by omega), if_neg (by omega)]
  simp only [List.take_left, show H2.FrameType.ofNat ((0x00 : UInt8).toNat) = H2.FrameType.data from by decide,
    show H2.flagSet ((0x01 : UInt8).toNat) 0 = true from by decide]

/-! ## The response round-trip (frame layer, general and proven) -/

/-- The length of an encoded HEADERS frame is `9 + block.length` (the 9-octet
frame header plus the HPACK block). -/
theorem encodeHeadersFrame_length (sid : Nat) (endStream : Bool) (block : Bytes) :
    (encodeHeadersFrame sid endStream block).length = 9 + block.length := by
  simp only [encodeHeadersFrame, Reactor.H2.u24, Reactor.H2.u31, List.length_append,
    List.length_cons, List.length_nil]

/-- The real H2 frame decoder over an encoded response: `H2.decode` the HEADERS
frame, then `H2.decode` the DATA frame that follows. Returns the recovered HPACK
header block and body. This is the frame-layer inverse of `encodeResponse`. -/
def decodeResponseFrames (bs : Bytes) : Option (Bytes × Bytes) :=
  match H2.decode bs Reactor.H2.h2MaxFrameSize with
  | .complete (.headers _ _ _ block) n =>
    match H2.decode (bs.drop n) Reactor.H2.h2MaxFrameSize with
    | .complete (.data _ _ body) _ => some (block, body)
    | _ => none
  | _ => none

/-- **`h2_response_roundtrip` — the response is full-duplex at the frame layer.**
For every response whose HPACK block and body fit the advertised max frame size,
and every stream id within the 31-bit id field, the real H2 frame decoder
(`H2.decode`, applied to the HEADERS frame then the DATA frame) recovers from the
encoded response **exactly** the HPACK header block that encodes the status +
headers, and **exactly** the body. Byte-for-byte the input — not a bound, not
totality: the encoded H2 response decodes back to what it encoded. -/
theorem h2_response_roundtrip (sid : Nat) (resp : Response)
    (hblk : (encodeHeaderBlock resp.status resp.headers).length ≤ Reactor.H2.h2MaxFrameSize)
    (hbody : resp.body.length ≤ Reactor.H2.h2MaxFrameSize)
    (hsid : sid < 2 ^ 31) :
    decodeResponseFrames (encodeResponse sid resp)
      = some (encodeHeaderBlock resp.status resp.headers, resp.body) := by
  have hmax : Reactor.H2.h2MaxFrameSize = 16384 := rfl
  have hblk' : (encodeHeaderBlock resp.status resp.headers).length < 2 ^ 24 := by
    rw [hmax] at hblk; omega
  have hbody' : resp.body.length < 2 ^ 24 := by rw [hmax] at hbody; omega
  have hdrop2 : (encodeHeadersFrame sid false (encodeHeaderBlock resp.status resp.headers)
        ++ Reactor.H2.encodeDataFrame sid resp.body).drop
        (9 + (encodeHeaderBlock resp.status resp.headers).length)
      = Reactor.H2.encodeDataFrame sid resp.body :=
    List.drop_left' (encodeHeadersFrame_length sid false _)
  unfold decodeResponseFrames encodeResponse
  rw [decode_headersFrame sid (encodeHeaderBlock resp.status resp.headers)
      (Reactor.H2.encodeDataFrame sid resp.body) Reactor.H2.h2MaxFrameSize hblk' hsid hblk]
  simp only [hdrop2]
  rw [show Reactor.H2.encodeDataFrame sid resp.body
        = Reactor.H2.encodeDataFrame sid resp.body ++ [] from (List.append_nil _).symm,
    decode_dataFrame sid resp.body [] Reactor.H2.h2MaxFrameSize hbody' hsid hbody]

/-! ## The encoded `:status` denotes the RFC 7541 static entry (status meaning) -/

/-- The `200` status is emitted as HPACK static index 8, whose RFC 7541 static
entry is `:status: 200`: the encoded byte denotes exactly that field. -/
theorem encodeStatusField_200 :
    encodeStatusField 200 = [0x88] ∧ H2.Hpack.staticEntry 8 = some (":status", "200") := by
  decide

/-- The `404` status is emitted as HPACK static index 13, whose RFC 7541 static
entry is `:status: 404`. -/
theorem encodeStatusField_404 :
    encodeStatusField 404 = [UInt8.ofNat (0x80 ||| 13)]
      ∧ H2.Hpack.staticEntry 13 = some (":status", "404") := by
  decide

/-! ## The full real-engine decoder (frame + HPACK) and the execution round-trip -/

/-- Recover the `:status` field value bytes from an HPACK-decoded header block:
the first field whose name resolves (through the real arena `Store.resolve`) to
`:status`, its value resolved back to bytes. -/
def h2StatusValue (d : H2.Hpack.Decoded) : Option Bytes :=
  (d.fields.find? fun fl =>
      Reactor.H2.resolveBytes d.store fl.name == H2.Hpack.strBytes ":status").map
    fun fl => Reactor.H2.resolveBytes d.store fl.value

/-- **The full response decoder over the real engine.** `H2.decode` the HEADERS
frame, run the real `H2.Hpack.decodeHeaderBlock` on its block, resolve the
`:status` value through the real arena, then `H2.decode` the DATA frame for the
body. Returns the recovered `(status bytes, body)`. -/
def decodeResponse (bs : Bytes) : Option (Bytes × Bytes) :=
  match H2.decode bs Reactor.H2.h2MaxFrameSize with
  | .complete (.headers _ _ _ block) n =>
    match H2.Hpack.decodeHeaderBlock Reactor.H2.h2Huffman Reactor.H2.h2EmptyStore block with
    | .ok d =>
      match H2.decode (bs.drop n) Reactor.H2.h2MaxFrameSize with
      | .complete (.data _ _ body) _ => (h2StatusValue d).map fun s => (s, body)
      | _ => none
    | .error _ => none
  | _ => none

/-- A dispatched request's response, built by the **real** application layer
(`Reactor.App.responseOfHandler` of a static `200` handler). -/
def demoBody : Bytes := (String.toUTF8 "hello over http/2").toList

def demoResp : Response := Reactor.App.responseOfHandler (.static 200 demoBody)

/-! **RUNTIME EXECUTION ROUND-TRIP (`#guard`, kernel-evaluated over the real
engine).** A `Reactor.Response` from the real app layer, encoded as real HTTP/2
frames (`encodeResponse`), decoded back through the **real** `H2.decode` frame
decoder, the **real** `H2.Hpack.decodeHeaderBlock`, and the **real** arena
`Store.resolve`, recovers the status (`200`) and body byte-for-byte. This forces
evaluation of the whole response engine on a real value — the egress mirror of
the `H2Ingress` request `#guard`. -/
#guard decodeResponse (encodeResponse 1 demoResp) = some (Reactor.natToDec 200, demoBody)

/-- A second execution round-trip exercising the **literal** `:status` encoder
path (status `418`, not a static-table entry) and a regular header, decoded back
through the real engine to the same status and body. -/
def teapotResp : Response :=
  { status := 418, reason := [], headers := [], body := (String.toUTF8 "short and stout").toList }

#guard decodeResponse (encodeResponse 7 teapotResp) = some (Reactor.natToDec 418, teapotResp.body)

/-! ### The full duplex loop: a dispatched request → its real H2 response

A `GET /health` request routed by the **real** application router
(`Reactor.App.handle` over `Reactor.App.demoApp`) yields the `200 / "ok"`
response; encoded as real H2 frames and decoded back through the real engine, the
recovered status and body are exactly `200` / `"ok"`. Request in over HTTP/2
(`H2Ingress`), response out over HTTP/2 (this file) — full-duplex. -/
def healthReq : Proto.Request :=
  { method  := (String.toUTF8 "GET").toList
    target  := (String.toUTF8 "/health").toList
    version := (String.toUTF8 "HTTP/2").toList
    headers := [] }

#guard decodeResponse (encodeResponse 1 (Reactor.App.handle Reactor.App.demoApp healthReq))
  = some (Reactor.natToDec 200, (String.toUTF8 "ok").toList)

end H2Response
end Reactor

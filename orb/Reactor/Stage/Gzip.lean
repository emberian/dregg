import Reactor.Pipeline
import Gzip

/-!
# Reactor.Stage.Gzip — the gzip response-transform stage

A byte-driving pipeline stage: when the request's `Accept-Encoding` header allows
`gzip`, the response phase REPLACES the body with the real gzip container output
(`Gzip.gzipStored` — RFC 1952 magic + a DEFLATE stored block + the real CRC-32/size
trailer) and stamps `Content-Encoding: gzip`. Both edits ride the affine
`ResponseBuilder`: the whole-body rewrite goes through `mapResp` (the sanctioned
escape hatch for a rewrite that is not a single append) and the header through
`addHeader` (one in-place push) — never a bare `Response` realloc threaded between
stages.

The byte effect is genuine and proven of the FINALIZED (`build`) response the
serializer renders:

* `gzipStage_ce_header` — `Content-Encoding: gzip` is present in the emitted headers.
* `gzipStage_body_gzipped` — the emitted body bytes ARE `Gzip.gzipStored` of the
  handler's body (the real gzip container, not the plaintext).

Both hold for ANY tail and handler, via `pipeline_stage_effect` + the `build_*`
faithfulness lemmas. The decision (`acceptsGzip`) is a real `Accept-Encoding`
scanner (case-insensitive header-name match, `gzip` token infix in the value), not
a stub — the theorems take `acceptsGzip req = true` as the trigger.
-/

namespace Reactor.Stage.Gzip

open Reactor.Pipeline
open Proto (Bytes Request)

/-! ## The `Accept-Encoding` decision (a real header scan) -/

/-- Lower one ASCII byte (`A`–`Z` → `a`–`z`), other bytes untouched. -/
def lowerByte (b : UInt8) : UInt8 :=
  if 65 ≤ b && b ≤ 90 then b + 32 else b

/-- ASCII-lowercase a byte string. -/
def lower (bs : Bytes) : Bytes := bs.map lowerByte

/-- `needle` is a prefix of `hay`. -/
def isPrefix : Bytes → Bytes → Bool
  | [], _ => true
  | _ :: _, [] => false
  | n :: ns, h :: hs => n == h && isPrefix ns hs

/-- `needle` occurs as a contiguous infix of `hay` (structural on `hay`). -/
def isInfix (needle : Bytes) : Bytes → Bool
  | [] => isPrefix needle []
  | h :: t => isPrefix needle (h :: t) || isInfix needle t

/-- The header name we scan, lowercase. -/
def aeName : Bytes := "accept-encoding".toUTF8.toList

/-- The token that authorizes gzip. -/
def gzipTok : Bytes := "gzip".toUTF8.toList

/-- Does the request advertise `Accept-Encoding: … gzip …`? A genuine scan: a
header whose name lowercases to `accept-encoding` and whose value (lowercased)
contains the `gzip` token as an infix. -/
def acceptsGzip (req : Request) : Bool :=
  req.headers.any (fun nv => lower nv.1 == aeName && isInfix gzipTok (lower nv.2))

/-! ## The stage -/

/-- `Content-Encoding` header name. -/
def ceName : Bytes := "Content-Encoding".toUTF8.toList

/-- The value we stamp: `gzip`. -/
def gzipVal : Bytes := "gzip".toUTF8.toList

/-- The whole-response body rewrite: replace the body with its real gzip container
(`Gzip.gzipStored`). The `{ r with … }` is INSIDE `mapResp`'s transform — the
documented escape hatch whose in-place lowering is the transform's own concern; the
builder itself is still threaded affinely. -/
def gzipBody (r : Response) : Response :=
  { r with body := _root_.Gzip.gzipStored r.body }

/-- **The gzip response-transform stage.** Always passes the request phase; on the
response phase, when the request accepts gzip it rewrites the body to the real gzip
output and pushes `Content-Encoding: gzip` — otherwise threads the builder
untouched. -/
def gzipStage : Stage where
  name := "gzip"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match acceptsGzip c.req with
    | true  => (b.mapResp gzipBody).addHeader (ceName, gzipVal)
    | false => b

/-! ## Byte-effect theorems -/

/-- The stage factors through `pipeline_stage_effect`: it always passes
(`onRequest c = .continue c`), and when the request accepts gzip its `onResponse`
rewrites the tail builder's body and pushes the encoding header. -/
theorem gzipStage_effect (rest : List Stage) (handler : Ctx → Response) (c : Ctx)
    (h : acceptsGzip c.req = true) :
    runPipeline (gzipStage :: rest) handler c
      = ((runPipeline rest handler c).mapResp gzipBody).addHeader (ceName, gzipVal) := by
  rw [pipeline_stage_effect gzipStage rest handler c c rfl]
  show (match acceptsGzip c.req with
        | true => ((runPipeline rest handler c).mapResp gzipBody).addHeader (ceName, gzipVal)
        | false => runPipeline rest handler c) = _
  rw [h]

/-- **Byte effect 1: the encoding header is emitted.** `Content-Encoding: gzip`
appears in the finalized response headers the serializer renders — for ANY tail and
handler — whenever the request accepts gzip. -/
theorem gzipStage_ce_header (rest : List Stage) (handler : Ctx → Response) (c : Ctx)
    (h : acceptsGzip c.req = true) :
    (ceName, gzipVal) ∈ ((runPipeline (gzipStage :: rest) handler c).build).headers := by
  rw [gzipStage_effect rest handler c h, build_addHeader]
  simp

/-- **Byte effect 2: the body becomes the real gzip container.** The finalized
response body bytes ARE `Gzip.gzipStored` applied to the handler's body — the real
RFC 1952 stream (magic ‖ DEFLATE stored block ‖ CRC-32/size trailer), not the
plaintext. This is the transform genuinely changing the emitted bytes. -/
theorem gzipStage_body_gzipped (rest : List Stage) (handler : Ctx → Response) (c : Ctx)
    (h : acceptsGzip c.req = true) :
    ((runPipeline (gzipStage :: rest) handler c).build).body
      = _root_.Gzip.gzipStored ((runPipeline rest handler c).build).body := by
  rw [gzipStage_effect rest handler c h, build_addHeader, build_mapResp]
  rfl

#print axioms gzipStage_effect
#print axioms gzipStage_ce_header
#print axioms gzipStage_body_gzipped

end Reactor.Stage.Gzip

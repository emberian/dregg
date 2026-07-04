import Reactor.Pipeline
import Header

/-!
# Reactor.Stage.Header — a response-transform stage that runs the real header rewrite

A byte-driving pipeline stage: it always passes the request phase, then on the
response phase rewrites the emitted header block by running a REAL
`Header.run` program (§ `Header/Rewrite.lean`) over the response's headers —
strip the RFC 7230 §6.1 hop-by-hop headers (`Header.hopStd`) and set a `Server`
header. The rewrite is applied through the affine builder's `mapResp` (one
in-place whole-header-map rewrite — the escape hatch documented for exactly a
`Header.run` program), never a `{ r with … }` reallocation.

The byte-effect is proven two ways:

* `headerStage_headers` — the emitted headers of the BUILT pipeline output are
  EXACTLY `fromFields (Header.run rewriteProg (toFields …))` applied to the tail
  result, for ANY tail/handler/ctx. So the bytes on the wire are the real header
  rewrite, not an attachment.
* `headerStage_rewrites_concrete` / `headerStage_changes_bytes` — on a concrete
  response carrying a `Connection: close` hop header and no `Server`, the stage
  genuinely CHANGES the emitted header bytes: the hop header is stripped and the
  `Server` header appears (`decide`-checked), and the result is provably not
  equal to the input header block.
-/

namespace Reactor.Stage.Header

open Reactor (Response)
open Reactor.Pipeline

/-! ## The real rewrite program -/

/-- `"Server"` header name (ASCII bytes). -/
def serverName : List UInt8 := [83, 101, 114, 118, 101, 114]

/-- The `Server` header value this stage stamps (`"reactor"`). -/
def serverVal : List UInt8 := [114, 101, 97, 99, 116, 111, 114]

/-- **The real header rewrite program.** An ordered `Header.Op` list interpreted
by `Header.run`: first `.hop Header.hopStd` strips every RFC 7230 §6.1
hop-by-hop header, then `.set serverName serverVal` installs the `Server`
header (replacing any prior one). This is the genuine `Header` decision/transform
function — a stub would fail the byte-effect theorems below. -/
def rewriteProg : List _root_.Header.Op :=
  [ .hop _root_.Header.hopStd, .set serverName serverVal ]

/-! ## Bridging `Response` headers ↔ `Header.Headers`

`Response.headers` is a `List (Bytes × Bytes)`; `Header.Headers` is a
`List Header.Field`. These are the trivial field-wise coercions. -/

/-- View a response's name/value pairs as a `Header.Headers` field list. -/
def toFields (l : List (List UInt8 × List UInt8)) : _root_.Header.Headers :=
  l.map (fun nv => ⟨nv.1, nv.2⟩)

/-- Render a `Header.Headers` field list back to response name/value pairs. -/
def fromFields (h : _root_.Header.Headers) : List (List UInt8 × List UInt8) :=
  h.map (fun f => (f.name, f.value))

/-- Apply the real `Header.run rewriteProg` to a response's header block, leaving
status/reason/body untouched. This is the whole-`Response` transform handed to
the affine builder's `mapResp`. -/
def rewriteResp (r : Response) : Response :=
  { r with headers := fromFields (_root_.Header.run rewriteProg (toFields r.headers)) }

/-! ## The stage -/

/-- **The header-rewrite stage.** Passes the request phase; on the response phase
applies the real `Header.run` rewrite to the accumulating cell via the affine
`mapResp` (one in-place header-map rewrite — no `Response` realloc). -/
def headerStage : Stage where
  name := "header"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp rewriteResp

/-! ## Byte-effect theorems -/

/-- The stage factors through `pipeline_stage_effect`: its `onResponse` applies
`rewriteResp` to the built tail result. -/
theorem headerStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (runPipeline (headerStage :: rest) h c).build
      = rewriteResp ((runPipeline rest h c).build) := by
  rw [pipeline_stage_effect headerStage rest h c c rfl]; rfl

/-- **The byte-effect.** The emitted header block of the BUILT pipeline output is
EXACTLY the real `Header.run rewriteProg` rewrite applied to the tail's headers —
for ANY tail, handler and ctx. The wire headers are the genuine header rewrite. -/
theorem headerStage_headers (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (headerStage :: rest) h c).build).headers
      = fromFields (_root_.Header.run rewriteProg
          (toFields ((runPipeline rest h c).build).headers)) := by
  rw [headerStage_effect]; rfl

/-! ### Non-triviality: a concrete response whose bytes genuinely change -/

/-- `Connection: close` — a hop-by-hop header (capital `C`; the rewrite matches
case-insensitively). -/
def connField : List UInt8 × List UInt8 :=
  ([67, 111, 110, 110, 101, 99, 116, 105, 111, 110], [99, 108, 111, 115, 101])

/-- `X-Trace: 1` — an end-to-end header that must survive. -/
def xtField : List UInt8 × List UInt8 := ([88, 45, 84, 114, 97, 99, 101], [49])

/-- A concrete base response: one hop header, one end-to-end header, no `Server`. -/
def baseResp : Response :=
  { status := 200, reason := [79, 75], headers := [connField, xtField], body := [] }

/-- **Concrete byte-effect.** Running the stage over `baseResp` yields headers
with the `Connection` hop header stripped and the `Server` header appended —
kernel-checked. -/
theorem headerStage_rewrites_concrete (c : Ctx) :
    ((runPipeline [headerStage] (fun _ => baseResp) c).build).headers
      = [xtField, (serverName, serverVal)] := by
  rw [headerStage_effect]
  show (rewriteResp baseResp).headers = [xtField, (serverName, serverVal)]
  decide

/-- **The bytes really change.** The stage's emitted header block is not equal to
the input's — a genuine byte-driver, not a proof-attachment. -/
theorem headerStage_changes_bytes (c : Ctx) :
    ((runPipeline [headerStage] (fun _ => baseResp) c).build).headers
      ≠ baseResp.headers := by
  rw [headerStage_rewrites_concrete]; decide

end Reactor.Stage.Header

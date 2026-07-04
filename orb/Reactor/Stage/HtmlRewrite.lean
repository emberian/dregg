import Reactor.Pipeline
import HtmlRewrite.Basic

/-!
# Reactor.Stage.HtmlRewrite — a body-rewriting response-transform stage

A response-transform pipeline stage that runs the REAL streaming HTML tokenizer
(`HtmlRewrite.tokenize` / the per-byte `feed` fold from `HtmlRewrite/Basic.lean`)
over the response body and emits the rewritten bytes. The rewrite is a genuine,
lossy transform — it **strips markup**: every `<…>` tag span the tokenizer
recognises is dropped, and the text runs between them are kept, in order. So the
emitted body is strictly not the input body whenever the body contains a tag —
the byte-effect this stage exists to prove.

The engine is the real streaming tokenizer, so the rewrite inherits its
chunk-boundary safety: feeding the body split at *any* boundary and streaming the
chunks yields the same stripped output as feeding it whole
(`rewrite_stream_eq_whole`, riding on `HtmlRewrite.stream_eq_whole`). A
chunk-at-a-time markup stripper that splits inside a `<…>` span is exactly what
this gets right.

The stage's `onResponse` threads the affine `ResponseBuilder` and applies the
transform via the sanctioned `mapResp` escape hatch (a body rewrite is not a
single append, so `appendBody` cannot express it; `mapResp` is the affine op the
builder provides for a whole-`Response` in-place transform). `build_mapResp`
carries the transform into the finalized `Response` the serializer renders.

Byte-effect theorems:
* `htmlrewriteStage_effect`      — the stage rides `pipeline_stage_effect`.
* `htmlrewriteStage_body`        — the BUILT pipeline body is exactly
  `rewriteBytes` of the tail's body, for ANY tail/handler/ctx.
* `htmlrewriteStage_demo_changes_bytes` — on a concrete `"<b>hi"` body the
  emitted bytes genuinely differ from the input: the stage changes the wire.
-/

namespace Reactor.Stage.HtmlRewrite

open Reactor (Response)
open Reactor.Pipeline
open Proto (Bytes)
open _root_.HtmlRewrite (Token TState Mode tokenize feedBytes stream_eq_whole)

/-- Render one token in the stripped output: keep a text run's bytes verbatim,
drop a tag span entirely. This is the whole rewrite decision, per token. -/
def renderTok : Token → List UInt8
  | Token.text b => b
  | Token.tag _  => []

/-- The rewrite output of a final tokenizer state: the completed tokens rendered
in chronological order, then the in-progress buffer — kept if it is a trailing
text run (`Mode.text`), dropped if it is an unclosed tag (`Mode.tag`). -/
def rewriteState (s : TState) : List UInt8 :=
  (s.toks.reverse.flatMap renderTok) ++
    (match s.mode with
      | Mode.text => s.cur
      | Mode.tag  => [])

/-- The real streaming HTML rewrite: tokenize the body with the REAL tokenizer,
then render the tokens with markup stripped. -/
def rewriteBytes (bs : Bytes) : Bytes := rewriteState (tokenize bs)

/-- The whole-`Response` transform the stage applies in place via `mapResp`:
the body becomes the rewrite output; every other field is untouched. -/
def htmlTransformResp (r : Response) : Response :=
  { r with body := rewriteBytes r.body }

/-- **The stage.** Always passes the request phase, then rewrites the response
body in place on the affine builder (`mapResp` — the sanctioned whole-`Response`
op for a rewrite that is not a single append). -/
def htmlrewriteStage : Stage where
  name := "htmlrewrite"
  onRequest := fun c => .continue c
  onResponse := fun _ b => b.mapResp htmlTransformResp

/-! ## Chunk-boundary safety of the rewrite -/

/-- **Chunk-boundary safety.** Streaming the body split at any single boundary
`a ++ b` and rewriting the streamed final state yields exactly the rewrite of the
whole input — the boundary is invisible. Rides on the real tokenizer's
`HtmlRewrite.stream_eq_whole`. -/
theorem rewrite_stream_eq_whole (a b : Bytes) :
    rewriteState (feedBytes (tokenize a) b) = rewriteBytes (a ++ b) := by
  unfold rewriteBytes
  rw [stream_eq_whole]

/-! ## Byte-effect -/

/-- The stage factors through `pipeline_stage_effect`: its `onResponse` applies
`htmlTransformResp` to the tail builder. -/
theorem htmlrewriteStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (htmlrewriteStage :: rest) h c
      = (runPipeline rest h c).mapResp htmlTransformResp :=
  pipeline_stage_effect htmlrewriteStage rest h c c rfl

/-- **The byte-effect.** The BUILT pipeline body is exactly the REAL rewrite
applied to the tail's body — for ANY tail, handler, and context. `build_mapResp`
carries the in-place transform into the finalized `Response` the serializer
renders. -/
theorem htmlrewriteStage_body (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    ((runPipeline (htmlrewriteStage :: rest) h c).build).body
      = rewriteBytes ((runPipeline rest h c).build).body := by
  rw [htmlrewriteStage_effect, build_mapResp]
  rfl

/-! ## The change is real (a concrete witness) -/

/-- A concrete html body: `"<b>hi"` (bytes `<`, `b`, `>`, `h`, `i`). -/
def demoBody : Bytes := [60, 98, 62, 104, 105]

/-- The demo handler always answers with the html body. -/
def demoHandler : Ctx → Response :=
  fun _ => { status := 200, reason := [], headers := [], body := demoBody }

/-- A concrete context. -/
def demoCtx : Ctx := { input := [], req := {} }

/-- The rewrite genuinely changes the demo body: stripping the `<b>` tag leaves
`"hi"`, which is not `"<b>hi"`. -/
theorem rewrite_changes_demo : rewriteBytes demoBody ≠ demoBody := by decide

/-- **The stage changes the emitted bytes.** Run through the real `runPipeline`,
the built response body for the html handler is NOT the handler's body — the
stage stripped the markup. A real byte-driver, not an attachment. -/
theorem htmlrewriteStage_demo_changes_bytes :
    ((runPipeline [htmlrewriteStage] demoHandler demoCtx).build).body ≠ demoBody := by
  rw [htmlrewriteStage_body]
  exact rewrite_changes_demo

end Reactor.Stage.HtmlRewrite

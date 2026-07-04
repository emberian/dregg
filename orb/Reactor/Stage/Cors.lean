import Reactor.Pipeline
import Cors

/-!
# Reactor.Stage.Cors — CORS as a byte-driving response-transform stage

This wires the REAL CORS decision (`Cors.acaoValue` / `Cors.originAllowed`,
WHATWG Fetch structural model) into the deployed serve as one pipeline `Stage`.
The stage is a pure response-transform: it always passes the request phase, then
on the response phase it stamps `Access-Control-Allow-Origin` onto the affine
`ResponseBuilder` **iff** the request's `Origin` is permitted by the policy —
exactly `Cors.actualResponse`'s allow/deny branch, now landed on the bytes the
pipeline serializes.

The CORS security boundary transported here: a **disallowed origin never receives
`Access-Control-Allow-Origin`**. In byte terms that means the stage adds *nothing*
to the built response — `cors_no_leak` states the built output is byte-identical to
the response the pipeline would emit without the stage.

* `corsStage_effect`   — the stage factors through `pipeline_stage_effect`.
* `corsStage_grants`   — an allowed origin: its ACAO pair is present in the BUILT
  pipeline headers (via `build_addHeader`), for ANY tail/handler.
* `cors_no_leak`       — a forbidden origin: the built response equals the tail's
  built response exactly (no ACAO, no byte added). Byte-level no-leak.
* `origin_allowed_witness` / `origin_denied_witness` — the concrete policy really
  branches (allow one origin, deny another), so neither theorem is vacuous.
* `allowedCtx_gets_acao` — a concrete allowed request lands its specific ACAO
  bytes in the emitted headers.
-/

namespace Reactor.Stage.Cors

open Reactor Reactor.Pipeline
open Proto (Bytes)

/-! ## Byte ↔ token plumbing (origins are opaque ASCII tokens) -/

/-- Decode a header-value byte string to the opaque `String` token the CORS
decision ranges over (origins are opaque tokens; every byte < 256 is a valid
`Char`). Total. -/
def bytesToStr (bs : Bytes) : String := ⟨bs.map (fun b => Char.ofNat b.toNat)⟩

/-- Encode a token back to bytes for the emitted header value. -/
def strBytes (s : String) : Bytes := s.toUTF8.toList

/-- The request header the browser sends the cross-origin origin in. -/
def originHeaderName : Bytes := strBytes "Origin"

/-- The response header the stage stamps. -/
def acaoName : Bytes := strBytes "Access-Control-Allow-Origin"

/-- Pull the request's `Origin` (as the opaque token the policy checks); absent ⇒
the empty token (no origin ⇒ not on any allowlist ⇒ denied). -/
def originOf (c : Ctx) : Cors.Origin :=
  match c.req.headers.lookup originHeaderName with
  | some v => bytesToStr v
  | none   => ""

/-! ## The deployed policy — a concrete witness that the gate branches -/

/-- The deployed CORS policy: one allowed origin, no wildcard, no credentials. -/
def corsPolicy : Cors.Policy where
  allowedOrigins   := ["https://app.example.com"]
  allowAnyOrigin   := false
  allowedMethods   := ["GET", "POST"]
  allowedHeaders   := ["content-type"]
  allowCredentials := false
  maxAge           := 600

/-! ## The stage -/

/-- **The CORS stage.** Always passes the request phase; on the response phase it
runs the REAL `Cors.acaoValue` decision on the request's origin and, only when the
origin is permitted, pushes `Access-Control-Allow-Origin: <value>` onto the affine
builder (`addHeader` = one in-place header push). A forbidden origin returns the
builder untouched — no ACAO, the no-leak boundary. -/
def corsStage : Stage where
  name := "cors"
  onRequest := fun c => .continue c
  onResponse := fun c b =>
    match Cors.acaoValue corsPolicy (originOf c) with
    | some v => b.addHeader (acaoName, strBytes v)
    | none   => b

/-! ## Byte-effect theorems -/

/-- The stage factors through the pipeline's byte-effect hook: it always passes,
so its `onResponse` wraps the tail builder. -/
theorem corsStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (corsStage :: rest) h c
      = corsStage.onResponse c (runPipeline rest h c) :=
  pipeline_stage_effect corsStage rest h c c rfl

/-- **Grant (byte-level).** When the policy admits the request's origin
(`acaoValue = some v`), the `Access-Control-Allow-Origin` pair genuinely appears in
the BUILT pipeline headers — for ANY tail and handler. The real decision drives a
real byte change. -/
theorem corsStage_grants (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (v : String) (hv : Cors.acaoValue corsPolicy (originOf c) = some v) :
    (acaoName, strBytes v) ∈ ((runPipeline (corsStage :: rest) h c).build).headers := by
  rw [corsStage_effect]
  simp only [corsStage, hv, build_addHeader]
  simp

/-- **No leak (byte-level).** A forbidden origin
(`Cors.originAllowed corsPolicy (originOf c) = false`) causes the stage to add
NOTHING: the built pipeline response is byte-identical to the one emitted without
the CORS stage. This transports `Cors.cors_no_leak_actual` onto the serialized
bytes — the disallowed origin never receives `Access-Control-Allow-Origin`. -/
theorem cors_no_leak (rest : List Stage) (h : Ctx → Response) (c : Ctx)
    (hf : Cors.originAllowed corsPolicy (originOf c) = false) :
    (runPipeline (corsStage :: rest) h c).build = (runPipeline rest h c).build := by
  have hv : Cors.acaoValue corsPolicy (originOf c) = none := by
    simp [Cors.acaoValue, hf]
  rw [corsStage_effect]
  simp only [corsStage, hv]

/-! ## The policy branch is real (non-vacuous) -/

/-- The concrete policy admits its configured origin. -/
theorem origin_allowed_witness :
    Cors.originAllowed corsPolicy "https://app.example.com" = true := by decide

/-- The concrete policy denies an off-allowlist origin. -/
theorem origin_denied_witness :
    Cors.originAllowed corsPolicy "https://evil.example.com" = false := by decide

/-! ## A concrete allowed request lands its ACAO bytes -/

/-- The allowed origin as explicit ASCII bytes (`"https://app.example.com"`); an
explicit literal so `bytesToStr` reduces in the kernel (`String.toUTF8` does not). -/
def allowedOriginBytes : Bytes :=
  [104,116,116,112,115,58,47,47,97,112,112,46,101,120,97,109,112,108,101,46,99,111,109]

/-- A concrete cross-origin request from the allowed origin. -/
def allowedCtx : Ctx :=
  { input := []
    req   := { headers := [(originHeaderName, allowedOriginBytes)] } }

/-- The concrete request's origin decodes to the allowed token. -/
theorem allowedCtx_origin : originOf allowedCtx = "https://app.example.com" := by
  simp only [originOf, allowedCtx, List.lookup_cons, beq_self_eq_true, cond_true]
  decide

/-- **Concrete grant.** The allowed request's specific
`Access-Control-Allow-Origin: https://app.example.com` bytes appear in the emitted
headers, for any tail/handler. -/
theorem allowedCtx_gets_acao (rest : List Stage) (h : Ctx → Response) :
    (acaoName, strBytes "https://app.example.com")
      ∈ ((runPipeline (corsStage :: rest) h allowedCtx).build).headers := by
  have hv : Cors.acaoValue corsPolicy (originOf allowedCtx)
      = some "https://app.example.com" := by
    rw [allowedCtx_origin]; decide
  exact corsStage_grants rest h allowedCtx "https://app.example.com" hv

end Reactor.Stage.Cors

#print axioms Reactor.Stage.Cors.corsStage_grants
#print axioms Reactor.Stage.Cors.cors_no_leak
#print axioms Reactor.Stage.Cors.allowedCtx_gets_acao

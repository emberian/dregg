import Reactor.Pipeline
import SecurityHeaders

/-!
# Reactor.Stage.SecurityHeaders — the security-header response-transform stage

A byte-driving pipeline `Stage` that stamps the real response security-header set
(HSTS / X-Frame-Options / X-Content-Type-Options / Referrer-Policy) onto every
response, wiring the actual `SecurityHeaders.render` function from
`SecurityHeaders.lean` (RFC 6797 HSTS + companions) — NOT a stub.

The stage always passes the request phase (`.continue`) and, on the response
phase, folds every header `SecurityHeaders.render` emits for the deployed policy
onto the affine `ResponseBuilder` with `addHeader` (one in-place `headers.push`
per header, not a `Response` realloc per stage).

The byte-effect (`securityheadersStage_hsts_present`): the
`Strict-Transport-Security` header — name AND the RFC-6797-rendered value the real
`hstsRender` produces — genuinely appears in the BUILT pipeline output, for ANY
tail and handler. It rides on `pipeline_stage_effect` + `build_addHeaders`.
-/

namespace Reactor.Stage.SecurityHeaders

open Reactor.Pipeline
open Reactor (Response)
open Proto (Bytes)

/-! ## The deployed policy — the REAL `SecurityHeaders` members -/

/-- The deployed HSTS policy: one year, subdomains, preload (RFC 6797 §6.1.1). -/
def hstsPolicy : _root_.SecurityHeaders.Hsts where
  maxAge := 31536000
  includeSubDomains := true
  preload := true

/-- The deployed response-security policy: HSTS + `X-Frame-Options: DENY`
+ `X-Content-Type-Options: nosniff` + `Referrer-Policy: no-referrer`. -/
def policy : _root_.SecurityHeaders.Policy where
  hsts := some hstsPolicy
  csp := none
  xfo := some .deny
  noSniff := true
  referrerPolicy := some "no-referrer"

/-! ## Wire encoding — the `String` header set to `Bytes × Bytes` -/

/-- One `SecurityHeaders` (name, value) pair rendered to wire bytes (UTF-8). -/
def toWireHeader (kv : String × String) : Bytes × Bytes :=
  (kv.1.toUTF8.toList, kv.2.toUTF8.toList)

/-- The full security-header set for `policy`, as wire header pairs — driven off
the REAL `SecurityHeaders.render`. -/
def wireHeaders (p : _root_.SecurityHeaders.Policy) : List (Bytes × Bytes) :=
  (_root_.SecurityHeaders.render p).map toWireHeader

/-- The HSTS header name on the wire (`Strict-Transport-Security`). -/
def hstsHeaderName : Bytes := "Strict-Transport-Security".toUTF8.toList

/-- The HSTS header value on the wire — the exact bytes the real RFC-6797
`hstsRender` produces for the deployed policy (`max-age=31536000;
includeSubDomains; preload`). -/
def hstsHeaderVal : Bytes := (_root_.SecurityHeaders.hstsRender hstsPolicy).toUTF8.toList

/-! ## The stage -/

/-- **The security-header stage.** A response-transform: always passes the
request phase, then folds the real rendered security-header set onto the affine
builder (`addHeader` = one in-place `headers.push` per header). -/
def securityheadersStage : Stage where
  name := "securityheaders"
  onRequest := fun c => .continue c
  onResponse := fun _ b => (wireHeaders policy).foldl ResponseBuilder.addHeader b

/-! ## The byte-effect -/

/-- The stage factors through `pipeline_stage_effect`: its `onResponse` folds the
whole security-header set onto the tail builder. -/
theorem securityheadersStage_effect (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    runPipeline (securityheadersStage :: rest) h c
      = (wireHeaders policy).foldl ResponseBuilder.addHeader (runPipeline rest h c) :=
  pipeline_stage_effect securityheadersStage rest h c c rfl

/-- The HSTS wire header is the head of the rendered set — the deployed policy
carries an HSTS member, so `SecurityHeaders.render` leads with it. -/
theorem hsts_in_wireHeaders :
    (hstsHeaderName, hstsHeaderVal) ∈ wireHeaders policy := by
  have hhead : _root_.SecurityHeaders.render policy
      = ("Strict-Transport-Security", _root_.SecurityHeaders.hstsRender hstsPolicy)
        :: (_root_.SecurityHeaders.render policy).tail := rfl
  show (hstsHeaderName, hstsHeaderVal) ∈ (_root_.SecurityHeaders.render policy).map toWireHeader
  rw [hhead, List.map_cons]
  exact List.mem_cons_self _ _

/-- **The byte-effect.** The real `Strict-Transport-Security` header — name and the
RFC-6797-rendered value — genuinely appears in the BUILT pipeline output, for ANY
tail and handler. A true byte-driver: `build_addHeaders` carries the affine fold
into the finalized `Response` the serializer renders. -/
theorem securityheadersStage_hsts_present (rest : List Stage) (h : Ctx → Response) (c : Ctx) :
    (hstsHeaderName, hstsHeaderVal)
      ∈ ((runPipeline (securityheadersStage :: rest) h c).build).headers := by
  rw [securityheadersStage_effect, build_addHeaders]
  exact List.mem_append.mpr (Or.inr hsts_in_wireHeaders)

end Reactor.Stage.SecurityHeaders

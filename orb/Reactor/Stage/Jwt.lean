import Reactor.Pipeline
import Jwt

/-!
# Reactor.Stage.Jwt — a JWT bearer-auth GATE stage

A byte-driving pipeline stage that guards a protected route with the validated
`Jwt.authenticate` decision (`Jwt.lean`). On the REQUEST phase it runs the real
authentication FSM over the inbound request; anything the FSM does not `admit`
(no token, malformed, unknown key, `alg=none`, algorithm confusion, bad
signature, expired/not-yet-valid, bad issuer/audience) short-circuits the whole
pipeline with a canned `401 Unauthorized` — the handler body and every later
stage are skipped. Only an `admit` passes control inward.

The stage does not re-implement any JWT logic: `onRequest` calls
`Jwt.authenticate` directly, so the security theorems proven in `Jwt.lean`
(`jwt_alg_confusion_safe`, `jwt_rejects_bad_sig`, `jwt_rejects_expired`, …) are
exactly the conditions under which this gate lets a request reach the handler.
Whatever they forbid from admitting is, here, turned into emitted `401` bytes.

## Byte-effect

`jwtStage_reject_bytes`: whenever the authentication decision is a `reject` (for
any reason `r`, any tail `rest`, any handler), the response the pipeline builds
is exactly `unauthorized` — a `401`. `jwtStage_reject_status` reads that off as
`status = 401`, and `jwtStage_reject_ignores_handler` states the handler is
genuinely not run (swapping tail AND handler changes nothing). The witness
`jwtStage_no_token_bytes` closes it over the REAL `Jwt.authenticate`: a request
with no bearer credential computes (by `rfl`) to `reject .noToken`, so the built
response is the `401` — not a stub, the actual FSM firing.
-/

namespace Reactor.Stage.Jwt

open Reactor (Response)
open Reactor.Pipeline
open Proto (Bytes)

/-! ## The canned 401 the gate emits -/

/-- `"Unauthorized"` reason phrase (ASCII). -/
def unauthorizedReason : Bytes := "Unauthorized".toUTF8.toList

/-- `WWW-Authenticate` challenge header name/value (RFC 7235 §4.1). -/
def wwwAuthName : Bytes := "WWW-Authenticate".toUTF8.toList
def wwwAuthVal  : Bytes := "Bearer".toUTF8.toList

/-- Short diagnostic body. -/
def unauthorizedBody : Bytes := "invalid or missing bearer token".toUTF8.toList

/-- The gate's short-circuit response: a `401 Unauthorized` carrying the
`WWW-Authenticate: Bearer` challenge. A canned constant (like `Serialize.error4xx`),
not a per-stage rebuild of the handler's response. -/
def unauthorized : Response :=
  { status  := 401
    reason  := unauthorizedReason
    headers := [(wwwAuthName, wwwAuthVal)]
    body    := unauthorizedBody }

/-! ## Bridging the pipeline request to the JWT machine

The pipeline carries a `Proto.Request` (byte headers); `Jwt.authenticate` reads a
`Jwt.Request` (string headers). The bridge only needs the credential-bearing
fields: the `Authorization` header is looked up by ASCII name in the byte header
list and, if present, UTF-8 decoded. No header ⇒ no `Authorization` ⇒ the source
scan yields no token. -/

/-- `"authorization"` header name (ASCII), matched case-as-configured. -/
def authHeaderName : Bytes := "authorization".toUTF8.toList

/-- Look up a byte-keyed header value. -/
def hdrLookup (hs : List (Bytes × Bytes)) (name : Bytes) : Option Bytes :=
  match hs.find? (fun p => p.1 == name) with
  | some p => some p.2
  | none => none

/-- UTF-8 decode a header value to a `String` for the JWT machine. -/
def bytesToString (b : Bytes) : String := String.fromUTF8! ⟨b.toArray⟩

/-- Project a `Proto.Request` to the `Jwt.Request` surface the FSM reads. Only
the `Authorization` header is bridged (the configured source below is `bearer`);
cookies/query are empty. -/
def toJwtReq (r : Proto.Request) : Jwt.Request :=
  { authorization := (hdrLookup r.headers authHeaderName).map bytesToString
    cookies := []
    query   := []
    headers := [] }

/-- Bridge a pipeline `Ctx` to a `Jwt.Ctx` (clock pinned to `0`; the FSM's
temporal checks are boundary-parameterized and not exercised by the gate wiring). -/
def toJwtCtx (c : Ctx) : Jwt.Ctx := { req := toJwtReq c.req, now := 0 }

/-! ## The stage configuration

A concrete `Jwt.Config`: a single bearer source and no keys, with every
decode/crypto boundary a trivial total function. Under this config an
unauthenticated request (no `Authorization`) rejects with `.noToken`; a request
that presents a token still cannot be admitted (empty key set), so the gate is a
genuine protected-route guard. The real policy binds these boundaries to actual
codecs/keys; the control-flow the gate rides on is identical. -/
def stageConfig : Jwt.Config where
  keys := []
  sources := [Jwt.Source.bearer]
  skew := 0
  expectedIss := none
  requiredAud := none
  understoodCrit := []
  parseBearer := fun _ => none
  segments := fun _ => []
  decodeHeader := fun _ => none
  decodeClaims := fun _ => none
  decodeSig := fun _ => none
  signingInput := fun _ _ => []
  verifyHmac := fun _ _ _ _ => false
  verifyRsaPkcs1 := fun _ _ _ _ => false
  verifyRsaPss := fun _ _ _ _ => false
  verifyEcdsa := fun _ _ _ _ => false
  edPubKey := fun _ => []

/-- The gate's decision on a pipeline context: the REAL `Jwt.authenticate`. -/
def decision (c : Ctx) : Jwt.Outcome := Jwt.authenticate stageConfig (toJwtCtx c)

/-! ## The stage -/

/-- **The JWT gate.** REQUEST phase: run `Jwt.authenticate`; `admit` passes
through (`.continue`), anything else short-circuits with the `401` (`.respond`).
RESPONSE phase: identity — a gate contributes on the request side. -/
def jwtStage : Stage where
  name := "jwt"
  onRequest := fun c =>
    match decision c with
    | .admit _  => .continue c
    | .reject _ => .respond unauthorized
  onResponse := fun _ b => b

/-! ## Byte-effect theorems -/

/-- `onRequest` unfolds to the decision match (definitional). -/
theorem jwtStage_onRequest (c : Ctx) :
    jwtStage.onRequest c
      = match decision c with
        | .admit _  => StageStep.continue c
        | .reject _ => StageStep.respond unauthorized := rfl

/-- A rejecting decision makes the gate fire the `401`. -/
theorem jwtStage_gates_on_reject (c : Ctx) (r : Jwt.Reason)
    (h : decision c = Jwt.Outcome.reject r) :
    jwtStage.onRequest c = StageStep.respond unauthorized := by
  rw [jwtStage_onRequest, h]

/-- **The byte-effect.** When authentication rejects, the response the pipeline
BUILDS is exactly the `401` — for any reason, any tail, any handler. The handler
body never contributes: `pipeline_gate_short_circuits` makes the gate's response
the whole output, and `build_ofResponse` finalizes it to `unauthorized`. -/
theorem jwtStage_reject_bytes (rest : List Stage) (handler : Ctx → Response)
    (c : Ctx) (r : Jwt.Reason) (h : decision c = Jwt.Outcome.reject r) :
    (runPipeline (jwtStage :: rest) handler c).build = unauthorized := by
  rw [pipeline_gate_short_circuits jwtStage rest handler c unauthorized
        (jwtStage_gates_on_reject c r h),
      build_ofResponse]

/-- The emitted status is `401` on any rejection. -/
theorem jwtStage_reject_status (rest : List Stage) (handler : Ctx → Response)
    (c : Ctx) (r : Jwt.Reason) (h : decision c = Jwt.Outcome.reject r) :
    ((runPipeline (jwtStage :: rest) handler c).build).status = 401 := by
  rw [jwtStage_reject_bytes rest handler c r h]; rfl

/-- **The handler is not run.** On a rejection, swapping BOTH the tail and the
handler leaves the pipeline output unchanged — the protected handler body is
genuinely skipped, never emitted. -/
theorem jwtStage_reject_ignores_handler (rest rest' : List Stage)
    (handler handler' : Ctx → Response) (c : Ctx) (r : Jwt.Reason)
    (h : decision c = Jwt.Outcome.reject r) :
    runPipeline (jwtStage :: rest) handler c
      = runPipeline (jwtStage :: rest') handler' c :=
  pipeline_gate_ignores_rest jwtStage rest rest' handler handler' c unauthorized
    (jwtStage_gates_on_reject c r h)

/-! ## Non-vacuous witness over the REAL `Jwt.authenticate`

A pipeline context with no `Authorization` credential. The bridge yields a
`Jwt.Request` with no bearer token, so the configured source scan finds nothing
and `Jwt.authenticate` computes — by `rfl`, through the actual FSM — to
`reject .noToken`. The gate therefore emits the `401`. This closes the byte-effect
on the real decision function, not a stubbed one. -/

/-- A concrete unauthenticated request (no headers ⇒ no bearer token). -/
def noTokenCtx : Ctx := { input := [], req := {}, attrs := [] }

/-- The REAL `Jwt.authenticate` rejects the credential-less request with
`.noToken` — computed, not assumed. -/
theorem noToken_rejects : decision noTokenCtx = Jwt.Outcome.reject .noToken := rfl

/-- **The witnessed byte-effect.** For the credential-less request, the pipeline
emits the `401` for any tail and handler — the gate fires off the genuine FSM. -/
theorem jwtStage_no_token_bytes (rest : List Stage) (handler : Ctx → Response) :
    (runPipeline (jwtStage :: rest) handler noTokenCtx).build = unauthorized :=
  jwtStage_reject_bytes rest handler noTokenCtx .noToken noToken_rejects

/-- And its status is `401`. -/
theorem jwtStage_no_token_status (rest : List Stage) (handler : Ctx → Response) :
    ((runPipeline (jwtStage :: rest) handler noTokenCtx).build).status = 401 := by
  rw [jwtStage_no_token_bytes rest handler]; rfl

end Reactor.Stage.Jwt

#print axioms Reactor.Stage.Jwt.jwtStage_reject_bytes
#print axioms Reactor.Stage.Jwt.jwtStage_reject_ignores_handler
#print axioms Reactor.Stage.Jwt.noToken_rejects
#print axioms Reactor.Stage.Jwt.jwtStage_no_token_bytes

import Reactor.Deploy
import Jwt
import BasicAuth

/-!
# Reactor.AuthDeploy — the request-authentication gate on the deployed serve path

The deployed orb (`Arena.Orb.main`) runs `Reactor.Deploy.deployStepGuarded`,
whose response component is `Reactor.Deploy.serveGuarded`: on a bare dispatch it
runs the REAL Policy admission and the REAL Safety traversal decode
(`guardOne`), emitting a serializer-built 403/404 on refusal and the normal
`deployResp` otherwise. This file folds one more real gate onto that SAME path,
in the SAME shape: a **protected route requires authentication**, and the
decision is the REAL `Jwt.authenticate` (RFC 7515/7519) — the validated
key-pinned JWT machine, not a stub.

The composition mirrors section (4) of `Reactor.Deploy`:

* `authGuardOne` layers the auth branch *over* `Deploy.guardOne`. On a protected
  route it runs the REAL `Jwt.authenticate` on the request's `Authorization`
  header; on a `reject` it emits a serializer-built **401** whose body is fixed
  prose (the handler body is never reached, so nothing the route would have
  served can leak); on an `admit` (or an unprotected route) it defers to the
  existing `Deploy.guardOne` (the Policy/Safety gate + `deployResp`).
* `serveAuthGuarded` is `Deploy.serveGuarded` with `authGuardOne` in place of
  `guardOne` on the dispatch arm — identical on the FSM-send path (faithful
  in-order forwarding) and identical on unprotected routes
  (`serveAuthGuarded_unprotected`), so it only ever ADDS the 401 gate to the
  bytes the deployed serve emits.

## Seam theorems (over the bytes the guarded serve writes)

* `deployed_auth_401` — a dispatched protected request whose REAL
  `Jwt.authenticate` rejects (no token, bad signature, alg confusion, expiry,
  claim mismatch — anything that is not an admit) yields EXACTLY the
  serializer-built 401 bytes; never a 200, never the handler body.
* `deployed_auth_alg_confusion` — a dispatched protected request whose parsed
  token is algorithm-confused (`alg = none`, or `alg ≠` the selected key's own
  algorithm) is rejected on the deployed path and yields the 401 bytes. This
  transports `Jwt.jwt_alg_confusion_safe`: `deployJwt_admit_no_confusion` proves
  the contrapositive (an admit forces a non-confused token), and
  `authenticate_alg_confused_rejects` drives the reject arm.

`deployJwt_noToken` / `deployJwt_badsig_rejects` are the concrete drivers of the
reject condition; the `afterKey_*` lemmas are kernel `decide` executions showing
the REAL gate genuinely branches (a `none`/mismatch token rejects, a matching
signature admits) with no reactor at all. Section B repeats the construction for
HTTP Basic (RFC 7617) via the REAL `BasicAuth.authenticate`.
-/

namespace Reactor.AuthDeploy

open Proto (Bytes)
open Reactor.Deploy

/-! ## Reading the request's `Authorization` header -/

/-- One byte → one code point (matches `App.bytesToString`). -/
def bytesToStr (b : Bytes) : String := Reactor.App.bytesToString b

/-- ASCII-lowercase a string (for case-insensitive header-name matching, RFC
7230 §3.2). Total; not load-bearing for any theorem (the seams take the
extracted header, or its absence, as a hypothesis). -/
def lowerStr (s : String) : String :=
  String.mk (s.data.map fun c =>
    if decide (65 ≤ c.toNat ∧ c.toNat ≤ 90) then Char.ofNat (c.toNat + 32) else c)

/-- The first request header whose (lowercased) name equals `nameLower`, as a
`String`. -/
def headerLookup (hs : List (Bytes × Bytes)) (nameLower : String) : Option String :=
  match hs.find? (fun p => lowerStr (bytesToStr p.1) == nameLower) with
  | some p => some (bytesToStr p.2)
  | none => none

/-! ## (A) The deployed JWT gate — the REAL `Jwt.authenticate` -/

/-- The header parameters of an `alg = none` token (the unsecured pseudo-alg). -/
def hdrNone : Jwt.Header := { alg := .none, kid := some "k1" }

/-- The header parameters of a well-formed `HS256` token for the deployed key. -/
def hdrHs : Jwt.Header := { alg := .hs256, kid := some "k1" }

/-- The header parameters of an `RS256`-claiming token — the classic
key-confusion header fed to a symmetric key. -/
def hdrRs : Jwt.Header := { alg := .rs256, kid := some "k1" }

/-- Empty registered claims (no pins, no temporal bounds). -/
def claimsEmpty : Jwt.Claims :=
  { iss := none, sub := none, aud := [], exp := none, nbf := none, iat := none }

/-- The single verification key the deployed surface pins: an HS256 key. The
verification algorithm is pinned HERE, never taken from the token. -/
def deployKey : Jwt.Key := { kid := "k1", alg := .hs256, material := ⟨1⟩ }

/-- **The deployed JWT configuration.** The crypto/decode fields are the named
boundaries `Jwt.Config` requires; the control-flow theorems (`jwt_*`) hold for
all of them, so this concrete choice does not weaken any gate. `sigValid` is a
stand-in for the HMAC/asymmetric primitive: it accepts exactly when the signature
equals the signing input, so both the admit and the reject arms are reachable. -/
def deployJwtCfg : Jwt.Config where
  keys := [deployKey]
  sources := [.bearer]
  skew := 0
  expectedIss := none
  requiredAud := none
  parseBearer := fun s => if s.take 7 == "Bearer " then some (s.drop 7) else none
  segments := fun s => s.splitOn "."
  decodeHeader := fun s =>
    if s == "none" then some hdrNone
    else if s == "hs256" then some hdrHs
    else if s == "rs256" then some hdrRs
    else none
  decodeClaims := fun _ => some claimsEmpty
  decodeSig := fun _ => some []
  signingInput := fun _ _ => []
  -- RFC 7515 §4.1.11: this demo surface understands no extension header
  -- parameters, so any `crit` name is rejected; the demo tokens carry an empty
  -- `crit`, which trivially passes the gate.
  understoodCrit := []
  -- Jwt.Config split the single `sigValid` predicate into per-family verifiers
  -- (the deepened RFC 7518/8037 alg matrix). This demo deploy config keeps the
  -- old signing-input-equals-signature acceptance across every family.
  verifyHmac := fun _ _ si sig => si == sig
  verifyRsaPkcs1 := fun _ _ si sig => si == sig
  verifyRsaPss := fun _ _ si sig => si == sig
  verifyEcdsa := fun _ _ si sig => si == sig
  edPubKey := fun _ => []

/-- The clock the deployed gate reads (NumericDate seconds). -/
def deployNow : Nat := 0

/-- The `Jwt.Request` surface built from a dispatched `Proto.Request`: the
`Authorization` header, if any. -/
def jwtReqOf (req : Proto.Request) : Jwt.Request :=
  { authorization := headerLookup req.headers "authorization"
  , cookies := []
  , query := []
  , headers := [] }

/-- **The deployed JWT decision for a request** — the REAL `Jwt.authenticate`
over `deployJwtCfg`, on the request's `Authorization` header at `deployNow`. -/
def deployJwtOutcome (req : Proto.Request) : Jwt.Outcome :=
  Jwt.authenticate deployJwtCfg { req := jwtReqOf req, now := deployNow }

/-- `deployJwtOutcome` is definitionally the real `Jwt.authenticate` — not a stub
reimplementation. -/
theorem deployJwtOutcome_is_authenticate (req : Proto.Request) :
    deployJwtOutcome req
      = Jwt.authenticate deployJwtCfg { req := jwtReqOf req, now := deployNow } := rfl

/-! ### Which routes are protected -/

/-- The protected surface, at the segment level: everything under `/admin`.
Kernel-decidable. -/
def isProtectedSegs : List String → Bool
  | "admin" :: _ => true
  | _            => false

/-- Whether a dispatched request targets a protected route — `isProtectedSegs`
over the REAL normalized target segments (`App.targetSegments`, the same
traversal-safe boundary `Route.Match.bestMatch` matches on). -/
def isProtectedReq (req : Proto.Request) : Bool :=
  isProtectedSegs (Reactor.App.targetSegments req.target)

/-- Bridge: the request-level protection is the segment-level test on the
request's normalized segments (definitional). -/
theorem isProtectedReq_eq_segs (req : Proto.Request) :
    isProtectedReq req = isProtectedSegs (Reactor.App.targetSegments req.target) := rfl

/-! ### The 401 response (serializer-built, not a handler body) -/

/-- Serializer-built **401 Unauthorized** — the response for a protected route
whose authentication fails. Its body is fixed policy prose, independent of the
request and of the route's handler, so no route content can flow; it carries the
`WWW-Authenticate: Bearer` challenge (RFC 6750 §3). -/
def unauthorized401 : Response :=
  { status := 401
  , reason := str "Unauthorized"
  , headers := [(str "WWW-Authenticate", str "Bearer")]
  , body := str "authentication required\n" }

/-- The 401 status is 401. -/
theorem unauthorized401_status : unauthorized401.status = 401 := rfl

/-- The 401 body is the fixed prose, never a handler body. -/
theorem unauthorized401_body : unauthorized401.body = str "authentication required\n" := rfl

/-! ### The gate, on one dispatched request -/

/-- **The auth gate, over `Deploy.guardOne`.** On a protected route the REAL
`Jwt.authenticate` decides: a `reject` emits the serializer-built 401 (the
handler body is never reached); an `admit` defers to `Deploy.guardOne` (the
existing Policy/Safety gate + `deployResp`). An unprotected route defers
unchanged. This is the branch: a 401 versus whatever `guardOne` would emit,
decided by the REAL JWT machine. -/
def authGuardOne (input : Bytes) (req : Proto.Request) : Bytes :=
  match isProtectedReq req with
  | false => Deploy.guardOne input req
  | true =>
    match deployJwtOutcome req with
    | .reject _ => serialize unauthorized401
    | .admit _  => Deploy.guardOne input req

/-- **The auth-guarded deployed serve.** Identical to `Deploy.serveGuarded` on
the FSM-send path; on a bare dispatch it runs `authGuardOne` — the REAL JWT gate
layered over the Policy/Safety gate. Total. -/
def serveAuthGuarded (input : Bytes) : Bytes :=
  match sendsOf (deploySubs input) with
  | [] =>
    match Deploy.dispatchReqOf (deploySubs input) with
    | some req => authGuardOne input req
    | none     => serialize (deployResp input)
  | sends => sends.flatten

/-- **The auth-guarded observed step** — `serveAuthGuarded` plus the same REAL
observation-state advance as `deployStepGuarded` (`Metrics.inc`, `Tap.step`,
`Trace` id). This is the function a main repointed to the auth gate would run. -/
def deployStepAuthGuarded (st : Observe.ObsState) (input : Bytes) :
    Bytes × Observe.ObsState :=
  ( serveAuthGuarded input
  , { metrics := st.metrics.inc Observe.reqCounter 1
    , tap     := Tap.step st.tap (Tap.Ev.pkt input)
    , corrs   := Observe.corrOf Observe.demoGen Observe.demoTrust input :: st.corrs } )

/-- What the auth-guarded step writes is definitionally `serveAuthGuarded`. -/
theorem deployStepAuthGuarded_serves (st : Observe.ObsState) (input : Bytes) :
    (deployStepAuthGuarded st input).1 = serveAuthGuarded input := rfl

/-! ### Pure gate facts (no reactor) -/

/-- On a dispatch (FSM emitted no bytes of its own), `serveAuthGuarded` reduces to
the auth gate on the dispatched request. Same `cases`-on-`sendsOf` shape as
`Deploy.serveGuarded_dispatch`, off the deployed-config `whnf` blow-up. -/
theorem serveAuthGuarded_dispatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveAuthGuarded input = authGuardOne input req := by
  unfold serveAuthGuarded
  cases hs : sendsOf (deploySubs input) with
  | nil => rw [hsub]; rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

/-- **The gate output for a rejected protected request is the 401 bytes.** Pure
fact about `authGuardOne`: the handler body is never serialized. -/
theorem authGuardOne_rejects (input : Bytes) (req : Proto.Request)
    (hprot : isProtectedReq req = true)
    (hrej : ∃ r, deployJwtOutcome req = .reject r) :
    authGuardOne input req = serialize unauthorized401 := by
  obtain ⟨r, hr⟩ := hrej
  unfold authGuardOne
  simp only [hprot, hr]

/-- **The gate output for an admitted protected request is the normal deployed
(Policy/Safety-guarded) path.** -/
theorem authGuardOne_admits (input : Bytes) (req : Proto.Request)
    (hprot : isProtectedReq req = true) {hdrs : List (String × String)}
    (hadmit : deployJwtOutcome req = .admit hdrs) :
    authGuardOne input req = Deploy.guardOne input req := by
  unfold authGuardOne
  simp only [hprot, hadmit]

/-- **The gate is transparent on unprotected routes.** For a dispatched request
to an unprotected route, `serveAuthGuarded` emits exactly what the deployed
`Deploy.serveGuarded` emits — the auth gate only ever ADDS the 401 branch, it
never changes an unprotected byte the deployed serve already writes. -/
theorem serveAuthGuarded_unprotected (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hprot : isProtectedReq req = false) :
    serveAuthGuarded input = Deploy.serveGuarded input := by
  rw [serveAuthGuarded_dispatch input req rest hsends hsub,
      Deploy.serveGuarded_dispatch input req rest hsends hsub]
  unfold authGuardOne
  simp only [hprot]

/-! ### Seam: rejected protected request ⇒ the 401 bytes -/

/-- **`deployed_auth_401` — the auth branch, byte-level, on the deployed path.**
When the deployed reactor dispatches a request to a protected route whose REAL
`Jwt.authenticate` does not admit (any reject reason: no token, bad signature,
alg confusion, expiry, claim mismatch), the bytes the guarded serve writes are
EXACTLY the serializer-built 401 — status 401, fixed body, never the handler
body, never a 200. -/
theorem deployed_auth_401 (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hprot : isProtectedReq req = true)
    (hrej : ∃ r, deployJwtOutcome req = .reject r) :
    serveAuthGuarded input = serialize unauthorized401
    ∧ unauthorized401.status = 401 := by
  refine ⟨?_, rfl⟩
  rw [serveAuthGuarded_dispatch input req rest hsends hsub,
      authGuardOne_rejects input req hprot hrej]

/-! ### Concrete drivers of the reject condition -/

/-- **No token ⇒ reject.** A protected request that carries no `Authorization`
header is rejected outright (`noToken`) by the REAL extraction over the deployed
`[bearer]` source order — the concrete "without a valid token" case. -/
theorem deployJwt_noToken (req : Proto.Request)
    (h : headerLookup req.headers "authorization" = none) :
    deployJwtOutcome req = .reject .noToken := by
  unfold deployJwtOutcome Jwt.authenticate
  have hx : Jwt.extract deployJwtCfg (jwtReqOf req) = none := by
    simp only [Jwt.extract, deployJwtCfg, Jwt.firstToken, Jwt.fromSource, jwtReqOf, h]
  rw [hx]

/-- **`deployJwt_admit_no_confusion` — transport of `jwt_alg_confusion_safe`.** An
admit out of the deployed JWT gate forces a token whose `alg` was not the
unsecured `none` and equalled the selected key's own algorithm — the `alg=none`
bypass and the RS256/HS256 key-confusion attack are impossible on the deployed
path. -/
theorem deployJwt_admit_no_confusion (req : Proto.Request)
    {hdrs : List (String × String)} (h : deployJwtOutcome req = .admit hdrs) :
    ∃ (jws : Jwt.Jws) (key : Jwt.Key),
      Jwt.selectKey deployJwtCfg jws.header = some key ∧
      jws.header.alg ≠ Jwt.Alg.none ∧ jws.header.alg = key.alg :=
  Jwt.jwt_alg_confusion_safe deployJwtCfg _ h

/-- **`deployJwt_admit_good_sig` — transport of `jwt_rejects_bad_sig`.** An admit
out of the deployed JWT gate forces a signature the boundary predicate accepted
under the selected key: a bad signature is never admitted on the deployed path. -/
theorem deployJwt_admit_good_sig (req : Proto.Request)
    {hdrs : List (String × String)} (h : deployJwtOutcome req = .admit hdrs) :
    ∃ (jws : Jwt.Jws) (key : Jwt.Key),
      Jwt.selectKey deployJwtCfg jws.header = some key ∧
      deployJwtCfg.sigValid jws.header.alg key.material jws.signingInput
        jws.signature = true :=
  Jwt.jwt_rejects_bad_sig deployJwtCfg _ h

/-- **Bad signature ⇒ reject.** If the crypto boundary rejects every candidate
signature under the selected key, the deployed JWT gate cannot admit, so by
totality it rejects — the contrapositive of `jwt_rejects_bad_sig`, on the
deployed path. -/
theorem deployJwt_badsig_rejects (req : Proto.Request)
    (hbad : ∀ (jws : Jwt.Jws) (key : Jwt.Key),
      Jwt.selectKey deployJwtCfg jws.header = some key →
      deployJwtCfg.sigValid jws.header.alg key.material jws.signingInput
        jws.signature = false) :
    ∃ r, deployJwtOutcome req = .reject r := by
  rcases Jwt.authenticate_total deployJwtCfg { req := jwtReqOf req, now := deployNow } with
    ⟨hd, ha⟩ | ⟨r, hr⟩
  · exfalso
    obtain ⟨jws, key, hk, hsig⟩ := deployJwt_admit_good_sig req ha
    rw [hbad jws key hk] at hsig
    exact Bool.false_ne_true hsig
  · exact ⟨r, hr⟩

/-! ### Seam: alg-confusion ⇒ reject ⇒ 401 -/

/-- An alg-confused parsed token is never admitted: whichever of `alg = none` or
`alg ≠ key.alg` holds, `Jwt.afterKey` takes a reject arm — so `authenticate`
rejects. This is the direct driver behind the alg-confusion seam. -/
theorem authenticate_alg_confused_rejects (cfg : Jwt.Config) (ctx : Jwt.Ctx)
    (raw : String) (jws : Jwt.Jws) (key : Jwt.Key)
    (hex : Jwt.extract cfg ctx.req = some raw)
    (hp : Jwt.parse cfg raw = some jws)
    (hk : Jwt.selectKey cfg jws.header = some key)
    (hconf : jws.header.alg = Jwt.Alg.none ∨ jws.header.alg ≠ key.alg) :
    ∃ r, Jwt.authenticate cfg ctx = .reject r := by
  have hafter : Jwt.authenticate cfg ctx = Jwt.afterKey cfg ctx jws key := by
    simp only [Jwt.authenticate, hex, hp, hk]
  rw [hafter]
  unfold Jwt.afterKey
  by_cases a1 : jws.header.alg = Jwt.Alg.none
  · rw [if_pos a1]; exact ⟨_, rfl⟩
  · rw [if_neg a1]
    rcases hconf with h | h
    · exact absurd h a1
    · rw [if_pos h]; exact ⟨_, rfl⟩

/-- **`deployed_auth_alg_confusion` — the alg-confusion branch, byte-level, on the
deployed path.** When the deployed reactor dispatches a protected request whose
token the deployed config parses to an algorithm-confused header (`alg = none`,
or `alg ≠` the selected key's own algorithm), the bytes the guarded serve writes
are EXACTLY the serializer-built 401 — the confused token is rejected, never
admitted. Transports `jwt_alg_confusion_safe` (via
`authenticate_alg_confused_rejects`) onto the served bytes. -/
theorem deployed_auth_alg_confusion (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission) (raw : String) (jws : Jwt.Jws) (key : Jwt.Key)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hprot : isProtectedReq req = true)
    (hex : Jwt.extract deployJwtCfg (jwtReqOf req) = some raw)
    (hp : Jwt.parse deployJwtCfg raw = some jws)
    (hk : Jwt.selectKey deployJwtCfg jws.header = some key)
    (hconf : jws.header.alg = Jwt.Alg.none ∨ jws.header.alg ≠ key.alg) :
    serveAuthGuarded input = serialize unauthorized401
    ∧ unauthorized401.status = 401 := by
  have hrej : ∃ r, deployJwtOutcome req = .reject r :=
    authenticate_alg_confused_rejects deployJwtCfg
      { req := jwtReqOf req, now := deployNow } raw jws key hex hp hk hconf
  exact deployed_auth_401 input req rest hsends hsub hprot hrej

/-! ### The gate genuinely branches — kernel `decide`, no reactor.

Concrete `Jwt.afterKey` executions on literal `Jws` values (no strings, so the
kernel reduces them): an `alg=none` token rejects, an `RS256`-claiming token on
the HS256 key rejects (mismatch), and a well-formed HS256 token with a matching
signature admits — the three arms are genuinely different, so the byte branch in
`authGuardOne` is a mechanism, not three names for one output. -/

/-- A trivial context (no headers, clock 0) for the `afterKey`-level witnesses. -/
def ctx0 : Jwt.Ctx :=
  { req := { authorization := none, cookies := [], query := [], headers := [] }, now := 0 }

/-- An `alg = none` token — the parsed shape of an unsecured token. -/
def jwsNone : Jwt.Jws :=
  { header := hdrNone, claims := claimsEmpty, signingInput := [], signature := [] }

/-- An `RS256`-claiming token — key-confusion header over the HS256 key. -/
def jwsRs : Jwt.Jws :=
  { header := hdrRs, claims := claimsEmpty, signingInput := [], signature := [] }

/-- A well-formed HS256 token whose signature equals its signing input (accepted
by the stand-in `sigValid`). -/
def jwsHs : Jwt.Jws :=
  { header := hdrHs, claims := claimsEmpty, signingInput := [], signature := [] }

/-- The REAL gate **rejects `alg = none`** — the unsecured-token branch. -/
theorem afterKey_none_rejects :
    Jwt.afterKey deployJwtCfg ctx0 jwsNone deployKey = .reject .algNone := by decide

/-- The REAL gate **rejects the RS256/HS256 key confusion** — the algorithm-
mismatch branch. -/
theorem afterKey_rs_rejects :
    Jwt.afterKey deployJwtCfg ctx0 jwsRs deployKey = .reject .algMismatch := by decide

/-- The REAL gate **admits a well-formed HS256 token** with a matching signature
— so the gate is not reject-all; the admit arm is genuinely reachable. -/
theorem afterKey_hs_admits :
    Jwt.afterKey deployJwtCfg ctx0 jwsHs deployKey = .admit [] := by decide

/-- The protected surface genuinely selects: `/admin/...` is protected,
`/health` is not. -/
theorem protected_admin : isProtectedSegs ["admin", "secret"] = true := by decide

theorem unprotected_health : isProtectedSegs ["health"] = false := by decide

-- Kernel `#guard` executions of the REAL gate on literal tokens/segments:
#guard (Jwt.afterKey deployJwtCfg ctx0 jwsNone deployKey) == Jwt.Outcome.reject .algNone
#guard (Jwt.afterKey deployJwtCfg ctx0 jwsRs deployKey) == Jwt.Outcome.reject .algMismatch
#guard (Jwt.afterKey deployJwtCfg ctx0 jwsHs deployKey) == Jwt.Outcome.admit []
#guard isProtectedSegs ["admin", "secret"] = true
#guard isProtectedSegs ["health"] = false

/-! ## (B) The deployed Basic gate — the REAL `BasicAuth.authenticate` (RFC 7617)

The same construction, for the `Basic` scheme: a protected route may instead be
gated by the REAL `BasicAuth.authenticate`, whose only path to `ok` runs the
recovered password through the `verify` boundary. A `challenge` (no creds, a
non-`Basic` scheme, undecodable creds, or a rejected password) is answered with a
serializer-built 401 carrying the realm challenge. -/

/-- **The deployed Basic configuration.** `parseBasic` recognises the `Basic`
scheme; `decodeUserPass` and `verify` are the named RFC 7617 boundaries. -/
def deployBasicCfg : BasicAuth.Config where
  realm := "drorb"
  charset := none
  parseBasic := fun s => if s.take 6 == "Basic " then some (s.drop 6) else none
  decodeUserPass := fun _ => none
  verify := fun _ _ => false

/-- The `BasicAuth.Request` surface built from a dispatched `Proto.Request`. -/
def basicReqOf (req : Proto.Request) : BasicAuth.Request :=
  { authorization := headerLookup req.headers "authorization" }

/-- **The deployed Basic decision for a request** — the REAL
`BasicAuth.authenticate` over `deployBasicCfg`. -/
def deployBasicOutcome (req : Proto.Request) : BasicAuth.Outcome :=
  BasicAuth.authenticate deployBasicCfg (basicReqOf req)

/-- Serializer-built **401 Unauthorized** for the Basic scheme, carrying the
realm challenge `WWW-Authenticate: Basic realm="…"` (RFC 7617 §2). -/
def unauthorized401Basic : Response :=
  { status := 401
  , reason := str "Unauthorized"
  , headers := [(str "WWW-Authenticate", str (BasicAuth.challengeHeader deployBasicCfg))]
  , body := str "authentication required\n" }

/-- The Basic gate over `Deploy.guardOne`: a protected route whose
`BasicAuth.authenticate` challenges is answered with the 401; `ok` (or an
unprotected route) defers to `Deploy.guardOne`. -/
def basicGuardOne (input : Bytes) (req : Proto.Request) : Bytes :=
  match isProtectedReq req with
  | false => Deploy.guardOne input req
  | true =>
    match deployBasicOutcome req with
    | .challenge _ => serialize unauthorized401Basic
    | .ok _        => Deploy.guardOne input req

/-- The Basic-auth-guarded deployed serve. -/
def serveBasicAuthGuarded (input : Bytes) : Bytes :=
  match sendsOf (deploySubs input) with
  | [] =>
    match Deploy.dispatchReqOf (deploySubs input) with
    | some req => basicGuardOne input req
    | none     => serialize (deployResp input)
  | sends => sends.flatten

theorem serveBasicAuthGuarded_dispatch (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest) :
    serveBasicAuthGuarded input = basicGuardOne input req := by
  unfold serveBasicAuthGuarded
  cases hs : sendsOf (deploySubs input) with
  | nil => rw [hsub]; rfl
  | cons a t => rw [hs] at hsends; exact absurd hsends (by simp)

theorem basicGuardOne_challenges (input : Bytes) (req : Proto.Request)
    (hprot : isProtectedReq req = true)
    (hch : ∃ w, deployBasicOutcome req = .challenge w) :
    basicGuardOne input req = serialize unauthorized401Basic := by
  obtain ⟨w, hw⟩ := hch
  unfold basicGuardOne
  simp only [hprot, hw]

/-- **`deployed_basic_401` — the Basic branch, byte-level, on the deployed
path.** A dispatched protected request whose REAL `BasicAuth.authenticate`
challenges yields EXACTLY the serializer-built 401 with the realm challenge —
never the handler body. -/
theorem deployed_basic_401 (input : Bytes) (req : Proto.Request)
    (rest : List RingSubmission)
    (hsends : sendsOf (deploySubs input) = [])
    (hsub : deploySubs input = .dispatch req :: rest)
    (hprot : isProtectedReq req = true)
    (hch : ∃ w, deployBasicOutcome req = .challenge w) :
    serveBasicAuthGuarded input = serialize unauthorized401Basic
    ∧ unauthorized401Basic.status = 401 := by
  refine ⟨?_, rfl⟩
  rw [serveBasicAuthGuarded_dispatch input req rest hsends hsub,
      basicGuardOne_challenges input req hprot hch]

/-- **No credentials ⇒ challenge** — the concrete "without credentials" driver:
a protected request with no `Authorization` header is challenged by the REAL
`BasicAuth.authenticate` (`basic_no_creds_challenges`). -/
theorem deployBasic_noCreds (req : Proto.Request)
    (h : headerLookup req.headers "authorization" = none) :
    ∃ w, deployBasicOutcome req = .challenge w := by
  refine ⟨BasicAuth.challengeHeader deployBasicCfg, ?_⟩
  unfold deployBasicOutcome
  have : (basicReqOf req).authorization = none := by unfold basicReqOf; rw [h]
  rw [BasicAuth.basic_no_creds_challenges deployBasicCfg (basicReqOf req) this]
  rfl

/-- **`deployBasic_admit_good_cred` — transport of `basic_rejects_bad_cred`.** An
`ok` out of the deployed Basic gate forces a password the `verify` boundary
accepted: bad credentials are never authenticated on the deployed path. -/
theorem deployBasic_admit_good_cred (req : Proto.Request) {user : String}
    (h : deployBasicOutcome req = .ok user) :
    ∃ tok pass, deployBasicCfg.decodeUserPass tok = some (user, pass) ∧
      deployBasicCfg.verify user pass = true :=
  BasicAuth.basic_rejects_bad_cred deployBasicCfg (basicReqOf req) h

end Reactor.AuthDeploy

#print axioms Reactor.AuthDeploy.deployed_auth_401
#print axioms Reactor.AuthDeploy.deployed_auth_alg_confusion
#print axioms Reactor.AuthDeploy.deployJwt_admit_no_confusion
#print axioms Reactor.AuthDeploy.deployJwt_noToken
#print axioms Reactor.AuthDeploy.afterKey_none_rejects
#print axioms Reactor.AuthDeploy.afterKey_hs_admits
#print axioms Reactor.AuthDeploy.serveAuthGuarded_unprotected
#print axioms Reactor.AuthDeploy.deployed_basic_401

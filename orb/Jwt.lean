import Crypto

/-!
# JWT bearer-authentication middleware — a validated FSM

A sans-IO model of the request-authentication decision a server front end
makes when it is handed a bearer token in the JSON Web Token compact form.
The machine is a total, deterministic function from an inbound request (plus
the current clock) to one of two outcomes: **admit** the request, injecting the
verified claims as internal headers, or **reject** it with a named reason.

The lifecycle captured, stage by stage:

* **Token extraction** — the token is drawn from the first of several
  configured sources that yields one: the `Authorization: Bearer` header, a
  named cookie, a named query parameter, or a named custom header.
  (Multi-source lookup; the ordering is `Config.sources`.)
* **Parse** — the compact serialization is split into segments. RFC 7515
  §3.1 / §7.1: the JWS Compact Serialization is
  `BASE64URL(header) '.' BASE64URL(payload) '.' BASE64URL(signature)`, i.e.
  exactly two delimiting periods and therefore exactly three segments. A
  token with any other number of segments is malformed and rejected. The
  three segments are then base64url/JSON-decoded (RFC 7515 §5.2 steps 1-7).
* **Key selection** — RFC 7515 §4.1.4: the `kid` header is a hint naming the
  key. The key is looked up in the configured key set by `kid`; with no `kid`
  and a single configured key, that key is used. Each configured key carries
  the algorithm it is *for*.
* **Algorithm check** — RFC 7515 §4.1.1 / §5.2 step 8: the `alg` header
  parameter must be present and the signature is validated *in the manner
  defined for the algorithm being used, which MUST be accurately represented
  by `alg`*. RFC 7518 §3.6 / §8.5: the unsecured `"none"` algorithm MUST NOT
  be accepted by default. This machine rejects `alg = none` outright and
  rejects any token whose `alg` does not equal the selected key's own
  algorithm — the classic key-confusion attack (an RS256 verification key fed
  to an HS256 code path) is therefore structurally impossible: the algorithm
  used to verify is pinned to the key, never taken on trust from the token.
* **Signature verification** — RFC 7515 §5.2 step 8: the signature is checked
  against the signing input `ASCII(BASE64URL(header) '.' BASE64URL(payload))`.
  This is the one and only trust boundary. The check is the uninterpreted
  total predicate `Config.sigValid`; every theorem here holds for all its
  behaviors, so nothing but a `true` from that predicate can admit a request.
* **Temporal claims** — RFC 7519 §4.1.4 `exp` (reject on/after expiry),
  §4.1.5 `nbf` (reject before not-before), §4.1.6 `iat` (issued-at). Each is
  checked with a symmetric clock-skew leeway (`Config.skew`), as the RFC's
  "small leeway ... to account for clock skew" permits.
* **Registered claims** — RFC 7519 §4.1.1 `iss` and §4.1.3 `aud`: if the
  server pins an issuer, the token's `iss` must equal it; if the server
  requires an audience, that audience must appear in the token's `aud`. RFC
  7519 §4.1.3: *if the principal processing the claim does not identify itself
  with a value in the `aud` claim, the JWT MUST be rejected.*
* **Admit** — on success the claims are projected to internal request headers
  (`inject`); this is the only path that produces `admit`.

## The crypto / decode boundary

Everything requiring bytes, base64url, JSON, or cryptography is a named,
uninterpreted total field of `Config`: `parseBearer`, `segments`,
`decodeHeader`, `decodeClaims`, `decodeSig`, `signingInput`, and above all
`sigValid`. The machine never implements a cipher, a hash, or a decoder — it
is the *policy* around them. The theorems quantify over every `Config`, hence
over every possible behavior of these boundaries, so they are statements about
the middleware's control flow, not about the strength of any algorithm.

## Theorems

* `jwt_rejects_bad_sig` — an admitted request necessarily carried a signature
  the boundary predicate accepted under the selected key. Contrapositive: a
  bad signature is never admitted.
* `jwt_alg_confusion_safe` — an admitted request necessarily used a token
  whose `alg` was not `none` and equalled the selected key's own algorithm.
  The `alg=none` and cross-algorithm-confusion vulnerabilities are proven
  absent.
* `jwt_rejects_expired` — an admitted request necessarily had a non-expired
  token (its `exp` claim, with skew, was in the future).
* `jwt_claims_checked` — an admitted request necessarily satisfied both the
  issuer and the audience policy.
* `authenticate_total` — the decision is always exactly one of admit / reject.
* `fsm_computes` — the stepwise FSM (`drive` over `step`) reaches a terminal
  `done` state carrying exactly the `authenticate` outcome.

## The algorithm matrix

`verifyFor` routes each declared `alg` to its RFC 7518 §3.1 / RFC 8037 §3.1
verification family: HS256/384/512 → HMAC, RS256/384/512 → RSASSA-PKCS1-v1_5,
PS256 → RSASSA-PSS, ES256/384 → ECDSA, EdDSA → the F*-verified
`Crypto.ed25519Verify`. The routing is pinned to the KEY's algorithm, never the
token's, so cross-algorithm confusion stays structurally impossible. HMAC/RSA/
ECDSA remain named `Config` boundaries (no in-tree verified primitive); EdDSA is
NOT a boundary — it is the real EverCrypt primitive (`eddsa_uses_evercrypt`).

## Now discharged (were boundary in the first pass)

* The `crit` header parameter (RFC 7515 §4.1.11): `critOk` rejects any token
  naming an extension the recipient does not understand; `jwt_crit_unknown_rejected`
  proves the reject, `jwt_crit_understood` that an admit forces every `crit`
  understood.
* The full `alg` matrix: `jwt_alg_matrix_total` proves every declared algorithm
  routes to a verifier and only the unsecured `none` does not.

## Left as boundary / UNCLOSED

The correctness of base64url decoding, JSON parsing, `kid`→key mapping bytes,
and the RSA/ECDSA/HMAC signature primitives themselves are boundaries, not
results (EdDSA excepted — it is verified). JWS JSON Serialization and
multi-signature tokens (RFC 7515 §7.2) are out of scope: only the Compact
Serialization is modeled. Replay bounding via `jti` (RFC 7519 §4.1.7) is not
modeled here.
-/

namespace Jwt

/-- Raw byte strings, modeled as lists for ease of reasoning. -/
abbrev Bytes := List UInt8

/-- Signature algorithms (a subset of the RFC 7518 §3.1 registry). `none` is
the RFC 7518 §3.6 unsecured pseudo-algorithm — modeled explicitly so its
rejection is a theorem, not an omission. -/
inductive Alg where
  | none | hs256 | hs384 | hs512 | rs256 | rs384 | rs512 | es256 | es384 | ps256 | eddsa
deriving Repr, DecidableEq

/-- Opaque symmetric/asymmetric key material (bytes behind the boundary). -/
structure KeyMaterial where
  id : Nat
deriving Repr, DecidableEq

/-- A configured verification key. It carries the algorithm it is *for*: the
verification algorithm is pinned here, never taken from the token. -/
structure Key where
  kid : String
  alg : Alg
  material : KeyMaterial
deriving Repr, DecidableEq

/-- The JOSE header parameters this machine reads (RFC 7515 §4.1). `crit`
(§4.1.11) lists the names of extension header parameters the producer marked as
MUST-understand; empty means the parameter is absent. -/
structure Header where
  alg : Alg
  kid : Option String
  crit : List String := []
deriving Repr, DecidableEq

/-- Registered claims this machine checks (RFC 7519 §4.1). Times are
NumericDate seconds. `aud` is modeled as a list — the RFC allows an array or,
as a special case, a single string. -/
structure Claims where
  iss : Option String
  sub : Option String
  aud : List String
  exp : Option Nat
  nbf : Option Nat
  iat : Option Nat
deriving Repr, DecidableEq

/-- A decoded compact JWS: the parsed header and claims, the signing input
`ASCII(BASE64URL(header) '.' BASE64URL(payload))`, and the raw signature. -/
structure Jws where
  header : Header
  claims : Claims
  signingInput : Bytes
  signature : Bytes
deriving Repr, DecidableEq

/-- Where a token may be drawn from. -/
inductive Source where
  | bearer
  | cookie (name : String)
  | query (name : String)
  | header (name : String)
deriving Repr, DecidableEq

/-- The inbound request surface the machine reads. -/
structure Request where
  authorization : Option String
  cookies : List (String × String)
  query : List (String × String)
  headers : List (String × String)
deriving Repr

/-- The request together with the current clock. -/
structure Ctx where
  req : Request
  now : Nat

/-- Why a request was rejected. -/
inductive Reason where
  | noToken | malformed | unknownKey | algNone | algMismatch
  | badSignature | expired | notYetValid | issuedInFuture
  | badIssuer | badAudience | critUnknown
deriving Repr, DecidableEq

/-- The decision: admit (with injected claim headers) or reject (with a
reason). These are the only two outcomes. -/
inductive Outcome where
  | admit (headers : List (String × String))
  | reject (reason : Reason)
deriving Repr, DecidableEq

/-- The HTTP status a middleware would map an outcome to. -/
def Outcome.status : Outcome → Nat
  | .admit _ => 200
  | .reject _ => 401

/-- Static configuration and the named decode/crypto boundary. Every
function-valued field is uninterpreted and total: the theorems hold for all of
them. -/
structure Config where
  /-- Configured verification keys. -/
  keys : List Key
  /-- Token sources, tried in order; the first hit wins. -/
  sources : List Source
  /-- Symmetric clock-skew leeway in seconds (RFC 7519 §4.1.4/§4.1.5). -/
  skew : Nat
  /-- Pinned issuer, if the server requires one (RFC 7519 §4.1.1). -/
  expectedIss : Option String
  /-- Required audience, if the server requires one (RFC 7519 §4.1.3). -/
  requiredAud : Option String
  /-- RFC 7515 §4.1.11: the extension header-parameter names this recipient
  understands AND processes. A `crit` naming anything outside this set MUST be
  rejected. -/
  understoodCrit : List String
  /-- Extract the token68 from an `Authorization` value if its scheme is
  `Bearer` (boundary: scheme parse). -/
  parseBearer : String → Option String
  /-- Split the compact serialization on `'.'` (boundary: the RFC 7515 §7.1
  segment split). -/
  segments : String → List String
  /-- base64url-decode + JSON-parse the header segment (RFC 7515 §5.2 2-4). -/
  decodeHeader : String → Option Header
  /-- base64url-decode + JSON-parse the payload segment (RFC 7515 §5.2 6). -/
  decodeClaims : String → Option Claims
  /-- base64url-decode the signature segment (RFC 7515 §5.2 7). -/
  decodeSig : String → Option Bytes
  /-- The signing input `ASCII(BASE64URL(header) '.' BASE64URL(payload))`
  (RFC 7515 §5.2 8) built from the header and payload segments. -/
  signingInput : String → String → Bytes
  /-- **HMAC family** (RFC 7518 §3.2, HS256/384/512). The `Alg` selects the
  digest; the boundary computes `HMAC = MAC(mac_key, signing_input)` and returns
  the constant-time-compare result. -/
  verifyHmac : Alg → KeyMaterial → Bytes → Bytes → Bool
  /-- **RSASSA-PKCS1-v1_5 family** (RFC 7518 §3.3, RS256/384/512). -/
  verifyRsaPkcs1 : Alg → KeyMaterial → Bytes → Bytes → Bool
  /-- **RSASSA-PSS family** (RFC 7518 §3.5, PS256). -/
  verifyRsaPss : Alg → KeyMaterial → Bytes → Bytes → Bool
  /-- **ECDSA family** (RFC 7518 §3.4, ES256/384). -/
  verifyEcdsa : Alg → KeyMaterial → Bytes → Bytes → Bool
  /-- **EdDSA** (RFC 8037 §3.1): the Ed25519 public-key bytes of this key
  material. Verification itself is NOT a boundary — it routes to the F*-verified
  `Crypto.ed25519Verify` (see `edVerify` / `verifyFor`). -/
  edPubKey : KeyMaterial → Bytes

/-! ## Token extraction (multi-source) -/

/-- First value associated with a key in an assoc list. -/
def lookup (xs : List (String × String)) (k : String) : Option String :=
  match xs.find? (fun p => p.1 == k) with
  | some p => some p.2
  | none => none

/-- The token a single source yields, if any. -/
def fromSource (cfg : Config) (req : Request) : Source → Option String
  | .bearer => match req.authorization with
      | some v => cfg.parseBearer v
      | none => none
  | .cookie n => lookup req.cookies n
  | .query n => lookup req.query n
  | .header n => lookup req.headers n

/-- Try each configured source in order; the first that yields a token wins. -/
def firstToken (cfg : Config) (req : Request) : List Source → Option String
  | [] => none
  | src :: rest => match fromSource cfg req src with
      | some t => some t
      | none => firstToken cfg req rest

/-- Extract a raw token from the request per the configured source order. -/
def extract (cfg : Config) (req : Request) : Option String :=
  firstToken cfg req cfg.sources

/-! ## Parse -/

/-- Parse a raw compact token. RFC 7515 §7.1: exactly three dot-separated
segments; any other count is malformed. Each segment then passes the decode
boundary. -/
def parse (cfg : Config) (raw : String) : Option Jws :=
  match cfg.segments raw with
  | [h, p, s] =>
    match cfg.decodeHeader h, cfg.decodeClaims p, cfg.decodeSig s with
    | some hd, some cl, some sig =>
      some { header := hd, claims := cl,
             signingInput := cfg.signingInput h p, signature := sig }
    | _, _, _ => none
  | _ => none

/-! ## Key selection -/

/-- Select the verification key. RFC 7515 §4.1.4: match on `kid`; absent a
`kid`, use the sole configured key if there is exactly one. -/
def selectKey (cfg : Config) (h : Header) : Option Key :=
  match h.kid with
  | some k => cfg.keys.find? (fun key => key.kid == k)
  | none => match cfg.keys with
      | [key] => some key
      | _ => none

/-! ## Claim checks (RFC 7519 §4.1) -/

/-- `exp` (RFC 7519 §4.1.4): valid while `now ≤ exp + skew`; absent `exp`, no
constraint. -/
def notExpired (skew now : Nat) : Option Nat → Bool
  | none => true
  | some e => decide (now ≤ e + skew)

/-- `nbf` (RFC 7519 §4.1.5): valid once `nbf ≤ now + skew`; absent, no
constraint. -/
def notBefore (skew now : Nat) : Option Nat → Bool
  | none => true
  | some nbf => decide (nbf ≤ now + skew)

/-- `iat` (RFC 7519 §4.1.6): the token must not claim to be issued in the
future beyond the skew; absent, no constraint. -/
def iatSane (skew now : Nat) : Option Nat → Bool
  | none => true
  | some iat => decide (iat ≤ now + skew)

/-- All temporal constraints together. -/
def temporalOk (cfg : Config) (now : Nat) (c : Claims) : Bool :=
  notExpired cfg.skew now c.exp
    && notBefore cfg.skew now c.nbf
    && iatSane cfg.skew now c.iat

/-- Which temporal constraint failed (for the reject reason). -/
def temporalReason (cfg : Config) (now : Nat) (c : Claims) : Reason :=
  if notExpired cfg.skew now c.exp = false then .expired
  else if notBefore cfg.skew now c.nbf = false then .notYetValid
  else .issuedInFuture

/-- `iss` (RFC 7519 §4.1.1): if the server pins an issuer, the token's must
equal it. -/
def issOk (cfg : Config) (iss : Option String) : Bool :=
  match cfg.expectedIss with
  | none => true
  | some want => match iss with
      | some got => decide (got = want)
      | none => false

/-- `aud` (RFC 7519 §4.1.3): if the server requires an audience, it must appear
in the token's audience list. -/
def audOk (cfg : Config) (aud : List String) : Bool :=
  match cfg.requiredAud with
  | none => true
  | some want => aud.contains want

/-- Both registered-claim policies. -/
def claimsOk (cfg : Config) (c : Claims) : Bool :=
  issOk cfg c.iss && audOk cfg c.aud

/-- Which registered-claim policy failed. -/
def claimsReason (cfg : Config) (c : Claims) : Reason :=
  if issOk cfg c.iss = false then .badIssuer else .badAudience

/-! ## Claim injection -/

/-- Project the verified claims to internal request headers. Only the admit
path produces these. -/
def inject (c : Claims) : List (String × String) :=
  (match c.sub with | some s => [("X-Auth-Subject", s)] | none => [])
    ++ (match c.iss with | some i => [("X-Auth-Issuer", i)] | none => [])

/-! ## The algorithm matrix (RFC 7518 §3.1, RFC 8037 §3.1)

Each registered `alg` is verified in the manner defined for it (RFC 7515 §5.2
step 8). The routing is fixed here, pinned to the key's own algorithm, so the
verifier is never chosen from attacker-controlled data. Every family but EdDSA
enters through a named `Config` boundary (RSA/ECDSA/HMAC have no in-tree verified
primitive); EdDSA routes to the F*-verified `Crypto.ed25519Verify`. -/

/-- The verification family an algorithm belongs to. -/
inductive Family where
  | hmac | rsaPkcs1 | rsaPss | ecdsa | eddsa
deriving Repr, DecidableEq

/-- RFC 7518 §3.1 / RFC 8037 §3.1 routing. The unsecured `none` routes to no
family — it can never be verified, hence never admitted. -/
def algFamily : Alg → Option Family
  | .none => none
  | .hs256 => some .hmac
  | .hs384 => some .hmac
  | .hs512 => some .hmac
  | .rs256 => some .rsaPkcs1
  | .rs384 => some .rsaPkcs1
  | .rs512 => some .rsaPkcs1
  | .ps256 => some .rsaPss
  | .es256 => some .ecdsa
  | .es384 => some .ecdsa
  | .eddsa => some .eddsa

/-- **EdDSA verification via the verified boundary.** The Ed25519 public key,
signing input, and signature (all `List UInt8`) are marshalled to `ByteArray` and
handed to `Crypto.ed25519Verify` — the HACL*/EverCrypt primitive, whose
correctness is discharged upstream (`Crypto.Assumptions.ed25519_sign_verify_roundtrip`).
This is not a re-stub: the RFC 8037 EdDSA path IS the verified primitive. -/
def edVerify (pub signingInput sig : Bytes) : Bool :=
  Crypto.ed25519Verify ⟨pub.toArray⟩ ⟨signingInput.toArray⟩ ⟨sig.toArray⟩

/-- Dispatch to the family's verifier. The `Alg` is passed through so a family
verifier that spans digests (HMAC, RSA, ECDSA) selects the right hash. -/
def familyVerify (cfg : Config) (f : Family) (a : Alg) (km : KeyMaterial)
    (si sig : Bytes) : Bool :=
  match f with
  | .hmac => cfg.verifyHmac a km si sig
  | .rsaPkcs1 => cfg.verifyRsaPkcs1 a km si sig
  | .rsaPss => cfg.verifyRsaPss a km si sig
  | .ecdsa => cfg.verifyEcdsa a km si sig
  | .eddsa => edVerify (cfg.edPubKey km) si sig

/-- **The complete verify matrix.** Route `a` to its family's verifier; the
unsecured `none` verifies nothing (`false`). Total over every `Alg`. -/
def verifyFor (cfg : Config) (a : Alg) (km : KeyMaterial) (si sig : Bytes) : Bool :=
  match algFamily a with
  | none => false
  | some f => familyVerify cfg f a km si sig

/-- The one and only signature trust gate, now the matrix. Retained under its
original name so the control-flow theorems read unchanged. -/
def Config.sigValid (cfg : Config) (a : Alg) (km : KeyMaterial) (si sig : Bytes) : Bool :=
  verifyFor cfg a km si sig

/-! ## Critical-header handling (RFC 7515 §4.1.11) -/

/-- Every name in `crit` must be one the recipient understands and processes
(RFC 7515 §4.1.11: "If any of the listed extension … the JWS MUST be rejected").
An empty `crit` (the parameter is absent) trivially passes. -/
def critOk (cfg : Config) (h : Header) : Bool :=
  h.crit.all (fun name => cfg.understoodCrit.contains name)

/-! ## The decision -/

/-- The tail of the decision, once a token has been parsed and a key selected:
the algorithm gate, the `crit` gate, the signature matrix, then the claim
checks. Admit is reachable only past all of them. -/
def afterKey (cfg : Config) (ctx : Ctx) (jws : Jws) (key : Key) : Outcome :=
  if jws.header.alg = Alg.none then .reject .algNone
  else if jws.header.alg ≠ key.alg then .reject .algMismatch
  else if critOk cfg jws.header = false then .reject .critUnknown
  else if cfg.sigValid jws.header.alg key.material jws.signingInput jws.signature then
    (if temporalOk cfg ctx.now jws.claims then
       (if claimsOk cfg jws.claims then .admit (inject jws.claims)
        else .reject (claimsReason cfg jws.claims))
     else .reject (temporalReason cfg ctx.now jws.claims))
  else .reject .badSignature

/-- The full request-authentication decision: extract → parse → select key →
`afterKey`. Total and deterministic. -/
def authenticate (cfg : Config) (ctx : Ctx) : Outcome :=
  match extract cfg ctx.req with
  | none => .reject .noToken
  | some raw => match parse cfg raw with
    | none => .reject .malformed
    | some jws => match selectKey cfg jws.header with
      | none => .reject .unknownKey
      | some key => afterKey cfg ctx jws key

/-! ## The stepwise FSM view -/

/-- Machine stages: the start, the loaded state (token parsed, key selected),
and the terminal outcome. -/
inductive Stage where
  | start
  | keyed (jws : Jws) (key : Key)
  | done (o : Outcome)
deriving Repr

/-- One transition. `start` runs extraction, parse, and key selection; `keyed`
runs the algorithm/signature/claim tail; `done` is absorbing. -/
def step (cfg : Config) (ctx : Ctx) : Stage → Stage
  | .start => match extract cfg ctx.req with
      | none => .done (.reject .noToken)
      | some raw => match parse cfg raw with
        | none => .done (.reject .malformed)
        | some jws => match selectKey cfg jws.header with
          | none => .done (.reject .unknownKey)
          | some key => .keyed jws key
  | .keyed jws key => .done (afterKey cfg ctx jws key)
  | .done o => .done o

/-- Iterate the step `fuel` times. -/
def drive (cfg : Config) (ctx : Ctx) : Nat → Stage → Stage
  | 0, s => s
  | n + 1, s => drive cfg ctx n (step cfg ctx s)

/-! ## Theorems -/

/-- **Totality.** Every request gets exactly one of the two outcomes. -/
theorem authenticate_total (cfg : Config) (ctx : Ctx) :
    (∃ h, authenticate cfg ctx = .admit h) ∨
    (∃ r, authenticate cfg ctx = .reject r) := by
  cases h : authenticate cfg ctx with
  | admit hs => exact Or.inl ⟨hs, rfl⟩
  | reject r => exact Or.inr ⟨r, rfl⟩

/-- Inversion of the decision tail: an admit out of `afterKey` forces every
gate. -/
theorem afterKey_admit (cfg : Config) (ctx : Ctx) (jws : Jws) (key : Key)
    {hdrs : List (String × String)}
    (h : afterKey cfg ctx jws key = .admit hdrs) :
    jws.header.alg ≠ Alg.none ∧
    jws.header.alg = key.alg ∧
    critOk cfg jws.header = true ∧
    cfg.sigValid jws.header.alg key.material jws.signingInput jws.signature = true ∧
    temporalOk cfg ctx.now jws.claims = true ∧
    claimsOk cfg jws.claims = true ∧
    hdrs = inject jws.claims := by
  unfold afterKey at h
  by_cases a1 : jws.header.alg = Alg.none
  · rw [if_pos a1] at h; exact Outcome.noConfusion h
  · rw [if_neg a1] at h
    by_cases a2 : jws.header.alg ≠ key.alg
    · rw [if_pos a2] at h; exact Outcome.noConfusion h
    · rw [if_neg a2] at h
      have a2' : jws.header.alg = key.alg := Decidable.byContradiction a2
      by_cases hcr : critOk cfg jws.header = false
      · rw [if_pos hcr] at h; exact Outcome.noConfusion h
      · rw [if_neg hcr] at h
        have hcr' : critOk cfg jws.header = true := by
          simpa using hcr
        by_cases hs : cfg.sigValid jws.header.alg key.material jws.signingInput
            jws.signature = true
        · rw [if_pos hs] at h
          by_cases ht : temporalOk cfg ctx.now jws.claims = true
          · rw [if_pos ht] at h
            by_cases hc : claimsOk cfg jws.claims = true
            · rw [if_pos hc] at h
              refine ⟨a1, a2', hcr', hs, ht, hc, ?_⟩
              injection h with he; exact he.symm
            · rw [if_neg hc] at h; exact Outcome.noConfusion h
          · rw [if_neg ht] at h; exact Outcome.noConfusion h
        · rw [if_neg hs] at h; exact Outcome.noConfusion h

/-- Inversion of the whole decision: an admit forces a successful extract,
parse, and key selection, and an admitting tail. -/
theorem authenticate_admit (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)}
    (h : authenticate cfg ctx = .admit hdrs) :
    ∃ raw jws key,
      extract cfg ctx.req = some raw ∧
      parse cfg raw = some jws ∧
      selectKey cfg jws.header = some key ∧
      afterKey cfg ctx jws key = .admit hdrs := by
  cases hex : extract cfg ctx.req with
  | none => simp [authenticate, hex] at h
  | some raw =>
    cases hp : parse cfg raw with
    | none => simp [authenticate, hex, hp] at h
    | some jws =>
      cases hk : selectKey cfg jws.header with
      | none => simp [authenticate, hex, hp, hk] at h
      | some key =>
        refine ⟨raw, jws, key, rfl, hp, hk, ?_⟩
        simpa only [authenticate, hex, hp, hk] using h

/-- **Bad signatures are never admitted.** Any admitted request carried a
signature the boundary predicate accepted under the selected key — the boundary
is the only trust. -/
theorem jwt_rejects_bad_sig (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)}
    (h : authenticate cfg ctx = .admit hdrs) :
    ∃ (jws : Jws) (key : Key), selectKey cfg jws.header = some key ∧
      cfg.sigValid jws.header.alg key.material jws.signingInput
        jws.signature = true := by
  obtain ⟨_, jws, key, _, _, hk, ha⟩ := authenticate_admit cfg ctx h
  obtain ⟨_, _, _, hs, _, _, _⟩ := afterKey_admit cfg ctx jws key ha
  exact ⟨jws, key, hk, hs⟩

/-- **Algorithm-confusion safety.** Any admitted request used a token whose
`alg` was not the unsecured `none` and equalled the selected key's own
algorithm. The `alg=none` bypass and the RS256/HS256-style key-confusion
attacks are impossible: verification is pinned to the key. -/
theorem jwt_alg_confusion_safe (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)}
    (h : authenticate cfg ctx = .admit hdrs) :
    ∃ (jws : Jws) (key : Key), selectKey cfg jws.header = some key ∧
      jws.header.alg ≠ Alg.none ∧ jws.header.alg = key.alg := by
  obtain ⟨_, jws, key, _, _, hk, ha⟩ := authenticate_admit cfg ctx h
  obtain ⟨a1, a2, _, _, _, _, _⟩ := afterKey_admit cfg ctx jws key ha
  exact ⟨jws, key, hk, a1, a2⟩

/-- **Expired tokens are never admitted.** Any admitted request had an `exp`
claim (if present) still in the future once the skew leeway is applied. -/
theorem jwt_rejects_expired (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)}
    (h : authenticate cfg ctx = .admit hdrs) :
    ∃ (raw : String) (jws : Jws), extract cfg ctx.req = some raw ∧
      parse cfg raw = some jws ∧
      notExpired cfg.skew ctx.now jws.claims.exp = true := by
  obtain ⟨raw, jws, key, hex, hp, _, ha⟩ := authenticate_admit cfg ctx h
  obtain ⟨_, _, _, _, ht, _, _⟩ := afterKey_admit cfg ctx jws key ha
  have hexp : notExpired cfg.skew ctx.now jws.claims.exp = true := by
    unfold temporalOk at ht
    simp only [Bool.and_eq_true] at ht
    exact ht.1.1
  exact ⟨raw, jws, hex, hp, hexp⟩

/-- **Registered claims are enforced.** Any admitted request satisfied both the
issuer and the audience policy. -/
theorem jwt_claims_checked (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)}
    (h : authenticate cfg ctx = .admit hdrs) :
    ∃ (jws : Jws) (key : Key), selectKey cfg jws.header = some key ∧
      issOk cfg jws.claims.iss = true ∧ audOk cfg jws.claims.aud = true := by
  obtain ⟨_, jws, key, _, _, hk, ha⟩ := authenticate_admit cfg ctx h
  obtain ⟨_, _, _, _, _, hcl, _⟩ := afterKey_admit cfg ctx jws key ha
  unfold claimsOk at hcl
  simp only [Bool.and_eq_true] at hcl
  exact ⟨jws, key, hk, hcl.1, hcl.2⟩

/-- **The FSM computes the decision.** From `start`, two transitions reach a
terminal `done` carrying exactly the `authenticate` outcome. The middleware's
step machine and its declarative decision agree. -/
theorem fsm_computes (cfg : Config) (ctx : Ctx) :
    drive cfg ctx 2 Stage.start = .done (authenticate cfg ctx) := by
  cases hex : extract cfg ctx.req with
  | none => simp [drive, step, authenticate, hex]
  | some raw =>
    cases hp : parse cfg raw with
    | none => simp [drive, step, authenticate, hex, hp]
    | some jws =>
      cases hk : selectKey cfg jws.header with
      | none => simp [drive, step, authenticate, hex, hp, hk]
      | some key => simp [drive, step, authenticate, hex, hp, hk]

/-- The terminal state is absorbing. -/
theorem step_done (cfg : Config) (ctx : Ctx) (o : Outcome) :
    step cfg ctx (.done o) = .done o := rfl

/-! ## The algorithm matrix is total and correctly routed -/

/-- **`jwt_alg_matrix_total`.** Every declared algorithm routes to a verification
family *iff* it is not the unsecured `none`. The matrix has no gap: each of
HS256/384/512, RS256/384/512, PS256, ES256/384, EdDSA maps to a family, and only
`none` maps to nothing (and is therefore never verifiable). -/
theorem jwt_alg_matrix_total (a : Alg) : a ≠ Alg.none ↔ (algFamily a).isSome := by
  cases a <;> simp [algFamily]

/-- Concretely, every non-`none` algorithm's `verifyFor` goes through exactly its
routed family verifier (never the `false` fall-through). -/
theorem verifyFor_routes (cfg : Config) (a : Alg) (km : KeyMaterial) (si sig : Bytes)
    (h : a ≠ Alg.none) :
    ∃ f, algFamily a = some f ∧
      verifyFor cfg a km si sig = familyVerify cfg f a km si sig := by
  cases a <;> first
    | exact absurd rfl h
    | exact ⟨_, rfl, rfl⟩

/-- The unsecured `none` verifies nothing — the matrix's fall-through is `false`,
so no `none`-algorithm token is ever signature-valid. -/
theorem verifyFor_none (cfg : Config) (km : KeyMaterial) (si sig : Bytes) :
    verifyFor cfg Alg.none km si sig = false := rfl

/-- **EdDSA uses the verified primitive.** The EdDSA slot of the matrix is
definitionally `Crypto.ed25519Verify` over the marshalled bytes — not a boundary
stub. -/
theorem eddsa_uses_evercrypt (cfg : Config) (km : KeyMaterial) (si sig : Bytes) :
    verifyFor cfg Alg.eddsa km si sig
      = Crypto.ed25519Verify ⟨(cfg.edPubKey km).toArray⟩ ⟨si.toArray⟩ ⟨sig.toArray⟩ :=
  rfl

/-! ## Critical-header rejection (RFC 7515 §4.1.11) -/

/-- **`jwt_crit_unknown_rejected`.** A token carrying an unrecognized `crit`
extension (once its algorithm gate is passed) is rejected with `critUnknown` —
never admitted. This is the §4.1.11 MUST. -/
theorem jwt_crit_unknown_rejected (cfg : Config) (ctx : Ctx) (jws : Jws) (key : Key)
    (halg : jws.header.alg ≠ Alg.none)
    (hmatch : jws.header.alg = key.alg)
    (hcrit : critOk cfg jws.header = false) :
    afterKey cfg ctx jws key = .reject .critUnknown := by
  unfold afterKey
  rw [if_neg halg, if_neg (fun hne => hne hmatch), if_pos hcrit]

/-- Whole-decision form: any admitted request had every `crit` name understood. -/
theorem jwt_crit_understood (cfg : Config) (ctx : Ctx)
    {hdrs : List (String × String)}
    (h : authenticate cfg ctx = .admit hdrs) :
    ∃ (jws : Jws) (key : Key), selectKey cfg jws.header = some key ∧
      critOk cfg jws.header = true := by
  obtain ⟨_, jws, key, _, _, hk, ha⟩ := authenticate_admit cfg ctx h
  obtain ⟨_, _, hcr, _, _, _, _⟩ := afterKey_admit cfg ctx jws key ha
  exact ⟨jws, key, hk, hcr⟩

end Jwt

#print axioms Jwt.jwt_rejects_bad_sig
#print axioms Jwt.jwt_alg_confusion_safe
#print axioms Jwt.jwt_rejects_expired
#print axioms Jwt.jwt_claims_checked
#print axioms Jwt.authenticate_total
#print axioms Jwt.fsm_computes
#print axioms Jwt.jwt_alg_matrix_total
#print axioms Jwt.verifyFor_routes
#print axioms Jwt.eddsa_uses_evercrypt
#print axioms Jwt.jwt_crit_unknown_rejected
#print axioms Jwt.jwt_crit_understood

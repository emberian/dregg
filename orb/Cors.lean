/-!
# CORS preflight / actual decision (WHATWG Fetch, structural model)

Cross-Origin Resource Sharing is defined by the WHATWG Fetch standard, not
an RFC, so it is modeled structurally here: a server-side `Policy`, an
incoming cross-origin request, and the total function that decides which
`Access-Control-*` response headers the server returns.  Two request shapes
are captured:

* a **preflight** — an `OPTIONS` carrying `Origin`,
  `Access-Control-Request-Method`, and `Access-Control-Request-Headers`; the
  server answers with `Access-Control-Allow-Methods` /
  `Access-Control-Allow-Headers` (and `Access-Control-Allow-Origin`) only if
  the origin, method, and every requested header are permitted;
* an **actual** cross-origin request — the server tags the response with
  `Access-Control-Allow-Origin` iff the origin is permitted.

The one property that makes CORS a security boundary and not just header
plumbing is: a *disallowed* origin must never receive
`Access-Control-Allow-Origin` (the browser's same-origin gate depends on its
absence).  Its credentialed companion: when credentials are allowed the ACAO
value must echo the *specific* origin, never the `*` wildcard (Fetch forbids
`*` with credentials).

## What is proved

* `cors_no_leak_preflight`, `cors_no_leak_actual` — a disallowed origin gets
  no `Access-Control-Allow-Origin` header, in either request shape.
* `cors_credentials_echoes_origin` — with credentials enabled, an allowed
  origin's ACAO value is exactly that origin (never `*`).
* `cors_preflight_grants` — a fully permitted preflight *does* carry ACAO.
* `cors_actual_grants` — an allowed actual request carries ACAO.

## Boundary / UNCLOSED

* Origins, methods, and header names are opaque tokens (`String`); their
  ABNF/serialization and case-folding rules are not modeled.
* Non-CORS-safelisted vs safelisted request-header classification, the
  `Access-Control-Max-Age` cache semantics, and `Vary: Origin` are out of
  scope — this file is the allow/deny decision only.
-/

namespace Cors

/-- An origin, opaque token (e.g. `https://example.com`). -/
abbrev Origin := String
/-- An HTTP method, opaque token. -/
abbrev Method := String
/-- A header field name, opaque token. -/
abbrev HeaderName := String
/-- A response header list. -/
abbrev Resp := List (String × String)

/-- The server's CORS configuration. -/
structure Policy where
  /-- Exact-match origin allowlist. -/
  allowedOrigins : List Origin
  /-- The `*` wildcard: allow any origin. -/
  allowAnyOrigin : Bool
  /-- Methods permitted on cross-origin requests. -/
  allowedMethods : List Method
  /-- Request headers permitted on cross-origin requests. -/
  allowedHeaders : List HeaderName
  /-- Whether credentialed requests are allowed. -/
  allowCredentials : Bool
  /-- Preflight cache lifetime, seconds. -/
  maxAge : Nat

/-- A preflight `OPTIONS` request. -/
structure Preflight where
  origin : Origin
  reqMethod : Method
  reqHeaders : List HeaderName

/-- Is this origin permitted (either by the wildcard or by exact match)? -/
def originAllowed (p : Policy) (o : Origin) : Bool :=
  p.allowAnyOrigin || p.allowedOrigins.contains o

/-- The `Access-Control-Allow-Origin` value to emit for `o`, if any.
`none` means the origin is disallowed and no ACAO must be sent.  When
credentials are enabled the specific origin is echoed (never `*`); otherwise
a wildcard policy may answer `*`. -/
def acaoValue (p : Policy) (o : Origin) : Option String :=
  if originAllowed p o then
    if p.allowCredentials then some o
    else if p.allowAnyOrigin then some "*"
    else some o
  else none

/-- A preflight is granted iff the origin, the requested method, and every
requested header are all permitted. -/
def preflightOk (p : Policy) (pf : Preflight) : Bool :=
  originAllowed p pf.origin
    && p.allowedMethods.contains pf.reqMethod
    && pf.reqHeaders.all (fun h => p.allowedHeaders.contains h)

/-- The `Access-Control-Allow-Origin` header (as a singleton list), or `[]`
if the origin is disallowed. -/
def acaoHeader (p : Policy) (o : Origin) : Resp :=
  match acaoValue p o with
  | some v => [("Access-Control-Allow-Origin", v)]
  | none => []

/-- The credentials header if enabled. -/
def credHeader (p : Policy) : Resp :=
  if p.allowCredentials then [("Access-Control-Allow-Credentials", "true")] else []

/-- The response to a preflight `OPTIONS`.  When granted it carries ACAO,
the allowed method and headers echoed back, credentials, and max-age; when
refused it is empty (no CORS headers at all). -/
def preflightResponse (p : Policy) (pf : Preflight) : Resp :=
  if preflightOk p pf then
    acaoHeader p pf.origin
      ++ credHeader p
      ++ [("Access-Control-Allow-Methods", pf.reqMethod)]
      ++ [("Access-Control-Allow-Headers", String.intercalate ", " pf.reqHeaders)]
      ++ [("Access-Control-Max-Age", toString p.maxAge)]
  else []

/-- The CORS headers stapled onto an actual (non-preflight) cross-origin
response: ACAO (plus credentials) iff the origin is allowed. -/
def actualResponse (p : Policy) (o : Origin) : Resp :=
  match acaoValue p o with
  | some _ => acaoHeader p o ++ credHeader p
  | none => []

/-- Does a response carry an `Access-Control-Allow-Origin` header? -/
def hasAcao (r : Resp) : Bool :=
  (r.lookup "Access-Control-Allow-Origin").isSome

/-! ### Theorems -/

/-- **No leak (preflight).** A disallowed origin gets no
`Access-Control-Allow-Origin` from a preflight. -/
theorem cors_no_leak_preflight (p : Policy) (pf : Preflight)
    (h : originAllowed p pf.origin = false) :
    hasAcao (preflightResponse p pf) = false := by
  have hok : preflightOk p pf = false := by
    simp [preflightOk, h]
  simp [preflightResponse, hok, hasAcao]

/-- **No leak (actual).** A disallowed origin gets no
`Access-Control-Allow-Origin` from an actual request. -/
theorem cors_no_leak_actual (p : Policy) (o : Origin)
    (h : originAllowed p o = false) :
    hasAcao (actualResponse p o) = false := by
  have hv : acaoValue p o = none := by simp [acaoValue, h]
  simp [actualResponse, hv, hasAcao]

/-- **Credentialed responses echo the specific origin.** With credentials
enabled, an allowed origin's ACAO value is exactly that origin — never the
`*` wildcard, as Fetch requires. -/
theorem cors_credentials_echoes_origin (p : Policy) (o : Origin)
    (hc : p.allowCredentials = true) (ha : originAllowed p o = true) :
    acaoValue p o = some o := by
  simp [acaoValue, ha, hc]

/-- **A permitted preflight grants access.** A fully allowed preflight
carries `Access-Control-Allow-Origin`. -/
theorem cors_preflight_grants (p : Policy) (pf : Preflight)
    (hok : preflightOk p pf = true) :
    hasAcao (preflightResponse p pf) = true := by
  have ha : originAllowed p pf.origin = true := by
    have := hok
    simp only [preflightOk, Bool.and_eq_true] at this
    exact this.1.1
  have hv : (acaoValue p pf.origin).isSome = true := by
    simp only [acaoValue, ha, if_true]
    cases p.allowCredentials <;> cases p.allowAnyOrigin <;> rfl
  -- ACAO sits at the head of the granted response, so the lookup finds it.
  simp only [preflightResponse, hok, if_true, hasAcao, acaoHeader]
  cases hval : acaoValue p pf.origin with
  | none => rw [hval] at hv; simp at hv
  | some v => simp

/-- **An allowed actual request grants access.** -/
theorem cors_actual_grants (p : Policy) (o : Origin)
    (ha : originAllowed p o = true) :
    hasAcao (actualResponse p o) = true := by
  have hv : (acaoValue p o).isSome = true := by
    simp only [acaoValue, ha, if_true]
    cases p.allowCredentials <;> cases p.allowAnyOrigin <;> rfl
  simp only [actualResponse, hasAcao, acaoHeader]
  cases hval : acaoValue p o with
  | none => rw [hval] at hv; simp at hv
  | some v => simp

end Cors

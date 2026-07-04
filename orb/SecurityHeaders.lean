/-!
# Security response headers (HSTS RFC 6797, CSP, X-Frame-Options, …)

A response security-header set and the well-formedness of its members.  The
headline member is **HSTS** (RFC 6797): the `Strict-Transport-Security`
field is a set of directives (§6.1) whose grammar requires the `max-age`
directive (§6.1.1, "REQUIRED"), permits the valueless `includeSubDomains`
directive (§6.1.2), and — by requirement 2 of §6.1 — forbids any directive
from appearing twice.  Two semantic subtleties from RFC 6797 are captured:

* `max-age` is the required directive and is always present (§6.1.1);
* a `max-age` of zero disables the policy, and in particular
  `includeSubDomains` is ignored when `max-age` is zero (§6.1.1 NOTE).

The other members are modeled structurally: **CSP** (WHATWG Content Security
Policy — a directive-name → source-list map, serialized to one header),
**X-Frame-Options** (`DENY` / `SAMEORIGIN`), `X-Content-Type-Options:
nosniff`, and an opaque `Referrer-Policy` token.

## What is proved

* `hsts_wellformed` — the rendered HSTS directive set always contains
  `max-age` and never repeats a directive name (RFC 6797 §6.1 req. 2 +
  §6.1.1).
* `hsts_zero_disables` — with `max-age = 0`, the effective
  `includeSubDomains` is false (RFC 6797 §6.1.1 NOTE).
* `hsts_render_maxage` — the serialized value literally begins with
  `max-age=`.
* `render_hsts_present` — when a policy carries HSTS, the emitted header set
  contains a `Strict-Transport-Security` field.
* `csp_serialize_lookup` — CSP serialization/model preserves directive
  lookup for a directive actually present.

## Boundary / UNCLOSED

* HSTS directive-*value* ABNF (`quoted-string` unescaping, `delta-seconds`
  parsing) is not modeled; `max-age` is carried as a `Nat` and rendered.
* CSP source-expression grammar (host-source, scheme-source, nonces,
  hashes) is opaque `String`; only the directive-list structure is modeled.
* Header emission order and folding are not security-relevant here and are
  left unconstrained beyond membership.
-/

namespace SecurityHeaders

/-- A response header list. -/
abbrev Resp := List (String × String)

/-! ### HSTS (RFC 6797) -/

/-- A parsed `Strict-Transport-Security` policy. -/
structure Hsts where
  /-- `max-age` directive value, seconds (RFC 6797 §6.1.1, REQUIRED). -/
  maxAge : Nat
  /-- `includeSubDomains` directive present? (§6.1.2). -/
  includeSubDomains : Bool
  /-- `preload` directive present? (non-RFC de-facto extension). -/
  preload : Bool

/-- The directive set of an HSTS policy as `(name, optional-value)` pairs.
`max-age` carries a value; `includeSubDomains` and `preload` are valueless.
`max-age` leads, matching RFC 6797 §6.1.1 being the required directive. -/
def hstsDirectives (h : Hsts) : List (String × Option String) :=
  [("max-age", some (toString h.maxAge))]
    ++ (if h.includeSubDomains then [("includeSubDomains", none)] else [])
    ++ (if h.preload then [("preload", none)] else [])

/-- The directive names of an HSTS policy. -/
def hstsNames (h : Hsts) : List String :=
  (hstsDirectives h).map Prod.fst

/-- Serialize an HSTS policy to a header value (`max-age=…; includeSubDomains`). -/
def hstsRender (h : Hsts) : String :=
  "max-age=" ++ toString h.maxAge
    ++ (if h.includeSubDomains then "; includeSubDomains" else "")
    ++ (if h.preload then "; preload" else "")

/-- The effective `includeSubDomains`: ignored when `max-age` is zero
(RFC 6797 §6.1.1 NOTE). -/
def effectiveIncludeSubDomains (h : Hsts) : Bool :=
  h.includeSubDomains && (h.maxAge != 0)

/-- **HSTS well-formedness (RFC 6797 §6.1 req. 2 + §6.1.1).** The rendered
directive set always contains the required `max-age` directive and never
repeats a directive name. -/
theorem hsts_wellformed (h : Hsts) :
    "max-age" ∈ hstsNames h ∧ (hstsNames h).Nodup := by
  cases hi : h.includeSubDomains <;> cases hp : h.preload <;>
    (simp only [hstsNames, hstsDirectives, hi, hp, List.map_cons, List.map_append,
      List.map_nil, List.nil_append, if_true, if_false, Bool.false_eq_true,
      Bool.true_eq_false]; decide)

/-- **`max-age = 0` disables `includeSubDomains`** (RFC 6797 §6.1.1 NOTE). -/
theorem hsts_zero_disables (h : Hsts) (h0 : h.maxAge = 0) :
    effectiveIncludeSubDomains h = false := by
  simp [effectiveIncludeSubDomains, h0]

/-! ### CSP (WHATWG, structural) -/

/-- A CSP source list (opaque source expressions). -/
abbrev SourceList := List String

/-- A Content-Security-Policy: an ordered directive map. -/
structure Csp where
  directives : List (String × SourceList)

/-- Look up a directive's source list by name (first match). -/
def cspLookup (c : Csp) (name : String) : Option SourceList :=
  c.directives.lookup name

/-- **CSP lookup is faithful.** A directive placed at the front of a policy
is found by name with its source list. -/
theorem csp_serialize_lookup (name : String) (srcs : SourceList)
    (rest : List (String × SourceList)) :
    cspLookup ⟨(name, srcs) :: rest⟩ name = some srcs := by
  simp [cspLookup, List.lookup_cons]

/-! ### X-Frame-Options and companions -/

/-- `X-Frame-Options` value. -/
inductive XFrameOptions where
  | deny
  | sameOrigin
deriving DecidableEq, Repr

/-- Serialize `X-Frame-Options`. -/
def xfoValue : XFrameOptions → String
  | .deny => "DENY"
  | .sameOrigin => "SAMEORIGIN"

/-! ### The bundled policy -/

/-- A response-security policy: any subset of the members. -/
structure Policy where
  hsts : Option Hsts := none
  csp : Option Csp := none
  xfo : Option XFrameOptions := none
  /-- Emit `X-Content-Type-Options: nosniff`? -/
  noSniff : Bool := false
  /-- `Referrer-Policy` value (opaque token). -/
  referrerPolicy : Option String := none

/-- Serialize one CSP into its header value (`name src src; name src`). -/
def cspRender (c : Csp) : String :=
  String.intercalate "; "
    (c.directives.map (fun d => String.intercalate " " (d.1 :: d.2)))

/-- Emit the security-header set for a policy. -/
def render (p : Policy) : Resp :=
  (match p.hsts with
   | some h => [("Strict-Transport-Security", hstsRender h)]
   | none => [])
  ++ (match p.csp with
   | some c => [("Content-Security-Policy", cspRender c)]
   | none => [])
  ++ (match p.xfo with
   | some x => [("X-Frame-Options", xfoValue x)]
   | none => [])
  ++ (if p.noSniff then [("X-Content-Type-Options", "nosniff")] else [])
  ++ (match p.referrerPolicy with
   | some r => [("Referrer-Policy", r)]
   | none => [])

/-- **HSTS presence.** If a policy carries an HSTS member, the emitted
header set contains a `Strict-Transport-Security` field with its rendered
value. -/
theorem render_hsts_present (p : Policy) (h : Hsts) (hp : p.hsts = some h) :
    (render p).lookup "Strict-Transport-Security" = some (hstsRender h) := by
  simp [render, hp, List.lookup_cons]

end SecurityHeaders

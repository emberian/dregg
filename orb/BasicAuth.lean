/-!
# HTTP Basic authentication middleware (RFC 7617)

A sans-IO model of the request-authentication decision a server front end makes
under the `Basic` authentication scheme. The machine is a total, deterministic
function from an inbound request to one of two outcomes: **ok** (the request is
authenticated as a named user, mapped to HTTP 200) or **challenge** (the server
returns HTTP 401 with a `WWW-Authenticate: Basic realm="…"` header inviting the
client to retry with credentials).

The scheme captured (RFC 7617 §2):

* A request carrying an `Authorization` header whose scheme is `Basic` supplies
  `token68` credentials. RFC 7617 §2: *both scheme and parameter names are
  matched case-insensitively.* Extracting the `token68` from an `Authorization`
  value is the boundary `Config.parseBasic`.
* The `token68` is the Base64 (RFC 4648 §4) encoding of `user-id ":" password`.
  RFC 7617 §2: the credentials are recovered by base64-decoding and splitting on
  the **first** colon; a `user-id` may not itself contain a colon. Recovering
  the `(user-id, password)` pair is the boundary `Config.decodeUserPass`, which
  yields `none` when the octets are not valid Base64 or contain no colon.
* The recovered password is verified against the stored credential by the
  uninterpreted boundary predicate `Config.verify` — the model of a
  constant-time password-hash comparison (e.g. bcrypt). This is the one and
  only trust boundary; nothing but a `true` from it can produce `ok`.
* On any failure — no `Authorization` header, a non-`Basic` scheme, undecodable
  credentials, or a rejected password — the server issues the realm challenge
  (RFC 7617 §2): `WWW-Authenticate: Basic realm="<realm>"`, optionally carrying
  the `charset` auth-param (RFC 7617 §2.1).

## The crypto / decode boundary

`parseBasic`, `decodeUserPass`, and `verify` are named, uninterpreted total
fields of `Config`. The machine never implements Base64 or a password hash — it
is the policy around them. Every theorem quantifies over all `Config`, hence
over all behaviors of these boundaries.

## Theorems

* `basic_rejects_bad_cred` — the only path to `ok` runs the password through
  `verify` and gets `true`; therefore a request whose recovered credentials the
  boundary rejects can never be authenticated (never 200).
* `basic_bad_cred_challenges` — the direct form: decodable credentials that
  `verify` rejects yield exactly the realm challenge.
* `basic_no_creds_challenges` — a request with no `Authorization` header yields
  the realm challenge.
* `challenge_names_realm` — every challenge header names the configured realm.
* `ok_is_200` / `challenge_is_401` — the outcomes map to the RFC's status
  codes.
* `authenticate_total` — the decision is always exactly one of ok / challenge.

## Left as boundary / UNCLOSED

The correctness of Base64 decoding, the first-colon split, the case-insensitive
scheme match, and the password-hash comparison itself are boundaries, not
results. Character-encoding of `user-pass` (RFC 7617 §2, left undefined by the
spec beyond US-ASCII compatibility) and the `charset` negotiation semantics
(RFC 7617 §2.1) are carried as inert configuration, not modeled behaviorally.
The `407` proxy variant (RFC 7617 §2) is not modeled.
-/

namespace BasicAuth

/-- The inbound request surface the machine reads: the `Authorization` header
value, if present. -/
structure Request where
  authorization : Option String
deriving Repr

/-- The decision outcome. -/
inductive Outcome where
  /-- Authenticated as this user (HTTP 200). -/
  | ok (user : String)
  /-- Not authenticated: return this `WWW-Authenticate` value (HTTP 401). -/
  | challenge (www : String)
deriving Repr, DecidableEq

/-- The HTTP status the outcome maps to. -/
def Outcome.status : Outcome → Nat
  | .ok _ => 200
  | .challenge _ => 401

/-- Static configuration and the named decode/verify boundary. Every
function-valued field is uninterpreted and total. -/
structure Config where
  /-- The protection-space realm (RFC 7617 §2). -/
  realm : String
  /-- Optional `charset` auth-param (RFC 7617 §2.1), carried inertly. -/
  charset : Option String
  /-- Extract the `token68` from an `Authorization` value if its scheme is
  `Basic`, matched case-insensitively (boundary). -/
  parseBasic : String → Option String
  /-- Base64-decode the `token68` and split on the first colon into
  `(user-id, password)`; `none` if not valid Base64 or no colon (boundary). -/
  decodeUserPass : String → Option (String × String)
  /-- **The trust boundary.** Verify a password against the stored credential
  for a user-id (models a constant-time bcrypt compare). Uninterpreted. -/
  verify : String → String → Bool

/-- The `WWW-Authenticate` challenge header value (RFC 7617 §2), optionally
carrying the `charset` param (RFC 7617 §2.1). -/
def challengeHeader (cfg : Config) : String :=
  match cfg.charset with
  | none => "Basic realm=\"" ++ cfg.realm ++ "\""
  | some cs => "Basic realm=\"" ++ cfg.realm ++ "\", charset=\"" ++ cs ++ "\""

/-- The realm challenge outcome. -/
def challenge (cfg : Config) : Outcome := .challenge (challengeHeader cfg)

/-! ## The decision -/

/-- The full Basic-authentication decision: parse the scheme, decode the
credentials, verify the password. Total and deterministic. The only path to
`ok` passes `verify`. -/
def authenticate (cfg : Config) (req : Request) : Outcome :=
  match req.authorization with
  | none => challenge cfg
  | some v => match cfg.parseBasic v with
    | none => challenge cfg
    | some tok => match cfg.decodeUserPass tok with
      | none => challenge cfg
      | some (user, pass) =>
        if cfg.verify user pass then .ok user
        else challenge cfg

/-! ## Theorems -/

/-- **Totality.** Every request gets exactly one of the two outcomes. -/
theorem authenticate_total (cfg : Config) (req : Request) :
    (∃ u, authenticate cfg req = .ok u) ∨
    (∃ w, authenticate cfg req = .challenge w) := by
  cases h : authenticate cfg req with
  | ok u => exact Or.inl ⟨u, rfl⟩
  | challenge w => exact Or.inr ⟨w, rfl⟩

/-- Inversion: an `ok` outcome forces a `Basic` scheme, decodable credentials,
and a password the boundary accepted. -/
theorem authenticate_ok (cfg : Config) (req : Request) {user : String}
    (h : authenticate cfg req = .ok user) :
    ∃ v tok pass, req.authorization = some v ∧
      cfg.parseBasic v = some tok ∧
      cfg.decodeUserPass tok = some (user, pass) ∧
      cfg.verify user pass = true := by
  cases hv : req.authorization with
  | none => simp [authenticate, challenge, hv] at h
  | some v =>
    cases ht : cfg.parseBasic v with
    | none => simp [authenticate, challenge, hv, ht] at h
    | some tok =>
      cases hd : cfg.decodeUserPass tok with
      | none => simp [authenticate, challenge, hv, ht, hd] at h
      | some up =>
        obtain ⟨u, p⟩ := up
        simp only [authenticate, hv, ht, hd] at h
        by_cases hb : cfg.verify u p = true
        · rw [if_pos hb] at h
          -- h : Outcome.ok u = Outcome.ok user
          injection h with hu
          subst hu
          exact ⟨v, tok, p, rfl, ht, hd, hb⟩
        · rw [if_neg hb] at h
          exact absurd h.symm (by simp [challenge])

/-- **Bad credentials are never authenticated.** The only path to `ok` runs the
recovered password through `verify` and gets `true`; the boundary is the only
trust. Contrapositive: a `verify`-rejected request is never 200. -/
theorem basic_rejects_bad_cred (cfg : Config) (req : Request) {user : String}
    (h : authenticate cfg req = .ok user) :
    ∃ tok pass, cfg.decodeUserPass tok = some (user, pass) ∧
      cfg.verify user pass = true := by
  obtain ⟨_, tok, pass, _, _, hd, hv⟩ := authenticate_ok cfg req h
  exact ⟨tok, pass, hd, hv⟩

/-- **Bad credentials get the challenge**, direct form: if the credentials
decode but `verify` rejects the password, the decision is exactly the realm
challenge — a 401, never a 200. -/
theorem basic_bad_cred_challenges (cfg : Config) (v tok user pass : String)
    (hv : cfg.parseBasic v = some tok)
    (hd : cfg.decodeUserPass tok = some (user, pass))
    (hbad : cfg.verify user pass = false) :
    authenticate cfg { authorization := some v } = challenge cfg := by
  simp only [authenticate, hv, hd]
  rw [if_neg (by rw [hbad]; exact Bool.false_ne_true)]

/-- A request with no `Authorization` header is challenged with the realm. -/
theorem basic_no_creds_challenges (cfg : Config)
    (req : Request) (h : req.authorization = none) :
    authenticate cfg req = challenge cfg := by
  simp [authenticate, h]

/-- Every challenge carries exactly the realm header (RFC 7617 §2). -/
theorem challenge_is_realm_header (cfg : Config) :
    challenge cfg = .challenge (challengeHeader cfg) := rfl

/-- Without a `charset`, the challenge header names the realm literally
(RFC 7617 §2). -/
theorem challengeHeader_names_realm (cfg : Config) (h : cfg.charset = none) :
    challengeHeader cfg = "Basic realm=\"" ++ cfg.realm ++ "\"" := by
  simp [challengeHeader, h]

/-- With a `charset`, the header names both the realm and the charset
(RFC 7617 §2.1). -/
theorem challengeHeader_names_realm_charset (cfg : Config) (cs : String)
    (h : cfg.charset = some cs) :
    challengeHeader cfg =
      "Basic realm=\"" ++ cfg.realm ++ "\", charset=\"" ++ cs ++ "\"" := by
  simp [challengeHeader, h]

/-- An `ok` outcome is HTTP 200. -/
theorem ok_is_200 (u : String) : (Outcome.ok u).status = 200 := rfl

/-- A challenge outcome is HTTP 401. -/
theorem challenge_is_401 (cfg : Config) : (challenge cfg).status = 401 := rfl

/-- The status of the whole decision is 401 whenever it is not an `ok`. -/
theorem not_ok_is_401 (cfg : Config) (req : Request)
    (h : ∀ u, authenticate cfg req ≠ .ok u) :
    (authenticate cfg req).status = 401 := by
  rcases authenticate_total cfg req with ⟨u, hu⟩ | ⟨w, hw⟩
  · exact absurd hu (h u)
  · rw [hw]; rfl

end BasicAuth

#print axioms BasicAuth.basic_rejects_bad_cred
#print axioms BasicAuth.basic_bad_cred_challenges
#print axioms BasicAuth.basic_no_creds_challenges
#print axioms BasicAuth.authenticate_total
#print axioms BasicAuth.not_ok_is_401

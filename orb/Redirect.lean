/-
# Redirect — the 3xx redirection responses (RFC 9110 §15.4)

A total model of a server's redirect handler: pick a redirection status
code, build the `Location` header by substituting the request's path and
query into a configured template, and (for a user agent following the
redirect) decide what request method the followed request carries.

Captured:

  * **The four method-explicit redirect codes** (RFC 9110 §15.4):
    `301 Moved Permanently`, `302 Found`, `307 Temporary Redirect`,
    `308 Permanent Redirect`. Each is classified on two axes the RFC draws:
    permanent vs temporary, and method-preserving vs method-may-change.
    RFC 9110 §15.4.8/§15.4.9: 307 and 308 are method-preserving; §15.4.2/
    §15.4.3 (with the historical note): 301 and 302 allow a POST to be
    redirected as GET.
  * **`Location` template substitution**: the configured template is a token
    list of literals and the `{path}` / `{query}` placeholders (a common
    rewrite-rule idiom, e.g. `https://{...}{path}?{query}`). Rendering
    substitutes the request's actual path and query verbatim, in order.
  * **The followed request method** (RFC 9110 §15.4 step 4): a
    method-preserving code resends the original method; a non-preserving
    code downgrades an unsafe method to GET.

Theorems:
  * `redirect_location_wellformed` — the response `Location` is exactly the
    faithful in-order substitution of the request's path/query into the
    template (render = in-order concatenation of token values), and the status is a
    genuine 3xx redirect code that carries a `Location`.
  * `render_eq_join`             — substitution is faithful: every `{path}`
                                   becomes the request path, every `{query}`
                                   the request query, literals unchanged.
  * `method_preserved`           — 307/308 resend the original method.
  * `method_safe_downgrade`      — 301/302 downgrade to GET.
  * `status_is_redirect`         — the status is one of {301,302,307,308}.

Left as a boundary / UNCLOSED:
  * The template is already tokenized; parsing a raw template string into
    tokens (finding `{path}`/`{query}`) is not modeled.
  * `Location` is produced as an opaque `String`; this file does not model
    resolving a relative `Location` against the request target (RFC 9110
    §15.4 step 1) nor URI syntax validity (RFC 3986) beyond faithful
    concatenation. `303 See Other` and `300`/`304`/`305` are out of scope
    (this file models the four method-explicit codes).
-/

namespace Redirect

/-! ## Redirection status codes (RFC 9110 §15.4) -/

/-- The four method-explicit redirect status codes (RFC 9110 §15.4.2,
§15.4.3, §15.4.8, §15.4.9). -/
inductive Code where
  | moved301   -- 301 Moved Permanently
  | found302   -- 302 Found
  | temp307    -- 307 Temporary Redirect
  | perm308    -- 308 Permanent Redirect
deriving DecidableEq, Repr

/-- The numeric status line. -/
def Code.status : Code → Nat
  | .moved301 => 301
  | .found302 => 302
  | .temp307 => 307
  | .perm308 => 308

/-- Permanent (301, 308) vs temporary (302, 307): whether the client SHOULD
update stored references (RFC 9110 §15.4.2 / §15.4.9 vs §15.4.3 / §15.4.8). -/
def Code.permanent : Code → Bool
  | .moved301 => true
  | .found302 => false
  | .temp307 => false
  | .perm308 => true

/-- Method-preserving (307, 308) vs method-may-change (301, 302). RFC 9110
§15.4.8/§15.4.9 define 307/308 to preserve the method; §15.4.2/§15.4.3 (with
the note) allow 301/302 to redirect a POST as GET. -/
def Code.methodPreserving : Code → Bool
  | .moved301 => false
  | .found302 => false
  | .temp307 => true
  | .perm308 => true

/-! ## Request methods (the subset relevant to redirect method handling) -/

/-- Request methods, coarsely: the safe idempotent read `get`/`head` and a
representative unsafe method `post` (RFC 9110 §9.2.1 safe methods); `other`
stands for any further method. -/
inductive Method where
  | get | head | post | other
deriving DecidableEq, Repr

/-! ## The Location template -/

/-- A template token: a literal chunk, or a placeholder substituted at
render time with the request's path or query string. -/
inductive Tok where
  | lit (s : String)
  | path
  | query
deriving DecidableEq, Repr

/-- The value a token denotes for a given request path and query. -/
def Tok.value (path query : String) : Tok → String
  | .lit s => s
  | .path => path
  | .query => query

/-- Render a template: substitute the request's path and query into the
placeholders and concatenate all token values in order. -/
def render (toks : List Tok) (path query : String) : String :=
  match toks with
  | [] => ""
  | t :: rest => t.value path query ++ render rest path query

/-- The faithful substitution as a right fold over the token values: map
each token to its value for this request, then concatenate in order. This
is the reference against which `render` is proved faithful. -/
def subst (path query : String) (toks : List Tok) : String :=
  (toks.map (Tok.value path query)).foldr (· ++ ·) ""

/-! ## The redirect response -/

/-- A redirect response: a status code and the built `Location` header. -/
structure Resp where
  status : Nat
  location : String
deriving DecidableEq, Repr

/-- Build the redirect response for a request whose path/query are given,
under a configured status code and `Location` template. -/
def redirect (code : Code) (template : List Tok) (path query : String) : Resp :=
  { status := code.status, location := render template path query }

/-! ## Faithful substitution -/

/-- **`render_eq_join`.** Rendering is exactly the in-order concatenation of
the token values: every `{path}` placeholder becomes the request path
verbatim, every `{query}` the request query, literals pass through unchanged,
all in order. This is the faithful-substitution property. -/
theorem render_eq_join (toks : List Tok) (path query : String) :
    render toks path query = subst path query toks := by
  induction toks with
  | nil => rfl
  | cons t rest ih =>
    simp only [render, subst, List.map_cons, List.foldr_cons, ih]

/-- A `{path}` placeholder renders as exactly the request path. -/
theorem render_path (path query : String) :
    render [Tok.path] path query = path := by
  simp [render, Tok.value]

/-- A `{query}` placeholder renders as exactly the request query. -/
theorem render_query (path query : String) :
    render [Tok.query] path query = query := by
  simp [render, Tok.value]

/-! ## Well-formedness -/

/-- The status codes this handler ever emits: the four §15.4 redirect codes. -/
def redirectStatuses : List Nat := [301, 302, 307, 308]

/-- Every `Code` maps to a status in `redirectStatuses`. -/
theorem status_mem (code : Code) : code.status ∈ redirectStatuses := by
  cases code <;> decide

/-- **`status_is_redirect`.** A redirect response carries one of the four
§15.4 redirect status codes — always a 3xx that comes with a `Location`. -/
theorem status_is_redirect (code : Code) (template : List Tok)
    (path query : String) :
    (redirect code template path query).status ∈ redirectStatuses :=
  status_mem code

/-- **`redirect_location_wellformed`.** The redirect response is well-formed:
(1) its `Location` is exactly the faithful in-order substitution of the
request's path and query into the template (no placeholder is dropped,
duplicated, or reordered — it is the in-order concatenation of the token values), and
(2) its status is a genuine §15.4 redirect code that carries a `Location`. -/
theorem redirect_location_wellformed (code : Code) (template : List Tok)
    (path query : String) :
    (redirect code template path query).location
        = subst path query template ∧
    (redirect code template path query).status ∈ redirectStatuses := by
  refine ⟨?_, status_mem code⟩
  simp only [redirect, render_eq_join]

/-! ## The followed request method (RFC 9110 §15.4 step 4) -/

/-- The method a user agent's followed request carries: a method-preserving
code (307/308) resends the original method; a non-preserving code (301/302)
downgrades to GET (the prevailing-practice safe choice, RFC 9110 §15.4). A
`head` stays `head` since it is already safe. -/
def followedMethod (code : Code) (m : Method) : Method :=
  if code.methodPreserving then m
  else match m with
       | .head => .head
       | _ => .get

/-- **`method_preserved`.** A method-preserving redirect (307/308) resends the
original request method unchanged (RFC 9110 §15.4.8/§15.4.9). -/
theorem method_preserved (code : Code) (m : Method)
    (h : code.methodPreserving = true) :
    followedMethod code m = m := by
  simp only [followedMethod, h, if_true]

/-- **`method_safe_downgrade`.** A non-method-preserving redirect (301/302)
downgrades an unsafe method (`post`/`other`) to GET (RFC 9110 §15.4.2/
§15.4.3). -/
theorem method_safe_downgrade (code : Code) (m : Method)
    (h : code.methodPreserving = false)
    (hunsafe : m = Method.post ∨ m = Method.other) :
    followedMethod code m = Method.get := by
  rcases hunsafe with hm | hm <;> subst hm <;>
    simp only [followedMethod, h, Bool.false_eq_true, if_false]

/-! ## Axis classification (RFC 9110 §15.4) -/

/-- 307 and 308 are exactly the method-preserving codes. -/
theorem preserving_iff (code : Code) :
    code.methodPreserving = true ↔ (code = .temp307 ∨ code = .perm308) := by
  cases code <;> simp [Code.methodPreserving]

/-- 301 and 308 are exactly the permanent codes. -/
theorem permanent_iff (code : Code) :
    code.permanent = true ↔ (code = .moved301 ∨ code = .perm308) := by
  cases code <;> simp [Code.permanent]

/-! ## Concrete witnesses -/

/-- A canonical rewrite: `https://new.example{path}?{query}` on request
`/a/b` with query `x=1` yields the full absolute `Location`. -/
theorem redirect_example :
    (redirect .perm308
      [Tok.lit "https://new.example", Tok.path, Tok.lit "?", Tok.query]
      "/a/b" "x=1").location = "https://new.example/a/b?x=1" := by
  simp [redirect, render, Tok.value]

/-- The same rewrite carries status 308. -/
theorem redirect_example_status :
    (redirect .perm308
      [Tok.lit "https://new.example", Tok.path, Tok.lit "?", Tok.query]
      "/a/b" "x=1").status = 308 := by decide

/-- A 302 downgrades a POST to a GET on the followed request. -/
theorem post_downgrades_on_302 :
    followedMethod .found302 .post = .get := by decide

/-- A 307 preserves a POST on the followed request. -/
theorem post_preserved_on_307 :
    followedMethod .temp307 .post = .post := by decide

end Redirect

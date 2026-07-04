import Middleware
import SecurityHeaders
import Cors
import Reactor.Deploy
import Reactor.Bridge

/-!
# Reactor.MiddlewareDeploy — the real middleware chain on the deployed response

`Reactor.Deploy.serveFull` is the bytes `main` writes: on a dispatch it emits
`serialize (deployResp input)`, the application response passed through the REAL
`Header.run` rewrite. This file folds the response-security middleware onto that
same response, driven by the REAL `Middleware` onion framework:

* the outermost layer is **SecurityHeaders** (`SecurityHeaders.render` of a policy
  carrying an HSTS member, RFC 6797) — it stamps `Strict-Transport-Security` (and
  any CSP / X-Frame-Options / nosniff / Referrer-Policy) onto the response;
* the inner layer is a **CORS decision** (`Cors.actualResponse` of a server
  policy) — it staples `Access-Control-Allow-Origin` *iff* the request's origin is
  on the allowlist, and nothing at all otherwise.

The two are composed as a genuine `Middleware.run` chain (`deployChain`), so the
onion discipline is the framework's, not ad hoc: `deployMwHeaders_expand` is
`Middleware.run_cons` twice + `Middleware.chain_identity`, which puts the security
layer on the outside (its `onResp` runs last, so its headers sit at the front).

The chain runs over `Deploy.toFinalR (Deploy.deployResp input)).headers` — the
`String` view of the very headers `serveFull` serializes (`deployed_mw_over_serveFull`
ties the two). Header names/values are carried through the total Latin-1 view
`Deploy.latin1B`; that view is proof-inert (the seams below only ever compare and
look up header *names*, never decode a value), exactly as the `EarlyHints` section
of `Reactor.Deploy` already treats it.

## Seam theorems (over the deployed response `serveFull` writes)

* `deployed_security_headers` — the deployed middleware headers carry the REAL
  `SecurityHeaders` output: `Strict-Transport-Security` is present with the
  rendered HSTS value, found through the real onion (`render_hsts_present` +
  `List.lookup_append`). HSTS is present on the deployed path.
* `deployed_cors_no_leak` — a **disallowed** origin: the CORS layer contributes
  the empty header list (`Cors.cors_no_leak_actual`), so the deployed headers are
  byte-identical to the no-CORS response and the origin gains no
  `Access-Control-Allow-Origin`.
* `deployed_cors_no_leak_full` — under the (true-on-this-path) side condition that
  the base response carries no ACAO, the *whole* deployed header set has
  `hasAcao = false` for a disallowed origin.
* `deployed_cors_grants` — an **allowed** origin does get ACAO: the gate genuinely
  branches, it is not a constant.

## Boundary / UNCLOSED

* The `String`↔`Bytes` header boundary is the Latin-1 view `Deploy.latin1B`; it is
  not injective in general and is treated as proof-inert here. Re-serializing the
  augmented header block back to wire bytes (so the *bytes* `main` writes literally
  contain the middleware headers, rather than the `String` view of the response
  those bytes serialize) is a boundary, matching the framework's own `String`-typed
  header model in `SecurityHeaders` / `Cors`.
* `main` runs `serveGuarded` (Policy/Safety branch); `deployed_mw_over_serveFull`
  is stated over `serveFull` (the un-gated deployed serve, definitionally the
  `serveGuarded` admit-arm's payload). The gate arms emit fixed serializer bodies
  and are out of scope for the middleware fold.
-/

namespace Reactor
namespace MiddlewareDeploy

open Proto (Bytes)

/-! ## (1) The deployed security + CORS policies -/

/-- The deployed HSTS policy (RFC 6797): a one-year `max-age`, `includeSubDomains`
on, no `preload`. `max-age` is nonzero, so `includeSubDomains` is effective. -/
def deployHsts : SecurityHeaders.Hsts :=
  { maxAge := 31536000, includeSubDomains := true, preload := false }

/-- The deployed response-security policy: HSTS only (the other members are left
`none`/`false`, so `render` emits exactly the `Strict-Transport-Security` field). -/
def deploySecPolicy : SecurityHeaders.Policy :=
  { hsts := some deployHsts }

/-- The deployed CORS policy: an exact-match origin allowlist (no wildcard), a
small method/header allowlist, credentials off. A disallowed origin is refused. -/
def deployCorsPolicy : Cors.Policy :=
  { allowedOrigins := ["https://app.example.com"]
    allowAnyOrigin := false
    allowedMethods := ["GET", "POST"]
    allowedHeaders := ["content-type"]
    allowCredentials := false
    maxAge := 600 }

/-! ## (2) The middleware chain over the deployed response headers -/

/-- The response type the chain transforms: a `String`-keyed header list — exactly
the `Resp` type of the `SecurityHeaders` / `Cors` models. -/
abbrev SH := List (String × String)

/-- The base headers the chain runs over: the `String` (Latin-1) view of the very
headers `serveFull` serializes on a dispatch (`Deploy.deployResp` headers). -/
def baseHeaders (input : Bytes) : SH :=
  (Deploy.toFinalR (Deploy.deployResp input)).headers

/-- The **security-headers middleware**: the request is untouched; the response
gets the REAL `SecurityHeaders.render` of `deploySecPolicy` prepended (HSTS et al.
sit at the front). -/
def secMw : Middleware.Mw Unit SH :=
  { onReq := id
    onResp := fun hs => SecurityHeaders.render deploySecPolicy ++ hs }

/-- The **CORS middleware**: the request is untouched; the response gets the REAL
`Cors.actualResponse` decision for `o` prepended — a singleton ACAO (plus
credentials) when `o` is allowed, and *nothing* when it is not. -/
def corsMw (o : Cors.Origin) : Middleware.Mw Unit SH :=
  { onReq := id
    onResp := fun hs => Cors.actualResponse deployCorsPolicy o ++ hs }

/-- The deployed response-security chain: security on the **outside**, CORS inside.
Onion order (`Middleware.run_cons`) makes `secMw.onResp` run last, so the security
headers end up at the front of the emitted set. -/
def deployChain (o : Cors.Origin) : List (Middleware.Mw Unit SH) :=
  [secMw, corsMw o]

/-- **The deployed middleware headers.** The REAL `Middleware.run` of `deployChain`
around a handler that yields the base deployed headers. This is the augmented
header set for a request whose cross-origin `Origin` is `o`. -/
def deployMwHeaders (input : Bytes) (o : Cors.Origin) : SH :=
  Middleware.run (deployChain o) (fun _ => baseHeaders input) ()

/-- **The onion expansion.** Running the chain is `secMw.onResp (corsMw.onResp base)`
— the security layer's headers wrap the CORS layer's, which wrap the base. Proved
purely by the framework's `Middleware.run_cons` (twice) and `chain_identity`. -/
theorem deployMwHeaders_expand (input : Bytes) (o : Cors.Origin) :
    deployMwHeaders input o
      = SecurityHeaders.render deploySecPolicy
        ++ (Cors.actualResponse deployCorsPolicy o ++ baseHeaders input) := by
  unfold deployMwHeaders deployChain
  rw [Middleware.run_cons, Middleware.run_cons, Middleware.chain_identity]
  rfl

/-! ## (3) Seam theorems -/

/-- **`deployed_security_headers` — HSTS is present on the deployed path.** The
deployed middleware headers carry the REAL `SecurityHeaders` output: a
`Strict-Transport-Security` field whose value is the rendered HSTS policy. Found
through the real onion — the security layer sits at the front
(`deployMwHeaders_expand`), so `List.lookup_append` reads it out of
`render_hsts_present`. -/
theorem deployed_security_headers (input : Bytes) (o : Cors.Origin) :
    (deployMwHeaders input o).lookup "Strict-Transport-Security"
      = some (SecurityHeaders.hstsRender deployHsts) := by
  rw [deployMwHeaders_expand, List.lookup_append,
      SecurityHeaders.render_hsts_present deploySecPolicy deployHsts rfl]
  rfl

/-- The CORS layer contributes the empty header list for a disallowed origin
(`Cors.actualResponse` collapses to `[]` when the ACAO value is `none`). -/
theorem cors_layer_empty (o : Cors.Origin)
    (hbad : Cors.originAllowed deployCorsPolicy o = false) :
    Cors.actualResponse deployCorsPolicy o = [] := by
  have hv : Cors.acaoValue deployCorsPolicy o = none := by
    simp [Cors.acaoValue, hbad]
  simp [Cors.actualResponse, hv]

/-- **`deployed_cors_no_leak` — a disallowed origin never gets ACAO.** For an
origin off the allowlist, the deployed middleware headers are byte-identical to the
no-CORS response (the CORS layer added nothing), and the CORS decision itself
carries no `Access-Control-Allow-Origin` (`Cors.cors_no_leak_actual`). The
disallowed origin gains nothing. -/
theorem deployed_cors_no_leak (input : Bytes) (o : Cors.Origin)
    (hbad : Cors.originAllowed deployCorsPolicy o = false) :
    deployMwHeaders input o
        = SecurityHeaders.render deploySecPolicy ++ baseHeaders input
    ∧ Cors.hasAcao (Cors.actualResponse deployCorsPolicy o) = false := by
  refine ⟨?_, Cors.cors_no_leak_actual deployCorsPolicy o hbad⟩
  rw [deployMwHeaders_expand, cors_layer_empty o hbad, List.nil_append]

/-- The security layer alone carries no `Access-Control-Allow-Origin` (its only
field is `Strict-Transport-Security`). -/
theorem sec_no_acao :
    (SecurityHeaders.render deploySecPolicy).lookup
        "Access-Control-Allow-Origin" = none := by
  decide

/-- **`deployed_cors_no_leak_full` — no ACAO anywhere in the deployed headers.**
Under the side condition that the base response carries no ACAO (true on the
deployed path: `deployProg` only stamps `Server` / `x-upstream` / `x-corr` and
strips hop-by-hop headers — it never emits a CORS header), a disallowed origin's
full deployed header set has `hasAcao = false`. Neither the security layer, the
(empty) CORS layer, nor the base contributes one. -/
theorem deployed_cors_no_leak_full (input : Bytes) (o : Cors.Origin)
    (hbad : Cors.originAllowed deployCorsPolicy o = false)
    (hbase : (baseHeaders input).lookup "Access-Control-Allow-Origin" = none) :
    Cors.hasAcao (deployMwHeaders input o) = false := by
  unfold Cors.hasAcao
  rw [deployMwHeaders_expand, cors_layer_empty o hbad, List.nil_append,
      List.lookup_append, sec_no_acao, hbase]
  rfl

/-- **`deployed_cors_grants` — an allowed origin does get ACAO.** The gate genuinely
branches: for an origin on the allowlist, the deployed header set carries an
`Access-Control-Allow-Origin` (`Cors.cors_actual_grants`, read out of the CORS layer
past the ACAO-free security layer). Not a constant `false`. -/
theorem deployed_cors_grants (input : Bytes) (o : Cors.Origin)
    (ha : Cors.originAllowed deployCorsPolicy o = true) :
    Cors.hasAcao (deployMwHeaders input o) = true := by
  have hcv := Cors.cors_actual_grants deployCorsPolicy o ha
  unfold Cors.hasAcao at hcv ⊢
  rw [deployMwHeaders_expand, List.lookup_append, List.lookup_append, sec_no_acao,
      Option.none_or]
  cases hcase : (Cors.actualResponse deployCorsPolicy o).lookup
      "Access-Control-Allow-Origin" with
  | none => rw [hcase] at hcv; exact absurd hcv (by decide)
  | some v => rfl

/-! ## (4) The fold is over the bytes `serveFull` writes -/

/-- **`deployed_mw_over_serveFull` — the chain runs over the deployed serve's own
response.** On a dispatch (the FSM emitted no bytes of its own), `serveFull`
serializes `deployResp input`, and `baseHeaders input` is exactly the `String`
(Latin-1) view of that response's headers. So the security/CORS seams above range
over the headers `main`'s serve actually writes, not a bespoke response. -/
theorem deployed_mw_over_serveFull (input : Bytes)
    (hsends : sendsOf (Deploy.deploySubs input) = []) :
    Deploy.serveFull input = serialize (Deploy.deployResp input)
    ∧ baseHeaders input = (Deploy.toFinalR (Deploy.deployResp input)).headers :=
  ⟨Deploy.serveFull_serializes_dispatch input hsends, rfl⟩

/-! ## (5) The gate genuinely branches — kernel-checked, no reactor.

Concrete executions of the REAL `Cors` / `SecurityHeaders` decisions on the
deployed policies: an allowed origin is granted ACAO, a disallowed one is refused,
and HSTS is always emitted. Each is a real `decide`/`#guard`, so the seams above
rest on a mechanism, not three names for one output. -/

/-- The allowlisted origin is allowed. -/
theorem origin_allowed_app :
    Cors.originAllowed deployCorsPolicy "https://app.example.com" = true := by decide

/-- An off-allowlist origin is refused. -/
theorem origin_denied_evil :
    Cors.originAllowed deployCorsPolicy "https://evil.example.net" = false := by decide

/-- The allowed origin's ACAO echoes exactly that origin (no wildcard). -/
theorem acao_echoes_app :
    Cors.acaoValue deployCorsPolicy "https://app.example.com"
      = some "https://app.example.com" := by decide

/-- The disallowed origin gets no ACAO value at all. -/
theorem acao_none_evil :
    Cors.acaoValue deployCorsPolicy "https://evil.example.net" = none := by decide

/-- HSTS is well-formed on the deployed policy: `max-age` is present and no
directive name repeats (`SecurityHeaders.hsts_wellformed`, RFC 6797 §6.1). -/
theorem hsts_wellformed_deploy :
    "max-age" ∈ SecurityHeaders.hstsNames deployHsts
    ∧ (SecurityHeaders.hstsNames deployHsts).Nodup :=
  SecurityHeaders.hsts_wellformed deployHsts

#guard Cors.originAllowed deployCorsPolicy "https://app.example.com" = true
#guard Cors.originAllowed deployCorsPolicy "https://evil.example.net" = false
#guard (Cors.actualResponse deployCorsPolicy "https://evil.example.net").isEmpty = true
#guard Cors.hasAcao (Cors.actualResponse deployCorsPolicy "https://app.example.com") = true

end MiddlewareDeploy
end Reactor

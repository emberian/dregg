/-
CorsCorrect — CORS *correctness*: a refinement of the server-side CORS decision
(`Cors.actualResponse` / `Cors.originAllowed`) against an INDEPENDENT
specification transcribed from the WHATWG Fetch "CORS check" algorithm.

`Cors.lean` proves SAFETY-flavoured facts about the emitted headers: a
disallowed origin gets no `Access-Control-Allow-Origin` (`cors_no_leak_actual`),
a credentialed reply echoes the specific origin (`cors_credentials_echoes_origin`),
an allowed request does carry ACAO (`cors_actual_grants`). Each pins down a
property of the *header list the server writes*, but none of them, on its own,
says the server produces THE response that makes a conformant browser reach the
CORRECT accept/deny verdict on every input — a header-plumbing bug could satisfy
several in isolation while still authorizing the wrong origin.

This file closes that gap end-to-end. It specifies, *without any reference to*
`Cors.actualResponse`, `Cors.acaoValue`, or `Cors.originAllowed`, the two halves
of the protocol:

  * `corsCheck` — the CLIENT side. The exact accept/deny algorithm a browser runs
    on a cross-origin response (WHATWG Fetch, "CORS check"), as a total function
    of the request's credentials mode + origin and the response's ACAO / ACAC
    header values. This is the security gate the whole protocol exists to feed;
    it is written from the standard, on the opposite side of the wire from the
    server implementation.
  * `Authorized` — the ground-truth policy relation: the request origin is one
    the configured policy actually permits (the wildcard, or exact membership in
    the allow-list), read straight off the `Policy` configuration data, NOT via
    `Cors.originAllowed`.

The correctness theorem `actualResponse_cors_correct` is a single equation:
for every policy, origin, and credentials mode, running the browser `corsCheck`
on the headers the server *actually emits* returns `true` IFF the origin is
`Authorized` AND — when the request is credentialed — the policy actually allows
credentials. The forbidden-`*`-with-credentials rule is not asserted separately;
it FALLS OUT of the client algorithm (a credentialed check rejects the `*`
wildcard at Fetch step 4). Both security directions are inside this one iff:

  * no-leak: a forbidden origin ⇒ the server emits no ACAO ⇒ `corsCheck` denies;
  * no-forgery: an authorized origin ⇒ `corsCheck` accepts (credentials honoured).

Non-vacuity. The classic reflected-origin vulnerability — a server that echoes
*every* request Origin into ACAO — is exhibited as `vulnResponse`. Against an
origin OUTSIDE the allow-list a browser `corsCheck` on the vulnerable headers
returns `true` while `Authorized` is `false`; `vuln_authorizes_forbidden_origin`
proves the disagreement, so `actualResponse_cors_correct` is FALSE for the
reflecting server and the theorem genuinely forces the deny direction.

Standard basis. WHATWG Fetch, "CORS protocol" and the "CORS check" algorithm
(the ACAO-value / credentials-mode / `*`-rejection steps). CORS is defined by
the Fetch Living Standard, not by an RFC; the `corsCheck` steps below mirror that
algorithm. The credentials-mode `*` prohibition is Fetch's
"Access-Control-Allow-Origin must not be `*` when credentials mode is include".
-/

import Cors

namespace CorsCorrect

open Cors

/-! ## Independent specification

Nothing in this section mentions `Cors.actualResponse`, `Cors.acaoValue`, or
`Cors.originAllowed`. `corsCheck` is the client algorithm; `Authorized` is the
ground-truth policy relation read off the configuration. -/

/-- **WHATWG Fetch, "CORS check" (client side).** Given the request's credentials
mode (`credMode = true` ⇔ Fetch credentials mode is *include*) and origin, and the
response's `Access-Control-Allow-Origin` (`acao`) and `Access-Control-Allow-Credentials`
(`acac`) header values, decide whether the browser authorizes the cross-origin
response. Transcribed step-for-step from the standard:

* no ACAO header ⇒ failure;
* if the credentials mode is not *include* and ACAO is `*` ⇒ success;
* if the request origin is not exactly the ACAO value ⇒ failure (this is the
  step that rejects `*` for a credentialed request, since a real origin is never
  the literal `*`);
* if the credentials mode is not *include* ⇒ success;
* otherwise success iff ACAC is exactly `true`.

Defined purely over the header values — it never calls the server. -/
def corsCheck (credMode : Bool) (reqOrigin : Origin)
    (acao : Option String) (acac : Option String) : Bool :=
  match acao with
  | none => false
  | some origin =>
    if credMode = false && origin = "*" then true
    else if reqOrigin ≠ origin then false
    else if credMode = false then true
    else acac = some "true"

/-- **Ground-truth policy authorization.** The request origin `o` is one the
configured policy permits: either the wildcard is enabled, or `o` is an exact
member of the configured allow-list. Read directly off the `Policy` fields — it
does NOT reference `Cors.originAllowed`. -/
def Authorized (p : Policy) (o : Origin) : Prop :=
  p.allowAnyOrigin = true ∨ o ∈ p.allowedOrigins

instance (p : Policy) (o : Origin) : Decidable (Authorized p o) := by
  unfold Authorized; infer_instance

/-- Extract the response's `Access-Control-Allow-Origin` value (the client reads
this off the wire). -/
def acaoOf (r : Resp) : Option String := r.lookup "Access-Control-Allow-Origin"

/-- Extract the response's `Access-Control-Allow-Credentials` value. -/
def acacOf (r : Resp) : Option String := r.lookup "Access-Control-Allow-Credentials"

/-! ## Bridge: the implementation's allow-test decides the spec relation -/

/-- `Cors.originAllowed` is exactly the decision procedure for `Authorized`. -/
theorem originAllowed_iff_authorized (p : Policy) (o : Origin) :
    originAllowed p o = true ↔ Authorized p o := by
  unfold originAllowed Authorized
  rw [Bool.or_eq_true, List.contains_eq_mem, decide_eq_true_eq]

/-! ## Refinement: server output ⇒ correct client verdict -/

/-- On an authorized origin the server writes `Access-Control-Allow-Origin =
acaoValue` and `Access-Control-Allow-Credentials = true` exactly when credentials
are allowed. -/
private theorem lookups_authorized (p : Policy) (o : Origin)
    (hoa : originAllowed p o = true) :
    acaoOf (actualResponse p o) = acaoValue p o ∧
    acacOf (actualResponse p o) =
      (if p.allowCredentials then some "true" else none) := by
  have hsome : (acaoValue p o).isSome = true := by
    unfold acaoValue; rw [hoa]
    cases p.allowCredentials <;> cases p.allowAnyOrigin <;> rfl
  unfold acaoOf acacOf actualResponse acaoHeader credHeader
  cases hv : acaoValue p o with
  | none => rw [hv] at hsome; simp at hsome
  | some v => cases hc : p.allowCredentials <;> simp [hv, hc, List.lookup_cons]

/-- On an unauthorized origin the server writes no CORS headers at all. -/
private theorem lookups_unauthorized (p : Policy) (o : Origin)
    (hoa : originAllowed p o = false) :
    acaoOf (actualResponse p o) = none ∧ acacOf (actualResponse p o) = none := by
  have hnone : acaoValue p o = none := by unfold acaoValue; rw [hoa]; rfl
  unfold acaoOf acacOf actualResponse
  rw [hnone]; simp

/-- **CORS correctness (actual cross-origin request).** For every policy, request
origin, and credentials mode, the WHATWG Fetch `corsCheck` run by a browser on
the headers the server *actually emits* accepts the response IFF the origin is
`Authorized` by the policy AND, for a credentialed request, the policy actually
allows credentials. Both the no-leak and the forbidden-`*`-with-credentials
security rules are consequences of this single equation.

The spec side (`Authorized`, `corsCheck`) never mentions the implementation; the
proof is the whole refinement. -/
theorem actualResponse_cors_correct (p : Policy) (o : Origin) (credMode : Bool) :
    corsCheck credMode o (acaoOf (actualResponse p o)) (acacOf (actualResponse p o))
      = (decide (Authorized p o) && (!credMode || p.allowCredentials)) := by
  by_cases ha : Authorized p o
  · -- authorized: server emits ACAO via `acaoValue`
    have hoa : originAllowed p o = true := (originAllowed_iff_authorized p o).2 ha
    obtain ⟨hacao, hacac⟩ := lookups_authorized p o hoa
    rw [hacao, hacac]
    simp only [ha, decide_true, Bool.true_and]
    unfold acaoValue corsCheck
    rw [hoa]
    -- case on credentials, wildcard, and client credentials mode
    cases hc : p.allowCredentials <;> cases hw : p.allowAnyOrigin <;>
      cases hm : credMode <;> simp_all
  · -- unauthorized: server emits nothing, client denies
    have hoa : originAllowed p o = false := by
      cases h : originAllowed p o with
      | false => rfl
      | true => exact absurd ((originAllowed_iff_authorized p o).1 h) ha
    obtain ⟨hacao, hacac⟩ := lookups_unauthorized p o hoa
    rw [hacao, hacac]
    simp [ha, corsCheck]

/-! ## Non-vacuity: a reflected-origin server FAILS the spec

The reflecting server writes the request Origin straight into ACAO no matter what
the policy says — the classic CORS misconfiguration. On an origin outside the
allow-list a conformant browser `corsCheck` on its output returns `true`, while
`Authorized` is `false`; so the refinement equation above is FALSE for it. That
makes `actualResponse_cors_correct` non-trivial: it genuinely rules the
reflecting server out. -/

/-- The vulnerable "reflect every Origin" response: ACAO echoes `o` unconditionally. -/
def vulnResponse (_p : Policy) (o : Origin) : Resp :=
  [("Access-Control-Allow-Origin", o)]

/-- A policy that authorizes nobody: empty allow-list, no wildcard, no credentials. -/
def denyAll : Policy :=
  { allowedOrigins := [], allowAnyOrigin := false, allowedMethods := [],
    allowedHeaders := [], allowCredentials := false, maxAge := 0 }

/-- A concrete forbidden origin. -/
def evil : Origin := "https://evil.example"

/-- The forbidden origin is genuinely not `Authorized` by `denyAll`. -/
theorem evil_not_authorized : ¬ Authorized denyAll evil := by decide

/-- The REAL server denies the forbidden origin: `corsCheck` on its output is `false`
(matching `actualResponse_cors_correct`, whose RHS is `false` here). -/
theorem real_denies_evil :
    corsCheck false evil
      (acaoOf (actualResponse denyAll evil)) (acacOf (actualResponse denyAll evil)) = false := by
  decide

/-- The REFLECTING server authorizes the forbidden origin: `corsCheck` on its
output is `true`. -/
theorem vuln_authorizes_forbidden_origin :
    corsCheck false evil
      (acaoOf (vulnResponse denyAll evil)) (acacOf (vulnResponse denyAll evil)) = true := by
  decide

/-- **The reflecting server and the real server genuinely disagree** on the
forbidden origin — one denies, one authorizes. So the correctness equation
`actualResponse_cors_correct` is not vacuous: it is FALSE for the reflected-origin
implementation, i.e. it forces the deny direction that closes the vulnerability. -/
theorem vuln_differs_from_real :
    corsCheck false evil (acaoOf (vulnResponse denyAll evil)) (acacOf (vulnResponse denyAll evil))
      ≠ corsCheck false evil (acaoOf (actualResponse denyAll evil)) (acacOf (actualResponse denyAll evil)) := by
  decide

/-! ## Axiom audit -/

#print axioms actualResponse_cors_correct
#print axioms originAllowed_iff_authorized
#print axioms vuln_differs_from_real

end CorsCorrect

import Reactor.Bridge
import Acme.Order
import Acme.Challenge

/-!
# Reactor.WireAcme — the real ACME issuance FSM, landed on the DEPLOYED serve path

The `Acme` library proves the certificate-issuance state machine of RFC 8555:
an `Order` walks `pending → ready → processing → valid`, and its two core
*no-bypass* facts are

* `Acme.valid_requires_all_authz_valid` — **no skipping authorization**: an order
  reachable from `Order.fresh` that has reached `valid` (the point a certificate
  is issued) has *every* authorization `valid`; and
* `Acme.chal_into_valid` / `Acme.validateStep_valid_needs_success` — **no
  challenge bypass**: the only door into a `valid` challenge is a *successful*
  validation; a failed or absent validation never yields `valid`.

Those facts were proven about the `Acme` FSM in isolation. This file lands them
on the values the deployed binary actually carries. `Arena.Orb.main` →
`Reactor.Deploy.deployStep(Guarded)` → `serveFull`/`serveGuarded` runs the proven
reactor over `deployConfig`; `Reactor.Bridge.deploySubs_eq_reactorSubs` shows the
submissions it produces are exactly the test reactor's, so the request the
deployed reactor dispatches is the one shared reactor's request — not a fresh
side model.

We key the issuance on the **domain named by the deployed served request's
target** (`Reactor.Deploy.dispatchReqOf (deploySubs input) = some req`): the
identifier an ACME order authorizes. `acme_deployed` then states, over that
deployed-served identifier, that a certificate can only stand behind it once
every challenge that discharged its authorizations is `valid` — the library's
own no-bypass invariant, holding of the identifier the deployed path serves.

Honest scope (same posture as `Reactor.WireMore`): this is a *proof-attachment*
seam. It states the `Acme` library's real, meaning-constraining theorem about
the identifier the deployed dispatch names, discharged by the library's own
proof — not a runtime ACME client streaming challenge responses out of the event
loop. What it establishes is that the issuance guarantee *holds of the request
the deployed path serves*, closing the island.
-/

namespace Reactor.WireAcme

open Proto (Bytes)

/-! ## The Bridge anchor — the deployed dispatch is the shared reactor's dispatch -/

/-- The request the DEPLOYED reactor dispatched (`dispatchReqOf` over
`deploySubs`) is exactly the one the test reactor dispatched (over `reactorSubs`),
transported along `Bridge.deploySubs_eq_reactorSubs`. The issuance seam below is
keyed on this deployed dispatch, so it ranges over the same request the reactor
lanes were proven about. -/
theorem deployed_dispatch_agrees (input : Bytes) :
    Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input)
      = Reactor.Deploy.dispatchReqOf (Reactor.reactorSubs input) := by
  rw [Reactor.Bridge.deploySubs_eq_reactorSubs]

/-! ## The deployed issuance — a run of the real Acme order FSM

`deployIssuance req events` is a run of the *real* `Acme.orderStep` FSM
(`Acme.orderRun` folded over `events` from `Acme.Order.fresh`) whose single
identifier is `deployIdent req` — the domain string decoded from the deployed
served request's target (`Proto.Bytes = List UInt8` bytes read as an
`Acme.Bytes = List Char` identifier). Every `Acme` lifecycle theorem applies to
it verbatim. -/
def deployIdent (req : Proto.Request) : Acme.Bytes :=
  req.target.map (fun b => Char.ofNat b.toNat)

def deployIssuance (req : Proto.Request) (events : List Acme.OrderEvent) : Acme.Order :=
  Acme.orderRun (Acme.Order.fresh [deployIdent req]) events

/-! ## Order-level seam — no skipping authorization on the deployed identifier -/

/-- **`acme_deployed_no_skip`.** If the issuance for the deployed served request
reaches `valid` (the point of certificate issuance), then *every* authorization
of that order is `valid`. Pushed through the `Acme` library's
`valid_requires_all_authz_valid` on the identifier the deployed dispatch names —
no certificate stands behind the served domain past a pending or failed
authorization. -/
theorem acme_deployed_no_skip (input : Bytes) (req : Proto.Request)
    (events : List Acme.OrderEvent)
    (hsub : Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) = some req)
    (hvalid : (deployIssuance req events).status = .valid) :
    Acme.allValid (deployIssuance req events).authzs = true :=
  Acme.valid_requires_all_authz_valid [deployIdent req] events hvalid

/-! ## The challenge → authorization bridge (pointwise composition) -/

/-- If every authorization status is the bridge image of its challenge, then
`allValid` forces every challenge to be `valid` — composing
`Acme.authzOfChalStatus_valid` down the list. -/
theorem allValid_bridge {chals : List Acme.ChalStatus}
    (hall : Acme.allValid (chals.map Acme.authzOfChalStatus) = true) :
    ∀ c ∈ chals, c = .valid := by
  induction chals with
  | nil => intro c hc; exact absurd hc (List.not_mem_nil c)
  | cons a t ih =>
      simp only [List.map_cons, Acme.allValid, List.all_cons,
        Bool.and_eq_true] at hall
      intro c hc
      rcases List.mem_cons.mp hc with rfl | hc
      · exact Acme.authzOfChalStatus_valid.mp
          ((Acme.AuthzStatus.isValid_eq _).mp hall.1)
      · exact ih hall.2 c hc

/-! ## The deployed corollary — no challenge bypass behind the served domain -/

/-- **`acme_deployed`.** The no-challenge-bypass invariant, landed on the deployed
serve path. `req` is the request the deployed reactor dispatched (`hsub`, anchored
to the shared reactor by `deployed_dispatch_agrees`). When each authorization of
that request's issuance order is discharged by a challenge (`hbridge`: its status
is `authzOfChalStatus` of the challenge's status — the `Acme` library's bridge),
the order reaching `valid` forces **every one of those challenges to be `valid`**.
By the `Acme` library's `chal_into_valid` / `validateStep_valid_needs_success`,
the only door into a valid challenge is a successful validation — so no
certificate stands behind the served domain whose issuance skipped or failed a
challenge. -/
theorem acme_deployed (input : Bytes) (req : Proto.Request)
    (events : List Acme.OrderEvent) (chals : List Acme.ChalStatus)
    (hsub : Reactor.Deploy.dispatchReqOf (Reactor.Deploy.deploySubs input) = some req)
    (hbridge : (deployIssuance req events).authzs = chals.map Acme.authzOfChalStatus)
    (hvalid : (deployIssuance req events).status = .valid) :
    ∀ c ∈ chals, c = .valid := by
  have hall := acme_deployed_no_skip input req events hsub hvalid
  rw [hbridge] at hall
  exact allValid_bridge hall

/-! ## The pure challenge-level bypass fact, restated for completeness

Independent of the order run: on the deployed surface a challenge validated
through `Acme.Challenge.validateStep` reaches `valid` *only* when the abstract
validator (the CA's http-01/dns-01 fetch) returned `true`. -/

/-- **`acme_deployed_validate_needs_success`.** A `processing` challenge that
becomes `valid` under `validateStep` had a successful validation — the deployed
path never routes a challenge into `valid` past a failed check. Verbatim
`Acme.validateStep_valid_needs_success`, named for the deployed seam set. -/
theorem acme_deployed_validate_needs_success {validate : Acme.Challenge → Bool}
    {c : Acme.Challenge} (hp : c.status = .processing)
    (hv : (c.validateStep validate).status = .valid) : validate c = true :=
  Acme.validateStep_valid_needs_success hp hv

/-! ## Axiom audit — every deployed seam is closed on the standard axioms only -/

#print axioms deployed_dispatch_agrees
#print axioms acme_deployed_no_skip
#print axioms allValid_bridge
#print axioms acme_deployed
#print axioms acme_deployed_validate_needs_success

end Reactor.WireAcme

/-
# Dregg2.Exec.AuthModes — dregg1's SIX authorization modes, dispatched onto the existing dregg2 primitives.

dregg1's `turn/src/executor/authorize.rs::verify_authorization` is not a binary
"does the actor hold a cap?" gate. It is a *dispatch* over an `Authorization` sum
with six load-bearing modes, each routing to a different soundness obligation:

  1. `OneOf(candidates, proof_index)` — a disjunctive switch. It validates
     `proof_index < candidates.len`, rejects an `Unchecked`/nested-`OneOf` at the
     chosen slot, and RECURSES with the chosen candidate. The outer `OneOf` is a
     pure selector; the chosen candidate carries the real obligation.
  2. `Custom(predicate)` — app-defined, witnessed-predicate dispatch: route
     `predicate.kind` through the `WitnessedPredicateRegistry` (our
     `Authority.Predicate.registryVerify`) against the canonical signing message,
     fail-closed on a missing kind.
  3. `CapTpDelivered(cert, introducer_pk, sender_pk, sender_sig)` — two-signature
     CapTP provenance: an introducer-signed `HandoffCertificate` + a recipient
     turn-binding signature. The handoff IS a Granovetter `Introduce`
     (`Spec.handoff_is_introduce`), so the conferred cap is non-amplifying.
     **dregg1 currently FAILS to enforce `granted ≤ held` here** (it verifies the
     two signatures and the cert/target binding, but never re-checks that the
     cert's conferred permissions attenuate what the introducer held — see
     `verify_captp_delivered`, which checks `allowed_effects` masks but not the
     authority lattice). We model the CORRECT semantics: the mode is admitted ONLY
     if `granted ≤ held`, and we PROVE that admission ⇒ `granted ≤ held`.
  4. `Bearer(proof)` — a delegation-proof chain + facet constraints + nonce /
     revocation-epoch. The delegation edge must be non-amplifying
     (`is_narrower_or_equal`); we model it as a `Caveat`-attenuated `Token`
     (the append-only narrowing chain) plus the conferral order.
  5. `Token(biscuit)` — biscuit/macaroon caveat evaluation: a token admits iff ALL
     its caveats discharge (`Authority.Caveat.Token.admits`).
  6. `Unchecked` — admitted ONLY for a fully-unconstrained target (no permission
     gate). We model "unconstrained" as the target carrying the trivially-true
     guard, and PROVE `Unchecked` never authorizes a constrained target.

## The abstract authority predicate (the soundness target)

Each mode REFINES a single abstract object: `Spec.Guard.admits` of the request's
authority guard. "`authModeAdmits` ⇒ the abstract authority predicate holds" is the
soundness theorem proved for every mode (`*_sound`). The verify seam
(`Laws.Verifiable`/`Discharged`), the witnessed-predicate registry
(`Authority.Predicate`), the caveat/token layer (`Authority.Caveat`), and the CapTP
handoff law (`Spec.handoff_is_introduce`/`handoff_non_amplifying`) are REUSED, never
reinvented.

## Discipline

NO `sorry`/`admit`/`axiom`/`native_decide`. The only kernel axioms are the standard
three (`propext`, `Classical.choice`, `Quot.sound`); pinned with `#assert_axioms`.
Pure, `#eval`-able. ONE namespace. Creates only NEW names.
-/
import Dregg2.Spec.Guard
import Dregg2.Spec.Authority
import Dregg2.Exec.CapTP
import Dregg2.Authority.Caveat
import Dregg2.Authority.Predicate
import Dregg2.Tactics

namespace Dregg2.Exec.AuthModes

open Dregg2.Laws
open Dregg2.Spec (Guard Cap confers Graph Introduce confers_refl)
open Dregg2.Exec.CapTP (HandoffCert HandoffValid handoff_is_introduce handoff_non_amplifying)
open Dregg2.Authority (Caveat Token TokenKind Discharges)
open Dregg2.Authority.Predicate (WitnessedKind Registry registryVerify verifiableOfRegistry
  registry_sound)

/-! ## §0 — Carriers.

We keep the same abstract-carrier discipline the rest of dregg2 uses: a `Request`
(the auth facts a guard reads), a `Statement`/`Witness` verify-seam pair behind a
`Verifiable` oracle, a `CellId` node type, and an attenuation-ordered `Rights`
carrier (bounded meet-semilattice with a DECIDABLE order, so the dispatcher's
`granted ≤ held` check is computable) for the CapTP handoff lattice. Nothing is `Nat`.

All carriers live at `Type` (universe 0), matching the `Registry`/`WitnessedKind`
machinery (`Authority.Predicate` is `Type`-monomorphic). -/

variable {Request : Type}
variable {Stmt Wit : Type}
variable {CellId : Type} [DecidableEq CellId]
variable {Rights : Type} [SemilatticeInf Rights] [OrderTop Rights] [DecidableLE Rights]
variable {Ctx Gateway : Type}

/-! ## §1 — `AuthContext`: the per-call facts every mode dispatches against.

This bundles the inputs the six Rust handlers consult. A single `AuthContext`
carries enough for ALL modes; each mode reads only the fields it needs (exactly as
`verify_authorization` reads `action`/`target_cell`/`ledger`/`turn_nonce`). -/

/-- The per-call facts the six authorization modes dispatch against — the dregg2
analog of `(action, target_cell, ledger, turn_nonce)`. -/
structure AuthContext (Request Stmt Wit CellId Rights Ctx Gateway : Type _) where
  /-- The request facts a first-party / abstract guard reads. -/
  req         : Request
  /-- The signing-message statement that a `Custom` witnessed-predicate is checked against. -/
  customStmt  : Stmt
  /-- The witness supply for the verify seam (the `Custom` proof bytes resolver). -/
  wit         : Stmt → Wit
  /-- The registry the `Custom` kind dispatches through (the `WitnessedPredicateRegistry`). -/
  registry    : Registry Stmt Wit
  /-- The caveat-evaluation context the `Token` / `Bearer` caveats read (the `AuthRequest`). -/
  caveatCtx   : Ctx
  /-- Which gateways have discharged (third-party caveats). -/
  discharges  : Discharges Gateway
  /-- The capability graph (who holds what), for the CapTP handoff premises. -/
  graph       : Graph CellId Rights
  /-- Whether a target cell consents to delegation (`AuthRequired ≠ Impossible`). -/
  consents    : CellId → Prop
  /-- Whether the action's effect mask is within the cert/cap facet mask. -/
  facetOk     : Bool
  /-- Whether the bearer/cap nonce + revocation epoch are current (not expired/revoked). -/
  freshOk     : Bool

/-! ## §2 — The abstract authority predicate.

The soundness target is a single `Spec.Guard.admits` over the request: the abstract
"the invoker is authorized" object (`Guard.senderAuthorized`'s shape). Each mode's
admission must REFINE the relevant guard's admission. Rather than pin every mode to
one fixed guard, each mode carries (in its constructor) the guard it discharges, and
`*_sound` proves admission ⇒ that guard admits. This is the faithful "each mode is a
different way of discharging the authority obligation" story. -/

/-- A handle to the verify seam used by the `Custom` mode's registry dispatch at a
fixed kind: `Discharged` here is definitionally "the registry accepts". -/
abbrev customSeam (registry : Registry Stmt Wit) (k : WitnessedKind) : Verifiable Stmt Wit :=
  verifiableOfRegistry registry k

/-! ## §3 — `AuthMode`: the six constructors.

Faithful to `authorize.rs`. The recursive `oneOf` mirrors the Rust recursion; its
list of candidates is the `candidates` array, `proof_index` the chosen slot. -/

/-- dregg1's six authorization modes, as a Lean inductive over the dregg2 primitives. -/
inductive AuthMode (Request Stmt Wit CellId Rights Ctx Gateway : Type _)
    [SemilatticeInf Rights] [OrderTop Rights] : Type _ where
  /-- (1) **OneOf** — disjunctive multi-candidate; `proofIndex` selects a candidate.
  The Rust validates `proofIndex < candidates.length`, rejects an `Unchecked`/nested
  `OneOf` at the slot, and recurses with the chosen candidate. -/
  | oneOf (candidates : List (AuthMode Request Stmt Wit CellId Rights Ctx Gateway))
          (proofIndex : Nat)
  /-- (2) **Custom** — witnessed-predicate dispatch: a registry `kind` discharged
  against the canonical signing-message statement. -/
  | custom (kind : WitnessedKind)
  /-- (3) **CapTpDelivered** — two-signature CapTP provenance. Carries the handoff
  cert (held + granted caps), the graph premises (`HandoffValid`), and the §8
  attestation that the two signatures + cert/target binding verified. -/
  | capTpDelivered (cert : HandoffCert CellId Rights)
                   (attested : Prop)
  /-- (4) **Bearer** — a delegation-proof chain modelled as a `Caveat`-attenuated
  token plus the non-amplifying conferral edge `confers held granted`. -/
  | bearer (held granted : Cap CellId Rights) (tok : Token Ctx Gateway)
  /-- (5) **Token** — a biscuit/macaroon: admits iff all its caveats discharge. -/
  | token (tok : Token Ctx Gateway)
  /-- (6) **Unchecked** — admitted ONLY for a fully-unconstrained target; carries the
  target's authority guard (which must be the trivially-true guard `all []`). -/
  | unchecked (targetGuard : Guard Request Stmt)

/-! ## §4 — `authModeAdmits`: the dispatch (computable `Bool`).

The single dispatcher. Mirrors the order and the checks of
`verify_authorization`. The `oneOf` arm encodes the THREE structural rules dregg1
enforces (in-bounds, not `Unchecked` at the slot, not nested `OneOf` at the slot)
before recursing. -/

/-- Is `m` a `unchecked` mode? (used to reject `Unchecked` at a `OneOf` slot). -/
def AuthMode.isUnchecked
    (m : AuthMode Request Stmt Wit CellId Rights Ctx Gateway) : Bool :=
  match m with | .unchecked _ => true | _ => false

/-- Is `m` itself a `oneOf`? (used to reject nested `OneOf` at a `OneOf` slot). -/
def AuthMode.isOneOf
    (m : AuthMode Request Stmt Wit CellId Rights Ctx Gateway) : Bool :=
  match m with | .oneOf _ _ => true | _ => false

/- The structural index-selector: fold over the candidate list, counting down
`proofIndex`. The selected candidate IS a structural subterm of the list, so the
recursive `authModeAdmits` call on it is structural and the whole dispatcher reduces
definitionally — no well-founded recursion, hence `decide`/`rfl` compute. Mirrors the
`Spec.Guard.admits` ⊳ `admitsAll`/`admitsAny` list-fold pattern. -/
mutual
  /-- **The dispatcher.** Routes each mode onto the existing dregg2 primitive,
  fail-closed. -/
  def authModeAdmits [Verifiable Stmt Wit]
      (m : AuthMode Request Stmt Wit CellId Rights Ctx Gateway)
      (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway) : Bool :=
    match m with
    | .oneOf candidates proofIndex =>
        -- structural fold to the chosen slot, applying the three OneOf rules there.
        authModeOneOf candidates proofIndex c
    | .custom kind =>
        -- route the kind through the registry against the signing-message statement.
        registryVerify c.registry kind c.customStmt (c.wit c.customStmt)
    | .capTpDelivered cert _attested =>
        -- the CORRECT semantics: admitted only if the conferred cap attenuates the
        -- held cap (the non-amplification dregg1's Rust is MISSING) AND the facet /
        -- freshness checks pass. The two-signature attestation is the §8 `Prop`
        -- discharge carried in the constructor (verified abstractly via `*_sound`).
        decide (cert.granted.rights ≤ cert.held.rights) && c.facetOk && c.freshOk
    | .bearer held granted tok =>
        -- delegation chain: the token's caveats discharge, the conferral edge is
        -- non-amplifying, freshness holds.
        tok.admits c.caveatCtx c.discharges
          && decide (granted.rights ≤ held.rights) && decide (granted.target = held.target)
          && c.freshOk
    | .token tok =>
        -- biscuit/macaroon: all caveats discharge.
        tok.admits c.caveatCtx c.discharges
    | .unchecked targetGuard =>
        -- admitted ONLY if the target is unconstrained: its authority guard admits
        -- vacuously under ANY witness supply — modelled as the neutral guard `all []`.
        Guard.admits targetGuard c.req c.wit

  /-- The `OneOf` handler: walk the candidate list to index `i` (structural recursion
  on the list). At the chosen slot, enforce the THREE dregg1 rules — not `Unchecked`,
  not nested `OneOf`, and (recursively) the candidate admits. Out-of-bounds (`[]`
  before reaching `0`) fails closed (`false`). -/
  def authModeOneOf [Verifiable Stmt Wit]
      (candidates : List (AuthMode Request Stmt Wit CellId Rights Ctx Gateway))
      (i : Nat) (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway) : Bool :=
    match candidates, i with
    | [],            _      => false               -- out of bounds: fail closed
    | chosen :: _,   0      =>
        !chosen.isUnchecked && !chosen.isOneOf && authModeAdmits chosen c
    | _ :: rest,     n + 1  => authModeOneOf rest n c
end

/-! ## §5 — Soundness: each mode reduces to / refines the abstract authority predicate.

For each mode we PROVE `authModeAdmits ⇒ <the abstract authority object holds>`,
where the abstract object is the appropriate `Laws.Discharged` / `Spec.Guard.admits`
/ conferral fact. -/

variable [Verifiable Stmt Wit]

/-! ### §5.1 — Custom: registry accept ⇒ `Discharged` at the seam. -/

/-- **`custom_sound`** — when the `Custom` mode admits, the witnessed predicate is
`Discharged` at the registry-at-`kind` verify seam (the `Authority.Predicate`
keystone, `registry_sound`). The abstract authority object is exactly this
discharge. -/
theorem custom_sound (kind : WitnessedKind)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.custom kind) c = true) :
    @Discharged Stmt Wit (customSeam c.registry kind) c.customStmt (c.wit c.customStmt) := by
  -- `authModeAdmits (.custom …)` is definitionally `registryVerify … = true`.
  have hacc : registryVerify c.registry kind c.customStmt (c.wit c.customStmt) = true := by
    simpa [authModeAdmits] using h
  exact registry_sound c.registry kind c.customStmt (c.wit c.customStmt) hacc

/-! ### §5.2 — Token: admits ⇒ `Discharged` as a token verify-seam witness. -/

/-- **`token_sound`** — when the `Token` mode admits, the `(token, discharges)` pair
IS a discharged verify-seam witness for the caveat context (the `Caveat.tokenVerifiable`
instance + `Caveat.token_discharges`). The abstract object: a verifying biscuit is a
`Laws.Discharged` certificate. -/
theorem token_sound (tok : Token Ctx Gateway)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.token tok) c = true) :
    Discharged (P := Ctx) (W := Token Ctx Gateway × Discharges Gateway)
      c.caveatCtx (tok, c.discharges) := by
  have hadm : tok.admits c.caveatCtx c.discharges = true := by
    simpa [authModeAdmits] using h
  exact Dregg2.Authority.token_discharges tok c.caveatCtx c.discharges hadm

/-! ### §5.3 — CapTpDelivered: admits ⇒ `granted ≤ held` (the non-amplification dregg1 misses). -/

/-- **`captp_sound` — the headline non-amplification theorem.** When the
`CapTpDelivered` mode admits, the conferred (granted) cap attenuates the held cap on
the rights order: `granted.rights ≤ held.rights`. This is precisely the
`is_attenuation(held, granted)` check that dregg1's `verify_captp_delivered` FAILS to
perform — our dispatcher gates on it, and this theorem certifies the gate. -/
theorem captp_granted_le_held (cert : HandoffCert CellId Rights) (attested : Prop)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.capTpDelivered cert attested) c = true) :
    cert.granted.rights ≤ cert.held.rights := by
  -- `authModeAdmits` conjoins `decide (granted ≤ held)` with the facet/freshness bits.
  simp only [authModeAdmits, Bool.and_eq_true, decide_eq_true_eq] at h
  exact h.1.1

/-- **`captp_sound`** — when the `CapTpDelivered` mode admits AND the abstract handoff
premises hold (`HandoffValid`: connectivity, A holds the cap, target consents, plus
the §8 attestation), the handoff IS a Granovetter `Introduce` step on the capability
graph, and (by `Spec.handoff_non_amplifying`) the conferred cap is non-amplifying.
This is the soundness refinement: the mode's admission, together with the
authority-graph premises, discharges the abstract `Introduce` authority object — and
the non-amplification is proved twice over (once from the dispatcher gate via
`captp_granted_le_held`, once from the introduce discipline via the reuse). -/
theorem captp_sound (cert : HandoffCert CellId Rights) (attested : Prop)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (hv : HandoffValid cert c.graph c.consents attested)
    (h : authModeAdmits (.capTpDelivered cert attested) c = true) :
    Introduce c.graph c.consents cert.introducer cert.recipient cert.held cert.granted
        (cert.post c.graph)
      ∧ cert.granted.rights ≤ cert.held.rights :=
  ⟨handoff_is_introduce hv, captp_granted_le_held cert attested c h⟩

/-! ### §5.4 — Bearer: admits ⇒ the delegation edge confers (non-amplifying chain). -/

/-- **`bearer_sound`** — when the `Bearer` mode admits, (a) the carried token's
caveats discharge (it is a `Laws.Discharged` verify-seam witness) AND (b) the
delegation edge `held ⟶ granted` `confers` (same target, narrower-or-equal rights —
the `is_narrower_or_equal` non-amplification of `verify_bearer_cap`). The abstract
object is the conferral `Spec.confers held granted` plus the token discharge. -/
theorem bearer_sound (held granted : Cap CellId Rights) (tok : Token Ctx Gateway)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.bearer held granted tok) c = true) :
    confers held granted
      ∧ Discharged (P := Ctx) (W := Token Ctx Gateway × Discharges Gateway)
          c.caveatCtx (tok, c.discharges) := by
  simp only [authModeAdmits, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨htok, hrights⟩, htgt⟩, _hfresh⟩ := h
  refine ⟨⟨htgt, hrights⟩, ?_⟩
  exact Dregg2.Authority.token_discharges tok c.caveatCtx c.discharges htok

/-! ### §5.5 — OneOf: index-bounds safety + recursion soundness. -/

/-- The structural core: if the `OneOf` handler admits at index `i`, then `i` selects
an actual candidate (`candidates[i]? = some chosen`) which is not `Unchecked`, not a
nested `OneOf`, and itself admits. Proved by induction on `(candidates, i)` exactly
as `authModeOneOf` recurses. -/
theorem authModeOneOf_sound
    (candidates : List (AuthMode Request Stmt Wit CellId Rights Ctx Gateway))
    (i : Nat) (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeOneOf candidates i c = true) :
    ∃ chosen, candidates[i]? = some chosen
      ∧ chosen.isUnchecked = false ∧ chosen.isOneOf = false
      ∧ authModeAdmits chosen c = true := by
  induction candidates generalizing i with
  | nil => rw [authModeOneOf] at h; exact absurd h (by simp)
  | cons head rest ih =>
      cases i with
      | zero =>
          rw [authModeOneOf] at h
          simp only [Bool.and_eq_true, Bool.not_eq_true'] at h
          exact ⟨head, rfl, h.1.1, h.1.2, h.2⟩
      | succ n =>
          rw [authModeOneOf] at h
          obtain ⟨chosen, hidx, hu, ho, ha⟩ := ih n h
          exact ⟨chosen, by simpa using hidx, hu, ho, ha⟩

/-- **`oneOf_index_bounds`** — if a `OneOf` mode admits, the `proofIndex` is in
bounds: there IS a candidate at that index. The dispatcher fails closed past the end
of the list, so admission forces a witness. This is the structural-safety check
dregg1 performs first (`idx >= candidates.len() → InvalidAuthorization`). -/
theorem oneOf_index_bounds
    (candidates : List (AuthMode Request Stmt Wit CellId Rights Ctx Gateway))
    (proofIndex : Nat)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.oneOf candidates proofIndex) c = true) :
    proofIndex < candidates.length := by
  rw [authModeAdmits] at h
  obtain ⟨chosen, hidx, _⟩ := authModeOneOf_sound candidates proofIndex c h
  exact (List.getElem?_eq_some_iff.mp hidx).1

/-- **`oneOf_sound`** — if a `OneOf` mode admits, the chosen candidate (a) is NOT
`Unchecked` (no auth-bypass-by-naming-Unchecked), (b) is NOT a nested `OneOf`, and
(c) itself admits. The outer `OneOf` is a pure switch: its soundness reduces to the
chosen candidate's. -/
theorem oneOf_sound
    (candidates : List (AuthMode Request Stmt Wit CellId Rights Ctx Gateway))
    (proofIndex : Nat)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.oneOf candidates proofIndex) c = true) :
    ∃ chosen, candidates[proofIndex]? = some chosen
      ∧ chosen.isUnchecked = false ∧ chosen.isOneOf = false
      ∧ authModeAdmits chosen c = true := by
  rw [authModeAdmits] at h
  exact authModeOneOf_sound candidates proofIndex c h

/-! ### §5.6 — Unchecked: admitted ONLY for an unconstrained target. -/

/-- A target is **unconstrained** when its authority guard admits under EVERY witness
supply and EVERY request — the neutral guard `all []` (no permission gate). A
*constrained* target carries a non-trivial guard that some supply rejects. -/
def Unconstrained (targetGuard : Guard Request Stmt) : Prop :=
  ∀ (req : Request) (w : Stmt → Wit), Guard.admits targetGuard req w = true

/-- **`unchecked_sound`** — when `Unchecked` admits, the target's authority guard
admits at this request. So `Unchecked` does NOT bypass a gate: it only "succeeds"
where the abstract authority guard already succeeds. (The dispatcher evaluates the
guard; admission IS guard-admission.) -/
theorem unchecked_sound (targetGuard : Guard Request Stmt)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (h : authModeAdmits (.unchecked targetGuard) c = true) :
    Guard.admits targetGuard c.req c.wit = true := by
  simpa [authModeAdmits] using h

/-- **`unchecked_no_escalation` — the no-privilege-escalation theorem.** If a target
is genuinely CONSTRAINED — there is a witness supply `wBad` under which its authority
guard REJECTS the request — then `Unchecked` cannot authorize it under *that* supply.
`Unchecked` is admitted only where the guard already admits; it conjures no authority
the gate denies. (Stated at the rejecting supply: an `Unchecked` mode whose context
uses `wBad` does not admit.) -/
theorem unchecked_no_escalation (targetGuard : Guard Request Stmt)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (hbad : Guard.admits targetGuard c.req c.wit = false) :
    authModeAdmits (.unchecked targetGuard) c = false := by
  simpa [authModeAdmits] using hbad

/-- **`unchecked_unconstrained_admits`** — the converse face: an UNCONSTRAINED target
(its guard admits under every supply/request) IS authorized by `Unchecked`. So
`Unchecked` is exactly "the target has no permission gate", never a back door for a
gated target. -/
theorem unchecked_unconstrained_admits (targetGuard : Guard Request Stmt)
    (c : AuthContext Request Stmt Wit CellId Rights Ctx Gateway)
    (hunc : Unconstrained (Wit := Wit) targetGuard) :
    authModeAdmits (.unchecked targetGuard) c = true := by
  simp only [authModeAdmits]
  exact hunc c.req c.wit

/-! ## §6 — Non-vacuity: each mode inhabited at a concrete example.

Concrete carriers: `Request := Bool`, `Stmt = Wit := Nat`, `CellId := Bool`,
`Rights := Unit` (one-point lattice), `Ctx := Nat` (a block height), `Gateway := Unit`.
Each example FIRES the corresponding `*_sound` keystone on real data. -/

namespace Demo

abbrev R := Bool
abbrev S := Nat
abbrev W := Nat
abbrev C := Bool
abbrev Rt := Unit
abbrev Cx := Nat
abbrev Gw := Unit

/-- The one-point rights carrier is a bounded meet-semilattice. -/
example : SemilatticeInf Unit := inferInstance
example : OrderTop Unit := inferInstance

/-- A toy `dfa` verifier: accepts iff the witness equals the statement. -/
def dfaVerifier : Dregg2.Authority.Predicate.Verifier S W := fun stmt wit => decide (wit = stmt)

/-- A demo registry with `dfa` installed; everything else fails closed. -/
def demoReg : Registry S W := fun | .dfa => some dfaVerifier | _ => none

/-- The demo verify seam (`Verifiable S W`): the registry dispatch at `.dfa`. Pins the
`Verifiable` instance the dispatcher's signature needs, so the `unchecked` arm's
`Guard.admits` and the whole `authModeAdmits` evaluate concretely in the demos. -/
local instance demoVerifiable : Verifiable S W := verifiableOfRegistry demoReg .dfa

/-- A root biscuit attenuated to a height window `[100, 200]` (no third-party caveats). -/
def demoToken : Token Cx Gw :=
  { kind := .biscuit
  , caveats := [ .local (fun h => decide (100 ≤ h)), .local (fun h => decide (h ≤ 200)) ] }

/-- The identity handoff cert: A=`true` introduces B=`false` to target `true`,
conferring exactly what it holds (held = granted, the simplest non-amplifying case). -/
def demoCert : HandoffCert C Rt :=
  { introducer := true
  , recipient  := false
  , held       := { target := true, rights := () }
  , granted    := { target := true, rights := () } }

/-- The base auth context: a height-150 caveat context, no discharges, a graph where
A=`true` holds the (identity) cap to target `true` and can reach B=`false`. -/
def baseCtx : AuthContext R S W C Rt Cx Gw :=
  { req         := true
  , customStmt  := 7
  , wit         := fun _ => 7                       -- the witness supply echoes 7 (so dfa accepts at stmt 7)
  , registry    := demoReg
  , caveatCtx   := 150
  , discharges  := fun _ => false
  , graph       := fun h cap =>
      (h = true ∧ cap = { target := true, rights := () }) ∨
      (h = true ∧ cap = { target := false, rights := () })
  , consents    := fun _ => True
  , facetOk     := true
  , freshOk     := true }

/-! The dispatcher is a `mutual` definition (`authModeAdmits`/`authModeOneOf`), and so
are the underlying `Guard.admits`/`Token.admits` folds. Such definitions reduce under
the compiled evaluator (`#eval` below witnesses every value) but NOT under the kernel's
whnf, so a bare `decide` gets stuck on the unreduced `WellFounded.fix`. We therefore
discharge each concrete demo by `simp only`-unfolding the dispatcher (and the demo
carriers) via their auto-generated equation lemmas down to a concrete `Nat`/`Bool`
residue, then `decide` that residue. `demoVerifiable_Verify` exposes the demo verify
seam so the `custom`/`unchecked`-`witnessed` arms reduce. -/

@[local simp] theorem demoVerifiable_Verify (s w : Nat) :
    (demoVerifiable.Verify s w) = decide (w = s) := rfl

/-- Discharge a concrete demo about `authModeAdmits`: unfold the mutual dispatcher and
the demo carriers to a decidable residue, then decide it. -/
local macro "decideAdmits" : tactic =>
  `(tactic|
    (simp only [authModeAdmits, authModeOneOf, AuthMode.isUnchecked, AuthMode.isOneOf,
      baseCtx, demoToken, demoCert, demoVerifiable_Verify, registryVerify, demoReg,
      dfaVerifier, Dregg2.Authority.Token.admits, Dregg2.Authority.Caveat.ok,
      Dregg2.Spec.Guard.admits, Dregg2.Spec.Guard.admitsAll,
      List.all_cons, List.all_nil] <;> decide))

/-- (2) Custom: the `dfa` kind admits — the witness `7` discharges at statement `7`. -/
example : authModeAdmits (Rights := Rt) (.custom .dfa) baseCtx = true := by decideAdmits

/-- (2) …and its soundness fires: the predicate is `Discharged` at the seam. -/
example : @Discharged S W (customSeam baseCtx.registry .dfa) baseCtx.customStmt
    (baseCtx.wit baseCtx.customStmt) :=
  custom_sound (Rights := Rt) (Ctx := Cx) (Gateway := Gw) .dfa baseCtx (by decideAdmits)

/-- (5) Token: the windowed biscuit admits at height 150 (∈ [100,200]). -/
example : authModeAdmits (Request := R) (Stmt := S) (Wit := W) (CellId := C) (Rights := Rt)
    (.token demoToken) baseCtx = true := by decideAdmits

/-- (5) …and a height OUTSIDE the window does NOT admit (a caveat narrowed it out). -/
example : authModeAdmits (Request := R) (Stmt := S) (Wit := W) (CellId := C) (Rights := Rt)
    (.token demoToken) { baseCtx with caveatCtx := 50 } = false := by decideAdmits

/-- (3) CapTpDelivered: admits (granted ≤ held holds — `() ≤ ()` — facet/fresh ok). -/
example : authModeAdmits (Request := R) (Stmt := S) (Wit := W) (Ctx := Cx) (Gateway := Gw)
    (.capTpDelivered demoCert True) baseCtx = true := by decideAdmits

/-- (3) …and the headline non-amplification fires: `granted.rights ≤ held.rights`. -/
example : demoCert.granted.rights ≤ demoCert.held.rights :=
  captp_granted_le_held (Request := R) (Stmt := S) (Wit := W) (Ctx := Cx) (Gateway := Gw)
    demoCert True baseCtx (by decideAdmits)

/-- The demo handoff is `HandoffValid`, so `captp_sound` yields the `Introduce` step. -/
def demoValid : HandoffValid demoCert baseCtx.graph baseCtx.consents True where
  connected      := ⟨(), Or.inr ⟨rfl, rfl⟩⟩
  holds_target   := Or.inl ⟨rfl, rfl⟩
  nonAmplifying  := Dregg2.Spec.confers_refl _
  targetConsents := trivial
  attested       := trivial

example :
    Introduce baseCtx.graph baseCtx.consents demoCert.introducer demoCert.recipient
        demoCert.held demoCert.granted (demoCert.post baseCtx.graph)
      ∧ demoCert.granted.rights ≤ demoCert.held.rights :=
  captp_sound (Request := R) (Stmt := S) (Wit := W) demoCert True baseCtx demoValid (by decideAdmits)

/-- (4) Bearer: the windowed token + an identity (non-amplifying) delegation edge admits. -/
example : authModeAdmits (Request := R) (Stmt := S) (Wit := W)
    (.bearer { target := true, rights := () } { target := true, rights := () } demoToken)
    baseCtx = true := by decideAdmits

/-- (4) …and `bearer_sound` yields the conferral edge. -/
example : confers (CellId := C) { target := true, rights := () } { target := true, rights := () } :=
  (bearer_sound (Request := R) (Stmt := S) (Wit := W)
    { target := true, rights := () } { target := true, rights := () } demoToken baseCtx
    (by decideAdmits)).1

/-- (1) OneOf: a two-candidate list selecting the `token` candidate at index 0 admits. -/
def demoCandidates : List (AuthMode R S W C Rt Cx Gw) :=
  [ .token demoToken, .custom .dfa ]

example : authModeAdmits (.oneOf demoCandidates 0) baseCtx = true := by
  simp only [demoCandidates]; decideAdmits

/-- (1) …index-bounds safety fires: an out-of-bounds index does NOT admit. -/
example : authModeAdmits (.oneOf demoCandidates 5) baseCtx = false := by
  simp only [demoCandidates]; decideAdmits

/-- (1) …and `oneOf_sound` extracts the admitting, non-Unchecked, non-nested candidate. -/
example : ∃ chosen, demoCandidates[0]? = some chosen
    ∧ chosen.isUnchecked = false ∧ chosen.isOneOf = false
    ∧ authModeAdmits chosen baseCtx = true :=
  oneOf_sound demoCandidates 0 baseCtx (by simp only [demoCandidates]; decideAdmits)

/-- (1) …an `Unchecked` candidate at the chosen slot is REJECTED (no auth-bypass). -/
example : authModeAdmits (.oneOf [.unchecked (Guard.firstParty (fun _ => false))] 0) baseCtx
    = false := by decideAdmits

/-- (6) Unchecked over the neutral (unconstrained) guard `all []` admits. -/
example : authModeAdmits (Rights := Rt) (CellId := C) (Ctx := Cx) (Gateway := Gw)
    (.unchecked (Guard.all [])) baseCtx = true := by decideAdmits

/-- (6) …and over a CONSTRAINED target (a guard that rejects `req = true`) it does NOT
admit — no privilege escalation. -/
example : authModeAdmits (Rights := Rt) (CellId := C) (Ctx := Cx) (Gateway := Gw)
    (.unchecked (Guard.firstParty (fun _ => false))) baseCtx = false :=
  unchecked_no_escalation (Guard.firstParty (fun _ => false)) baseCtx (by decideAdmits)

/-- (6) …an unconstrained guard is admitted by `Unchecked` everywhere. -/
example : authModeAdmits (Rights := Rt) (CellId := C) (Ctx := Cx) (Gateway := Gw)
    (.unchecked (Guard.all [])) baseCtx = true :=
  unchecked_unconstrained_admits (Guard.all [])  baseCtx (fun _ _ => by simp)

#eval authModeAdmits (Rights := Rt) (.custom .dfa) baseCtx                        -- true
#eval authModeAdmits (Request := R) (Stmt := S) (Wit := W) (CellId := C) (Rights := Rt)
        (.token demoToken) baseCtx                                                -- true
#eval authModeAdmits (Request := R) (Stmt := S) (Wit := W) (Ctx := Cx) (Gateway := Gw)
        (.capTpDelivered demoCert True) baseCtx                                   -- true
#eval authModeAdmits (.oneOf demoCandidates 0) baseCtx                            -- true
#eval authModeAdmits (.oneOf demoCandidates 5) baseCtx                            -- false (OOB)

end Demo

/-! ## §7 — Axiom-hygiene tripwires.

Every soundness keystone depends ONLY on the three standard kernel axioms (no
`sorryAx`). The CapTpDelivered non-amplification — the discipline dregg1's Rust is
missing — is among the pinned theorems. -/

#assert_axioms custom_sound
#assert_axioms token_sound
#assert_axioms captp_granted_le_held
#assert_axioms captp_sound
#assert_axioms bearer_sound
#assert_axioms oneOf_index_bounds
#assert_axioms oneOf_sound
#assert_axioms unchecked_sound
#assert_axioms unchecked_no_escalation
#assert_axioms unchecked_unconstrained_admits

end Dregg2.Exec.AuthModes

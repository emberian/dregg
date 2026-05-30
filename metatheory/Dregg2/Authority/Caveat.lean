/-
# Dregg2.Authority.Caveat — the keys-as-caps token layer (biscuit / macaroon / caveat / discharge).

This mirrors dregg1's authority/credential framework — `Authorization::Token { encoded, key_ref,
discharges }` + `TokenKeyRef` (`turn/src/action.rs:422`), the macaroon caveat chain, the biscuit
delegation graph, third-party caveats + discharge — **into the dregg2 semantics**, through the
corpus's lens (the dregg1 shapes are *validated*, not merely copied: `00-synthesis §5.1` keeps the
biscuit/macaroon split as "the inside/between vat-boundary"; a caveat *is* a `WitnessedCondition`
binding-site+engine; `dregg2 §1.1` makes **attenuation "the one rule the whole system rests on"**).

The load-bearing content:
- a **token** = a `RootSeal` + an *append-only attenuation chain of caveats* (`biscuit` cross-vat /
  `macaroon` intra-vat), admitting a request iff **all** its caveats are discharged (the meet ⋀);
- **attenuation = appending a caveat = narrowing** — and the keystone law `attenuate_narrows` proves
  it can only ever *shrink* the admissible set (the concrete realization of
  `Authority.lossy_attenuation_only` / the Heyting residual `⇨`; "a key may only narrow");
- the **biscuit/macaroon split = the vat boundary**: a biscuit is public-key verifiable off-island;
  a macaroon's HMAC root secret is held only by its scoping cell, so it is *not* third-party
  verifiable (`discoveries §6.3`) — a macaroon presented cross-domain is rejected;
- a **third-party caveat = the await engine's authority-face**: it suspends until a named gateway's
  **discharge** resolves it (`dregg2 §3`, the discharge/`ConditionalTurn` isomorphism);
- the **bridge to the verify/find seam**: a token's verification IS a `Laws.Discharged` witness, so a
  presented, verifying token discharges the cross-vat case of the vat-boundary law.

Pure, computable, `#eval`-able.
-/
import Dregg2.Laws

namespace Dregg2.Authority

open Dregg2.Laws

/- The request binding-site `Ctx` — the `AuthRequest` facts a caveat is evaluated against (block
height, action, resource, sender, …). Abstract; instantiated by the real PI surface. `Gateway` =
the identity of a third-party caveat's resolving gateway. -/
variable {Ctx : Type}
variable {Gateway : Type}

/-- **A caveat** — the universal gate (`WitnessedCondition`), here in two engines: a **local**
checkable predicate over the request context (a macaroon 1st-party caveat / a biscuit fact / a
`CapabilityCaveat`), or a **third-party** caveat naming a `gateway` that must *discharge* it (the
await authority-face). -/
inductive Caveat (Ctx Gateway : Type) where
  | local      (check : Ctx → Bool)
  | thirdParty (gateway : Gateway)

/-- The discharges presented alongside a token (dregg1 `Authorization::Token.discharges`): which
gateways have produced a resolution. -/
abbrev Discharges (Gateway : Type) := Gateway → Bool

/-- A caveat is satisfied at a request iff its local check holds, or its gateway has discharged. -/
def Caveat.ok (c : Caveat Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Bool :=
  match c with
  | .local check  => check ctx
  | .thirdParty g => d g

/-- The two token carriers (dregg1 `TokenKeyRef`). -/
inductive TokenKind where
  /-- **biscuit** (`eb2_…`): cross-vat — Ed25519 public-key, offline-verifiable by *anyone*; the
  biscuit delegation graph ≡ the distributed CDT. -/
  | biscuit
  /-- **macaroon** (`em2_…`): intra-vat — a cell-scoped HMAC; the root secret is held only by the
  scoping cell, so it is NOT third-party-verifiable (`discoveries §6.3`). -/
  | macaroon
  deriving DecidableEq, Repr

/-- **A token** — a kind (biscuit/macaroon) + an **append-only attenuation chain of caveats**. The
chain *is* the path of monotone-narrowing `(parent → child)` edges from a `RootSeal` (the CDT
rendering); authority = the meet of all caveats. -/
structure Token (Ctx Gateway : Type) where
  kind    : TokenKind
  caveats : List (Caveat Ctx Gateway)

/-- **A token admits a request iff ALL its caveats are satisfied** (the conjunction / meet ⋀) — the
fail-closed authority decision. -/
def Token.admits (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) : Bool :=
  tok.caveats.all (fun c => c.ok ctx d)

/-- **Attenuation = appending a caveat** — the *one rule the system rests on* (`dregg2 §1.1`):
narrowing only. A child token = `attenuate parent cav`. -/
def Token.attenuate (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway) : Token Ctx Gateway :=
  { tok with caveats := tok.caveats ++ [c] }

/-! ## The keystone — attenuation can only NARROW (the LossyMorphism, realized). -/

/-- **`attenuate_narrows` (PROVED) — the one rule.** Anything an *attenuated* token admits, the
parent token already admitted: adding a caveat never grows authority. This is the concrete
realization of `Authority.lossy_attenuation_only` / the Heyting residual `⇨` ("a key may only
narrow") on the actual biscuit/macaroon chain. -/
theorem attenuate_narrows (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (ctx : Ctx) (d : Discharges Gateway) :
    (tok.attenuate c).admits ctx d = true → tok.admits ctx d = true := by
  simp only [Token.admits, Token.attenuate, List.all_append, Bool.and_eq_true]
  intro h; exact h.1

/-- **`attenuate_subset` (PROVED)** — the set form: a more-attenuated token's admissible-request set
is a *subset* of the parent's. Authority strictly shrinks down a delegation chain. -/
theorem attenuate_subset (tok : Token Ctx Gateway) (c : Caveat Ctx Gateway)
    (d : Discharges Gateway) :
    {ctx | (tok.attenuate c).admits ctx d = true} ⊆ {ctx | tok.admits ctx d = true} :=
  fun ctx h => attenuate_narrows tok c ctx d h

/-- Attenuating by a caveat that is *always-true* leaves authority unchanged (the trivial
attenuation = identity edge). A sanity companion to `attenuate_narrows`. PROVED. -/
theorem attenuate_trivial (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway) :
    (tok.attenuate (.local (fun _ => true))).admits ctx d = tok.admits ctx d := by
  simp [Token.admits, Token.attenuate, List.all_append, Caveat.ok]

/-! ## The biscuit / macaroon split IS the vat boundary. -/

/-- Only a **biscuit** verifies off-island (public-key); a **macaroon**'s HMAC root secret is held
only by its scoping cell, so a non-holder cannot verify it (`discoveries §6.3`: HMAC ≠
third-party-verifiable). -/
def Token.crossVatVerifiable (tok : Token Ctx Gateway) : Bool :=
  match tok.kind with | .biscuit => true | .macaroon => false

/-- **A macaroon is never cross-vat verifiable — PROVED.** Presenting it to a non-holding verifier
fails closed: keys-as-caps off-island is the biscuit's job, not the macaroon's. -/
theorem macaroon_not_crossvat (tok : Token Ctx Gateway) (h : tok.kind = .macaroon) :
    tok.crossVatVerifiable = false := by
  unfold Token.crossVatVerifiable; rw [h]

/-- **A biscuit is cross-vat verifiable — PROVED** (the `Obs` badge that leaves the vat). -/
theorem biscuit_crossvat (tok : Token Ctx Gateway) (h : tok.kind = .biscuit) :
    tok.crossVatVerifiable = true := by
  unfold Token.crossVatVerifiable; rw [h]

/-! ## Bridge to the verify/find seam: a verifying token IS a `Laws.Discharged` witness. -/

/-- A token (with its discharges) instantiates the verify/find seam (`Laws.Verifiable`): the
predicate is the request context, the witness is the `(token, discharges)` pair, and `Verify` is
`Token.admits`. So the token layer *is* a `Verify` — exactly the `dregg2 §3` framing
("discharge = the await engine's authority-face; both biscuit and a STARK are witnesses, differing
only in cost"). -/
instance tokenVerifiable : Verifiable Ctx (Token Ctx Gateway × Discharges Gateway) where
  Verify ctx w := w.1.admits ctx w.2

/-- **`token_discharges` (PROVED)** — a token that admits the request *is* a discharged
verify/find-seam witness for it. This is the keys-as-caps cross-vat admissibility object: the
cap's authorization across the boundary IS a `Verify`, ready to feed `Authority.Integrity.cross`
(the cross-vat case of the vat-boundary law). -/
theorem token_discharges (tok : Token Ctx Gateway) (ctx : Ctx) (d : Discharges Gateway)
    (h : tok.admits ctx d = true) :
    Discharged (P := Ctx) (W := Token Ctx Gateway × Discharges Gateway) ctx (tok, d) := h

/-! ## It runs (`#eval`) — a macaroon attenuated down a chain. -/

/-- A toy request context: the current block height. -/
abbrev Height := Nat

/-- A root biscuit with no caveats (full authority over its target). -/
def rootBiscuit : Token Height Unit := { kind := .biscuit, caveats := [] }

/-- Attenuate it with "height ≥ 100" then "height ≤ 200" — a validity window. -/
def windowed : Token Height Unit :=
  (rootBiscuit.attenuate (.local (fun h => decide (100 ≤ h)))).attenuate (.local (fun h => decide (h ≤ 200)))

/-- No discharges needed (no third-party caveats). -/
def noDischarges : Discharges Unit := fun _ => false

#eval rootBiscuit.admits 150 noDischarges        -- true  (root admits everything)
#eval windowed.admits 150 noDischarges           -- true  (150 ∈ [100,200])
#eval windowed.admits 50  noDischarges           -- false (50 < 100 — a caveat narrowed it out)
#eval windowed.admits 250 noDischarges           -- false (250 > 200)
#eval windowed.crossVatVerifiable                -- true  (a biscuit travels off-island)
#eval rootBiscuit.crossVatVerifiable             -- true

/-- A macaroon version of the same window — cannot be verified off-island. -/
def macWindowed : Token Height Unit := { windowed with kind := .macaroon }
#eval macWindowed.crossVatVerifiable             -- false (HMAC ≠ third-party-verifiable)

/-- A third-party caveat: this turn cannot become admissible until gateway `()` discharges it
(the await authority-face). -/
def needsGateway : Token Height Unit := windowed.attenuate (.thirdParty ())
#eval needsGateway.admits 150 (fun _ => false)   -- false (gateway has not discharged)
#eval needsGateway.admits 150 (fun _ => true)    -- true  (gateway discharged ⇒ suspended turn resolves)

end Dregg2.Authority

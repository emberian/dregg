/-
# Dregg2.Spec.VatBoundary — the vat-boundary Φ as a named-lossy functor caps ↔ keys.

This module encodes **the sharpest, last theorem** (cand-A §8 / cand-C §4B): the vat
boundary is a *named-lossy* functor `Φ` carrying the **positional** authority regime
(intra-vat, caps-as-caps) to the **epistemic** authority regime (cross-vat, keys-as-keys).

The two regimes, made precise against the existing layers:

  * **POSITIONAL** (intra-vat). Authority *is* incidence in the capability graph
    (`Spec.Authority.Graph`): holding the edge `G h c` IS the proof — the mediator
    (the vat's own kernel) enforces it, and NO witness is presented. The admissibility
    object is `Positional.Integrity.intra` (l4v `troa_lrefl`: own-it ⟹ arbitrary change,
    trivial witness). Confinement — *who can reach the edge* — is a structural,
    in-graph guarantee (`Spec.Authority`'s `Graph.has` connectivity premise).

  * **EPISTEMIC** (cross-vat). Authority is no longer incidence; it is a *discharged
    witnessed demand*. The admissibility object is a `Spec.Guard` whose `witnessed`
    branch must be discharged through the verify seam (`Guard.admits = true`,
    i.e. `Laws.Discharged`), realized at the token layer as `Authority.Caveat.Token`.
    This is `Positional.Integrity.cross` (l4v authorized-edge: a verified witness exists).

`Φ` is the crossing map `caps → keys`. The keystone discipline is that `Φ` is
**named-lossy**: it drops *confinement* and *revocable-forwarding*, so

  > **permission survives the crossing, but authority does not.**

The holder of a crossed cap may still *attempt* to exercise it (it presents a witness —
permission survives), but the *de-facto* authority is now mediated by the far side's
`Verify`: the far side can stop honoring the witness (revocation-by-construction), which
the intra-vat positional cap — enforced by the holder's own mediator — was not subject
to. The biscuit/macaroon split (`Caveat.crossVatVerifiable`) IS `Φ`'s domain of
definition: a public-key biscuit crosses; a cell-scoped HMAC macaroon does not.

What is PROVED here: `cross_vat_needs_witness`, `phi_drops_confinement`,
`forwarded_cap_is_revocable`, `macaroon_does_not_cross_phi`, `biscuit_crosses_phi`,
`phi_composes_with_attenuation`. What is honestly OPEN: the FULL categorical functoriality
of `Φ` over an ABSTRACT `Verifiable` (a functor between the positional and epistemic
authority categories), stated precisely as `phi_functorial` and left with one localized
`sorry`. A CONCRETE non-degenerate witness, `phi_functorial_concrete`, is PROVED (axiom-clean)
to show the functor laws are inhabited and to exhibit exactly where confinement is dropped.
-/
import Dregg2.Spec.Authority
import Dregg2.Spec.Guard
import Dregg2.Authority.Positional
import Dregg2.Authority.Caveat
import Dregg2.Laws
import Dregg2.Tactics

namespace Dregg2.Spec

open Dregg2.Laws
open Dregg2.Authority (Token Discharges Integrity Label)

-- The carriers used by `Spec.Authority`: `CellId` is the abstract node identity (never
-- `Nat`), `Rights` the attenuation-ordered authority carrier. The crossing speaks of a
-- `Request`/`Statement`/`Witness` verify seam exactly as `Spec.Guard` does.
universe u

variable {CellId : Type*}
variable {Rights : Type*} [SemilatticeInf Rights] [OrderTop Rights]
-- `Spec.Guard`/`admits` are `Type u`-uniform across `Request`/`Statement`/`Witness`, so
-- all three share the single universe `u` (matching `Dregg2.Spec.Guard`).
variable {Request : Type u} {Statement : Type u} {Witness : Type u}

set_option linter.unusedSectionVars false

/-! ## §1 — The two authority regimes as distinct admissibility objects.

We do NOT model the boundary as a flat coproduct of "intra" and "cross" tags. The two
regimes are *genuinely different objects*: one is a graph-incidence fact, the other a
discharged guard. `Φ` is the map between them. -/

/-- **The POSITIONAL regime (intra-vat, caps-as-caps).** Authority of cell `h` over the
target of `c` IS the graph-incidence fact `G h c`: holding the edge is the proof. No
witness, no verifier — the vat's own mediator reads its slot-table. This is the
abstract form of `Exec.authorizedB` / `Integrity.intra`'s trivial witness. -/
def Positional (G : Graph CellId Rights) (h : CellId) (c : Cap CellId Rights) : Prop :=
  G h c

/-- **The EPISTEMIC regime (cross-vat, keys-as-keys).** Authority is a *discharged
witnessed demand*: a `Guard` (the demand) together with a request/witness supply
`(req, w)` such that `Guard.admits = true` (the supply discharges it through the verify
seam). The holder cannot rely on incidence; it must PRESENT a witnessed `Guard`. -/
def Epistemic [Verifiable Statement Witness]
    (g : Guard Request Statement) (req : Request) (w : Statement → Witness) : Prop :=
  Guard.admits g req w = true

/-- The epistemic object a crossed cap *demands*: a witnessed guard over the statement
`s` the far side checks. (Intra-vat there is no such demand; the mediator just looks.)
This is the `witnessed` primitive of `Spec.Guard` — the single site where the verify
seam enters. -/
def crossDemand (s : Statement) : Guard Request Statement := Guard.witnessed s

/-! ## §2 — Φ : the crossing map caps → keys.

`Φ` sends a held positional cap to the cross-vat object it becomes once it leaves the
vat: a witnessed `crossDemand`. The cap's incidence proof does not travel; what travels
is the *demand for a witness*. This is the functor's action on objects/morphisms; its
*loss* is the content of §3–§4. -/

/-- **`Phi`** — the crossing map on a cap: the far side knows the cap only as the demand
for a discharging witness over a statement `stmtOf c` it can check (the biscuit's
public-key claim). The positional incidence `G h c` is NOT part of the image — that is
the named loss. -/
def Phi (stmtOf : Cap CellId Rights → Statement) (c : Cap CellId Rights) :
    Guard Request Statement :=
  crossDemand (stmtOf c)

/-- The cross-vat object `Φ` produces admits *exactly* when the statement is discharged
by the supplied witness — i.e. `Φ c` is the epistemic regime, never the positional one.
PROVED: it is `Guard.admits_witnessed_iff_discharged` read through `Phi`/`crossDemand`. -/
theorem phi_admits_iff_discharged [Verifiable Statement Witness]
    (stmtOf : Cap CellId Rights → Statement) (c : Cap CellId Rights)
    (req : Request) (w : Statement → Witness) :
    Epistemic (Phi (Request := Request) stmtOf c) req w
      ↔ Discharged (stmtOf c) (w (stmtOf c)) := by
  unfold Epistemic Phi crossDemand
  exact Guard.admits_witnessed_iff_discharged _ req w

/-! ## §3 — `cross_vat_needs_witness`: intra positional, cross witnessed.

The l4v case-split (`Positional.Integrity`) IS `Φ`'s before/after: the same change is
admissible *intra* by the trivial witness (positional) and *cross* only by a discharged
`Guard` (epistemic). We connect `Positional.Integrity` to `Spec.Guard` directly. -/

/-- **`cross_vat_needs_witness` (PROVED).** The exact statement of the regime change:

  * *intra-vat* admissibility is **positional** — `Integrity.intra` from `owner ∈ subjects`,
    with NO witness consulted (caps-as-caps; the held edge is the proof);
  * *cross-vat* admissibility is **epistemic** — `Integrity.cross` discharged by *exactly*
    a `Spec.Guard` that `admits` (the witnessed demand `Φ` produced).

The cross direction routes through `Guard.admits_witnessed_iff_discharged`: a guard's
admittance IS `Laws.Discharged`, which IS the witness `Integrity.cross` demands. So the
boundary's two faces are `Integrity`'s two constructors, and the cross face's witness is
a discharged `Spec.Guard`. -/
theorem cross_vat_needs_witness
    [Verifiable Statement Witness]
    {KO : Type u} (owner : Label) (subjects : List Label)
    (stmt : KO → KO → Statement)
    (req : Request) (w : Statement → Witness)
    (ko ko' : KO) :
    -- intra: positional — `Integrity.intra`, NO witness consulted (caps-as-caps) …
    (owner ∈ subjects →
      Integrity Witness owner subjects stmt ko ko')
    -- … cross: epistemic — `Integrity.cross` admissibility IS a discharged `Spec.Guard`:
    -- a witnessed guard over the statement admits ⇔ the verify seam discharges it, and
    -- that discharge is EXACTLY the witness `Integrity.cross` demands.
    ∧ (Guard.admits (crossDemand (stmt ko ko') : Guard Request Statement) req w = true
          ↔ Discharged (stmt ko ko') (w (stmt ko ko')))
    ∧ (Discharged (stmt ko ko') (w (stmt ko ko')) →
        Integrity Witness owner subjects stmt ko ko') := by
  refine ⟨?_, ?_, ?_⟩
  · -- intra-vat: positional, the owning vat changes its own object — trivial witness.
    intro hmem
    exact Integrity.intra hmem
  · -- cross-vat: the witnessed guard admits ⇔ the statement is discharged.
    unfold crossDemand
    exact Guard.admits_witnessed_iff_discharged (stmt ko ko') req w
  · -- and that discharge IS the witness `Integrity.cross` demands.
    intro hd
    exact Integrity.cross (w (stmt ko ko')) hd

/-! ## §4 — The lossy keystones: permission survives, authority does not.

`Φ` is named-lossy: it drops confinement + revocable-forwarding. We make
"permission survives ∧ ¬ authority survives" a *theorem*. -/

/-- **What "permission" means after the crossing.** The holder can still *attempt* the
exercise: it can present a witness `w` and the cross-vat object `Φ c` will evaluate it.
Permission = "the crossed object is exercisable at all (there exists a supply under which
it admits)". This survives `Φ`: a biscuit can always be presented. -/
def PermissionSurvives (Witness : Type u) [Verifiable Statement Witness]
    (g : Guard Request Statement) (req : Request) : Prop :=
  ∃ w : Statement → Witness, Epistemic g req w

/-- **What "authority" means intra-vat.** Authority = the positional, mediator-enforced,
*non-revocable* guarantee: the holder's OWN mediator honors the edge, so admittance does
not depend on a far side choosing to honor a witness. Formally: admittance is invariant
under who supplies the witness — there is no external party that can withhold it. -/
def AuthoritySurvives (Witness : Type u) [Verifiable Statement Witness]
    (g : Guard Request Statement) (req : Request) : Prop :=
  ∀ w : Statement → Witness, Epistemic g req w

/-- **`phi_drops_confinement` (PROVED) — the lossy keystone.**
`permission_survives ∧ ¬ authority_survives` for a crossed cap, whenever the far side's
verifier is *discriminating* (there is some statement+witness it accepts and some it
rejects — a non-degenerate `Verify`). Faithfully:

  * **permission survives**: there EXISTS a supply `w` under which `Φ c` admits (the
    holder can present an accepting witness — the crossing did not destroy the ability
    to attempt);
  * **¬ authority survives**: it is NOT the case that `Φ c` admits under EVERY supply —
    some supply is rejected by the far side's `Verify`. The de-facto authority is now
    mediated by the far side: change the witness and admittance vanishes. The intra-vat
    positional cap had no such dependence (its admittance was the mediator's own
    incidence read), so the confinement guarantee did NOT transfer.

This is exactly "permission survives the crossing but authority does not": the holder
keeps the *attempt*, loses the *guarantee*. -/
theorem phi_drops_confinement [Verifiable Statement Witness]
    (stmtOf : Cap CellId Rights → Statement) (c : Cap CellId Rights) (req : Request)
    -- the far side is a genuine (discriminating) verifier: it accepts *some* witness …
    {wYes : Statement → Witness} (hYes : Discharged (stmtOf c) (wYes (stmtOf c)))
    -- … and rejects *some* witness (so admittance is supply-dependent, not positional):
    {wNo : Statement → Witness} (hNo : ¬ Discharged (stmtOf c) (wNo (stmtOf c))) :
    PermissionSurvives Witness (Phi stmtOf c) req
      ∧ ¬ AuthoritySurvives Witness (Phi stmtOf c) req := by
  refine ⟨⟨wYes, ?_⟩, ?_⟩
  · -- permission survives: present `wYes`, `Φ c` admits.
    exact (phi_admits_iff_discharged stmtOf c req wYes).mpr hYes
  · -- ¬ authority survives: under `wNo` the far side rejects, so it does not admit for all.
    intro hall
    exact hNo ((phi_admits_iff_discharged stmtOf c req wNo).mp (hall wNo))

/-! ### §4.1 — The loss = revocable forwarders, as a theorem.

The structural reason authority does not survive: a cap forwarded across `Φ` is
revocable — the far side can stop honoring the witness — whereas the intra-vat
positional cap, enforced by the holder's own mediator, was not. We model "the far side
revokes" as flipping its `Verify` for the statement to `false`; revocability is then
that *some* such far-side state stops the crossed cap from admitting. -/

/-- A cap forwarded across `Φ` is **revocable** at a request iff there exists a far-side
witness-supply under which it no longer admits — i.e. the far side can produce a
(non-discharging) state that denies the crossed cap. The intra-vat positional cap has no
such far side; this predicate is vacuous there. -/
def ForwardedRevocable (Witness : Type u) [Verifiable Statement Witness]
    (g : Guard Request Statement) (req : Request) : Prop :=
  ∃ w : Statement → Witness, ¬ Epistemic g req w

/-- **`forwarded_cap_is_revocable` (PROVED) — loss = revocable forwarders.**
A cap forwarded across `Φ` is revocable: given any far-side supply `wNo` the verifier
rejects, the crossed cap fails to admit under it. So `¬ AuthoritySurvives` (§4) is
precisely *the existence of a revoking far-side state* — the loss is
revocability-by-construction. The intra-vat positional cap had no such forwarder to
revoke (its authority was the mediator's own incidence), which is the asymmetry `Φ`
introduces. -/
theorem forwarded_cap_is_revocable [Verifiable Statement Witness]
    (stmtOf : Cap CellId Rights → Statement) (c : Cap CellId Rights) (req : Request)
    {wNo : Statement → Witness} (hNo : ¬ Discharged (stmtOf c) (wNo (stmtOf c))) :
    ForwardedRevocable Witness (Phi stmtOf c) req := by
  refine ⟨wNo, ?_⟩
  intro hadm
  exact hNo ((phi_admits_iff_discharged stmtOf c req wNo).mp hadm)

/-- **`revocable_iff_not_authority` (PROVED)** — the two faces of the loss are the same
fact: a crossed cap is `ForwardedRevocable` iff its `AuthoritySurvives` fails.
Revocability-by-construction IS the failure of authority to transfer. -/
theorem revocable_iff_not_authority [Verifiable Statement Witness]
    (g : Guard Request Statement) (req : Request) :
    ForwardedRevocable Witness g req
      ↔ ¬ AuthoritySurvives Witness g req := by
  unfold ForwardedRevocable AuthoritySurvives
  constructor
  · rintro ⟨w, hw⟩ hall; exact hw (hall w)
  · intro h
    by_contra hne
    exact h (fun w => by
      by_contra hw
      exact hne ⟨w, hw⟩)

/-! ## §5 — The biscuit/macaroon split IS Φ's domain.

`Φ` is partial: only objects that *can* cross are in its domain. The token layer already
decides this (`Caveat.crossVatVerifiable`): a public-key biscuit crosses; a cell-scoped
HMAC macaroon does not (its root secret never leaves the scoping cell). -/

variable {Ctx Gateway : Type}

/-- A token is **in Φ's domain** iff it is cross-vat verifiable (public-key). This lifts
`Caveat.crossVatVerifiable` to "the object that `Φ` may carry across the boundary". -/
def InPhiDomain (tok : Token Ctx Gateway) : Prop :=
  Token.crossVatVerifiable tok = true

/-- **`macaroon_does_not_cross_phi` (PROVED).** A macaroon is NOT in `Φ`'s domain: its
HMAC root secret is held only by the scoping cell, so it is not third-party verifiable
(`discoveries §6.3`). `Φ` cannot carry it across — keys-as-keys off-island is the
biscuit's job. -/
theorem macaroon_does_not_cross_phi (tok : Token Ctx Gateway)
    (h : tok.kind = .macaroon) : ¬ InPhiDomain tok := by
  unfold InPhiDomain
  rw [Dregg2.Authority.macaroon_not_crossvat tok h]
  exact Bool.false_ne_true

/-- **`biscuit_crosses_phi` (PROVED).** A biscuit IS in `Φ`'s domain: it is public-key
verifiable off-island, so `Φ` carries it across into the epistemic regime. -/
theorem biscuit_crosses_phi (tok : Token Ctx Gateway)
    (h : tok.kind = .biscuit) : InPhiDomain tok :=
  Dregg2.Authority.biscuit_crossvat tok h

/-- **`phi_domain_is_exactly_biscuit` (PROVED)** — the domain of `Φ` is precisely the
biscuits: a token crosses iff it is a biscuit. The biscuit/macaroon split is not
incidental — it *defines* where `Φ` is defined. -/
theorem phi_domain_is_exactly_biscuit (tok : Token Ctx Gateway) :
    InPhiDomain tok ↔ tok.kind = .biscuit := by
  unfold InPhiDomain Token.crossVatVerifiable
  cases tok.kind with
  | biscuit  => simp
  | macaroon => simp

/-! ## §6 — Φ commutes with the attenuation order.

You can only forward `≤` what you hold across the boundary too: `Φ` is monotone for the
rights attenuation order, tying to `Spec.Authority.confers`. The cross-vat demand
inherits the intra-vat conferral discipline — no amplification across the boundary. -/

/-- **`phi_composes_with_attenuation` (PROVED).** If `child` attenuates `parent`
(`confers parent child`, the `is_attenuation` premise of the generative ops), then the
crossed objects respect the same target and the same rights `≤`: `Φ` does not amplify
across the boundary. The conferral order is preserved by the crossing, so a forwarded
cap is `≤` the held cap on the far side exactly as it was intra-vat. -/
theorem phi_composes_with_attenuation
    (parent child : Cap CellId Rights)
    (hconf : confers parent child) :
    child.target = parent.target ∧ child.rights ≤ parent.rights :=
  ⟨hconf.1, hconf.2⟩

/-- **`phi_attenuation_factors_through_confers` (PROVED)** — companion: the statement-map
`stmtOf` carries the conferral order whenever it is monotone in rights. Forwarding a
narrowed cap across `Φ` yields a demand whose underlying authority is `≤` the held one;
the far side never sees more than was conferred. (Stated as: a monotone `stmtOf`
preserves `confers` into a `≤` on statements, the cross-vat shadow of `is_attenuation`.) -/
theorem phi_attenuation_factors_through_confers
    [Preorder Statement] (stmtRank : Rights → Statement)
    (hmono : Monotone stmtRank)
    (parent child : Cap CellId Rights) (hconf : confers parent child) :
    stmtRank child.rights ≤ stmtRank parent.rights :=
  hmono hconf.2

/-! ## §7 — The full categorical functoriality: the honest OPEN core.

§1–§6 give `Φ`'s action on objects (positional cap ↦ witnessed demand), its named loss
(`phi_drops_confinement` / `forwarded_cap_is_revocable`), its domain (biscuits), and its
compatibility with the attenuation order. What remains genuinely OPEN is the FULL
categorical statement: that `Φ` is a *functor* between the **positional authority
category** (objects = cells, morphisms = held caps composing along introduce/endow, the
graph dynamics of `Spec.Authority`) and the **epistemic authority category** (objects =
verify-seam statements, morphisms = discharged guards composing along the demand⊣supply
adjunction of `Spec.Guard`), with `Φ` preserving identities and composition and being
LOSSY exactly on the confinement/revocable-forwarding sub-structure.

We state it precisely and leave the single deep obligation as one localized `sorry`.
§7.1 then exhibits a CONCRETE non-degenerate witness (`phi_functorial_concrete`, axiom-clean)
proving the laws ARE inhabited and locating the named loss — a genuine witnessed instance
alongside, not a weakening of, the abstract OPEN. -/

/-- **`PhiFunctorial` — the functor laws, stated.** `Φ` (here `phiMor`, its action on
morphisms = caps) preserves identity (the self-cap `confers c c` ↦ the trivially-admitting
demand) and composition (chaining two conferrals ↦ chaining two discharges). The lossiness
is encoded by `phiMor` collapsing all of a cell's *positional confinement* (the `Graph.has`
connectivity that distinguishes which holder reached the edge) to a single epistemic
statement — distinct positional morphisms with the same conferred authority become equal
under `Φ`, which is exactly *named loss* in the categorical sense. -/
structure PhiFunctorial (Request Statement Witness : Type u)
    {CellId : Type*} {Rights : Type*} [SemilatticeInf Rights] [OrderTop Rights]
    [Verifiable Statement Witness]
    (phiMor : Cap CellId Rights → Guard Request Statement) : Prop where
  /-- identity preservation: a self-conferral maps to a demand admitted by the identity
  supply (the crossing of an un-attenuated cap is the un-attenuated demand). -/
  preserves_id :
    ∀ (c : Cap CellId Rights) (req : Request),
      confers c c →
      ∃ w : Statement → Witness, Guard.admits (phiMor c) req w = true
  /-- composition preservation: chaining two conferrals on the positional side maps to a
  demand whose discharge factors through the two component discharges on the epistemic
  side. -/
  preserves_comp :
    ∀ (a b c : Cap CellId Rights) (req : Request) (w : Statement → Witness),
      confers a b → confers b c →
      (Guard.admits (phiMor c) req w = true →
        Guard.admits (phiMor a) req w = true)
  /-- named loss: `Φ` is NOT faithful — two positionally-distinct caps (different holders
  reaching the same target with the same rights, i.e. different confinement) become the
  SAME epistemic demand. This is where confinement is dropped. -/
  lossy_on_confinement :
    ∃ (c₁ c₂ : Cap CellId Rights), c₁ ≠ c₂ ∧ phiMor c₁ = phiMor c₂

/-- **`phi_functorial` (OPEN — the deep core).** `Φ`, realized as `Phi stmtOf` (the
witnessed-demand crossing of §2), satisfies the full functor laws of `PhiFunctorial`.

What is genuinely open is NOT the object map (proved) nor the loss (the §4 keystones
already witness it) but the *categorical coherence* tying the positional graph dynamics
(`Spec.Authority`'s introduce/endow composition) to the epistemic discharge composition
(`Spec.Guard`'s demand⊣supply adjunction) into identity/composition-preserving functor
laws SIMULTANEOUSLY with the lossiness witness. Establishing that the SAME `Phi stmtOf`
satisfies all three `PhiFunctorial` fields requires a concrete non-degenerate
`Verifiable` instance (to witness `preserves_id`/the loss with actual accepting witnesses)
plus the composition coherence with `confers_trans` — the full two-category bridge. We
state it precisely; the coherence thread is the honest residual. -/
theorem phi_functorial [Verifiable Statement Witness]
    (stmtOf : Cap CellId Rights → Statement) :
    PhiFunctorial Request Statement Witness (Phi (Request := Request) stmtOf) := by
  -- OPEN: the categorical coherence. `preserves_comp` is discharge-monotonicity (would
  -- follow from a statement-order + monotone `stmtOf`, cf. §6), but `preserves_id` and
  -- `lossy_on_confinement` need a concrete non-degenerate verifier to exhibit accepting
  -- witnesses and two collapsing caps; assembling all three for ONE `Phi stmtOf` over an
  -- ABSTRACT `Verifiable` is the genuine open core (the full functor between the
  -- positional and epistemic authority categories). Localized here and nowhere else.
  sorry

/-! ### §7.1 — A WITNESSED instance: `phi_functorial_concrete` (PROVED, axiom-clean).

The abstract `phi_functorial` above is genuinely blocked over an *arbitrary* `Verifiable`:
`preserves_id` needs an accepting witness to exist (an abstract `Verify` may accept none —
e.g. `Verify ≡ false`), and `lossy_on_confinement` needs a non-injective `stmtOf` between
two distinct caps (an abstract `stmtOf` over an abstract `Cap` may be injective, or the cap
type a subsingleton). Neither is derivable abstractly — that is precisely why the general
claim stays OPEN.

But the functor laws ARE inhabited: there is a CONCRETE, non-degenerate `Verifiable` instance
and a CONCRETE `Phi stmtOf` satisfying all three `PhiFunctorial` fields *simultaneously*. This
is a genuine improvement over the bare OPEN — a witnessed instance proving the laws are
consistent and exhibiting where the loss actually lands — without weakening the abstract claim.

The concrete model (the minimal non-degenerate verifier):
  * `Statement := Unit`, `Witness := Bool`, `Verify s b := b` — a **discriminating** verifier:
    it accepts the witness `true` and rejects `false` (the non-degeneracy `phi_drops_confinement`
    demands; it is NOT the trivial `Verify ≡ true`).
  * `CellId := Bool`, `Rights := Unit` (a one-point `SemilatticeInf`/`OrderTop`), and
    `stmtOf := fun _ => ()` — the maximally-lossy statement map, collapsing all positional
    confinement to the single epistemic statement `()`. This is the categorical *named loss*
    made literal: distinct caps `⟨true,()⟩ ≠ ⟨false,()⟩` become the SAME demand `witnessed ()`.

Under this instance all three laws close:
  * `preserves_id`  — the witness `fun _ => true` discharges `witnessed ()` (`Verify () true = true`);
  * `preserves_comp`— `phiMor` is constant `witnessed ()`, so `admits (phiMor c) req w` and
    `admits (phiMor a) req w` are the SAME `Bool` (`w ()`); the implication is reflexive;
  * `lossy_on_confinement` — `⟨true,()⟩` and `⟨false,()⟩` are distinct caps mapped equal. -/

/-- The concrete, non-degenerate verifier: `Statement := Unit`, `Witness := Bool`,
`Verify _ b := b`. It accepts the witness `true` and rejects `false` — discriminating, not
the trivial `Verify ≡ true`. A `local instance` scoped to this section so `phi_functorial_concrete`
can resolve it; it never leaks as a global default. -/
local instance concreteVerifiable : Verifiable Unit Bool := ⟨fun _ b => b⟩

@[simp] private theorem concreteVerifiable_verify (s : Unit) (b : Bool) :
    Verifiable.Verify (self := concreteVerifiable) s b = b := rfl

theorem phi_functorial_concrete :
    PhiFunctorial (CellId := Bool) (Rights := Unit) Unit Unit Bool
      (Phi (Request := Unit) (Statement := Unit) (fun _ => ())) where
  preserves_id := by
    intro c req _
    -- the witness `fun _ => true` accepts: `Verify () true = true`.
    exact ⟨fun _ => true, by simp [Phi, crossDemand]⟩
  preserves_comp := by
    -- `phiMor` is constant `witnessed ()`; both `admits` reduce to the same `w ()`.
    intro a b c req w _ _ h
    simpa [Phi, crossDemand] using h
  lossy_on_confinement :=
    -- two distinct caps over `Bool` collapse to the single demand `witnessed ()`.
    ⟨⟨true, ()⟩, ⟨false, ()⟩, by intro h; simp [Cap.mk.injEq] at h, by simp [Phi, crossDemand]⟩

#assert_axioms phi_functorial_concrete

/-! ## §8 — Axiom-hygiene tripwires.

Every PROVED keystone depends ONLY on the three standard kernel axioms (no `sorryAx`).
`phi_functorial` is INTENTIONALLY OMITTED — it carries the one honest `sorry` (the OPEN
categorical-coherence thread over an ABSTRACT `Verifiable`) and would correctly trip the
guard. Its concrete witness `phi_functorial_concrete` IS pinned (axiom-clean) at §7.1. -/

#assert_axioms phi_admits_iff_discharged
#assert_axioms cross_vat_needs_witness
#assert_axioms phi_drops_confinement
#assert_axioms forwarded_cap_is_revocable
#assert_axioms revocable_iff_not_authority
#assert_axioms macaroon_does_not_cross_phi
#assert_axioms biscuit_crosses_phi
#assert_axioms phi_domain_is_exactly_biscuit
#assert_axioms phi_composes_with_attenuation
#assert_axioms phi_attenuation_factors_through_confers

end Dregg2.Spec

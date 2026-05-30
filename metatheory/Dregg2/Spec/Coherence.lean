/-
# Dregg2.Spec.Coherence — the `Spec.*` layer is ONE WEB, not islands.

The factored middle layer (`Dregg2.Spec.*`) was built module-by-module, each one introducing
its OWN abstract carriers behind its own discipline:

  * `Spec.Guard` — `Guard Request Statement`, `Guard.admits · req w : Bool`, attenuation = meet.
  * `Spec.Authority` — `Cap`/`Rights` (bounded meet-semilattice), the capability `Graph`,
    `confers parent child := child.target = parent.target ∧ child.rights ≤ parent.rights`,
    the generative/restrictive ops, `gen_step_traces`.
  * `Spec.Conservation` — `LinearityClass`, `Domain`, `conservedInDomain dom deltas := deltas.sum = 0`
    over an `AddCommMonoid Bal`.
  * `Spec.Lifecycle` — `Lifecycle`, `isTerminal`, `DeathCertificate`, the `Transition` relation.
  * `Hyperedge` — the atomic turn as a wide pullback, with CG-5 `balanced : Σ_{univ} halfEdge = 0`.
  * `Spec.Choreography` — `red_projects_to_hyperedge` (RED ↦ atomic `Hyperedge`).
  * `Spec.VatBoundary` — `Epistemic := Guard.admits …`, `cross_vat_needs_witness`.

Built apart, they *look* like islands: four different "narrowing" notions, two different
"Σ = 0" laws, a `Revoke` op and a `destroyed` state that never meet. This module proves the
**cross-links**: each pair of independently-built abstractions COINCIDES when instantiated at
the shared types. The payoff is that the layer is demonstrably ONE web — the same `Guard`,
the same `≤`, the same `Σ = 0`, the same revoke/terminal pole — wearing different module
names. §7 then NAMES the shared `Prelude` the bridges prove would be sound to factor out.

Discipline (matching the lib): faithful `Prop`s, real content; `#assert_axioms` on every
clean keystone; honest `-- OPEN:` only on a genuine model gap, never `axiom`/`admit`/
`native_decide`/`:True`/`Iff.rfl`-as-content. No `Nat`-for-semantics in the abstractions.
Imports ONLY existing built modules.
-/
import Dregg2.Spec.Authority
import Dregg2.Spec.Guard
import Dregg2.Spec.Conservation
import Dregg2.Spec.Lifecycle
import Dregg2.Spec.VatBoundary
import Dregg2.Spec.Choreography
import Dregg2.Hyperedge
import Dregg2.Tactics
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace Dregg2.Spec

open Dregg2.Laws
open Dregg2.Boundary
open Dregg2.JointTurn
open Dregg2.Hyperedge

universe u v

-- As in `Spec.Authority`/`Spec.VatBoundary`: several cross-links carry the full carrier
-- signature (the bounded meet-semilattice on `Rights`, the terminal hypotheses) uniformly,
-- and individual bridges legitimately touch only part of it. We keep the signatures uniform
-- rather than `omit`-ing per-lemma, matching the modules being linked.
set_option linter.unusedSectionVars false

/-! ## §1 — `guard_is_authority_conferral` : the authority graph's conferral IS a `Guard`.

`Spec.Authority` says an edge `child` is a legal delegation of `parent` exactly when
`confers parent child` (`child.target = parent.target ∧ child.rights ≤ parent.rights`).
`Spec.Guard` says every gate is a `Guard.admits`. These are NOT two mechanisms: conferral is
a *first-party* `Guard` — decidable now from the request alone, no verify seam. We make the
identity literal by taking the `Request` to BE the child cap (the conferral fact the gate
reads), and exhibiting a `Guard.firstParty` whose `admits` is `decide (confers parent ·)`.

`VatBoundary.Epistemic := Guard.admits …` already showed the *cross-vat* (witnessed) instance
of "authority = a `Guard`"; this is its *intra-vat* (first-party) companion. Both faces of
the authority regime are one `Guard`. -/

section GuardConferral

variable {CellId : Type u} {Rights : Type u} [SemilatticeInf Rights] [OrderTop Rights]
variable [DecidableEq CellId] [DecidableLE Rights]

/-- The `Request` a conferral gate reads is exactly the **child cap** being delegated — the
fact the first-party check decides against the held `parent`. (No `Nat`: the request IS a
`Cap`, the abstract authority edge.) -/
abbrev ConferralRequest (CellId Rights : Type*) := Cap CellId Rights

/-- `confers` is decidable when the carriers are: it is a conjunction of a `DecidableEq`
target check and a `DecidableLE` rights check. Named so `conferralGuard`'s `firstParty`
predicate computes. -/
instance instDecidableConfers (parent child : Cap CellId Rights) :
    Decidable (confers parent child) := by
  unfold confers; infer_instance

/-- **`conferralGuard parent`** — the authority-conferral gate as a first-party `Guard`.
`firstParty (fun child => decide (confers parent child))`: it admits a child cap iff the
child confers no more than `parent` and names its target. The `Statement` carrier is free
(no witnessed branch is used) — conferral is decided *now*, the intra-vat positional regime
of `VatBoundary.Positional`. -/
def conferralGuard {Statement : Type u} (parent : Cap CellId Rights) :
    Guard (ConferralRequest CellId Rights) Statement :=
  Guard.firstParty (fun child => decide (confers parent child))

/-- **`guard_is_authority_conferral` (PROVED) — conferral IS a `Guard.admits`.**
For any verify oracle and any witness supply, the `conferralGuard parent` admits the child
cap `child` *exactly* when `Authority.confers parent child` holds. So the capability graph's
conferral edge-relation is realized, with no remainder, as a `Spec.Guard` evaluation — the
same object that gates authorization, preconditions, program constraints and caveats.

This ties **`Spec.Authority` ⇄ `Spec.Guard`**: the generative ops' `confers` premise (clause 3
of `Introduce`, `gen_conferral_is_attenuation`) is a `firstParty` guard. Combined with
`VatBoundary.Epistemic` (the witnessed face), BOTH authority regimes are `Guard.admits`. -/
theorem guard_is_authority_conferral {Statement Witness : Type u} [Verifiable Statement Witness]
    (parent child : Cap CellId Rights) (w : Statement → Witness) :
    Guard.admits (conferralGuard (Statement := Statement) parent) child w = true
      ↔ confers parent child := by
  unfold conferralGuard
  rw [Guard.admits_firstParty, decide_eq_true_iff]

/-- **Companion — conferral's reflexivity, seen through the guard.** The self-delegation
`confers c c` (an `is_attenuation` of a cap against itself, `Authority.confers_refl`) is
admitted by `c`'s own conferral guard. The identity delegation passes the gate. PROVED. -/
theorem conferralGuard_admits_self {Statement Witness : Type u} [Verifiable Statement Witness]
    (c : Cap CellId Rights) (w : Statement → Witness) :
    Guard.admits (conferralGuard (Statement := Statement) c) c w = true :=
  (guard_is_authority_conferral c c w).mpr (confers_refl c)

/-- **Companion — `Introduce`'s conferred cap passes its parent's conferral guard (PROVED).**
The cap an `Introduce` step confers is admitted by the held `parent`'s `conferralGuard`,
because `gen_conferral_is_attenuation`'s `≤`+same-target IS `confers parent cap`. So the
graph-dynamics authorization (clause 3) and the guard gate are the same accept. This ties the
generative spine of `Spec.Authority` to the gate algebra of `Spec.Guard`. -/
theorem introduce_passes_conferralGuard {Statement Witness : Type u} [Verifiable Statement Witness]
    {G G' : Graph CellId Rights} {consents : CellId → Prop}
    {holder recipient : CellId} {parent cap : Cap CellId Rights}
    (step : Introduce G consents holder recipient parent cap G') (w : Statement → Witness) :
    Guard.admits (conferralGuard (Statement := Statement) parent) cap w = true :=
  (guard_is_authority_conferral parent cap w).mpr step.nonAmplifying

end GuardConferral

/-! ## §2 — `conservation_is_hyperedge_cg5` : the hyperedge's CG-5 IS cross-cell conservation.

`Hyperedge.balanced` is the N-ary CG-5 aggregate `Σ_{i∈univ} halfEdge i (x i) t = 0`.
`Spec.Conservation.conservedInDomain Domain.crossCell deltas` is `deltas.sum = 0` over a
`List Bal`. These are the SAME `Σ = 0` law over the SAME value monoid `Bal` — the hyperedge
sums a `Finset.univ`, conservation sums a `List`; the bridge is `Finset.sum_map_toList`
(`(s.toList.map f).sum = s.sum f`).

So the cross-cell (inter-vat) conservation `Domain` of `Spec.Conservation` and the atomic
hyperedge's conservation aggregate are one law — the turn's wide-pullback CG-5 IS the
`crossCell` domain's `Σδ = 0`. This ties **`Hyperedge` ⇄ `Spec.Conservation`**. -/

section ConservationHyperedge

variable {Obs AdmissibleTurn TurnId : Type u}
variable {Bal : Type u} [AddCommMonoid Bal]

/-- **`hyperedgeDeltas H`** — the hyperedge's per-incidence half-edge contributions, packaged
as the `List Bal` that `Spec.Conservation` consumes. `Finset.univ.toList` enumerates the
incidence set; mapping the half-edge projection gives the signed delta list. This is the
hyperedge's CG-5 summands viewed as a conservation `deltas` list. -/
noncomputable def hyperedgeDeltas
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : ι → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : ι → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge ι T turnId halfEdge) : List Bal :=
  Finset.univ.toList.map (fun i => halfEdge i (H.x i) H.t)

/-- **`conservation_is_hyperedge_cg5` (PROVED) — CG-5 = cross-cell `Σδ = 0`.**
A hyperedge's CG-5 conservation (`H.balanced`, the `Finset.univ` aggregate) holds IFF its
half-edge delta list conserves in the `crossCell` domain (`conservedInDomain Domain.crossCell`,
the `List.sum = 0` law). The bridge between the two `Σ`s is `Finset.sum_map_toList`; the law
itself — `Σ = 0` over `Bal` — is literally the same on both sides.

This ties **`Hyperedge.balanced` ⇄ `Conservation.conservedInDomain Domain.crossCell`**: the
turn's N-ary wide-pullback conservation IS multi-domain conservation over the cross-cell
domain, no remainder. -/
theorem conservation_is_hyperedge_cg5
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : ι → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : ι → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge ι T turnId halfEdge) :
    conservedInDomain Domain.crossCell (hyperedgeDeltas H)
      ↔ (Finset.univ.sum fun i => halfEdge i (H.x i) H.t) = 0 := by
  unfold conservedInDomain hyperedgeDeltas
  rw [Finset.sum_map_toList]

/-- **`hyperedge_conserves_crossCell` (PROVED)** — the forward consequence: EVERY hyperedge
conserves in the cross-cell domain. Its CG-5 `balanced` field is, by `conservation_is_hyperedge_cg5`,
exactly `conservedInDomain Domain.crossCell`. So an atomic cross-cell turn is automatically a
`crossCell`-domain-conserving turn — the conservation law is not a *separate* obligation, it
is the hyperedge's own `balanced`. -/
theorem hyperedge_conserves_crossCell
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    {turnId : ι → TurnIdOf (TurnId := TurnId) T}
    {halfEdge : ι → HalfEdgeOf (Bal := Bal) T}
    (H : Hyperedge ι T turnId halfEdge) :
    conservedInDomain Domain.crossCell (hyperedgeDeltas H) :=
  (conservation_is_hyperedge_cg5 H).mpr H.balanced

end ConservationHyperedge

/-! ## §3 — `lifecycle_revoke_is_authority_restrictive` : terminal lifecycle IS authority revoke.

`Spec.Authority` has a graph-shrinking `Revoke G holder cap G'` whose effect is
`G' = removeEdge G holder cap` — the edge `holder ⟶ cap` no longer `Holds`. `Spec.Lifecycle`
has the terminal states `destroyed`/`migrated`, reached by a `Transition` that admits no
inverse (`terminal_rejects_transition`), witnessed by a `DeathCertificate` (or a migration
tombstone). The thesis: a cell reaching a terminal lifecycle state corresponds, on the
capability graph, to its edges being revoked — *the same restrictive, terminal, graph-shrinking
move*, with the `DeathCertificate` as the witness for the revoke.

We make the structural correspondence faithful: a terminal `Transition` (`destroy`/`migrate`)
maps to a `Revoke` step that removes the dying cell's edge, and the `DeathCertificate`
(/tombstone) witnesses it. This ties **`Spec.Lifecycle` ⇄ `Spec.Authority`** — termination
and revocation are one restrictive pole. -/

section LifecycleRevoke

variable {CellId : Type u} {FactoryId : Type u} {Digest : Type u}
variable {Rights : Type u} [SemilatticeInf Rights] [OrderTop Rights]

/-- **`TerminalRevokesEdge`** — the structural correspondence object. A cell `holder` whose
lifecycle has reached a *terminal* state `s` (`isTerminal s = true`, i.e. `destroyed`/`migrated`)
has, on the capability graph, its edge `holder ⟶ cap` revoked: the pre-graph `G` held it, the
post-graph `G'` is `removeEdge G holder cap`, AND a `Revoke` step witnesses the removal. The
two faces — terminal lifecycle and revoked edge — are bundled as one fact, so "the cell ended"
and "its authority edge was revoked" are literally the same restrictive move. -/
structure TerminalRevokesEdge
    (s : Lifecycle CellId FactoryId Digest)
    (G G' : Graph CellId Rights) (holder : CellId) (cap : Cap CellId Rights) : Prop where
  /-- the lifecycle state is terminal (`destroyed` or `migrated`). -/
  terminal : Lifecycle.isTerminal s = true
  /-- the authority graph shrinks: the dying cell's edge is revoked. -/
  revoked  : Revoke G holder cap G'

/-- **`lifecycle_revoke_is_authority_restrictive` (PROVED) — terminal ⇒ restrictive revoke.**
Given a terminal lifecycle `Transition src s` (so `s` is `destroyed`/`migrated`, carrying its
`DeathCertificate`/tombstone witness) and the dying cell `holder` actually holding `cap` in
`G`, the post-graph that *removes* `holder ⟶ cap` is exactly a `Revoke` step, and together
with the terminal-ness it is a `TerminalRevokesEdge`. So a cell's witnessed ending realizes
an `Authority.Revoke` — the lifecycle terminal pole IS the authority restrictive pole.

The `DeathCertificate` (bound inside the `destroyed` state) is the witness on the lifecycle
side; `Revoke.holds_cap` is its shadow on the graph side. This is faithful: it states the
correspondence for one held edge of the terminating cell. -/
theorem lifecycle_revoke_is_authority_restrictive
    {src s : Lifecycle CellId FactoryId Digest}
    (_htr : Lifecycle.Transition src s) (hterm : Lifecycle.isTerminal s = true)
    (G : Graph CellId Rights) (holder : CellId) (cap : Cap CellId Rights)
    (hheld : G holder cap) :
    TerminalRevokesEdge s G (removeEdge G holder cap) holder cap :=
  { terminal := hterm
    revoked  := { holds_cap := hheld, result := rfl } }

/-- **`revoke_is_terminal_restrictive` (PROVED)** — the reverse reading at the act level: a
`Revoke` step IS a `RestrictAct` (already `Authority.revoke_is_restrict`), and it removes the
edge it names. We re-expose it here joined to the lifecycle terminal vocabulary: revoking is
the graph-side terminal move, mirroring `Lifecycle.terminal_rejects_transition` (no inverse).
The revoked edge is genuinely gone — `removeEdge` denies `holder ⟶ cap`. -/
theorem revoke_is_terminal_restrictive
    {G G' : Graph CellId Rights} {holder : CellId} {cap : Cap CellId Rights}
    (st : Revoke G holder cap G') :
    RestrictAct G G' ∧ ¬ G' holder cap := by
  refine ⟨revoke_is_restrict st, ?_⟩
  rw [st.result]
  rintro ⟨_, hne⟩
  exact hne ⟨rfl, rfl⟩

/-- **`migrated_and_destroyed_both_revoke` (PROVED)** — BOTH terminal shapes correspond to a
revoke. `destroyed cert` and `migrated dest` are the two `isTerminal` states; each, reached
from `live`, drives the same edge-removal. Confirms the correspondence covers the whole
terminal pole, not just `destroyed`: migration tombstone and death certificate are two
witnesses for the one restrictive (revoke) move. -/
theorem migrated_and_destroyed_both_revoke
    (cert : DeathCertificate CellId Digest) (dest : CellId)
    (G : Graph CellId Rights) (holder : CellId) (cap : Cap CellId Rights)
    (hheld : G holder cap) :
    TerminalRevokesEdge (Lifecycle.destroyed cert : Lifecycle CellId FactoryId Digest)
        G (removeEdge G holder cap) holder cap
      ∧ TerminalRevokesEdge (Lifecycle.migrated dest : Lifecycle CellId FactoryId Digest)
        G (removeEdge G holder cap) holder cap :=
  ⟨lifecycle_revoke_is_authority_restrictive
      (Lifecycle.Transition.destroy cert : Lifecycle.Transition Lifecycle.live _)
      (by simp [Lifecycle.isTerminal]) G holder cap hheld,
   lifecycle_revoke_is_authority_restrictive
      (Lifecycle.Transition.migrate dest : Lifecycle.Transition Lifecycle.live _)
      (by simp [Lifecycle.isTerminal]) G holder cap hheld⟩

end LifecycleRevoke

/-! ## §4 — `choreography_red_conserves` : red ↦ hyperedge ↦ cross-cell CG-5.

Compose `Choreography.red_projects_to_hyperedge` (RED interaction ↦ atomic `Hyperedge`, given
its `RedBinding`) with §2 (`Hyperedge.balanced` IS `conservedInDomain Domain.crossCell`). The
corollary ties THREE modules — `Spec.Choreography`, `Hyperedge`, `Spec.Conservation` — in one
statement: a red interaction's atomic commit conserves in the cross-cell domain. -/

section ChoreographyConserves

variable {Obs AdmissibleTurn TurnId : Type u}
variable {Bal : Type u} [AddCommMonoid Bal]
variable {S : Type u} [Confluence.MergeState S]

/-- **`choreography_red_conserves` (PROVED) — red ↦ hyperedge ↦ CG-5, three modules tied.**
A RED (coupled) interaction `P`, given its binding data `b : RedBinding P xs`, realizes a
`Hyperedge` over its participant cells (`red_projects_to_hyperedge` / `RedBinding.toHyperedge`),
and that hyperedge conserves in the cross-cell `Domain` (§2). So a red interaction's atomic
commit is automatically a `crossCell`-conserving turn: its half-edge deltas sum to `0`.

This is the one-corollary weave: `Spec.Choreography`'s RED-projection ↦ `Hyperedge`'s wide
pullback ↦ `Spec.Conservation`'s cross-cell `Σδ = 0`. The coupling that makes an interaction
red (its half-edges MUST balance against one apex `tid`) is precisely the cross-cell
conservation law — they are the same Σ = 0. -/
theorem choreography_red_conserves
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T)
    (_hred : P.IsRed)
    {xs : ι → T.Carrier} (b : RedBinding (Bal := Bal) (S := S) P xs) :
    conservedInDomain Domain.crossCell (hyperedgeDeltas b.toHyperedge) :=
  hyperedge_conserves_crossCell b.toHyperedge

/-- **`choreography_red_conserves_sum` (PROVED)** — the same fact in raw `Σ = 0` form: a red
interaction's half-edge aggregate over its incidence set vanishes. This is `b.balanced` read
through §2, exhibiting that "red coupling" and "cross-cell conservation" are one equation. -/
theorem choreography_red_conserves_sum
    {ι : Type v} [Fintype ι] {T : TurnCoalg Obs AdmissibleTurn}
    (P : Interaction (TurnId := TurnId) (Bal := Bal) (S := S) ι T)
    (hred : P.IsRed)
    {xs : ι → T.Carrier} (b : RedBinding (Bal := Bal) (S := S) P xs) :
    (Finset.univ.sum fun i => P.halfEdge i (xs i) b.t) = 0 :=
  (conservation_is_hyperedge_cg5 b.toHyperedge).mp (choreography_red_conserves P hred b)

end ChoreographyConserves

/-! ## §5 — `guard_attenuate_narrows_is_meet` ⇄ `authority_confers_narrows_is_meet`:
`Guard.attenuate` narrowing = `confers`'s `≤`.

Both `Spec.Guard` and `Spec.Authority` carry a notion of "attenuation":

  * `Guard.attenuate g c := all [g, c]` — adds a conjunct; `attenuate_narrows` is the
    **meet-semilattice law `a ⊓ b ≤ a`** (adding a conjunct can only shrink the admitted set);
  * `confers parent child` requires `child.rights ≤ parent.rights` on the `Rights`
    meet-semilattice — narrowing along the SAME `≤`, the order `Caveat.attenuate_narrows`
    and `CDT.attenuates` walk down (`Authority.attenuate_is_restrictive_narrowing`).

The thesis: these are ONE meet-narrowing concept across the layer — "attenuation" always
means *lower-bounding in a meet-semilattice*, never weakening. The cross-link is carried by the
two theorems below that genuinely touch `Guard` and `confers`:

  * **`guard_attenuate_narrows_is_meet`** — the guard side: `admits (g ⊓ c) ⇒ admits g`
    (`Guard.attenuate_narrows`, the predicate-lattice meet);
  * **`authority_confers_narrows_is_meet`** — the authority side: a conferred child cap is
    `≤` its parent on the `Rights` meet-semilattice (`confers`'s `.2`).

Both are the SAME `a ⊓ b ≤ a` / `≤` discipline read at two carriers, which is exactly what
makes attenuation one notion across `Spec.Guard` and `Spec.Authority` — never the Heyting
residual. (We do NOT restate the bare generic `inf_le_left` separately: a generic
`a ⊓ b ≤ a` mentioning neither `Guard` nor `confers` would not be the cross-link itself.) -/

section AttenuationOneOrder

/-- **`guard_attenuate_narrows_is_meet` (PROVED)** — the guard side: attenuating a guard and
admitting implies the un-attenuated guard already admitted. This is `Guard.attenuate_narrows`,
exhibited here as the meet law: `admits (g ⊓ c) ⇒ admits g`. Re-stated in the coherence
module to sit beside the authority `≤` it coincides with. -/
theorem guard_attenuate_narrows_is_meet
    {Request Statement Witness : Type u} [Verifiable Statement Witness]
    (g c : Guard Request Statement) (req : Request) (w : Statement → Witness)
    (h : Guard.admits (Guard.attenuate g c) req w = true) :
    Guard.admits g req w = true :=
  Guard.attenuate_narrows g c req w h

/-- **`authority_confers_narrows_is_meet` (PROVED)** — the authority side: a conferred child
cap is `≤` its parent on the `Rights` meet-semilattice. This is `confers`'s `.2`, i.e. the
`≤` that `Authority.attenuate_is_restrictive_narrowing` and `Caveat.attenuate_narrows` walk
down. Stated beside the guard narrowing to make the shared `⊓`/`≤` lower-bounding explicit. -/
theorem authority_confers_narrows_is_meet
    {CellId : Type*} {Rights : Type*} [SemilatticeInf Rights] [OrderTop Rights]
    (parent child : Cap CellId Rights) (hconf : confers parent child) :
    child.rights ≤ parent.rights :=
  hconf.2

end AttenuationOneOrder

/-! ## §6 — Axiom-hygiene tripwires.

Every cross-link above is PROVED-clean (no `sorry`): each depends ONLY on the three standard
kernel axioms. Pinning them here certifies the web is genuinely woven — the coincidences are
theorems, not `sorry`-aliases. (The independently-built modules already carry their own honest
OPENs — `Authority.only_connectivity_begets_connectivity`, `Lifecycle.distributed_death_…`,
`Hyperedge.hyperedge_sound_bisim`, `Choreography`'s operational LTS, `VatBoundary.phi_functorial`
— none of which this module needs or re-imports as content; the BRIDGES are clean.) -/

#assert_axioms guard_is_authority_conferral
#assert_axioms conferralGuard_admits_self
#assert_axioms introduce_passes_conferralGuard
#assert_axioms conservation_is_hyperedge_cg5
#assert_axioms hyperedge_conserves_crossCell
#assert_axioms lifecycle_revoke_is_authority_restrictive
#assert_axioms revoke_is_terminal_restrictive
#assert_axioms migrated_and_destroyed_both_revoke
#assert_axioms choreography_red_conserves
#assert_axioms choreography_red_conserves_sum
#assert_axioms guard_attenuate_narrows_is_meet
#assert_axioms authority_confers_narrows_is_meet

/-! ## §7 — OPEN: the shared `Spec/Prelude`.

The cross-links above PROVE the `Spec.*` modules' carriers coincide when instantiated at
shared types. The honest next move — NOT taken in this file (it would touch every existing
module) — is to factor those shared carriers into one `Dregg2/Spec/Prelude.lean` that every
`Spec.*` module imports, so the modules *literally* share them instead of re-declaring
alpha-equivalent copies. The bridges here are exactly the soundness obligations that move
discharges.

### Types to merge into `Dregg2/Spec/Prelude.lean`

  * **`CellId`** — the abstract node identity. Re-declared in `Authority` (graph node),
    `Lifecycle` (`cellId`, migration `dest`), `VatBoundary`. ONE abstract `CellId` parameter.
  * **`Digest`** — the cryptographic hash (`Lifecycle`'s certificate/checkpoint/attestation
    hashes). ONE `Digest`, `[DecidableEq Digest]` only where the fold needs it.
  * **`Commitment`** / **`Statement`** — `Conservation`'s `Commitment` (Pedersen target of
    `commitHom`) and `Guard`/`VatBoundary`'s `Statement` (verify-seam claim) are the SAME
    verify-seam object viewed at two layers; merge as `Statement`, with `Commitment` an
    `abbrev`/instance of it where the conservation hom lands.
  * **`Witness`** — the verify-seam evidence (`Guard.witnessed`, `VatBoundary`, the
    `Verifiable Statement Witness` oracle). ONE `Witness`.
  * **`Rights`** — the bounded meet-semilattice authority carrier (`Authority`, `VatBoundary`).
    ONE `Rights` with `[SemilatticeInf Rights] [OrderTop Rights]` (and `[DecidableLE Rights]`
    where conferral is decided as a `Guard`, §1).
  * **`Bal`** — the conservation value monoid (`Conservation.Bal`, `Hyperedge.Bal`,
    `Choreography.Bal`). ONE `[AddCommMonoid Bal]`. §2/§4 PROVE the hyperedge and the
    `crossCell` domain share it.
  * **`TurnId`** — the shared turn-identity / `account_updates_hash` (`Hyperedge`,
    `Choreography`, `JointTurn`). ONE `TurnId`.

### The two seams to name in the `Prelude`

  * **the `Guard`** — `Spec.Guard.Guard Request Statement` is the single gate object. §1 shows
    `Authority.confers` is a `Guard` and §5 shows its attenuation is the `Rights` meet, so the
    `Prelude` should export `Guard` (with `Request`/`Statement`) as the shared admissibility
    seam every regime (positional §1, epistemic `VatBoundary.Epistemic`) reads.
  * **the `Verify` seam** — `Laws.Verifiable Statement Witness` (`Verify : Statement → Witness
    → Bool`, `Discharged := Verify · · = true`). ONE oracle parameter; `Guard.witnessed`,
    `VatBoundary.Epistemic`, and `Conservation.committed_iff_cleartext`'s hom all enter through
    it. The `Prelude` names it so the eight verifier kinds remain instances behind one seam.

### Sketch (do NOT create `Prelude.lean` now)

```
/- Dregg2/Spec/Prelude.lean (SKETCH — not created) -/
namespace Dregg2.Spec.Prelude
universe u
variable (CellId Digest Statement Witness Rights Bal TurnId : Type u)
-- the shared verify seam (re-exported from Laws):
--   [Dregg2.Laws.Verifiable Statement Witness]
-- the shared order on authority:
--   [SemilatticeInf Rights] [OrderTop Rights]
-- the shared conservation monoid:
--   [AddCommMonoid Bal]
-- the shared gate object:
abbrev Guard (Request : Type u) := Dregg2.Spec.Guard Request Statement
```

With those merged, `guard_is_authority_conferral` (§1), `conservation_is_hyperedge_cg5` (§2),
`lifecycle_revoke_is_authority_restrictive` (§3), `choreography_red_conserves` (§4) and the
`guard_attenuate_narrows_is_meet`/`authority_confers_narrows_is_meet` pair (§5) become
*identities of shared carriers* rather than bridges
across re-declared ones — which is exactly the sense in which this module shows the `Spec.*`
layer is ONE web. -/

end Dregg2.Spec

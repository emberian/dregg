/-
# Dregg2.Spec.Authority — the GENERATIVE half of the capability-graph dynamics.

The metatheory already carries the **restrictive** half of the capability law in two
places — `Dregg2.Authority.Caveat.attenuate_narrows` (appending a caveat can only narrow
the admissible set) and `Dregg2.Authority.CDT.path_attenuates` (authority only shrinks
down a derivation path). Both are *narrowing-only* laws: they discipline how an existing
edge may be weakened. Neither says ANYTHING about how an edge comes to exist in the first
place. That is the gap this module fills.

The object-capability model is fundamentally a **graph dynamics**:

  * **nodes** = cells (`CellId`);
  * **edges** = capabilities — a `Cap = { target, rights }` where `Rights` carries an
    **attenuation preorder** `≤` ("narrower-or-equal"), a bounded meet-semilattice
    (`SemilatticeInf` + `OrderTop`); a graph `G` records which cell `Holds` which cap.

On this graph there are exactly two families of authorized moves:

  * **GENERATIVE** ops grow the graph, each one AUTHORIZED by something already in it —
    `introduce` (Granovetter delegation), `amplify` (sealer/unsealer rights amplification),
    `mint` (powerbox/factory), `endow` (parenthood at creation);
  * **RESTRICTIVE** ops shrink it — `attenuate` (narrow an edge via `≤`), `revoke`
    (remove an edge, terminal).

Grounded in dregg1's *actual* enforcement, not invented:

  * `turn/src/executor/apply.rs : apply_introduce` enforces the FOUR-part introduce
    discipline verbatim — (1) the introducer has access to the recipient
    (`has_access(recipient)`, the Granovetter connectivity premise), (2) the introducer
    holds a cap to the target (`lookup_by_target`), (3) `is_attenuation(held, granted)`
    ("granted permissions exceed introducer's own — **amplification denied**"), (4) the
    target consents (`delegate != Impossible`). The result is `grant_with_expiry` — an
    attenuated edge with abstract expiry.
  * `apply_unseal` requires the actor to **hold** the unsealer capability
    (`lookup_by_target(unsealer_cap_id)` or `CapabilityNotHeld`) before it will recover a
    cap — amplification needs a held amplifier.
  * `cell/src/factory.rs : FactoryDescriptor.allowed_cap_templates` — a held factory cap
    mints a child cap that must CONFORM to the factory's contract.

The headline invariant is Miller's **"only connectivity begets connectivity"** (no edge
ex nihilo, no ambient authority): in any graph reachable from initial conditions by the
authorized ops, every edge traces back to an authorized generative act.

This reframes attenuation: `attenuate_narrows` / `path_attenuates` are the **conferral
sub-rule** (clause 3 of `introduce`, the `≤` premise), NOT the whole law. The spine is the
generative discipline; narrowing is one premise inside it.

Faithful Props throughout. `CellId`/`Rights`/`FactoryContract` are abstract; `Rights`
carries an order, never `Nat`.
-/
import Dregg2.Authority.Positional
import Dregg2.Authority.Caveat
import Dregg2.Confluence
import Dregg2.Core
import Dregg2.Tactics
import Mathlib.Order.Lattice
import Mathlib.Order.BoundedOrder.Basic

namespace Dregg2.Spec

-- The abstract carrier `Rights` is a bounded meet-semilattice throughout; individual lemmas
-- that touch only `≤` (not `⊓`/`⊤`) legitimately do not USE every instance, but we keep the
-- full carrier signature uniform across the module rather than `omit`-ing per-lemma.
set_option linter.unusedSectionVars false

/-! ## §1 — The carriers: cells, rights, caps, the graph.

`CellId` is the abstract node identity (the cell's data-model value-hash in the real
system — opaque, NEVER `Nat`). `Rights` is the abstract authority carrier with the
**attenuation order**: it is a bounded meet-semilattice. `a ≤ b` reads "`a` is
narrower-or-equal to `b`"; `⊤` is the full/root authority; `a ⊓ b` is the largest authority
narrower than both (the meet that `Caveat.attenuate` realizes on the request lattice and
`CDT.attenuates` on the rights lattice). The order's reflexivity/transitivity ARE the
conferral discipline (`is_attenuation`); we take them as a typeclass parameter rather than
re-deriving a concrete lattice, exactly as `Positional`/`Guard` keep their carriers
abstract behind the verify seam. -/

variable {CellId : Type*}
variable {Rights : Type*} [SemilatticeInf Rights] [OrderTop Rights]

/-- **A capability = a directed, rights-labelled edge** `holder ⟶ target @ rights`. The
edge's `rights` is the authority the holder may exert on `target`; it lives in the
attenuation order. (Expiry is modelled abstractly — an expired edge is simply one a
`revoke` step may remove; we do not carry a clock, only the *shape* of the dynamics.) -/
structure Cap (CellId Rights : Type*) where
  target : CellId
  rights : Rights

/-- **A capability graph** `G` — which cell holds which cap. A `Prop`-valued relation
`Holds h c` ("cell `h` holds cap `c`"), the abstract form of the per-cell c-list /
slot-table (`apply.rs` `cell.capabilities`). Kept relational (not a `Finset`) so the
reachable-graph closure (§4) can quantify over arbitrary initial conditions. -/
abbrev Graph (CellId Rights : Type*) := CellId → Cap CellId Rights → Prop

/-- `G.has h t` — cell `h` holds *some* cap to target `t` (the `has_access` /
`lookup_by_target`-succeeds predicate, forgetting the rights). The Granovetter connectivity
premise is stated in terms of this. -/
def Graph.has (G : Graph CellId Rights) (h t : CellId) : Prop :=
  ∃ r, G h ⟨t, r⟩

/-! ## §2 — The conferral discipline: non-amplifying attenuation.

The single inequality that clause 3 of `apply_introduce` checks: `is_attenuation(held,
granted)`. We name it so it reads as a relation between caps, and so the generative ops can
carry it as a premise. -/

/-- **`confers parent child`** — the conferral edge invariant: `child` confers no more
authority than `parent`, and (for a delegation) names the same target. This IS
`is_attenuation(parent.rights, child.rights)` lifted to caps; it is the rights-lattice `≤`,
the very order `Caveat.attenuate_narrows` and `CDT.attenuates` narrow along. It is a
*premise* of the generative ops, not the law itself. -/
def confers (parent child : Cap CellId Rights) : Prop :=
  child.target = parent.target ∧ child.rights ≤ parent.rights

/-- Conferral is reflexive: a cap confers itself (the identity delegation — `is_attenuation`
of a cap against itself always holds; cf. the implicit self-cap in `apply.rs`'s self-grant
branch). PROVED. -/
theorem confers_refl (c : Cap CellId Rights) : confers c c :=
  ⟨rfl, le_refl _⟩

/-- Conferral is transitive: chaining two non-amplifying delegations is non-amplifying. The
authority order's transitivity, lifted — this is the engine of `path_attenuates` at the
graph level. PROVED. -/
theorem confers_trans {a b c : Cap CellId Rights}
    (hab : confers a b) (hbc : confers b c) : confers a c :=
  ⟨hbc.1.trans hab.1, le_trans hbc.2 hab.2⟩

/-! ## §3 — The ops. Two families, behind two predicates.

Each op is a relation `G ⟶ G'` between a pre-graph and a post-graph. The *authorization*
premise lives in the relation; firing the op without its premise is simply not a member of
the relation. We expose each op, then fold them under `GenAct` / `RestrictAct`. -/

/-- The post-graph after **adding** the edge `h ⟶ c` to `G` (the `grant`/`record_grant`
effect — a held slot appears in a cell's c-list). Everything `G` held is still held; `h`
additionally holds `c`. -/
def addEdge (G : Graph CellId Rights) (h : CellId) (c : Cap CellId Rights) :
    Graph CellId Rights :=
  fun h' c' => G h' c' ∨ (h' = h ∧ c' = c)

/-- The post-graph after **removing** every edge held by `h` to a given target/rights (the
`revoke` effect — a slot is cleared). Terminal: nothing depends on it, it only subtracts. -/
def removeEdge (G : Graph CellId Rights) (h : CellId) (c : Cap CellId Rights) :
    Graph CellId Rights :=
  fun h' c' => G h' c' ∧ ¬ (h' = h ∧ c' = c)

/-! ### §3.1 — GENERATIVE ops (each authorized by something already in `G`). -/

/-- **`Introduce G consents holder recipient parent cap G'`** — Granovetter introduction
(`apply_introduce`). The held cap `parent` the introduction rides is an explicit PARAMETER of
the relation (so this stays a faithful `Prop` while keeping the held cap visible in the
signature — a `Prop`-structure cannot project a data field). The four-part discipline,
verbatim:

  1. `G.has holder recipient` — the holder has a cap to the recipient (the **connectivity**
     premise: you can only introduce someone you can already reach — *only connectivity
     begets connectivity*);
  2. `G holder parent` with `parent.target = cap.target` — the holder holds the cap `parent`
     to the introduced target (`lookup_by_target`);
  3. `confers parent cap` — the conferred `cap` is **non-amplifying** w.r.t. that held cap
     (`is_attenuation`, "amplification denied");
  4. `consents cap.target` — the target consents (`delegate != Impossible`);

and the result `G'` adds `recipient ⟶ cap` (the attenuated edge). The `recipient` gains a
cap to `cap.target` that the holder could already exert. -/
structure Introduce (G : Graph CellId Rights)
    (consents : CellId → Prop)
    (holder recipient : CellId) (parent cap : Cap CellId Rights)
    (G' : Graph CellId Rights) : Prop where
  /-- (1) connectivity: the holder can reach the recipient. -/
  connected : G.has holder recipient
  /-- (2) the holder holds the cap `parent`. -/
  holds_parent : G holder parent
  /-- (3) non-amplifying: the conferred cap attenuates the held one. -/
  nonAmplifying : confers parent cap
  /-- (4) the target consents to delegation. -/
  consented : consents cap.target
  /-- result: `recipient` now holds `cap`. -/
  result : G' = addEdge G recipient cap

/-- **`Amplify G actor amplifier recovered G'`** — sealer/unsealer rights amplification
(`apply_unseal`). The discipline: the recovered cap may appear ONLY if the `actor` **holds**
the `amplifier` cap (`lookup_by_target(unsealer_cap_id)` or `CapabilityNotHeld`). A held
amplifier is the authorizing edge; the result adds the `recovered` cap to the actor. -/
structure Amplify (G : Graph CellId Rights)
    (actor : CellId) (amplifier recovered : Cap CellId Rights)
    (G' : Graph CellId Rights) : Prop where
  /-- the actor holds the amplifier capability — the whole discipline of amplification. -/
  holds_amplifier : G actor amplifier
  /-- result: the actor recovers `recovered`. -/
  result : G' = addEdge G actor recovered

/-- A **factory contract** — the abstract `FactoryDescriptor.allowed_cap_templates`: a
predicate carving out which child caps a factory is permitted to mint. Abstract (never a
concrete enumeration here); a real factory instantiates it from its templates + field
constraints. -/
abbrev FactoryContract (CellId Rights : Type*) := Cap CellId Rights → Prop

/-- **`Mint G factory contract child G'`** — powerbox / factory minting (`cell/src/factory.rs`).
A held factory cap `factory` mints a `child` cap that must **conform** to the factory's
`contract` (`allowed_cap_templates`). The discipline: minting needs a held factory cap AND
contract conformance; the result endows the minter with the conforming child cap. -/
structure Mint (G : Graph CellId Rights)
    (minter : CellId) (factory : Cap CellId Rights)
    (contract : FactoryContract CellId Rights) (child : Cap CellId Rights)
    (G' : Graph CellId Rights) : Prop where
  /-- the minter holds the factory capability. -/
  holds_factory : G minter factory
  /-- the minted child conforms to the factory contract. -/
  conforms : contract child
  /-- result: the minter now holds the conforming child cap. -/
  result : G' = addEdge G minter child

/-- **`Endow G parent child cap G'`** — parenthood / creation endowment. A creating `parent`
cell endows a freshly-created `child` cell with `cap`, authorized by the parent holding a
cap to the endowed target (the creator may only endow authority it possesses — the same
non-ex-nihilo discipline, at creation time). -/
structure Endow (G : Graph CellId Rights)
    (parent child : CellId) (cap source : Cap CellId Rights)
    (G' : Graph CellId Rights) : Prop where
  /-- the parent holds the `source` cap it endows from. -/
  holds_source : G parent source
  /-- the endowed cap is non-amplifying w.r.t. the source. -/
  nonAmplifying : confers source cap
  /-- result: the child is endowed with `cap`. -/
  result : G' = addEdge G child cap

/-! ### §3.2 — RESTRICTIVE ops. -/

/-- **`Attenuate G holder cap narrowed G'`** — narrow an edge's rights via `≤`. The holder
holds `cap`; the result replaces it with a `narrowed` cap to the same target conferring
strictly-or-equally less authority (`confers cap narrowed`). This is `Caveat.attenuate` /
`CDT.attenuates` AS A GRAPH STEP: appending a caveat = narrowing an edge. -/
structure Attenuate (G : Graph CellId Rights)
    (holder : CellId) (cap narrowed : Cap CellId Rights)
    (G' : Graph CellId Rights) : Prop where
  /-- the holder holds the cap being narrowed. -/
  holds_cap : G holder cap
  /-- narrowing is non-amplifying (the meet-semilattice law, as a premise). -/
  narrows : confers cap narrowed
  /-- result: the narrowed edge replaces the original. -/
  result : G' = addEdge (removeEdge G holder cap) holder narrowed

/-- **`Revoke G holder cap G'`** — remove an edge (terminal). The holder holds `cap`; the
result no longer has it. -/
structure Revoke (G : Graph CellId Rights)
    (holder : CellId) (cap : Cap CellId Rights)
    (G' : Graph CellId Rights) : Prop where
  /-- the holder holds the cap being revoked. -/
  holds_cap : G holder cap
  /-- result: the edge is gone. -/
  result : G' = removeEdge G holder cap

/-! ## §3.3 — The unified acts: every op is `GenAct` or `RestrictAct`.

This is the "derived instances" discipline (NO flat coproduct): the legacy ops are the small
orthogonal primitives above; `GenAct`/`RestrictAct` are *derived* predicates that say "this
step is an authorized generative/restrictive act", each constructor wrapping one primitive. -/

/-- **An authorized GENERATIVE act** — the step adds an edge, authorized by an
already-present edge. Each constructor is one generative primitive; `introduce`/`mint`/
`amplify`/`endow` are all instances of "authorized generative act". -/
inductive GenAct (consents : CellId → Prop)
    (G : Graph CellId Rights) (G' : Graph CellId Rights) : Prop where
  | introduce {holder recipient : CellId} {parent cap : Cap CellId Rights}
      (h : Introduce G consents holder recipient parent cap G')
  | amplify {actor : CellId} {amplifier recovered : Cap CellId Rights}
      (h : Amplify G actor amplifier recovered G')
  | mint {minter : CellId} {factory : Cap CellId Rights}
      {contract : FactoryContract CellId Rights} {child : Cap CellId Rights}
      (h : Mint G minter factory contract child G')
  | endow {parent child : CellId} {cap source : Cap CellId Rights}
      (h : Endow G parent child cap source G')

/-- **An authorized RESTRICTIVE act** — the step narrows or removes an edge. `attenuate`/
`revoke` are instances of "restrictive act". -/
inductive RestrictAct (G : Graph CellId Rights) (G' : Graph CellId Rights) : Prop where
  | attenuate {holder : CellId} {cap narrowed : Cap CellId Rights}
      (h : Attenuate G holder cap narrowed G')
  | revoke {holder : CellId} {cap : Cap CellId Rights}
      (h : Revoke G holder cap G')

/-- **An authorized step** — either family. The full transition relation of the capability
graph. -/
inductive AuthStep (consents : CellId → Prop)
    (G : Graph CellId Rights) (G' : Graph CellId Rights) : Prop where
  | gen (h : GenAct consents G G')
  | restrict (h : RestrictAct G G')

/-! ## §4 — The reachable-graph closure.

`Reachable consents G0 G` — `G` is obtained from the initial graph `G0` by a finite sequence
of authorized steps. This is the closure over which the headline invariant is stated. -/

/-- **`Reachable consents G0 G`** — reflexive-transitive closure of `AuthStep` from `G0`. -/
inductive Reachable (consents : CellId → Prop)
    (G0 : Graph CellId Rights) : Graph CellId Rights → Prop where
  | refl : Reachable consents G0 G0
  | step {G G' : Graph CellId Rights}
      (prev : Reachable consents G0 G) (s : AuthStep consents G G') :
      Reachable consents G0 G'

/-! ## §5 — THE KEYSTONE THEOREMS. -/

/-- **`introduce_non_amplifying` (PROVED) — the "amplification denied" rule.** The cap an
`Introduce` step confers is `≤` the introducer's own held cap, on the rights attenuation
order. This rides clause 3 (`confers parent cap`) of the introduce discipline directly: the
conferred rights never exceed the held rights. This is the grounded
`is_attenuation(held, granted)` check (`apply.rs:2835`, "granted permissions exceed
introducer's own — amplification denied"), as a theorem of the dynamics. -/
theorem introduce_non_amplifying {G G' : Graph CellId Rights}
    {consents : CellId → Prop} {holder recipient : CellId} {parent cap : Cap CellId Rights}
    (step : Introduce G consents holder recipient parent cap G') :
    cap.rights ≤ parent.rights :=
  step.nonAmplifying.2

/-- **`introduce_same_target` (PROVED)** — companion: the conferred cap names the SAME target
as the held parent cap. Introduction re-shares an existing edge's target; it cannot conjure a
cap to a target the introducer could not already reach. -/
theorem introduce_same_target {G G' : Graph CellId Rights}
    {consents : CellId → Prop} {holder recipient : CellId} {parent cap : Cap CellId Rights}
    (step : Introduce G consents holder recipient parent cap G') :
    cap.target = parent.target :=
  step.nonAmplifying.1

/-- **`amplify_needs_held_amplifier` (PROVED) — the amplification discipline.** An `Amplify`
step succeeds only if the actor HOLDS the amplifier cap in the pre-graph. Rights
amplification is not ambient: it requires the sealer/unsealer edge already in the graph
(`apply_unseal`'s `lookup_by_target(unsealer_cap_id)` premise — `CapabilityNotHeld`
otherwise). -/
theorem amplify_needs_held_amplifier {G G' : Graph CellId Rights}
    {actor : CellId} {amplifier recovered : Cap CellId Rights}
    (step : Amplify G actor amplifier recovered G') :
    G actor amplifier :=
  step.holds_amplifier

/-- **`mint_needs_held_factory` (PROVED)** — minting needs a held factory cap; the powerbox
is not ambient. -/
theorem mint_needs_held_factory {G G' : Graph CellId Rights}
    {minter : CellId} {factory : Cap CellId Rights}
    {contract : FactoryContract CellId Rights} {child : Cap CellId Rights}
    (step : Mint G minter factory contract child G') :
    G minter factory :=
  step.holds_factory

/-- **`mint_conforms_to_contract` (PROVED)** — the minted child cap conforms to the factory's
contract (`allowed_cap_templates`); a factory cannot mint outside its declared constructor
contract. -/
theorem mint_conforms_to_contract {G G' : Graph CellId Rights}
    {minter : CellId} {factory : Cap CellId Rights}
    {contract : FactoryContract CellId Rights} {child : Cap CellId Rights}
    (step : Mint G minter factory contract child G') :
    contract child :=
  step.conforms

/-! ### §5.1 — Attenuation reframed as a SUB-RULE.

The two narrowing laws already in the metatheory (`Caveat.attenuate_narrows`,
`CDT.path_attenuates`) are exactly clause 3 of the generative ops — the `confers` premise.
We make this literal: every generative op that re-shares a target (introduce/endow/attenuate)
carries `confers source result`, whose `.2` IS the `≤` of the narrowing laws. -/

/-- **`gen_conferral_is_attenuation` (PROVED) — the reframing.** For an `Introduce` step, the
conferral premise `confers parent cap` is precisely `Caveat`/`CDT`-style narrowing: the
conferred rights are `≤` the held rights. So `attenuate_narrows`/`path_attenuates` are the
*conferral sub-rule* of the generative law, NOT the spine — the spine is the four-part
generative discipline, of which this `≤` is clause 3. -/
theorem gen_conferral_is_attenuation {G G' : Graph CellId Rights}
    {consents : CellId → Prop} {holder recipient : CellId} {parent cap : Cap CellId Rights}
    (step : Introduce G consents holder recipient parent cap G') :
    cap.rights ≤ parent.rights ∧ cap.target = parent.target :=
  ⟨step.nonAmplifying.2, step.nonAmplifying.1⟩

/-- **`attenuate_is_restrictive_narrowing` (PROVED)** — the restrictive `Attenuate` step's
narrowed cap is `≤` the original on the rights order: the graph-level form of
`Caveat.attenuate_narrows`. The same `≤`, now firing as a *restrictive* (not generative) act —
showing the meet-semilattice attenuation appears on BOTH sides of the dynamics, always as a
premise/effect, never as the whole law. -/
theorem attenuate_is_restrictive_narrowing {G G' : Graph CellId Rights}
    {holder : CellId} {cap narrowed : Cap CellId Rights}
    (step : Attenuate G holder cap narrowed G') :
    narrowed.rights ≤ cap.rights :=
  step.narrows.2

/-! ### §5.2 — The non-forgeability invariant: only connectivity begets connectivity.

The headline. We state it FAITHFULLY: every edge in a reachable graph either was present
initially or was added by an authorized generative act whose authorizing edge was itself
present in the immediately-preceding graph. "No edge appears ex nihilo." -/

/-- **`AddedByAuthorizedGen consents G G' h c`** — the edge `h ⟶ c` that is *new* in the
step `G ⟶ G'` was added by an authorized generative act, and that act's authorizing edge was
present in `G`. This is the per-step content of non-forgeability: a freshly-appearing edge
traces to (a) an authorized generative constructor, with (b) its authorizing edge already in
`G`. (Restrictive steps add nothing, so they never satisfy this and never need to.) -/
def AddedByAuthorizedGen (consents : CellId → Prop)
    (G G' : Graph CellId Rights) (h : CellId) (c : Cap CellId Rights) : Prop :=
  G' h c ∧ ¬ G h c ∧
    -- the new edge `h ⟶ c` is the result of some authorized generative constructor,
    -- whose authorizing edge is present in `G`:
    ( (∃ holder recipient parent, h = recipient ∧
        Introduce G consents holder recipient parent c G' ∧ G holder parent)
    ∨ (∃ amplifier, Amplify G h amplifier c G' ∧ G h amplifier)
    ∨ (∃ factory contract, Mint G h factory contract c G' ∧ G h factory)
    ∨ (∃ parent source, Endow G parent h c source G' ∧ G parent source) )

/-- **`gen_step_traces` (PROVED) — the per-step non-forgeability lemma, the core of the
headline.** If a single generative step `G ⟶ G'` makes an edge `h ⟶ c` appear that was NOT
in `G`, then that edge is `AddedByAuthorizedGen`: it came from one of the four authorized
generative constructors, and that constructor's authorizing edge was already present in `G`.
No generative step can fabricate an edge whose authority is not already grounded in `G`.

This is the inductive STEP of "only connectivity begets connectivity", fully proved: it
establishes that connectivity (`G holder parent` / `G actor amplifier` / `G minter factory` /
`G parent source`) is what begets the new connectivity (`G' h c`). -/
theorem gen_step_traces {consents : CellId → Prop} {G G' : Graph CellId Rights}
    (act : GenAct consents G G') {h : CellId} {c : Cap CellId Rights}
    (hnew : G' h c) (hold : ¬ G h c) :
    AddedByAuthorizedGen consents G G' h c := by
  refine ⟨hnew, hold, ?_⟩
  cases act with
  | @introduce holder recipient parent cap st =>
      -- The only new edge `addEdge G recipient cap` introduces is `recipient ⟶ cap`.
      have hres := st.result
      rw [hres, addEdge] at hnew
      rcases hnew with hG | ⟨heq, hceq⟩
      · exact absurd hG hold
      · subst heq; subst hceq
        exact Or.inl ⟨holder, h, parent, rfl, st, st.holds_parent⟩
  | @amplify actor amplifier recovered st =>
      have hres := st.result
      rw [hres, addEdge] at hnew
      rcases hnew with hG | ⟨heq, hceq⟩
      · exact absurd hG hold
      · subst heq; subst hceq
        exact Or.inr (Or.inl ⟨amplifier, st, st.holds_amplifier⟩)
  | @mint minter factory contract child st =>
      have hres := st.result
      rw [hres, addEdge] at hnew
      rcases hnew with hG | ⟨heq, hceq⟩
      · exact absurd hG hold
      · subst heq; subst hceq
        exact Or.inr (Or.inr (Or.inl ⟨factory, contract, st, st.holds_factory⟩))
  | @endow parent child cap source st =>
      have hres := st.result
      rw [hres, addEdge] at hnew
      rcases hnew with hG | ⟨heq, hceq⟩
      · exact absurd hG hold
      · subst heq; subst hceq
        exact Or.inr (Or.inr (Or.inr ⟨parent, source, st, st.holds_source⟩))

/-- **`restrict_step_adds_nothing` (PROVED)** — a restrictive step never makes a new edge
appear: if `G' h c` after a `RestrictAct` then `G h c` was already true. Restriction only
subtracts (revoke) or replaces-by-narrowing (attenuate); the narrowed edge it adds is the
holder's *own* re-shaped cap, governed by the generative trace at the point it was first
conferred. So the only source of genuinely-new edges is `GenAct` — which `gen_step_traces`
grounds. (The narrowed cap added by `attenuate` CAN be new; this lemma is stated for the
edges restriction *preserves*, and the `attenuate`-adds-a-narrowing case is exactly why the
whole-history invariant below is OPEN — see the note.) -/
theorem revoke_step_adds_nothing {G G' : Graph CellId Rights}
    {holder : CellId} {cap : Cap CellId Rights}
    (st : Revoke G holder cap G') {h : CellId} {c : Cap CellId Rights}
    (hnew : G' h c) : G h c := by
  have hres := st.result
  rw [hres, removeEdge] at hnew
  exact hnew.1

/-- **`only_connectivity_begets_connectivity` (the headline invariant — PROVED, closed).**
The whole-history non-forgeability closure over `Reachable`, with the per-step generative core
(`gen_step_traces`) discharged into it AND the residual whole-history (`attenuate`) thread now
closed by carrying a `confers`-stable origin witness.

The FULL invariant we want: *in any reachable graph `G`, every edge `h ⟶ c` traces — through
the finite step history — back to either an initial edge of `G0` or an authorized generative
act, possibly through subsequent NON-AMPLIFYING narrowings.* The faithful statement is the
disjunction below, **strengthened** (not weakened) from the naïve "edge itself is a generative
addition": an edge `h ⟶ c` in a reachable `G` either

  (a) **descends by conferral** from an edge `h ⟶ c0` present in the initial graph `G0`
      (`confers c0 c` — `c`'s authority is `≤` and same-target as an initial edge held by `h`),
      OR
  (b) **descends by conferral** from an edge `h ⟶ c0` that, at some step `Gpre ⟶ Gpost` along
      the history, was the new edge of an authorized generative act (`AddedByAuthorizedGen`).

The `confers c0 c` witness is the key. It is the SINGLE collapsed `confers`-chain (conferral is
reflexive AND transitive — `confers_refl`/`confers_trans` — so an arbitrarily long chain of
narrowings collapses to ONE `confers`). A directly-conferred edge uses `confers_refl` (chain
length 0, recovering the naïve statement); an `attenuate` step that re-shapes `h ⟶ cap` into
`h ⟶ narrowed` extends the predecessor's witness by ONE narrowing via `confers_trans`
(`confers c0 cap` then `confers cap narrowed` ⟹ `confers c0 narrowed`). No edge appears ex
nihilo, and no narrowing forges authority — that is exactly what the `confers`-witness pins.

WHAT IS PROVED: ALL FOUR induction cases. `refl` (initial edges, `confers_refl`); generative
steps (new edge grounded by `gen_step_traces`, witness `confers_refl`; pre-existing edge
inherits the IH); `revoke` (only removes edges — `revoke_step_adds_nothing` — inherit the IH);
and the formerly-OPEN `attenuate` case: the freshly-added narrowed edge inherits the removed
predecessor cap's origin witness, extended by one narrowing through `confers_trans`. The
`#assert_axioms` pin below (which errors on `sorryAx`) certifies the closure is axiom-clean. -/
theorem only_connectivity_begets_connectivity {consents : CellId → Prop}
    {G0 G : Graph CellId Rights} (reach : Reachable consents G0 G)
    {h : CellId} {c : Cap CellId Rights} (hedge : G h c) :
    -- (a) the edge descends by conferral from an initial edge held by `h`, OR
    -- (b) it descends by conferral from an edge added by an authorized generative act.
    (∃ c0, confers c0 c ∧ G0 h c0) ∨
    (∃ c0 Gpre Gpost, confers c0 c ∧ Reachable consents G0 Gpre ∧
       AuthStep consents Gpre Gpost ∧ AddedByAuthorizedGen consents Gpre Gpost h c0) := by
  -- Generalize the edge `(h, c)` into the motive: the `attenuate` case needs the IH at a
  -- DIFFERENT edge (the removed predecessor cap), so the induction must quantify over edges.
  revert h c
  induction reach with
  | refl =>
      -- In `G0` itself, every edge is an initial edge — chain length 0 (`confers_refl`).
      intro h c hedge
      exact Or.inl ⟨c, confers_refl c, hedge⟩
  | @step Gmid Gnext prev s ih =>
      -- Case on the last step.
      intro h c hedge
      cases s with
      | gen act =>
          by_cases hwas : Gmid h c
          · -- the edge already held before this step: inherit its trace from the IH verbatim.
            exact ih hwas
          · -- the edge is NEW at this generative step: `gen_step_traces` grounds it; the
            -- conferral witness is reflexive (`c` descends from itself).
            exact Or.inr ⟨c, Gmid, Gnext, confers_refl c, prev, AuthStep.gen act,
              gen_step_traces act hedge hwas⟩
      | restrict ract =>
          cases ract with
          | revoke st =>
              -- revoke only removes edges: the edge was present before; inherit the IH verbatim.
              exact ih (revoke_step_adds_nothing st hedge)
          | @attenuate holder cap narrowed st =>
              -- `Gnext = addEdge (removeEdge Gmid holder cap) holder narrowed`.
              have hres := st.result
              rw [hres, addEdge, removeEdge] at hedge
              rcases hedge with ⟨hmid, _⟩ | ⟨heq, hceq⟩
              · -- the edge survived the removal: it was present in `Gmid`; inherit the IH.
                exact ih hmid
              · -- the genuinely-new narrowed edge `holder ⟶ narrowed`. Its authority is the
                -- removed predecessor cap `holder ⟶ cap`'s authority, narrowed once. The IH (at
                -- the DIFFERENT edge `holder ⟶ cap`) traces the predecessor; `confers_trans`
                -- extends that witness by ONE narrowing (`confers cap narrowed`, the `≤` of
                -- `Caveat.attenuate_narrows`). No new authority is forged — the same origin
                -- witness, one narrowing deeper.
                subst heq; subst hceq
                rcases ih st.holds_cap with ⟨c0, hconf, hG0⟩ | ⟨c0, Gpre, Gpost, hconf, hr, hs, htr⟩
                · -- predecessor descends from an initial edge: extend the chain.
                  exact Or.inl ⟨c0, confers_trans hconf st.narrows, hG0⟩
                · -- predecessor descends from a generative addition: extend the chain.
                  exact Or.inr ⟨c0, Gpre, Gpost, confers_trans hconf st.narrows, hr, hs, htr⟩

/-! ## §6 — Derived: the legacy ops ARE instances of the unified acts.

Closing the "no flat coproduct; legacy ops as derived instances" loop: each primitive op is
recovered as a `GenAct`/`RestrictAct` constructor — a one-line lift, with a lemma witnessing
it. -/

/-- `introduce` is an authorized generative act. DERIVED. -/
theorem introduce_is_gen {G G' : Graph CellId Rights} {consents : CellId → Prop}
    {holder recipient : CellId} {parent cap : Cap CellId Rights}
    (st : Introduce G consents holder recipient parent cap G') : GenAct consents G G' :=
  .introduce st

/-- `mint` is an authorized generative act. DERIVED. -/
theorem mint_is_gen {G G' : Graph CellId Rights} {consents : CellId → Prop}
    {minter : CellId} {factory : Cap CellId Rights}
    {contract : FactoryContract CellId Rights} {child : Cap CellId Rights}
    (st : Mint G minter factory contract child G') : GenAct consents G G' :=
  .mint st

/-- `amplify` is an authorized generative act. DERIVED. -/
theorem amplify_is_gen {G G' : Graph CellId Rights} {consents : CellId → Prop}
    {actor : CellId} {amplifier recovered : Cap CellId Rights}
    (st : Amplify G actor amplifier recovered G') : GenAct consents G G' :=
  .amplify st

/-- `attenuate` is a restrictive act. DERIVED. -/
theorem attenuate_is_restrict {G G' : Graph CellId Rights}
    {holder : CellId} {cap narrowed : Cap CellId Rights}
    (st : Attenuate G holder cap narrowed G') : RestrictAct G G' :=
  .attenuate st

/-- `revoke` is a restrictive act (terminal). DERIVED. -/
theorem revoke_is_restrict {G G' : Graph CellId Rights}
    {holder : CellId} {cap : Cap CellId Rights}
    (st : Revoke G holder cap G') : RestrictAct G G' :=
  .revoke st

/-! ## §7 — Axiom-hygiene tripwires.

Pin the clean keystones: each depends ONLY on the three standard kernel axioms (no
`sorryAx`). The headline `only_connectivity_begets_connectivity` is NOW INCLUDED — its
formerly-OPEN attenuate-trace thread is closed (the narrowed edge inherits its predecessor's
origin witness via `confers_trans`), so the closure is axiom-clean and the pin certifies it. -/

#assert_axioms confers_refl
#assert_axioms confers_trans
#assert_axioms introduce_non_amplifying
#assert_axioms introduce_same_target
#assert_axioms amplify_needs_held_amplifier
#assert_axioms mint_needs_held_factory
#assert_axioms mint_conforms_to_contract
#assert_axioms gen_conferral_is_attenuation
#assert_axioms attenuate_is_restrictive_narrowing
#assert_axioms gen_step_traces
#assert_axioms revoke_step_adds_nothing
#assert_axioms introduce_is_gen
#assert_axioms mint_is_gen
#assert_axioms amplify_is_gen
#assert_axioms attenuate_is_restrict
#assert_axioms revoke_is_restrict
-- The headline closure is now axiom-clean: this pin errors on `sorryAx`, so its passing
-- compilation certifies the formerly-OPEN attenuate-trace thread is genuinely discharged.
#assert_axioms only_connectivity_begets_connectivity

end Dregg2.Spec

# LEARNINGS — The two laws: linear logic, session types & resource theory

> Axis: formalize dregg's two ambient laws — **Law 1 Conservation** (the linear/monoidal
> resource structure) and **Law 2 Ordering** (the session/sequencing structure) — for the Lean4
> core in `./metatheory`. Grounded in the six PDFs below; cross-referenced to
> `docs/rebuild/00-synthesis.md` §1, §2, §8. Markers: **[G]** = grounded in a read paper;
> **[F]** = forward design (my proposal, defensible but not in any paper).

## Papers read

1. **Girard, *Linear Logic: its syntax and semantics*** (`girard-linear-logic-syntax-semantics.pdf`).
   The origin text. Resources can't be copied (no contraction) or discarded (no weakening);
   `−◦` is *causal* implication ("spend $1 to get cigarettes; the $1 is gone"); two conjunctions
   `⊗` (both, parallel) vs `&` (choose one); exponential `!A` re-introduces copyable "situations."
   The decisive line for us: **"theory = linear logic + axioms + current state"**, where a state
   is consumed by a transition (the chemical equation `2H₂ + O₂ −◦ 2H₂O`).
2. **Coecke, Fritz, Spekkens, *A mathematical theory of resources*** (`mathematical-theory-of-resources-1409.5531.pdf`).
   A resource theory **is** a symmetric monoidal category (SMC) `(D, ∘, ⊗, I)` — objects =
   resources, morphisms = free (zero-cost) conversions (Def 2.1). The *core* invariant content
   distils to a **commutative preordered monoid** `(R, +, ⪰, 0)` ("theory of resource
   convertibility," Def 4.1). A **monotone** is any `M : R → ℝ` with `a ⪰ b ⟹ M(a) ≥ M(b)`
   (Def 5.1) — a conserved/monotone quantity.
3. **Lindley & Morris, *Sessions as Propositions*** (`sessions-as-propositions-1406.3479.pdf`).
   Propositions-as-sessions: linear-logic propositions = session types, proofs = π-calculus
   processes, **cut-elimination = communication**. A session type is an *ordered* protocol
   (`!T.S`, `?T.S`, `⊕`, `&`, `end`); `fork`/`link`/`cut` connect dual endpoints; duality `S̄`.
4. **van den Heuvel & Pérez, *Comparing Session Type Systems derived from Linear Logic*** (`comparing-session-type-systems-linear-logic-2401.14763.pdf`).
   Classical (one-sided, single rule/connective) vs **intuitionistic** (two-sided `Γ; Δ ⊢ Λ`,
   **rely-guarantee** reading, enforces **locality**: a received channel can't become a server).
   Cut = parallel composition + connection; progress = no stuck states.
5. **Fu, Xi, Das, *Dependent Session Types for Verified Concurrent Programming*** (`dependent-session-types-verified-concurrency-2510.19129.pdf`).
   TLLᶜ. **Separates *protocol* from *channel type*** via dual constructors `ch⟨P⟩` / `hc⟨P⟩`
   (provider/client of the same protocol). Dependent session types let a *sequential* program be
   the *specification* of a concurrent one (relational verification). Intuitionistic chosen
   because it supports recursion without a self-dual operator.
6. **Selinger, *A survey of graphical languages for monoidal categories*** (`selinger-graphical-languages-monoidal-0908.3347.pdf`).
   The string-diagram bestiary + **coherence theorems** (equational reasoning = diagram
   deformation). Key formal fact for us (§6): a **cartesian** (finite-product) category =
   an SMC equipped with *natural* **copy** `Δ_A : A → A⊗A` and **erase** `◇_A : A → I` maps.
   Symmetric = braiding self-inverse `c_{A,B} = c_{B,A}⁻¹`.

## Key ideas (attributed)

- **[G, Girard]** Conservation = *absence of structural rules*. Weakening = "spend $1 for
  nothing" (discard a resource); contraction = "the petrol is not consumed by the motion" (copy a
  resource). Both are *exactly* the things conservation forbids. `⊗` is the conjunction where
  **both** happen and proportions matter; `&` is external choice ("if-then-else"). The state-as-
  formula / transition-as-`−◦` reading is *literally* dregg's turn: a turn `−◦` consumes the
  pre-state's resources and produces the post-state's.
- **[G, Coecke-Fritz]** Two-layer structure. (a) Rich layer: an **SMC** of resources+conversions
  — `⊗` = parallel combination, `∘` = sequencing, `I` = void resource. (b) **Forgetful "core"
  layer**: collapse each hom-set to "is there *any* conversion?" → a **commutative preordered
  monoid** `(R,+,⪰,0)`. *The monoid varies independently of the preorder* (their explicit
  result). **Monotones** `M : R→ℝ` are the conserved/quantitative quantities; "any measure is a
  crude shadow of the preorder" — the preorder is primary.
- **[G, Coecke-Fritz]** Free resources = `{A : D(I,A) ≠ ∅}` — reachable from nothing at zero cost.
  *Catalysis*: `c` enables `a→b` when `a⊁b` but `a+c ⪰ b+c` — a resource present-but-not-consumed.
- **[G, Lindley-Morris]** Ordering lives in the *sequent of connectives*; **a session type is an
  ordering of arrows**. Communication = cut-elimination = composing two dual proofs along a
  channel. `fork` opens a channel; `link`/`↔` is the forwarder (identity on a channel).
- **[G, van den Heuvel-Pérez]** **Intuitionistic** linear logic gives the *rely-guarantee*
  reading `Γ; Δ ⊢ Λ` ("relies on Δ, guarantees Λ") and **enforces locality** — a structural
  property: authority received over a channel cannot be re-served. Classical LL is more
  permissive (more typable processes) but *loses* locality.
- **[G, Fu-Xi-Das]** **Protocol ⊥ channel-type** separation; provider/client are `ch⟨P⟩`/`hc⟨P⟩`
  duals of one protocol `P`. Dependent session types make a sequential reference implementation
  the *spec* of the concurrent one.
- **[G, Selinger]** The copy/erase maps are *precisely the line* between cartesian and merely
  monoidal. A category that has them is cartesian (values are freely duplicable/discardable); one
  that *withholds* them is linear/resource-respecting. Coherence: any equation provable from the
  SMC axioms = any diagram deformation — so "string-diagram reasoning about turns" is sound.

## Takeaways for dregg (idea → move; map to synthesis §/Lean)

| # | Idea (paper) | Move for dregg | Maps to |
|---|---|---|---|
| T1 | Resource theory = SMC; core = preordered monoid (Coecke-Fritz) | **Law 1 = a symmetric-monoidal structure on the turn-category**, not (only) a typing discipline. Objects = cell-states, `⊗` = "these cells side-by-side" (multi-cell turn), `I` = the empty configuration. **[F]** | synthesis §1 (Law 1), §8.2 |
| T2 | Monotone `M:R→ℝ`, `a⪰b⟹M(a)≥M(b)` (Coecke-Fritz Def 5.1) | **`LinearityClass` conservation = a monotone** (actually a stricter *invariant*: equality, not ≥). Per class `k`, the total `Σ_k : Ob → ℕ` (or `→ℤ`) is a **strong monoidal functor to `(ℕ,+,0)`** — `Σ_k(A⊗B)=Σ_k(A)+Σ_k(B)` and every turn *preserves* it. **[F, grounded in [G] machinery]** | §1, §8.2 |
| T3 | No-weakening / no-contraction (Girard) | The turn-category must **not be cartesian**: forbid natural copy `Δ` and erase `◇` (Selinger §6). This *is* conservation stated structurally — a linear resource cannot be silently duplicated or dropped. **[G→F]** | §1, §8.2; §5.2 "Fork is not a coproduct" |
| T4 | State-as-formula, transition-as-`−◦` (Girard) | A turn **is** a linear implication `pre −◦ post` over the multiset of cell-resources; `EffectVM` honoring conservation = checking the `−◦` is a *valid linear sequent*. The chemical-equation reading is the honest model of `action.rs:698`'s exhaustive `LinearityClass` match. **[G]** | §1, §5.1 (LinearityClass keeper) |
| T5 | Session type = ordered protocol; cut = communication (Lindley-Morris) | **Law 2 (Ordering) = a session protocol per strand.** "Which arrows compose into which strand" = the sequence of dual sends/receives along a channel. The **held-until-commit** discipline = a session that is *not closed* (`end`) until the transaction commits — outgoing effects are the un-sent suffix of the protocol. **[G→F]** | §1 (Law 2), §1 "turn = transaction held until commit" |
| T6 | Intuitionistic = rely-guarantee + **locality** (van den Heuvel-Pérez) | **The membrane is an intuitionistic cut.** Inside a trust-root: `Γ; Δ ⊢ Λ` rely-guarantee, no witness — local composition. **Crossing a membrane = the cut where the `?`/`!` (client/server) sides meet across the boundary**, and *locality* is exactly "a capability received across the membrane cannot be re-served" — the structural twin of caps→keys lossiness. **[G→F]** | §2.2 (membrane = caps↔keys), §8.4 (membrane law) |
| T7 | Protocol ⊥ channel-type; `ch⟨P⟩`/`hc⟨P⟩` (Fu-Xi-Das) | **Separate the *turn-protocol* from the *channel/endpoint*.** dregg's `BindingSite` + `WitnessedPredicate` is the protocol; the cell endpoint is `ch⟨P⟩`/`hc⟨P⟩`. This is the clean type-level home for the `Predicate ⊣ Witness` adjunction: the *predicate* is the protocol, the *witness* is a proof the channel followed it. **[F]** | §3.1 (universal gate), §8.4 |
| T8 | Dependent session ⇒ sequential spec for concurrent impl (Fu-Xi-Das) | **The Lean core IS the sequential reference; Rust is the concurrent impl.** This is *exactly* the decided differential-testing architecture (synthesis §9.1: "Lean = golden oracle"). Dependent session types are the principled justification that a sequential oracle can certify a concurrent system. **[G→matches existing decision]** | §9.1 |
| T9 | Free resources `D(I,A)≠∅`; catalysis (Coecke-Fritz) | **Free = mintable-from-nothing** (a genesis cell / a `None`-permission grant). **Catalyst = a capability held but not consumed** by a turn — the read-only / attenuating cap. Gives a clean account of which authorities a turn *spends* vs *merely reads*. **[F]** | §5.1 (permission lattice), §3.2 (intent conservation) |

## Tensions & corrections (over-claims to avoid)

- **C1 — "thin posetal category" is *too small* for Law 1. [G, decisive]** A thin/posetal category
  (`Preorder.smallCategory`) has **≤1 morphism per hom-set** — it cannot carry a monoidal product
  with a *symmetry isomorphism* (the symmetry `c_{A,B}: A⊗B → B⊗A` and its inverse are *distinct
  data* that the coherence pentagon/hexagon constrain; in a thin category they collapse to
  triviality and you lose the structure that makes parallel composition mean anything). The
  synthesis §1 "thin posetal" claim is honest for the *ordering skeleton* (Law 2, where "is there
  a strand from S to S'" is a preorder) but **breaks for conservation**: multi-cell parallel turns
  need genuine `⊗` with non-trivial morphisms. **Verdict: the base is a (symmetric) monoidal
  category that is *thin in its ordering fragment*, not thin overall.** Resolve by splitting:
  the **convertibility preorder** (Law 2 skeleton) is thin; the **resource SMC** (Law 1) is not.
  This is precisely Coecke-Fritz's two-layer split (SMC vs. preordered-monoid core) — adopt it.
- **C2 — Fork is **not** a coproduct (synthesis §1 already flags; now *proved* via Selinger §6).
  [G]** A coproduct `A+B` has *injections* and a universal co-pairing; in a resource setting that
  would let you *merge two histories for free*, which is the dual of copy — and resource
  categories specifically *lack* the cartesian/cocartesian maps. Fork (splitting authority) and
  merge (re-rooting) are **monoidal `⊗`-manipulations plus side conditions** (cap-spine §4.2's
  "merge = re-root iff every edge stays a monotone attenuation"), **not** universal (co)products.
  Calling Fork a coproduct re-imports copy/discard and silently breaks conservation.
- **C3 — Conservation is *stronger* than a Coecke-Fritz monotone. [G→F]** A monotone only requires
  `M(a) ≥ M(b)` (non-increase) under a free conversion. dregg's `LinearityClass` sum is
  **conserved = invariant** (`=`, not `≥`) along an internal turn — minting/burning are *explicit
  typed effects*, not silent decreases. So the precise statement is: **`Σ_k` is a monoidal
  functor `(TurnCat, ⊗, I) → (ℕ, +, 0)` that is *constant on every hom-set*** (every turn `f:A→B`
  has `Σ_k(A)=Σ_k(B)`), except on the distinguished `Mint_k`/`Burn_k` generators where it changes
  by a declared amount. Don't under-claim it as mere monotonicity.
- **C4 — Classical vs intuitionistic LL is a *real* design fork, not cosmetic. [G]** The membrane
  wants **intuitionistic** (locality is the property we need: received authority can't be
  re-served = the caps→keys lossiness is structural). Classical LL is more permissive but drops
  locality. **Pick intuitionistic linear/session logic for the membrane law** (also matches
  Fu-Xi-Das's recursion argument). Recording classical's extra expressiveness as a *known
  trade*, not an accident.
- **C5 — `Predicate ⊣ Witness` is an *adjunction between thin categories* = a Galois connection.
  [G→F]** Because both the predicate lattice (Heyting) and the witness order are posetal, the
  adjunction is *not* a heavyweight `CategoryTheory.Adjunction` — it's an `Order.GaloisConnection`
  (`Predicate` left adjoint / lower, `Witness` right adjoint / upper, or vice-versa per
  orientation). This is *much* cheaper to build in Lean and is honest about "half-wired": a
  Galois connection with one direction `NotYetWired` is a *partial* `GaloisConnection` /
  `GaloisCoinsertion` stub.

## Proposed Lean/metatheory artifacts

All names verified present in `~/src/mathlib4` (2026-05-29). **[F]** unless noted.

### 1. Base category (the ordering skeleton, thin)
```lean
-- Cell-state configurations; thin ordering fragment = "is there a strand S ⟶ S'".
-- mathlib: CategoryTheory.Category, and Preorder ⇒ smallCategory for the thin part.
structure CellState : Type            -- objects
-- Law-2 reachability preorder (thin): use `Preorder StrandReach` →
--   `CategoryTheory.smallCategory` (Mathlib/CategoryTheory/Category/Preorder.lean)
```

### 2. Conservation = symmetric-monoidal structure (Law 1)
```lean
-- mathlib: CategoryTheory.MonoidalCategory, .SymmetricCategory (Monoidal/Braided/, Symmetric.lean)
variable {C : Type*} [Category C] [MonoidalCategory C] [SymmetricCategory C]
-- 𝟙_ C = empty configuration (I); ⊗ = cells side-by-side (multi-cell parallel turn)

-- A LinearityClass is an index k. Conservation = a strong monoidal functor to (ℕ,+).
-- mathlib: CategoryTheory.MonoidalFunctor ; target (ℕ, +, 0) as a Discrete/one-object
--   monoidal cat, OR phrase Σ_k directly as a function with the two laws below.
def Σ (k : LinearityClass) : C → ℕ
```
**Conservation theorem (the headline, [F] statement / [G] machinery):**
```lean
theorem conservation_preserved
    (k : LinearityClass) {A B : C} (f : A ⟶ B) (hf : ¬ f.IsMintBurn k) :
    Σ k A = Σ k B
-- and the monoidal compatibility (the "per-class sum" half):
theorem Σ_tensor (k) (A B : C) : Σ k (A ⊗ B) = Σ k A + Σ k B
theorem Σ_unit  (k)           : Σ k (𝟙_ C) = 0
-- Corollary: composition preserves the per-LinearityClass sum.
theorem conservation_comp (k) {A B D} (f : A ⟶ B) (g : B ⟶ D)
    (hf : ¬ f.IsMintBurn k) (hg : ¬ g.IsMintBurn k) : Σ k A = Σ k D
--   (by `conservation_preserved` twice + transitivity; the proof is the "all three spines
--    asserted it" claim, now machine-checked.)
```
*This is synthesis §8.2 made precise: "composition preserves the per-LinearityClass sum" is
`conservation_comp`.* **Non-cartesianity** (the no-copy/no-discard core of conservation) is
recorded as a *negative* lemma / design comment, contrasting with `Monoidal/Cartesian/Basic.lean`'s
`Δ`/`◇`: a `theorem not_cartesian : ¬ Nonempty (ChosenFiniteProducts C)` or simply *withholding*
the instance and proving `Σ` would be violated by any `Δ` (copy doubles the sum).

### 3. Ordering = session protocol (Law 2) + held-until-commit
```lean
-- A strand = a (dependent) session protocol; intuitionistic, two-sided rely/guarantee.
inductive Protocol      -- Send / Recv / Choose(⊕) / Offer(&) / End  (Lindley-Morris grammar)
structure Strand := (proto : Protocol) (committed : Bool)
-- held-until-commit: outgoing effects = the un-`End`ed suffix; commit = cut to End.
-- "which arrows compose into which strand" = a (thin) preorder on Strand prefixes.
```

### 4. The membrane law (the sharp target, synthesis §8.4)
```lean
-- TrustRoot (host/principal). A turn within one root needs no witness; crossing needs one.
def withinRoot (f : A ⟶ B) (r : TrustRoot) : Prop        -- intuitionistic cut, local
theorem membrane_law {A B} (f : A ⟶ B) :
    withinRoot f r ∨ RequiresWitness f
-- RequiresWitness = the Witness side of the Galois connection becomes mandatory.
-- Locality (van den Heuvel-Pérez): authority crossing out cannot be re-served inside.
```

### 5. The half-wired `Predicate ⊣ Witness` adjunction
```lean
-- BOTH sides are posets ⇒ a Galois connection, not a heavy Adjunction.
-- mathlib: Order.GaloisConnection (Mathlib/Order/GaloisConnection/Defs.lean),
--          Order.Heyting (Mathlib/Order/Heyting/Basic.lean) for the predicate lattice.
variable [HeytingAlgebra Pred]            -- the predicate algebra (synthesis §1)
def Witness  : Pred → WitnessOrder
def Predicate : WitnessOrder → Pred
theorem pred_witness_gc : GaloisConnection Predicate Witness   -- the wired direction
-- "half-wired": the other adjunct / the round-trip is `sorry`/`NotYetWired` — model as a
--   `GaloisCoinsertion` stub or an axiom flagged for discharge.
```

### 6. Monotone bridge (optional, ties to resource theory)
```lean
-- Coecke-Fritz Def 5.1: a monotone is an OrderHom to ℝ on the convertibility preorder.
-- mathlib: OrderHom (the `→o` bundled monotone map). Σ_k factors as such a monotone,
--   and conservation strengthens "monotone (≥)" to "invariant (=)" on non-mint/burn arrows.
```

### Recommended build order
1. `MonoidalCategory` + `SymmetricCategory` instance on `CellState` (Law 1 scaffold).
2. `Σ k` + `conservation_preserved` + `conservation_comp` (**the headline theorem**).
3. `GaloisConnection Predicate Witness` (the adjunction; half-wired stub honest).
4. `membrane_law` over `TrustRoot` (the architecture-resting claim).
5. Strand/Protocol (Law 2) last — it's the thin/ordering fragment and least load-bearing for the
   "does the generator generate?" stress test.

## Open questions / what to read next

- **Q1.** Is `LinearityClass` conservation better as one functor `Σ : C → (ℕ^K, +)` (vector of
  per-class sums) or `K` separate monotones? (Coecke-Fritz: the monoid can vary independently of
  the preorder — suggests the *vector* form is the honest monoid.) **[F]**
- **Q2.** Does the held-until-commit transaction need a **traced** monoidal structure (Selinger
  §5) to model the feedback of rollback/time-travel, or is plain SMC + a commit predicate enough?
  Selinger's trace = exactly "feedback loop"; rollback smells traced. Worth a focused read of
  Selinger §5 + §6.4 (traced coproduct) before committing.
- **Q3.** Classical-vs-intuitionistic for the *4-corners* regime (synthesis §9.2): off-diagonal
  corners (proof-carrying + single-writer) — does an off-diagonal membrane force classical LL
  (losing locality) at that corner? Re-read van den Heuvel-Pérez §4 (composition forms).
- **Q4.** Catalysis (Coecke-Fritz Def 4.8) as the formal model of **read-only / attenuating caps**
  (held, not consumed) — is the dregg attenuation order a sub-preorder of the convertibility
  preorder? **[F]**
- **Q5.** Dependent session types (Fu-Xi-Das `ch⟨P⟩`/`hc⟨P⟩`) as the Lean *channel* type for the
  CapTP near/far membrane — read their metatheory (soundness as term *and* process calculus) for
  the differential-testing oracle obligation (synthesis §9.1).
- **Not yet read, likely relevant to this axis:** `string-diagrams-closed-symmetric-monoidal-csl2026.pdf`
  (mechanized string diagrams — possible Lean tactic support), `handlers-of-algebraic-effects-*`
  / `effective-concurrency-algebraic-effects.pdf` (effects-as-the-EffectVM-semantics, the `−◦`
  operational side), `expressive-power-one-shot-control-2509.11901.pdf` (the await/continuation
  family, ties to synthesis §3).
